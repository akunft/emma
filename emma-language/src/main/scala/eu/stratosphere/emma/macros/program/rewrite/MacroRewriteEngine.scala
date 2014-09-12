package eu.stratosphere.emma.macros.program.rewrite

import eu.stratosphere.emma.macros.program.ContextHolder
import eu.stratosphere.emma.macros.program.dataflow.IntermediateRepresentation
import eu.stratosphere.emma.macros.program.util.ProgramUtils
import eu.stratosphere.emma.rewrite.RewriteEngine

import scala.reflect.macros.blackbox.Context

trait MacroRewriteEngine[C <: Context]
  extends ContextHolder[C]
  with IntermediateRepresentation[C]
  with ProgramUtils[C]
  with RewriteEngine {

  import c.universe._

  val rules: List[Rule] = List(SimplifyTupleProjection, UnnestHead, UnnestGenerator)

  object UnnestGenerator extends Rule {

    case class RuleMatch(parent: Comprehension, generator: ComprehensionGenerator, child: Comprehension)

    override protected def bind(r: ExpressionRoot) = new Traversable[RuleMatch] {
      override def foreach[U](f: (RuleMatch) => U) = {
        for (x <- sequence(r.expr)) x match {
          case parent@Comprehension(_, _, qualifiers) =>
            for (y <- qualifiers) y match {
              case generator@ComprehensionGenerator(_, child@Comprehension(_, ScalaExpr(_, _), _)) =>
                f(RuleMatch(parent, generator, child))
              case _ => Unit
            }
          case _ => Unit
        }
      }
    }

    override protected def guard(r: ExpressionRoot, m: RuleMatch) = {
      val parentIsSink = m.parent.qualifiers.size == 1 && m.parent.head.isInstanceOf[ScalaExpr] && (m.parent.head.asInstanceOf[ScalaExpr].tree match {
        case Apply(Select(Ident(TermName("ofmt")), TermName("write")), Ident(TermName(name)) :: Nil) => name.startsWith("snk$record$")
        case _ => false
      })

      val childIsSource = m.child.qualifiers.size == 2 && m.child.head.isInstanceOf[ScalaExpr] && (m.child.head.asInstanceOf[ScalaExpr].tree match {
        case Ident(TermName(name)) => name.startsWith("src$record$")
        case _ => false
      })

      !(childIsSource || parentIsSink)
    }

    override protected def fire(r: ExpressionRoot, m: RuleMatch) = {
      val name = m.generator.lhs
      val term = m.child.head.asInstanceOf[ScalaExpr]
      val rest = sequence(m.parent)
        .span(_ != m.generator)._2.tail // trim prefix
        .span(x => !x.isInstanceOf[ComprehensionGenerator] || x.asInstanceOf[ComprehensionGenerator].lhs.toString != m.generator.toString)._1 // trim suffix

      val (xs, ys) = m.parent.qualifiers.span(_ != m.generator)
      m.parent.qualifiers = xs ++ m.child.qualifiers ++ ys.tail

      for (e <- rest; if e.isInstanceOf[ScalaExpr]) substitute(e.asInstanceOf[ScalaExpr], name.toString, term)
    }
  }

  object UnnestHead extends Rule {

    case class RuleMatch(join: MonadJoin, parent: Comprehension, child: Comprehension)

    override protected def bind(r: ExpressionRoot) = new Traversable[RuleMatch] {
      override def foreach[U](f: (RuleMatch) => U) = {
        for (x <- sequence(r.expr)) x match {
          case join@MonadJoin(parent@Comprehension(_, child@Comprehension(_, _, _), _)) =>
            f(RuleMatch(join, parent, child))
          case _ =>
            Unit
        }
      }
    }

    override protected def guard(r: ExpressionRoot, m: RuleMatch) = true //FIXME

    override protected def fire(r: ExpressionRoot, m: RuleMatch) = {
      m.parent.qualifiers = m.parent.qualifiers ++ m.child.qualifiers
      m.parent.head = m.child.head
      m.parent.monad = m.child.monad
      r.expr = substitute(r.expr, m.join, m.parent)
    }
  }

  object SimplifyTupleProjection extends Rule {

    val projectionPattern = "_(\\d{1,2})".r

    case class RuleMatch(expr: ScalaExpr)

    override protected def bind(r: ExpressionRoot) = new Traversable[RuleMatch] {
      override def foreach[U](f: (RuleMatch) => U) = {
        for (x <- sequence(r.expr)) x match {
          case expr@ScalaExpr(_, _) =>
            f(RuleMatch(expr))
          case _ =>
            Unit
        }
      }
    }

    override protected def guard(r: ExpressionRoot, m: RuleMatch) = containsPattern(m.expr.tree)

    override protected def fire(r: ExpressionRoot, m: RuleMatch) = {
      m.expr.tree = simplify(m.expr.tree)
    }

    object containsPattern extends Traverser with (Tree => Boolean) {

      var result = false

      override def traverse(tree: Tree): Unit = tree match {
        case Select(Apply(TypeApply(Select(tuple@Select(Ident(TermName("scala")), _), TermName("apply")), types), args), TermName(_)) =>
          val isTupleConstructor = tuple.name.toString.startsWith("Tuple") && tuple.symbol.isModule && tuple.symbol.companion.asClass.baseClasses.contains(symbolOf[Product])
          val isProjectionMethod = tree.symbol.isMethod && projectionPattern.findFirstIn(tree.symbol.name.toString).isDefined
          if (isTupleConstructor && isProjectionMethod) {
            result = true
          } else {
            super.traverse(tree)
          }
        case _ =>
          super.traverse(tree)
      }

      override def apply(tree: Tree): Boolean = {
        containsPattern.result = false
        containsPattern.traverse(tree)
        containsPattern.result
      }
    }

    object simplify extends Transformer with (Tree => Tree) {

      var result = false

      override def transform(tree: Tree): Tree = tree match {
        case Select(Apply(TypeApply(Select(tuple@Select(Ident(TermName("scala")), _), TermName("apply")), types), args), TermName(_)) =>
          val isTupleConstructor = tuple.name.toString.startsWith("Tuple") && tuple.symbol.isModule && tuple.symbol.companion.asClass.baseClasses.contains(symbolOf[Product])
          val projectionMatch = projectionPattern.findFirstMatchIn(tree.symbol.name.toString)
          if (isTupleConstructor && tree.symbol.isMethod && projectionMatch.isDefined) {
            val offset = projectionMatch.get.group(1).toInt
            if (args.size >= offset && types.size >= offset)
              q"${args(offset - 1)}"
            else
              super.transform(tree)
          } else {
            super.transform(tree)
          }
        case _ =>
          super.transform(tree)
      }

      override def apply(tree: Tree): Tree = transform(tree)
    }

  }

}
