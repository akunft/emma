package eu.stratosphere.emma.macros.program


import eu.stratosphere.emma.api.Algorithm
import eu.stratosphere.emma.ir.Workflow
import eu.stratosphere.emma.macros.program.controlflow.ControlFlow
import eu.stratosphere.emma.macros.program.dataflow.IntermediateRepresentation
import eu.stratosphere.emma.macros.program.rewrite.MacroRewriteEngine
import eu.stratosphere.emma.macros.program.util.{Counter, ProgramUtils}

import scala.collection.mutable.ListBuffer
import scala.language.existentials
import scala.language.experimental.macros


class WorkflowMacros(val c: scala.reflect.macros.blackbox.Context) {

  /**
   * Lifts the root block of an Emma program into a monatic comprehension intermediate representation.
   *
   * @return
   */
  def workflow(e: c.Expr[Any]): c.Expr[Workflow] = {
    new LiftHelper[c.type](c).execute(e)
  }

  /**
   * Entry macro for emma algorithms.
   */
  def parallelize[T: c.WeakTypeTag](e: c.Expr[T]): c.Expr[Algorithm[T]] = {
    new LiftHelper[c.type](c).parallelize[T](e)
  }

  private class LiftHelper[C <: scala.reflect.macros.blackbox.Context](val c: C)
    extends ContextHolder[c.type]
    with ProgramUtils[c.type]
    with ControlFlow[c.type]
    with IntermediateRepresentation[c.type]
    with MacroRewriteEngine[c.type] {

    import c.universe._

    val apiModule = rootMirror.staticModule("eu.stratosphere.emma.api.package")
    val srcCount = new Counter()
    val snkCount = new Counter()
    val loopCount = new Counter()

    /**
     * Translates an Emma expression to an Algorithm.
     *
     * @return
     */
    def parallelize[T: c.WeakTypeTag](root: Expr[T]): Expr[Algorithm[T]] = {

      val rootTree = c.untypecheck(root.tree)

      // ----------------------------------------------------------------------
      // Code analysis
      // ----------------------------------------------------------------------

      // 1. Create control flow graph
      val cfGraph = createCFG(rootTree)

      // 2. Identify and isolate maximal comprehensions (TODO)

      // 3. Analyze variable usage

      // ----------------------------------------------------------------------
      // Code optimizations
      // ----------------------------------------------------------------------

      // 1. Comprehension rewrite (TODO)

      // 2. Derive logical plans (TODO)

      // ----------------------------------------------------------------------
      // Final object assembly
      // ----------------------------------------------------------------------

      // construct algorithm object
      val algorithmCode =
        q"""
        object __emmaAlgorithm extends eu.stratosphere.emma.api.Algorithm[${c.weakTypeOf[T]}] {

           // required imports
           import eu.stratosphere.emma.api._
           import eu.stratosphere.emma.ir

           def run(engine: runtime.Engine): ${c.weakTypeOf[T]} = engine match {
             case runtime.Native => runNative()
             case _ => runParallel(engine)
           }

           private def runNative(): ${c.weakTypeOf[T]} = $rootTree

           private def runParallel(engine: runtime.Engine): ${c.weakTypeOf[T]} = { ..${compileDriver[T](cfGraph)} }
        }
        """

      // algorithm driver (original algorithm)
      // def run(): ${c.weakTypeOf[T]} = ${root.tree}

      // construct and return a block that returns a Workflow using the above list of sinks
      val block = Block(List(algorithmCode), c.parse("__emmaAlgorithm"))
      c.Expr[Algorithm[T]](c.typecheck(block))
    }

    /**
     * Lifts the root block of an Emma program into an intermediate representation.
     *
     * @return
     */
    def execute(root: Expr[Any]): Expr[Workflow] = root.tree match {
      case _: Block =>
        c.Expr(liftRootBlock(root.tree.asInstanceOf[Block]))
      case _ =>
        c.abort(c.enclosingPosition, "Emma programs may consist only of term expressions")
    }

    /**
     * Lifts the root block of an Emma program.
     *
     * @param e The root block AST to be lifted.
     * @return
     */
    private def liftRootBlock(e: Block): Block = {

      // recursively lift to MC syntax starting from the sinks
      val sinks = (for (s <- extractSinkExprs(e.expr)) yield ExpressionRoot(lift(e, Nil)(resolve(e)(s)))).toList

      // a list of statements for the root block of the translated MC expression
      val stats = ListBuffer[Tree]()
      // 1) add required imports
      stats += c.parse("import eu.stratosphere.emma.ir._")
      stats += c.parse("import scala.collection.mutable.ListBuffer")
      stats += c.parse("import scala.reflect.runtime.universe._")
      // 2) initialize translated sinks list
      stats += c.parse("val sinks = ListBuffer[Comprehension]()")
      // 3) add the translated MC expressions for all sinks
      for (s <- sinks) {
        stats += q"sinks += ${serialize(rewrite(s).expr)}"
      }

      // construct and return a block that returns a Workflow using the above list of sinks
      Block(stats.toList, c.parse( """Workflow("Emma Workflow", sinks.toList)"""))
    }

    /**
     * Recursive lift method.
     *
     * @param scope The scope of the lifted tree
     * @param env The ValDef environment for the currently lifted tree
     * @param tree The tree to be lifted
     * @return A lifted, MC syntax version of the given tree
     */
    private def lift(scope: Tree, env: List[ValDef])(tree: Tree): Expression = {

      // ignore a top-level Typed node (side-effect of the Algebra inlining macros)
      val t = tree match {
        case Typed(inner, _) => inner
        case _ => tree
      }

      // translate based on matched expression type
      t match {

        // in.map(f)
        case Apply(TypeApply(Select(parent, TermName("map")), List(outTpe)), List(fn@Function(List(arg), body))) =>
          if (!isCollectionType(t.tpe.widen.typeSymbol)) {
            c.abort(t.pos, "Unsupported expression. Cannot apply MC translation scheme to non-collection type.")
          }

          val vd_arg = q"val ${arg.name} = null.asInstanceOf[${parent.tpe.widen.typeArgs.head}]".asInstanceOf[ValDef]

          val bind = ComprehensionGenerator(arg.name, lift(scope, env)(resolve(scope)(parent)).asInstanceOf[MonadExpression])
          val head = lift(scope, vd_arg :: env)(body)

          Comprehension(q"monad.Bag[$outTpe]", head, bind :: Nil)

        // in.flatMap(f)
        case Apply(TypeApply(Select(parent, TermName("flatMap")), List(outTpe)), List(fn@Function(List(arg), body))) =>
          if (!isCollectionType(t.tpe.widen.typeSymbol)) {
            c.abort(t.pos, "Unsupported expression. Cannot apply MC translation scheme to non-collection type.")
          }

          val vd_arg = q"val ${arg.name} = null.asInstanceOf[${parent.tpe.widen.typeArgs.head}]".asInstanceOf[ValDef]

          val bind = ComprehensionGenerator(arg.name, lift(scope, env)(resolve(scope)(parent)).asInstanceOf[MonadExpression])
          val head = lift(scope, vd_arg :: env)(body)

          MonadJoin(Comprehension(q"monad.Bag[$outTpe]", head, bind :: Nil))

        // in.withFilter(f)
        case Apply(Select(parent, TermName("withFilter")), List(fn@Function(List(arg), body))) =>
          if (!isCollectionType(t.tpe.widen.typeSymbol)) {
            c.abort(t.pos, "Unsupported expression. Cannot apply MC translation scheme to non-collection type.")
          }

          val vd_arg = q"val ${arg.name}: ${parent.tpe.widen.typeArgs.head} = null.asInstanceOf[${parent.tpe.widen.typeArgs.head}]".asInstanceOf[ValDef]

          val bind = ComprehensionGenerator(arg.name, lift(scope, env)(resolve(scope)(parent)).asInstanceOf[MonadExpression])
          val filter = Filter(lift(scope, vd_arg :: env)(body))
          val head = lift(scope, vd_arg :: env)(q"${vd_arg.name}")

          Comprehension(q"monad.Bag[${parent.tpe.widen.typeArgs.head}]", head, bind :: filter :: Nil)

        // in.asSet()
        case Apply(Select(parent, TermName("distinct")), Nil) =>
          if (!isCollectionType(t.tpe.widen.typeSymbol)) {
            c.abort(t.pos, "Unsupported expression. Cannot apply MC translation scheme to non-collection type.")
          }

          // get the child expression
          val child = lift(scope, env)(resolve(scope)(parent)).asInstanceOf[MonadExpression]

          // change the monad type of the first Comprehension descendant
          var descendant = child
          while (!descendant.isInstanceOf[Comprehension]) descendant match {
            case MonadJoin(expr) => descendant = expr
            case MonadUnit(expr) => descendant = expr
            case _ => c.abort(t.pos, "Unexpected non-MonadExpression node returned from recursive MC translation")
          }
          descendant.asInstanceOf[Comprehension].monad = q"monad.Set[${parent.tpe.widen.typeArgs.head}]"

          child

        // write[T](location, ofmt)(in)
        case Apply(Apply(TypeApply(PackageMethod("write"), List(inTpe)), location :: ofmt :: Nil), List(in: Tree)) => Some((inTpe, location, ofmt, in))
          val recordID = nextTermName("snk$record$", snkCount)

          val vd_ofmt = q"val ofmt = $ofmt".asInstanceOf[ValDef]
          val vd_record = q"val $recordID = null.asInstanceOf[$inTpe]".asInstanceOf[ValDef]

          val bind_record = ComprehensionGenerator(recordID, lift(scope, env)(resolve(scope)(in)).asInstanceOf[MonadExpression])

          val head = ScalaExpr(vd_record :: vd_ofmt :: env, q"ofmt.write($recordID)")

          Comprehension(q"monad.All", head, bind_record :: Nil)

        // read[T](location, ifmt)
        case Apply(TypeApply(PackageMethod("read"), List(outTpe)), location :: ifmt :: Nil) =>
          val bytesID = nextTermName("src$bytes$", srcCount.advance)
          val recordID = nextTermName("src$record$", srcCount)

          val vd_ifmt = q"val ifmt: InputFormat[$outTpe] = $ifmt".asInstanceOf[ValDef]
          val vd_dop = q"val dop = null.asInstanceOf[Int]".asInstanceOf[ValDef]
          val vd_bytes = q"val $bytesID = null.asInstanceOf[Seq[Byte]]".asInstanceOf[ValDef]
          val vd_record = q"val $recordID = null.asInstanceOf[$outTpe]".asInstanceOf[ValDef]

          val bind_bytes = ScalaExprGenerator(bytesID, ScalaExpr(vd_dop :: vd_ifmt :: env, q"ifmt.split($location, dop)"))

          val bind_record = ScalaExprGenerator(recordID, ScalaExpr(vd_bytes :: vd_ifmt :: env, q"ifmt.read($bytesID)"))

          val head = ScalaExpr(vd_record :: env, q"$recordID")

          Comprehension(q"monad.Bag[$outTpe]", head, bind_bytes :: bind_record :: Nil)

        // interpret as black box Scala expression (default)
        case _ =>
          ScalaExpr(env, t)
      }
    }

    // ---------------------------------------------------
    // Helper methods.
    // ---------------------------------------------------

    /**
     * Serializes a macro-level IR tree as code constructing an equivalent runtime-level IR tree.
     *
     * @param e The expression in IR to be serialized.
     * @return
     */
    private def serialize(e: Expression): Tree = e match {
      case MonadUnit(expr) =>
        q"MonadUnit(${serialize(expr)})"
      case MonadJoin(expr) =>
        q"MonadJoin(${serialize(expr)})"
      case Filter(expr) =>
        q"Filter(${serialize(expr)})"
      case ScalaExprGenerator(lhs, rhs) =>
        q"ScalaExprGenerator(${lhs.toString}, ${serialize(rhs)})"
      case ComprehensionGenerator(lhs, rhs: MonadExpression) =>
        q"{ val rhs = ${serialize(rhs)}; ComprehensionGenerator(${lhs.toString}, rhs) }"
      case ScalaExpr(env, t) =>
        q"ScalaExpr(${for (v <- referencedEnv(t, env)) yield v.name.toString}, { ..${referencedEnv(t, env)}; reify { ${freeEnv(t, env)} } })"
      case Comprehension(monad, head, qualifiers) =>
        q"""
        {
          // MC qualifiers
          val qualifiers = ListBuffer[Qualifier]()
          ..${for (q <- qualifiers) yield q"qualifiers += ${serialize(q)}"}

          // MC head
          val head = ${serialize(head)}

          // MC constructor
          Comprehension($monad, head, qualifiers.toList)
        }
         """
    }

    /**
     * Constructs a fresh TermName with the given prefix, incrementing the corresponding counter.
     *
     * @param prefix A previx to prepend to the TermName
     * @param counter A counter whose current value will be appended to the TermName
     * @return
     */
    private def nextTermName(prefix: String, counter: Counter) = TermName(f"${prefix}${counter.get}")

    /**
     * Custom matcher for eu.stratosphere.emma.package.* method applications.
     */
    private object PackageMethod {
      def unapply(t: Tree): Option[String] = t match {
        case Select(quantifier, TermName(method)) => if (quantifier.symbol == apiModule) Some(method) else None
        case _ => None
      }
    }

  }

}