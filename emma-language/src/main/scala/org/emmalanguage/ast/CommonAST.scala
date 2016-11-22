/*
 * Copyright © 2014 TU Berlin (emma@dima.tu-berlin.de)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.emmalanguage
package ast

import scala.annotation.tailrec
import scala.reflect.api.Universe

/**
 * Implements various utility functions that mitigate and/or workaround deficiencies in Scala's
 * macros and runtime reflection APIs, e.g. non-idempotent type checking, lack of hygiene,
 * capture-avoiding substitution, fully-qualified names, fresh name generation, identifying
 * closures, etc.
 *
 * This trait has to be instantiated with a [[scala.reflect.api.Universe]] type and works for both
 * runtime and compile time reflection.
 */
trait CommonAST {

  val universe: Universe
  lazy val u: universe.type = universe
  type =?>[-A, +B] = PartialFunction[A, B]

  import universe._
  import definitions._
  import internal._
  import Flag._

  private[ast] def freshNameSuffix: Char

  private[ast] def setOriginal(tpt: TypeTree, original: Tree): TypeTree

  // ----------------------------------------------------------------------------------------------
  // Parsing and type-checking
  // ----------------------------------------------------------------------------------------------

  /** Returns the enclosing owner of the current compilation context. */
  def enclosingOwner: Symbol

  /** Raises a compiler warning. */
  def warning(msg: String, pos: Position = NoPosition): Unit

  /** Raises an error and terminates compilation. */
  def abort(msg: String, pos: Position = NoPosition): Nothing

  /** Parses a snippet of source code and returns the AST. */
  def parse(code: String): Tree

  /** Type-checks a `tree` (use `typeMode=true` for type-trees). */
  def typeCheck(tree: Tree, typeMode: Boolean = false): Tree

  /** Removes all type and symbol attributes from a `tree`. */
  // FIXME: Replace with `c.untypecheck` or `tb.untypecheck` once SI-5464 is resolved.
  def unTypeCheck(tree: Tree): Tree = parse(showCode(tree, printRootPkg = true))

  /**
   * Evaluates a snippet of code and returns a value of type `T`.
   * Note: this can be called on type-checked trees (as opposed to the eval method in ToolBox).
   */
  def eval[T](code: Tree): T

  /** Infers an implicit value from the enclosing context (if possible). */
  def inferImplicit(tpe: Type): Tree

  // scalastyle:off
  // TODO: Replace uses with `api.Tree.With.tpe`
  /** Extractor for the type of a tree, if any. */
  object withType {
    def unapply(tree: Tree): Option[(Tree, Type)] =
      if (has.tpe(tree)) Some(tree, tree.tpe.dealias.widen) else None
  }// scalastyle:on

  // ----------------------------------------------------------------------------------------------
  // Property checks
  // ----------------------------------------------------------------------------------------------

  /** Constant limits. */
  object Max {

    /** Maximum number of lambda arguments. */
    val FunParams = FunctionClass.seq.size

    /** Maximum number of tuple elements. */
    val TupleElems = TupleClass.seq.size
  }

  object is {

    /** Does `sym` have the property encoded as flag(s)? */
    def apply(property: FlagSet)(sym: Symbol): Boolean =
      are(property)(flags(sym))

    /** The opposite of `is(property)(sym)`. */
    def not(property: FlagSet)(sym: Symbol): Boolean =
      are.not(property)(flags(sym))

    /** Is `name` non-degenerate? */
    def defined(name: Name): Boolean =
      name != null && name.toString.nonEmpty

    /** Is `pos` non-degenerate? */
    def defined(pos: Position): Boolean =
      pos != null && pos != NoPosition

    /** Is `sym` non-degenerate? */
    def defined(sym: Symbol): Boolean =
      sym != null && sym != NoSymbol

    /** Is `tree` non-degenerate? */
    def defined(tree: Tree): Boolean =
      tree != null && tree.nonEmpty

    /** Is `tpe` non-degenerate? */
    def defined(tpe: Type): Boolean =
      tpe != null && tpe != NoType

    /** Is `tpe` the type of a case class? */
    def caseClass(tpe: u.Type) =
      tpe.typeSymbol.isClass && tpe.typeSymbol.asClass.isCaseClass

    /** Is `name` a legal identifier (i.e. consisting only of word `\w+` characters)? */
    def encoded(name: Name): Boolean =
      name == name.encodedName

    /** Is `sym` a legal identifier (i.e. having an `encoded` name)? */
    def encoded(sym: Symbol): Boolean =
      is.encoded(sym.name)

    /** Is `sym` local (its owner being a binding or a method)? */
    def local(sym: Symbol): Boolean = {
      val owner = sym.owner
      !owner.isPackage && !owner.isClass && !owner.isModule
    }

    /** Is `sym` overloaded (i.e. having variants with different type signatures). */
    def overloaded(sym: Symbol): Boolean =
      sym.isTerm && sym.asTerm.isOverloaded

    /** Is `sym` the `_root_` symbol? */
    def root(sym: Symbol): Boolean =
      // This is tricky for Java classes
      sym.name == termNames.ROOTPKG || sym.name == rootMirror.RootClass.name

    /** Is `sym` a binding symbol (i.e. value, variable or parameter)? */
    def binding(sym: Symbol): Boolean = sym.isTerm && {
      val term = sym.asTerm
      term.isVal || term.isVar || term.isParameter
    }

    /** Is `sym` a value (`val`) symbol? */
    def value(sym: Symbol): Boolean =
      sym.isTerm && !sym.isParameter && sym.asTerm.isVal

    /** Is `sym` a variable (`var`) symbol? */
    def variable(sym: Symbol): Boolean =
      sym.isTerm && sym.asTerm.isVar

    /** Is `sym` a label (loop) symbol? */
    def label(sym: Symbol): Boolean =
      sym.isMethod && is(CONTRAVARIANT)(sym)

    /** Is `sym` a method (`def`) symbol? */
    def method(sym: Symbol): Boolean =
      sym.isMethod && is.not(CONTRAVARIANT)(sym)

    /** Is `sym` a by-name parameter? */
    def byName(sym: Symbol): Boolean =
      sym.isTerm && sym.asTerm.isByNameParam

    /** Is `sym` a stable identifier? */
    def stable(sym: u.Symbol): Boolean =
      sym.isTerm && sym.asTerm.isStable

    /** Is `tpe` legal for a term (i.e. not of a higher kind or method)? */
    def result(tpe: Type): Boolean =
      !tpe.takesTypeArgs && !is.method(tpe)

    /** Is `tpe` the type of a method (illegal for a term)? */
    @tailrec
    def method(tpe: Type): Boolean = tpe match {
      case PolyType(_, result)  => is.method(result)
      case _: NullaryMethodType => true
      case _: MethodType        => true
      case _ => false
    }

    /** Does `tree` define a symbol that owns the children of `tree`? */
    def owner(tree: Tree): Boolean = tree match {
      case _: Bind     => false
      case _: Function => true
      case _: LabelDef => false
      case _ => tree.isDef
    }

    /** Is `tree` a statement? */
    def stat(tree: Tree): Boolean = tree match {
      case _: Assign   => true
      case _: Bind     => false
      case _: LabelDef => true
      case _ => tree.isDef
    }

    /** Is `tree` a term? */
    def term(tree: Tree): Boolean = tree match {
      case Ident(termNames.WILDCARD) => false
      case id: Ident => has.sym(id) && has.tpe(id) &&
        id.symbol.isTerm && is.result(id.tpe)
      case sel: Select => has.sym(sel) && has.tpe(sel) &&
        sel.symbol.isTerm && is.result(sel.tpe)
      case app: Apply => has.tpe(app) && is.result(app.tpe)
      case tapp: TypeApply => has.tpe(tapp) && is.result(tapp.tpe)
      case _: Assign   => false
      case _: Bind     => false
      case _: LabelDef => false
      case _: New      => false
      case _ => tree.isTerm
    }

    /** Is `tree` a quoted type-tree? */
    def tpe(tree: Tree): Boolean = tree match {
      case id: Ident => has.sym(id) && id.symbol.isType
      case sel: Select => has.sym(sel) && sel.symbol.isType
      case _ => tree.isType
    }

    /** Is `tree` a valid pattern? */
    def pattern(tree: Tree): Boolean = tree match {
      case Ident(termNames.WILDCARD) => true
      case path @ (_: Ident | _: Select) =>
        has.sym(path) && has.tpe(path) &&
          path.symbol.isTerm &&
          is.stable(path.symbol) &&
          is.result(path.tpe)
      case app @ Apply(target, args) =>
        has.tpe(app) && is.tpe(target) &&
          args.nonEmpty && is.result(app.tpe)
      case _: Alternative => true
      case _: Bind        => true
      case _: Literal     => true
      case _: Typed       => true
      case _: UnApply     => true
      case _ => false
    }
  }

  object are {

    /** Are `flags` a superset of `property`? */
    def apply(property: FlagSet)(flags: FlagSet): Boolean =
      (flags | property) == flags

    /** The opposite of `are(property)(flags)`. */
    def not(property: FlagSet)(flags: FlagSet): Boolean =
      (flags | property) != flags

    /** Are all `trees` non-degenerate? */
    def defined(trees: Traversable[Tree]): Boolean =
      trees.forall(is.defined)

    /** Are all `trees` statements? */
    def stats(trees: Traversable[Tree]): Boolean =
      trees.forall(is.stat)

    /** Are all `trees` terms? */
    def terms(trees: Traversable[Tree]): Boolean =
      trees.forall(is.term)

    /** Are all `trees` quoted type-trees? */
    def types(trees: Traversable[Tree]): Boolean =
      trees.forall(is.tpe)

    /** Are all `trees` valid patterns? */
    def patterns(trees: Traversable[Tree]): Boolean =
      trees.forall(is.pattern)
  }

  object has {

    /** Does `sym` have a name? */
    def name(sym: Symbol): Boolean =
      is.defined(sym.name)

    /** Does `sym` have an owner? */
    def owner(sym: Symbol): Boolean =
      is.defined(sym.owner)

    /** Does `sym` have a position? */
    def pos(sym: Symbol): Boolean =
      is.defined(sym.pos)

    /** Does `tree` have a position? */
    def pos(tree: Tree): Boolean =
      is.defined(tree.pos)

    /** Does `tree` reference a symbol? */
    def sym(tree: Tree): Boolean =
      is.defined(tree.symbol)

    /** Does `tree` have a type? */
    def tpe(tree: Tree): Boolean =
      is.defined(tree.tpe)

    /** Does `sym` have a type? */
    def tpe(sym: Symbol): Boolean =
      is.defined(sym.info)
  }

  object have {

    /** Do all `symbols` have a name? */
    def name(symbols: Traversable[Symbol]): Boolean =
      symbols.forall(has.name)

    /** Do all `symbols` have an owner? */
    def owner(symbols: Traversable[Symbol]): Boolean =
      symbols.forall(has.owner)

    /** Do all `trees` have a position? */
    def pos(trees: Traversable[Tree]): Boolean =
      trees.forall(has.pos)

    /** Do all `trees` have a symbol? */
    def sym(trees: Traversable[Tree]): Boolean =
      trees.forall(has.sym)

    /** Do all `trees` have a type? */
    def tpe(trees: Traversable[Tree]): Boolean =
      trees.forall(has.tpe)
  }

  // ----------------------------------------------------------------------------------------------
  // Flags
  // ----------------------------------------------------------------------------------------------

  lazy val FlagsNoSynthetic =
    Flags - Flag.SYNTHETIC

  /** All explicit flags. */
  lazy val Flags = Set(
    Flag.ABSOVERRIDE,
    Flag.ABSTRACT,
    Flag.ARTIFACT,
    Flag.BYNAMEPARAM,
    Flag.CASE,
    Flag.CASEACCESSOR,
    Flag.ARTIFACT,
    Flag.CONTRAVARIANT,
    Flag.COVARIANT,
    Flag.DEFAULTINIT,
    Flag.DEFAULTPARAM,
    Flag.DEFERRED,
    Flag.ENUM,
    Flag.FINAL,
    Flag.IMPLICIT,
    Flag.INTERFACE,
    Flag.LAZY,
    Flag.LOCAL,
    Flag.MACRO,
    Flag.MUTABLE,
    Flag.OVERRIDE,
    Flag.PARAM,
    Flag.PARAMACCESSOR,
    Flag.PRIVATE,
    Flag.PROTECTED,
    Flag.SEALED,
    Flag.STABLE,
    Flag.SYNTHETIC,
    Flag.TRAIT)

  // ----------------------------------------------------------------------------------------------
  // Virtual nodes
  // ----------------------------------------------------------------------------------------------

  /** Common parent for all virtual AST nodes. */
  trait Node {
    override def toString: String =
      getClass.getSimpleName.dropRight(1)
  }
}
