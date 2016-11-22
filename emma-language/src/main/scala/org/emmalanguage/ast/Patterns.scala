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

/** Patterns (for pattern matching). */
trait Patterns { this: AST =>

  /** Patterns (for pattern matching). */
  trait PatternAPI { this: API =>

    import universe._
    import internal._
    import reificationSupport._

    /** Patterns. */
    object Pat extends Node {
      def unapply(pat: u.Tree): Option[u.Tree] =
        Option(pat).filter(is.pattern)
    }

    /** Alternative patterns. */
    object PatAlt extends Node {

      /**
       * Creates a type-checked alternative pattern.
       * @param alternatives Must be at least 2 valid patterns.
       * @return `case alternatives(0) | alternatives(1) | ... =>`
       */
      def apply(alternatives: u.Tree*): u.Alternative = {
        assert(alternatives.size >= 2,     s"$this requires at least 2 alternatives")
        assert(are.patterns(alternatives), s"Not all $this alternatives are valid patterns")
        assert(have.tpe(alternatives),     s"Not all $this alternatives have a type")
        val alt = u.Alternative(alternatives.toList)
        setType(alt, Type.lub(alternatives.map(_.tpe)))
      }

      def unapply(alt: u.Alternative): Option[Seq[u.Tree]] =
        Some(alt.trees)
    }

    /** The `_` wildcard pattern. */
    object PatAny extends Node {

      /** Creates a type-checked wildcard pattern. */
      def apply(): u.Ident = {
        val id = u.Ident(TermName.wildcard)
        setSymbol(id, Sym.none)
      }

      def unapply(pat: u.Ident): Option[Unit] = pat match {
        case u.Ident(TermName.wildcard) => Some(())
        case _ => None
      }
    }

    /** Typed patterns (ascriptions). */
    object PatAscr extends Node {

      /**
       * Creates a type-checked typed pattern.
       * @param target Must be a valid pattern.
       * @param tpe Must be a valid type.
       * @return `case target: tpe =>`
       */
      def apply(target: u.Tree, tpe: u.Type): u.Typed = {
        assert(is.defined(target), s"$this target is not defined")
        assert(is.pattern(target), s"$this target is not a pattern: ${Tree.show(target)}")
        assert(is.defined(tpe),    s"$this type is not defined")
        val ascr = u.Typed(target, TypeQuote(tpe))
        setType(ascr, tpe)
      }

      def unapply(pat: u.Typed): Option[(u.Tree, u.Type)] = pat match {
        case u.Typed(Pat(target), tpt) => Some(target, tpt.tpe)
        case _ => None
      }
    }

    /** Bindings in a pattern match. */
    object PatAt extends Node {

      /**
       * Creates a type-checked pattern match binding.
       * @param lhs Must be a value symbol.
       * @param rhs Must be a valid pattern.
       * @return `lhs @ rhs`.
       */
      def apply(lhs: u.TermSymbol, rhs: u.Tree): u.Bind = {
        assert(is.defined(lhs), s"$this LHS is not defined")
        assert(has.name(lhs),   s"$this LHS $lhs has no name")
        assert(has.tpe(lhs),    s"$this LHS $lhs has no type")
        assert(is.encoded(lhs), s"$this LHS $lhs is not encoded")
        assert(is.value(lhs),   s"$this LHS $lhs is not a value")
        assert(is.defined(rhs), s"$this RHS is not defined")
        assert(is.pattern(rhs), s"$this RHS is not a pattern:\n${Tree.show(rhs)}")
        val at = u.Bind(lhs.name, rhs)
        setSymbol(at, lhs)
        setType(at, lhs.info)
      }

      def unapply(at: u.Bind): Option[(u.TermSymbol, u.Tree)] = at match {
        case u.Bind(_, Pat(rhs)) => Some(at.symbol.asTerm, rhs)
        case _ => None
      }
    }

    /** Constant patterns (capitalized or back-quoted). */
    object PatConst extends Node {

      /**
       * Creates a type-checked constant pattern.
       * @param target Must be a stable symbol.
       * @return `case Lhs =>`.
       */
      def apply(target: u.TermSymbol): u.Ident = {
        assert(is.defined(target), s"$this target is not defined")
        assert(has.name(target),   s"$this target $target has no name")
        assert(target.isStable,    s"$this target $target is not stable")
        if (target.name.toString.head.isUpper) {
          TermRef(target)
        } else {
          assert(has.tpe(target), s"$this target $target has no type")
          val id = q"`$target`"
          setSymbol(id, target)
          setType(id, target.info)
          id.asInstanceOf[u.Ident]
        }
      }

      def unapply(pat: u.Ident): Option[u.TermSymbol] = pat match {
        case ref @ TermRef(lhs) if lhs.isStable &&
          (ref.isBackquoted || lhs.name.toString.head.isUpper)
          => Some(lhs)
        case _ => None
      }
    }

    /** Extractor patterns (case class destructors and `unapply` calls). */
    // TODO: Implement `apply()` constructor
    object PatExtr extends Node {
      def unapply(extr: u.Tree): Option[(u.Tree, Seq[u.Tree])] = extr match {
        case u.Apply(tpt: u.TypeTree, args)
          if is.caseClass(extr.tpe) => Some(tpt, args)
        case u.UnApply(unApp, args) => Some(unApp, args)
        case _ => None
      }
    }

    /** Literal patterns. */
    lazy val PatLit = Lit

    /** Qualified patterns. */
    object PatQual extends Node {

      /**
       * Creates a type-checked qualified pattern.
       * @param qual Must be a valid qualifier.
       * @param member Must be a stable member of `qual`.
       * @return `case target.member =>`
       */
      def apply(qual: u.Tree, member: u.TermSymbol): u.Select = {
        assert(is.defined(qual), s"$this qualifier is not defined")
        assert(qual match {
          case Id(_)     => true
          case Sel(_, _) => true
          case _ => false
        }, s"$this qualifier is not a valid path:\n${Tree.show(qual)}")
        assert(is.defined(member), s"$this member is not defined")
        assert(member.isStable,    s"$this member $member is not stable")
        Sel(qual, member)
      }

      def unapply(sel: u.Select): Option[(u.Tree, u.TermSymbol)] = sel match {
        case Sel(qual @ (Id(_) | Sel(_, _)), TermSym(member)) => Some(qual, member)
        case _ => None
      }
    }

    /** Variable patterns (untyped). */
    object PatVar extends Node {

      /**
       * Creates a type-checked variable pattern.
       * @param lhs Must be a non-capitalized value symbol.
       * @return `case lhs =>`.
       */
      def apply(lhs: u.TermSymbol): u.Ident = {
        assert(is.defined(lhs), s"$this LHS is not defined")
        assert(has.name(lhs),   s"$this LHS $lhs has no name")
        assert(lhs.name.toString.head.isLower, s"$this LHS $lhs cannot be capitalized")
        ValRef(lhs)
      }

      def unapply(pat: u.Ident): Option[u.TermSymbol] = pat match {
        case ref @ ValRef(lhs) if !ref.isBackquoted &&
          lhs.name.toString.head.isLower => Some(lhs)
        case _ => None
      }
    }

    /** Pattern match cases. */
    object PatCase extends Node {

      /**
       * Creates a type-checked `case` definition without a guard.
       * @param pat Must be a valid pattern.
       * @param body Must be a term.
       * @return `case pattern => body`.
       */
      def apply(pat: u.Tree, body: u.Tree): u.CaseDef =
        apply(pat, Empty(), body)

      /**
       * Creates a type-checked `case` definition with a guard.
       * @param pat Must be a valid pattern.
       * @param guard Must be a boolean expression (has access to bindings in `pattern`).
       * @param body Must be a term.
       * @return `case pattern if guard => body`.
       */
      def apply(pat: u.Tree, guard: u.Tree, body: u.Tree): u.CaseDef = {
        assert(is.defined(pat),  s"$this pattern is not defined")
        assert(is.pattern(pat),  s"$this pattern is not valid:\n${Tree.show(pat)}")
        assert(is.defined(body), s"$this body is not defined")
        assert(is.term(body),    s"$this body is not a term:\n${Tree.show(body)}")
        assert(has.tpe(body),    s"$this body has no type:\n${Tree.showTypes(body)}")
        val grd = if (!is.defined(guard)) Empty() else {
          assert(is.term(guard), s"$this guard is not a term:\n${Tree.show(guard)}")
          assert(has.tpe(guard), s"$this guard has no type:\n${Tree.showTypes(guard)}")
          assert(guard.tpe <:< Type.bool, s"$this guard is not boolean:\n${Tree.showTypes(guard)}")
          guard
        }

        val cse = u.CaseDef(pat, grd, body)
        setType(cse, body.tpe)
      }

      def unapply(cse: u.CaseDef): Option[(u.Tree, u.Tree, u.Tree)] = cse match {
        case u.CaseDef(Pat(pat), guard, Term(body)) => Some(pat, guard, body)
        case _ => None
      }
    }

    /** Pattern matches. */
    object PatMat extends Node {

      /**
       * Creates a type-checked pattern `match`.
       * @param sel The pattern match target (selector) must be a term.
       * @param cases The rest cases of the pattern `match`.
       * @return `sel match { cse; ..cases }`.
       */
      def apply(sel: u.Tree, cases: Seq[u.CaseDef]): u.Match = {
        assert(is.defined(sel),    s"$this selector is not defined")
        assert(is.term(sel),       s"$this selector is not a term: ${Tree.show(sel)}")
        assert(has.tpe(sel),       s"$this selector has no type:\n${Tree.showTypes(sel)}")
        assert(cases.nonEmpty,     s"$this expects at least one case")
        assert(are.defined(cases), s"Not all $this cases are defined")
        assert(have.tpe(cases),    s"Not all $this cases have types")
        val mat = u.Match(sel, cases.toList)
        setType(mat, Type.lub(cases.map(_.tpe)))
      }

      def unapply(mat: u.Match): Option[(u.Tree, Seq[u.CaseDef])] = mat match {
        case u.Match(Term(target), cases) => Some(target, cases)
        case _ => None
      }
    }
  }
}
