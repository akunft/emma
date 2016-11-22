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

import scala.language.higherKinds

trait Types { this: AST =>

  trait TypeAPI { this: API =>

    import universe._
    import definitions._
    import internal._
    import reificationSupport._

    /** Type names. */
    object TypeName extends Node {

      // Predefined type names
      val empty    = u.typeNames.EMPTY
      val wildcard = u.typeNames.WILDCARD
      val wildStar = u.typeNames.WILDCARD_STAR

      /** Creates a new type name (must be non-empty). */
      def apply(name: String): u.TypeName = {
        assert(name.nonEmpty, "Empty type name")
        apply(u.TypeName(name))
      }

      /** Encodes `name` and converts it to a type name. */
      def apply(name: u.Name): u.TypeName = {
        assert(is.defined(name), "Undefined name")
        name.encodedName.toTypeName
      }

      /** Extracts the type name of `sym`, if any. */
      def apply(sym: u.Symbol): u.TypeName = {
        assert(is.defined(sym), "Undefined symbol")
        assert(has.name(sym),  s"Symbol $sym has no name")
        apply(sym.name)
      }

      /** Creates a fresh type name with the given `prefix`. */
      def fresh(prefix: String): u.TypeName = apply {
        assert(prefix.nonEmpty, "Cannot create a fresh name with empty prefix")
        freshTypeName(s"$prefix$$$freshNameSuffix")
      }

      /** Creates a fresh type name with the given `prefix`. */
      def fresh(prefix: u.Name): u.TypeName = {
        assert(is.defined(prefix), "Undefined prefix")
        fresh(prefix.toString)
      }

      /** Creates a fresh type name with the given symbol's name as `prefix`. */
      def fresh(prefix: u.Symbol): u.TypeName = {
        assert(is.defined(prefix), "Undefined prefix")
        assert(has.name(prefix),  s"Prefix $prefix has no name")
        fresh(prefix.name)
      }

      def unapply(name: u.TypeName): Option[String] =
        for (name <- Option(name) if is.defined(name)) yield name.toString
    }

    /** Type symbols. */
    object TypeSym extends Node {

      /**
       * Creates a type-checked type symbol.
       * @param own The symbol of the enclosing named entity where this type is defined.
       * @param nme The name of this type (will be encoded).
       * @param flg Any (optional) modifiers (e.g. implicit, final, abstract).
       * @param pos The (optional) source code position where this type is defined.
       * @param ans Any (optional) annotations associated with this type.
       * @return A new type-checked type symbol.
       */
      def apply(own: u.Symbol, nme: u.TypeName,
        flg: u.FlagSet         = u.NoFlags,
        pos: u.Position        = u.NoPosition,
        ans: Seq[u.Annotation] = Seq.empty
      ): u.TypeSymbol = {
        assert(is.defined(nme), s"$this name is not defined")
        val sym = newTypeSymbol(own, TypeName(nme), pos, flg)
        setAnnotations(sym, ans.toList)
      }

      /** Creates a free type symbol (without an owner). */
      def free(nme: u.TypeName,
        flg: u.FlagSet         = u.NoFlags,
        pos: u.Position        = u.NoPosition,
        ans: Seq[u.Annotation] = Seq.empty
      ): u.FreeTypeSymbol = {
        assert(is.defined(nme), s"$this name is not defined")
        val free = internal.newFreeType(TypeName(nme).toString, flg, null)
        setAnnotations(free, ans.toList)
      }

      /** Creates a free type symbol with the same attributes as the `origin`. */
      def free(origin: u.TypeSymbol): u.FreeTypeSymbol =
        free(TypeName(origin), flags(origin), origin.pos, origin.annotations)

      /** Creates a fresh type symbol with the same attributes as the `origin`. */
      def fresh(origin: u.TypeSymbol): u.TypeSymbol =
        Sym.With(origin)(nme = TypeName.fresh(origin)).asType

      def unapply(sym: u.TypeSymbol): Option[u.TypeSymbol] =
        Option(sym)
    }

    object Type extends Node {

      // ------------------
      // Predefined types
      // ------------------

      // Top and bottom
      val any     = AnyTpe
      val nothing = NothingTpe

      // Primitives
      val anyVal = AnyValTpe
      val unit   = UnitTpe
      val bool   = BooleanTpe
      val char   = CharTpe
      val byte   = ByteTpe
      val short  = ShortTpe
      val int    = IntTpe
      val long   = LongTpe
      val float  = FloatTpe
      val double = DoubleTpe

      // Objects
      val anyRef = AnyRefTpe
      val obj    = ObjectTpe
      val nul    = NullTpe
      val string = Type[String]
      val bigInt = Type[BigInt]
      val bigDec = Type[BigDecimal]

      // Java types
      object Java {
        val void   = Type[java.lang.Void]
        val bool   = Type[java.lang.Boolean]
        val char   = Type[java.lang.Character]
        val byte   = Type[java.lang.Byte]
        val short  = Type[java.lang.Short]
        val int    = Type[java.lang.Integer]
        val long   = Type[java.lang.Long]
        val float  = Type[java.lang.Float]
        val double = Type[java.lang.Double]
        val bigInt = Type[java.math.BigInteger]
        val bigDec = Type[java.math.BigDecimal]
      }

      // Other
      val none = u.NoType
      val loop = Type.method()

      /** Applies a type `constructor` to the supplied arguments. */
      def apply(constructor: u.Type, args: Seq[u.Type] = Seq.empty): u.Type =
        if (args.isEmpty) constructor else {
          assert(is.defined(constructor),      "Type constructor is not defined")
          assert(constructor.takesTypeArgs,   s"Type $constructor takes no type arguments")
          assert(args.forall(is.defined),      "Not all type arguments are defined")
          assert(constructor.typeParams.size == args.size,
            s"Type params <-> args size mismatch for $constructor")
          u.appliedType(constructor, args.map(_.dealias.widen): _*)
        }

      /** Reifies a type from a tag. */
      def apply[T: u.TypeTag]: u.Type =
        kind0[T]

      /** Reifies a type from a weak tag. */
      def weak[T: u.WeakTypeTag]: u.Type = u.weakTypeOf[T]

      /** Reifies a type of kind `*`. */
      def kind0[T: u.TypeTag]: u.Type = u.typeOf[T]

      /** Reifies a type of kind `* -> *`. */
      def kind1[F[_]](arg: u.Type)
        (implicit tag: u.TypeTag[F[Nothing]]): u.Type
        = apply(apply(tag).typeConstructor, Seq(arg))

      /** Reifies a type of kind `* -> * -> *`. */
      def kind2[F[_, _]](arg1: u.Type, arg2: u.Type)
        (implicit tag: u.TypeTag[F[Nothing, Nothing]]): u.Type
        = apply(apply(tag).typeConstructor, Seq(arg1, arg2))

      /** Reifies a type of kind `* -> * -> * -> *`. */
      def kind3[F[_, _, _]](arg1: u.Type, arg2: u.Type, arg3: u.Type)
        (implicit tag: u.TypeTag[F[Nothing, Nothing, Nothing]]): u.Type
        = apply(apply(tag).typeConstructor, Seq(arg1, arg2, arg3))

      /** Creates a new array type. */
      def arrayOf(elements: u.Type): u.Type =
        kind1[Array](elements)

      /** Creates a new function (lambda) type. */
      def fun(
        params: Seq[u.Type] = Seq.empty,
        result: u.Type      = Type.unit
      ): u.Type = {
        val n = params.size
        assert(n <= Max.FunParams, s"Cannot have $n > ${Max.FunParams} lambda parameters")
        apply(Sym.fun(n).toTypeConstructor, params :+ result)
      }

      /** Creates a new tuple type. */
      def tupleOf(elements: Seq[u.Type]): u.Type = {
        val n = elements.size
        assert(n <= Max.TupleElems, s"Cannot have $n > ${Max.TupleElems} tuple elements")
        if (elements.isEmpty) Type.unit
        else apply(Sym.tuple(n).toTypeConstructor, elements)
      }

      /** Extracts the i-th (1-based) type argument of the applied type `tpe`. */
      def arg(i: Int, tpe: u.Type): u.Type = {
        assert(is.defined(tpe), "Undefined type")
        val args = tpe.dealias.widen.typeArgs
        assert(args.size >= i, s"Type $tpe has no type argument #$i")
        args(i - 1)
      }

      /** Type-checks a `tree` (use `typeMode=true` for type-trees). */
      def check(tree: u.Tree, typeMode: Boolean = false): u.Tree = {
        assert(is.defined(tree), "Cannot type-check undefined tree")
        assert(!has.tpe(tree),  s"Tree is already type-checked:\n${Tree.showTypes(tree)}")
        typeCheck(tree, typeMode)
      }

      /** Type-checks a `tree` as if `imports` were in scope. */
      def checkWith(imports: Seq[u.Tree], tree: u.Tree): u.Tree = {
        assert(are.defined(imports), "Not all imports are defined")
        assert(is.defined(tree),     "Cannot type-check undefined tree")
        assert(!has.tpe(tree),      s"Tree already type-checked:\n${Tree.showTypes(tree)}")
        Type.check(u.Block(imports.toList, tree)).children.last
      }

      /** Removes all type and symbol attributes from a `tree`. */
      def unCheck(tree: u.Tree): u.Tree = {
        assert(is.defined(tree), "Cannot un-type-check undefined tree")
        assert(has.tpe(tree),   s"Untyped tree:\n${Tree.showTypes(tree)}")
        unTypeCheck(tree)
      }

      /** Returns the least upper bound of all types. */
      def lub(types: Seq[u.Type]): u.Type =
        u.lub(types.toList)

      /** Returns the weak (considering coercions) least upper bound of all types. */
      def weakLub(types: Seq[u.Type]): u.Type =
        if (types.isEmpty) nothing
        else types.reduce { (T, U) =>
          if (T weak_<:< U) U
          else if (U weak_<:< T) T
          else lub(Seq(T, U))
        }

      /** Returns a new method type (possibly generic and with multiple arg lists). */
      def method(
        tps: Seq[u.TypeSymbol]      = Seq.empty,
        pss: Seq[Seq[u.TermSymbol]] = Seq.empty,
        res: u.Type                 = Type.unit
      ): u.Type = {
        assert(tps.forall(is.defined),         "Not all method type parameters are defined")
        assert(pss.flatten.forall(is.defined), "Not all method parameter types are defined")
        assert(is.defined(res),                "Undefined method return type")
        val mono = if (pss.isEmpty) {
          nullaryMethodType(res.dealias.widen)
        } else pss.foldRight(res.dealias.widen) { (params, ret) =>
          methodType(params.toList, ret)
        }

        if (tps.isEmpty) mono
        else polyType(tps.toList, mono)
      }

      /** Extracts the type signature of `sym` (with an optional target), if any. */
      def signature(sym: u.Symbol, in: u.Type = Type.none): u.Type = {
        assert(is.defined(sym), "Symbol is not defined")
        assert(has.tpe(sym),   s"Symbol $sym has no type signature")
        val sign = if (is.defined(in)) sym.typeSignatureIn(in) else sym.typeSignature
        if (is.byName(sym)) sign.typeArgs.head else sign
      }

      /** Returns the type constructor of an applied type `tpe`. */
      def constructor(tpe: u.Type): u.Type =
        tpe.dealias.widen.typeConstructor

      /** Infers an implicit value from the enclosing context (if possible). */
      def inferImplicit(tpe: u.Type): Option[u.Tree] = for {
        value <- Option(Types.this.inferImplicit(tpe))
        if value.nonEmpty
      } yield value.tpe match {
        case NullaryMethodType(res) => setType(value, res)
        case _ => value
      }

      /** Returns the original type-tree corresponding to `tpe`. */
      def tree(tpe: u.Type): u.Tree = {
        def original(tpe: u.Type): u.Tree = setType(tpe match {
          // Degenerate type: `this[staticID]`.
          case u.ThisType(parent) if parent.isStatic =>
            Tree.resolveStatic(parent)
          // This type: `this[T]`.
          case u.ThisType(parent) =>
            This(parent)
          // Super type: `this.super[T]`
          case u.SuperType(ths, parent) =>
            val sym = parent.typeSymbol.asType
            val tpt = u.Super(original(ths), sym.name)
            setSymbol(tpt, sym)
          // Package or class ref: `package` or `Class`.
          case u.SingleType(u.NoPrefix, target)
            if target.isPackage || target.isClass => Id(target)
          // Singleton type: `stableID.tpe`.
          case u.SingleType(u.NoPrefix, stableID) =>
            u.SingletonTypeTree(Id(stableID))
          // Qualified type: `pkg.T`.
          case u.SingleType(pkg, target) =>
            Sel(original(pkg), target)
          // Abstract type ref: `T`.
          case u.TypeRef(u.NoPrefix, target, Nil) =>
            Id(target)
          // Path dependent type: `path.T`.
          case u.TypeRef(path, target, Nil) =>
            Sel(original(path), target)
          // Applied type: `T[A, B, ...]`.
          case u.TypeRef(u.NoPrefix, target, args) =>
            u.AppliedTypeTree(Id(target), args.map(Type.tree))
          // Applied path dependent type: `path.T[A, B, ...]`
          case u.TypeRef(path, target, args) =>
            u.AppliedTypeTree(Sel(original(path), target), args.map(Type.tree))
          // Type bounds: `T >: lo <: hi`.
          case u.TypeBounds(lo, hi) =>
            u.TypeBoundsTree(Type.tree(lo), Type.tree(hi))
          // Existential type: `F[A, B, ...] forSome { type A; type B; ... }`
          case u.ExistentialType(quantified, underlying) =>
            u.ExistentialTypeTree(Type.tree(underlying), quantified.map(typeDef))
          // Annotated type: `A @ann1 @ann2 ...`
          case AnnotatedType(annotations, underlying) =>
            annotations.foldLeft(original(underlying)) {
              (tpt, ann) => u.Annotated(ann.tree, tpt)
            }
          // E.g. type refinement: `T { def size: Int }`
          case _ => abort(s"Cannot convert type $tpe to a type-tree")
        }, tpe)

        val tpt = u.TypeTree(tpe)
        setOriginal(tpt, original(tpe))
      }
    }

    /** Quoted type-trees. */
    object TypeQuote extends Node {

      val empty = u.TypeTree()

      /** Reifies `tpe` as a tree. */
      def apply(tpe: u.Type): u.TypeTree = {
        assert(is.defined(tpe), s"$this type is not defined")
        u.TypeTree(tpe)
      }

      /** Reifies `sym`'s type as a tree. */
      def apply(sym: u.Symbol): u.TypeTree = {
        assert(is.defined(sym), s"$this symbol is not defined")
        assert(has.tpe(sym),    s"$this symbol $sym has no type")
        apply(sym.info)
      }

      /** Reifies type `T` as a tree. */
      def apply[T: u.TypeTag]: u.TypeTree =
        apply(Type[T])

      def unapply(tree: u.Tree): Option[u.Type] = tree match {
        case tpt: u.TypeTree if has.tpe(tpt) => Some(tpt.tpe)
        case _ => None
      }
    }

    /** By-name types (`=> T`), legal only in parameter declarations. */
    // TODO: Define a constructor?
    object ByNameType {

      val sym: u.ClassSymbol = ByNameParamClass

      def unapply(tpe: u.TypeRef): Option[u.Type] = tpe match {
        case u.TypeRef(_, `sym`, Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    /** Vararg types (`T*`), legal only in parameter declarations. */
    // TODO: Define a constructor?
    object VarArgType {

      val scalaSym: u.ClassSymbol = RepeatedParamClass
      val javaSym:  u.ClassSymbol = JavaRepeatedParamClass

      def unapply(tpe: u.TypeRef): Option[u.Type] = tpe match {
        case u.TypeRef(_, `scalaSym`, Seq(arg)) => Some(arg)
        case u.TypeRef(_, `javaSym`, Seq(arg)) => Some(arg)
        case _ => None
      }
    }
  }
}
