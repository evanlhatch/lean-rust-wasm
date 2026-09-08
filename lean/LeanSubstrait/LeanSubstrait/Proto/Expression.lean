/-
# LeanSubstrait.Proto.Expression

Wire-faithful model of Substrait's `algebra.proto` expression surface.  Plain
total data, no proofs; the `Expr`-producing side of the typed layer lowers to
this.  `Subquery` is deliberately opaque (a name + a string payload): the text
grammar cannot express subqueries and we only need the wire slot to exist.

The `Expression.Literal` message carries a `nullable` flag and a
`literal_type` union — both mirrored here (`Literal.nullable`, `LiteralType`).

`Expression` is kept **inline** (each constructor carries its message fields
directly): the recursive-before-declaration problem that separate
sub-structures would create is avoided, and the shapes still mirror the proto
one-to-one (`IfThen` = list of (if, then) pairs + else, etc.).
-/
import LeanSubstrait.Proto.Type

namespace LeanSubstrait.Proto

/-- Proto `Expression.Literal.LiteralType` value kinds (skeleton). -/
inductive LiteralType where
  | bool   (b : Bool)
  | i8     (v : Int)
  | i16    (v : Int)
  | i32    (v : Int)
  | i64    (v : Int)
  | fp32   (v : Float)
  | fp64   (v : Float)
  | string (s : String)
  | binary (bytes : List UInt8)
  | null   (t : PType)
deriving Repr, BEq, Inhabited

/-- Proto `Expression.Literal` — a typed literal with its nullability flag. -/
structure Literal where
  literalType : LiteralType
  nullable : Bool := false
deriving Repr, BEq, Inhabited

/--
Proto `Expression.FieldReference` — a direct column reference (mirrors
`FieldReference { direct_reference { struct_field { field } }, root_reference }`).
`ordinal` is the index into the input (root) struct; `segment` an optional
deeper struct-field segment (unused by the text grammar).
-/
structure FieldReference where
  ordinal : Nat
  segment : Option Nat
deriving Repr, BEq, Inhabited

/-- Proto `Expression.Cast.FailureBehavior`. -/
inductive CastFailureBehavior where
  | unspecified
  | returnNull
  | throwException
deriving Repr, BEq, Inhabited

/--
Proto `Expression` — union mirroring `algebra.proto` `RexType`.  `Literal`
carries its own typing; `FieldReference` is a root-anchored ordinal reference;
`ScalarFunction` embeds its derived `outputType`; `IfThen` is a list of
(if cond, then value) pairs plus a required else; `Cast` carries a target
type and a failure behavior; `Subquery` is opaque.
-/
inductive Expression where
  | literal (lit : Literal)
  | field (ref : FieldReference)
  | scalarFunction
      (functionReference : Nat)
      (args : List Expression)
      (outputType : PType)
  | ifThen
      (ifs : List (Expression × Expression))
      (elseExpr : Expression)
  | cast
      (input : Expression)
      (targetType : PType)
      (failureBehavior : CastFailureBehavior)
  | subquery (name : String) (payload : String)
deriving Repr, BEq, Inhabited

end LeanSubstrait.Proto
