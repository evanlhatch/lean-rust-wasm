/-
# LeanSubstrait.Proto.Type

Wire-faithful model of Substrait's `type.proto` surface (plain total Lean data,
no proofs).  This mirrors the protobuf message shapes so that a future protoc
codegen / wire encoder has a stable target; everything here is `Repr`/`BEq`
comparable and evaluable.

Nullability is modelled with all three proto values (Unspecified / Nullable /
Required).  The typed layer (`LeanSubstrait.Typed`) never produces Unspecified
on the wire — see the emitter contract in `LeanSubstrait.Emit.Text`.

The inductive is named `PType` (not `Type`) to avoid colliding with Lean's
type-universe keyword; `Param` became `PParam`.  (A "P-Type"/"P-Param" naming
is the package's way to say "proto Type"/"proto Param".)
-/
namespace LeanSubstrait.Proto

/-- Proto `Type.Nullability` (values 0,1,2). -/
inductive Nullability where
  | unspecified
  | nullable
  | required
deriving Repr, BEq, Inhabited

mutual
  inductive PType where
    | bool (n : Nullability)
    | i8   (n : Nullability)
    | i16  (n : Nullability)
    | i32  (n : Nullability)
    | i64  (n : Nullability)
    | fp32 (n : Nullability)
    | fp64 (n : Nullability)
    | string (n : Nullability)
    | binary (n : Nullability)
    | decimal (precision scale : Nat) (n : Nullability)
    | list   (elem : PType) (n : Nullability)
    | map    (key value : PType) (n : Nullability)
    | struct (fields : List PType) (n : Nullability)
    | userDefined (anchor : Nat) (params : List PParam) (n : Nullability)
  deriving Repr, BEq, Inhabited

  inductive PParam where
    | boolean (b : Bool)
    | integer (i : Int)
    | string (s : String)
    | enum (e : String)
    | null (t : PType)      -- a null literal of the given type
    | dataType (t : PType)  -- a whole type, for parameterized types
  deriving Repr, BEq, Inhabited
end

/--
Coverage note: the full substrait type catalogue is deliberately not
replicated yet — this is the skeleton set the typed layer emits today.
`fixedchar`, `varchar`, `fixedbinary`, precision time/timestamp, interval and
uuid kinds are future work; they will be added as constructors when the emit
layer grows them.

The nullability of a type; helper accessor.
-/
def PType.nullability : PType → Nullability
  | .bool n        => n
  | .i8 n          => n
  | .i16 n         => n
  | .i32 n         => n
  | .i64 n         => n
  | .fp32 n        => n
  | .fp64 n        => n
  | .string n      => n
  | .binary n      => n
  | .decimal _ _ n => n
  | .list _ n      => n
  | .map _ _ n     => n
  | .struct _ n    => n
  | .userDefined _ _ n => n

end LeanSubstrait.Proto
