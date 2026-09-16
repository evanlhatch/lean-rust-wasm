/- # SchemaLang.Gen — the schema-typed value generators

LIFTED VERBATIM-SHAPE from `Tests/Main.lean`'s `CodecValueSweep` section
(`genU8`, `genChar`, `genShortList`, `genVal`, `valueEq`) into the
library: the foundation for schema-derived ROW generators. The sweep
stays the consumer — its `Pack`/`genPack`/`Shrinkable` wrappers remain
test-side; this module supplies the per-type value generators they were
built on.

Ownership: schema-lang's generator lane. `SchemaLang/Ty.lean` (the
universe + the `Value`/`VList`/`TVal` GADT families) and
`SchemaLang/CodecValue.lean` (the codec, `CodecClosed`, `unzigzag`,
`buildOne?`, `defaultValue`, `listToVList`) are read-only dependencies —
nothing is duplicated from them here.

Deliberate exclusions (scope honesty):
- The TEST-SIDE sweep scaffolding (`Pack`, `genLeafPack`/`genPack`,
  the `Arbitrary`/`ArbitraryFueled`/`Shrinkable`/`Repr` instances,
  `sizeV`/`sizeL`/`sizeT`/`sizeS`, `valueReprStr` and friends) stays in
  `Tests/Main.lean` — a `Pack` couples type+proof+value as one sample;
  a library consumer derives its own packs. The size measures serve
  only the debug repr chain's termination, which is test-side too.
- NO TVal/TSlices generator beyond what the `genVal` tensor arm needs:
  the shape-FILLED discipline means there is nothing separate to
  generate — the dims are the TYPE's data (never a choice), the flat
  elements are generated at `dims.prod`, assembled by the codec's own
  `buildOne?`, with the `defaultValue` fallback. A standalone
  size-bounded `TVal` generator would re-derive `buildOne?`'s assembly
  for no new values.
- `f32`/`f64` have no generator arm (they mirror `CodecClosed` — no
  closure case, no round-trip proof) and `.ty` refs carry no values.
- The ROW-GENERATOR command (`derive_row_gen`) lives in
  `SchemaLang/Meta/Gen.lean` (the elab half — it walks the registry);
  this module holds the runtime half (`FieldsClosed`/`genRowVals`,
  below).

Driving decision: `valueEq` is lifted (not left test-side) because it
is the executable equality on `Value t` — the GADT has no
`DecidableEq`, and the byte-equality route (encode both, compare) is
the total, reflexive, round-trip-faithful alternative. Any row-level
property needs to compare values, so the equality rides with the
generators.
-/

module

public import SchemaLang.CodecValue
public import SchemaLang.Trace
public import Plausible

@[expose] public section

namespace SchemaLang

open Plausible

/-! ## Leaf + list helpers (lifted verbatim-shape) -/

/-- Short bounded list (the sweep's list-shape bound). -/
def genShortList (g : Gen α) (maxLen : Nat) : Gen (List α) := do
  let len ← Gen.chooseNat
  let rec go : Nat → Gen (List α)
    | 0 => pure []
    | k + 1 => do pure ((← g) :: (← go k))
  go (len % (maxLen + 1))

/-- Chars from a tiny alphabet (`a b c`) — small supplies shrink well. -/
def genChar : Gen Char := do
  let n ← Gen.chooseNat
  pure (Char.ofNat ('a'.toNat + n % 3))

/-- Full-range u8 (the wire's leaf). -/
def genU8 : Gen UInt8 := do
  pure ((← Gen.chooseNat) % 256).toUInt8

/-! ## The value generator (lifted verbatim-shape) -/

/-- One value of type `t` (must be codec-closed), size-bounded by fuel.
    The tensor arm is SHAPE-FILLED: the dims are the type's data, the
    generator fills them — flat elements at `dims.prod`, assembled by
    the codec's own shape-checked `buildOne?`, the default tensor as
    the fallback. Fuel 0: composites fall back to the default value. -/
def genVal : (t : Ty) → CodecClosed t → Nat → Gen (Value t)
  | .bool, _, _ => do pure (.bool ((← Gen.chooseNat) % 2 == 0))
  | .u8, _, _ => do pure (.u8 (← genU8))
  | .u16, _, _ => do pure (.u16 ((← Gen.chooseNat) % 65536).toUInt16)
  | .u32, _, _ => do pure (.u32 ((← Gen.chooseNat) % 4294967296).toUInt32)
  | .u64, _, _ => do
      pure (.u64 ((← Gen.chooseNat) % 18446744073709551616).toUInt64)
  | .i8, _, _ => do pure (.i8 (Int8.ofInt (unzigzag ((← Gen.chooseNat) % 200))))
  | .i16, _, _ => do
      pure (.i16 (Int16.ofInt (unzigzag ((← Gen.chooseNat) % 40000))))
  | .i32, _, _ => do
      pure (.i32 (Int32.ofInt (unzigzag ((← Gen.chooseNat) % 4000000000))))
  | .i64, _, _ => do
      pure (.i64 (Int64.ofInt (unzigzag ((← Gen.chooseNat) % 1000000000000000000))))
  | .string, _, _ => do pure (.string (String.ofList (← genShortList genChar 4)))
  | .bytes, _, _ => do pure (.bytes (← genShortList genU8 4))
  | .option t, .option h, fuel + 1 => do
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure .none else pure (.some (← genVal t h fuel))
  | .result ok err, .result hok herr, fuel + 1 => do
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure (.ok (← genVal ok hok fuel))
      else pure (.err (← genVal err herr fuel))
  | .list t, .list h, fuel + 1 => do
      pure (.list (listToVList (← genShortList (genVal t h fuel) 3)))
  | .future t, .future h, fuel + 1 => do pure (.future (← genVal t h fuel))
  | .stream t, .stream h, fuel + 1 => do
      pure (.stream (listToVList (← genShortList (genVal t h fuel) 3)))
  | .tensor dims a, .tensor h, fuel + 1 => do
      -- the shape-FILLED random tensor: the flat elements generated at
      -- the type's count (the dims are the type's data, not a choice),
      -- assembled by the codec's own shape-checked builder; the
      -- fallback = the default tensor (the generator's base)
      let elems ← (List.range dims.prod).mapM (fun _ => genVal a h (fuel - 1))
      match buildOne? a (dims.prod * (dims.length + 1) + dims.length + 10) dims elems with
      | some (tv, []) => pure (.tensor tv)
      | _ => pure (defaultValue (.tensor dims a) (.tensor h))
  -- fuel 0: composites fall back to the default value (u8 is the
  -- oneOfWithDefault default leaf below, so the control still bites)
  | t, h, 0 => pure (defaultValue t h)
  termination_by _ _ fuel => fuel

/-! ## The executable equality on `Value t` -/

/-- Structural equality on `Value t`, THROUGH the codec: two values are
    equal iff their encodings are byte-equal. NOT a GADT match — the
    three-arg GADT match's unfold equations are underivable (the
    catch-all-vs-refined splitter limit); the codec route is total,
    reflexive (byte equality), and faithful on the codec-closed
    universe (the round-trip theorem: equal bytes decode equal). The
    sweep's properties and shrinker consume this. -/
def valueEq (t : Ty) (a b : Value t) : Bool :=
  encodeValue t a == encodeValue t b

/-- the refl pin, kernel-checked (the equality is not vacuous). -/
theorem valueEq_refl (t : Ty) (v : Value t) : valueEq t v v = true :=
  beq_self_eq_true _

/-! ## The ROW generators — the registry/item-level layer -/

/-- The row generator: one `genVal` per field, in SCHEMA order — the
    shape (fields, order, types) is the registry's data; the generator
    FILLS it, never chooses it (the same shape-FILLED rule the tensor
    arm obeys). Total: structural on the fields. Size-bounded: the fuel
    threads to every `genVal` (composite fields spend it, leaves fall
    back to `defaultValue` at fuel 0). The closedness witness is
    Trace's `FieldsClosed` (the same family the row-codec's round-trip
    theorem takes — generator and codec share the admission ticket). -/
def genRowVals : (fields : List Field) → FieldsClosed fields → Nat →
    Gen (RowVals fields)
  | [], .nil, _ => pure .nil
  | f :: fs, .cons h hr, fuel => do
      let v ← genVal f.ty h fuel
      let rest ← genRowVals fs hr fuel
      pure (.cons v rest)

end SchemaLang
