/-
# SchemaLang.Meta.WireCodec — `deriving WireCodec`: per-structure wire codec

W7.14 (runbook-2026-09-15): "per-structure codec + append-form round-trip
proof, generated (EnumWire is the working precedent at enum scale; Codec
combinators + CheckedProp do the lifting)". This module graduates the
review-2026-09-16 F2/F3 rows: `Kit.PartialIso` gets its codec consumer
(`WireCodec.toPartialIso`) and `RoundTripSpec` gets its generated
assembly (`<S>.roundTripSpec`).

**Deriving-vs-command (the pinned decision).** EnumWire is a COMMAND
because it must CREATE the inductive from a constructor list. Here the
structure already exists — the declaration-site hook that runs over an
existing declaration is `deriving`, and the work order names it
(`deriving WireCodec`). The registration discipline follows
`CodegenCore.Enumerable`'s handler (the in-tree deriving precedent):
gate → generate → `initialize registerDerivingHandler`.

## What the handler generates (for `structure S … deriving WireCodec`)

(a) `instance : WireCodec S` — the encoder/decoder over the Codec.lean
    combinators (fields in declaration order, self-delimiting
    concatenation) with the append-form law
    `dec? (enc a ++ rest) = some (a, rest)` PROVED;
(b) thin wrappers `S.encode` / `S.decode?` / `S.decode` (the EnumWire
    naming parity);
(c) `meta def S.roundTripSpec : CodegenCore.RoundTripSpec S` — the
    codec lands in the sweep machinery: the PropSpec bridge carries the
    decode∘encode sweep AND the mandatory byte-sabotage negative
    control (TestKit.PropSpec: an uncaught control fails the gate).
    Missing sweep-machinery instances (`Repr`, `BEq`, `Arbitrary`,
    `Shrinkable` — the `SampleableExt.selfContained` inputs) are
    derived when absent; pre-existing ones are used.

## The proof automation (why every supported field shape composes)

The class law is a FIELD of the instance, so the generated structure
proof never unfolds a codec: one `simp` rule
(`WireCodec.decode_encode_append`) rewrites each field's head decode in
place, `Option.bind` iota steps through, `List.append_assoc` +
`nil_append` normalize the concatenation. Field coverage = instance
coverage: the atoms (Bool / UInt8 / Nat / UInt64 / String) ride
Codec.lean's appendix of append-form lemmas once each; `Option`/`List`
compose through `decOpt_encOpt_append`/`decList_encList_append`; a
field of another `deriving WireCodec` structure composes through THAT
structure's instance. Where no instance exists the handler REFUSES
LOUDLY, naming the offending field — never a `sorry`, never a silent
skip. Refusals: non-structures (enums → `declare_enum_wire`),
parameterized structures (W8.12's monomorphization lane), recursive
occurrences (the instance does not exist mid-derivation — the field
check catches it), and field types with no `WireCodec` instance (Float,
Int, function types, …).

**Wire format**: fields in declaration order, each self-delimiting;
reordering fields is a WIRE-BREAKING change (the EnumWire tag rule at
structure scale). `S.decode` drops trailing bytes (RoundTripSpec's
documented boundary adaptation); the append form is the law of record.

Ownership: schema-lang owns this file (its Tests section is the only
consumer in-tree so far). Deliberate exclusions: golden byte-ties are
NOT generated (the handler cannot know a goldenDir; consumers override
`{ S.roundTripSpec with samples := …, goldenDir := … }`); no enum
support (EnumWire owns that lane); no `result`/`map`/`set`/`tensor`
field types (Codec.lean has no atoms for them — the refusal names the
field).
-/

module

public import Lean
public import SchemaLang.Codec
public import Plausible
public import TestKit
public import CodegenCore.Kit
public import CodegenCore.RoundTrip

@[expose] public section

namespace SchemaLang

/-- A binary wire codec for `α` over the Codec.lean combinators: a
    self-delimiting encoder, an append-form decoder (value + remaining
    bytes), and the append-form round-trip law AS A FIELD — the Kit
    `PartialIso` row transported through bind, made composable by
    keeping the law at the class level so structure proofs rewrite with
    it directly. -/
class WireCodec (α : Type) where
  /-- Encode (self-delimiting). -/
  enc : α → List UInt8
  /-- Append-form decode: the value plus the remaining bytes. -/
  dec? : List UInt8 → Option (α × List UInt8)
  /-- The append-form round-trip law (Codec.lean's composable shape). -/
  decode_encode_append : ∀ (a : α) (rest : List UInt8),
    dec? (enc a ++ rest) = some (a, rest)

namespace WireCodec

/-- The plain (non-append) decoder: the value, trailing bytes dropped. -/
def decode (α : Type) [WireCodec α] (bs : List UInt8) : Option α :=
  (WireCodec.dec? bs).map (·.1)

/-- The plain round trip (the kit `PartialIso` law shape), transported
    from the append form. -/
theorem decode_encode (α : Type) [WireCodec α] (a : α) :
    decode α (WireCodec.enc a) = some a := by
  have h := WireCodec.decode_encode_append (α := α) a []
  rw [List.append_nil] at h
  simp [decode, h]

/-- A `WireCodec` IS a kit `PartialIso` (canon row "a codec = a
    PartialIso (W1.2)" — the F2 graduation: the row's first codec
    consumer). -/
def toPartialIso (α : Type) [WireCodec α] : CodegenCore.PartialIso (List UInt8) α where
  decode := decode α
  encode := WireCodec.enc
  decode_encode := decode_encode α

end WireCodec

/-! ## The codec-supported atom instances (Codec.lean's atoms, once each) -/

instance : WireCodec Bool where
  enc := Codec.encodeBool
  dec? := Codec.decBool?
  decode_encode_append := Codec.decBool_encodeBool_append

instance : WireCodec UInt8 where
  enc := Codec.encodeU8
  dec? := Codec.decU8?
  decode_encode_append := Codec.decU8_encodeU8_append

instance : WireCodec Nat where
  enc := Codec.encVarNat
  dec? := Codec.decNat?
  decode_encode_append := Codec.decNat_encVarNat_append

instance : WireCodec UInt64 where
  enc := Codec.encU64
  dec? := Codec.decU64?
  decode_encode_append := Codec.decU64_encU64_append

instance : WireCodec String where
  enc := Codec.encString
  dec? := Codec.decString?
  decode_encode_append := Codec.decString_encString_append

/-- `Option`: the Codec.lean tag byte composes the element instance. -/
instance [WireCodec α] : WireCodec (Option α) where
  enc := Codec.encOpt (WireCodec.enc (α := α))
  dec? := Codec.decOpt? (WireCodec.dec? (α := α))
  decode_encode_append :=
    Codec.decOpt_encOpt_append _ _ fun a rest =>
      WireCodec.decode_encode_append a rest

/-- `List`: the Codec.lean length-prefix composes the element instance.
    (`List UInt8` fields ride this generic instance — the elementwise
    form, not `encBytes`; one list wire shape, one law.) -/
instance [WireCodec α] : WireCodec (List α) where
  enc := Codec.encList (WireCodec.enc (α := α))
  dec? := Codec.decList? (WireCodec.dec? (α := α))
  decode_encode_append :=
    Codec.decList_encList_append _ _ fun a rest =>
      WireCodec.decode_encode_append a rest

end SchemaLang

namespace SchemaLang.Meta

open Lean Elab Command
open Lean.Elab.Deriving (withoutExposeFromCtors)

/-- The generated binder name for a field (`id` ↦ `v_id`) — prefixed so
    a field name that collides with a reserved token (the `prefix`
    lesson) cannot break the generated quotations. -/
def wireVar (f : Name) : Name := f.appendBefore "v_"

/-- Does `declName` already carry an instance of class `cls`? (The
    conditional-derivation check: generate only what is missing.) -/
def hasInstance (cls declName : Name) : CommandElabM Bool :=
  liftTermElabM do
    let ty ← Meta.mkAppM cls #[mkConst declName]
    return (← Meta.synthInstance? ty).isSome

/-- The encoder: `fun ⟨v_f₁, …, v_fₙ⟩ => enc v_f₁ ++ (… ++ [])`. -/
def mkEncFn (fields : Array Name) : TermElabM Term := do
  let vs := fields.map fun f => mkIdent (wireVar f)
  let ets ← fields.toList.mapM fun f =>
    `(SchemaLang.WireCodec.enc $(mkIdent (wireVar f)))
  let rec chain : List Term → TermElabM Term
    | [] => `(([] : List UInt8))
    | [t] => pure t
    | t :: ts => do `($t ++ $(← chain ts))
  let body ← chain ets
  `(fun ⟨$vs,*⟩ => $body)

/-- The append-form decoder: a left-nested `Option.bind` chain, one
    `WireCodec.dec?` per field, ending `some (⟨v_f₁, …, v_fₙ⟩, rₙ)`. -/
def mkDecFn (fields : Array Name) : TermElabM Term := do
  let bs := mkIdent `bs
  let vs := fields.map fun f => mkIdent (wireVar f)
  let rs := fields.mapIdx fun i _ => mkIdent (Name.mkSimple s!"r{i + 1}")
  let rec go (i : Nat) (inp : Term) : TermElabM Term := do
    if i < fields.size then
      let inner ← go (i + 1) (rs[i]! : Term)
      `(Option.bind (SchemaLang.WireCodec.dec? $inp) (fun ($(vs[i]!), $(rs[i]!)) => $inner))
    else
      `(some (⟨$vs,*⟩, $inp))
  let body ← go 0 (bs : Term)
  `(fun $bs => $body)

/-- The codec instance itself: `enc` / `dec?` plus the append-form law,
    proved by the ONE class-law simp rule over the field chain (the
    module header's proof-automation note). -/
def mkCodecInstance (declName : Name) (fields : Array Name) :
    TermElabM (TSyntax `command) := do
  let encFn ← mkEncFn fields
  let decFn ← mkDecFn fields
  let vs := fields.map fun f => mkIdent (wireVar f)
  `(instance : SchemaLang.WireCodec $(mkCIdent declName) where
      enc := $encFn
      dec? := $decFn
      decode_encode_append := fun x rest => by
        cases x with
        | mk $[$vs]* =>
            simp [List.append_assoc, SchemaLang.WireCodec.decode_encode_append])

/-- The `Arbitrary` instance: one draw per field (`⟨·⟩`-assembled). -/
def mkArbitraryInstance (declName : Name) (fields : Array Name) :
    TermElabM (TSyntax `command) := do
  let vs := fields.map fun f => mkIdent (wireVar f)
  let arb := mkCIdent ``Plausible.Arbitrary.arbitrary
  let lets ← vs.mapM fun v => `(doElem| let $v ← $arb:ident)
  `(instance : Plausible.Arbitrary $(mkCIdent declName) where
      arbitrary := do
        $[$lets:doElem]*
        pure ⟨$vs,*⟩)

/-- The RoundTripSpec assembly (the F3 graduation): the codec's
    `PartialIso` rides the sweep machinery — the PropSpec bridge carries
    the decode∘encode sweep AND the mandatory byte-sabotage negative
    control. `meta`: `RoundTripSpec` is a meta-section citizen. -/
def mkRoundTripSpec (declName : Name) : TermElabM (TSyntax `command) := do
  `(meta def $(mkIdent (declName ++ `roundTripSpec)) :
      CodegenCore.RoundTripSpec $(mkCIdent declName) where
    name := $(quote declName.toString)
    iso := SchemaLang.WireCodec.toPartialIso $(mkCIdent declName))

/-- The `deriving WireCodec` handler. Gates (all LOUD — the module
    header's refusal surface): exactly one declaration; a structure; no
    parameters; every flattened field carries a `WireCodec` instance
    (the offending field is NAMED on failure). -/
def mkWireCodecHandler (declNames : Array Name) : CommandElabM Bool := do
  unless (← declNames.allM fun n => isInductive n) do return false
  unless declNames.size == 1 do
    throwError "deriving WireCodec: mutual blocks are not supported — \
      derive per structure"
  let declName := declNames[0]!
  let env ← getEnv
  unless isStructure env declName do
    throwError "deriving WireCodec: `{declName}` is not a structure — \
      for enums use `declare_enum_wire` (SchemaLang.EnumWire)"
  let indVal ← getConstInfoInduct declName
  unless indVal.numParams == 0 && indVal.numIndices == 0 do
    throwError "deriving WireCodec: `{declName}` is parameterized — \
      parameterized structures are W8.12's monomorphization lane; \
      derive at each concrete instantiation"
  let fields := getStructureFieldsFlattened env declName
  -- the refusal check: every field type must carry a WireCodec instance
  for f in fields do
    let some projName := getProjFnForField? env declName f
      | throwError "deriving WireCodec: `{declName}` field `{f}` has no \
          projection (internal — report)"
    let fty := (← getConstInfo projName).type.bindingBody!.instantiate1
      (mkConst declName)
    let ok ← liftTermElabM do
      return (← Meta.synthInstance? (← Meta.mkAppM ``SchemaLang.WireCodec #[fty])).isSome
    unless ok do
      let ftyPP ← liftTermElabM (Meta.ppExpr fty)
      throwError "deriving WireCodec: field `{f} : {ftyPP}` of \
        `{declName}` has no `SchemaLang.WireCodec` instance — \
        codec-supported field types: Bool / UInt8 / Nat / UInt64 / \
        String, Option and List over them, and other \
        `deriving WireCodec` structures (the wire family widens in \
        Codec.lean, not per call site)"
  withoutExposeFromCtors declName do
    -- (a) the codec + the law
    elabCommand (← liftTermElabM <| mkCodecInstance declName fields)
    -- (b) the EnumWire-parity wrappers
    elabCommand (← `(def $(mkIdent (declName ++ `encode)) :
        $(mkCIdent declName) → List UInt8 := SchemaLang.WireCodec.enc))
    elabCommand (← `(def $(mkIdent (declName ++ `decode?)) :
        List UInt8 → Option ($(mkCIdent declName) × List UInt8) :=
        SchemaLang.WireCodec.dec?))
    elabCommand (← `(def $(mkIdent (declName ++ `decode)) :
        List UInt8 → Option $(mkCIdent declName) :=
        SchemaLang.WireCodec.decode $(mkCIdent declName)))
    -- (c) the sweep machinery: derive the missing instances only
    unless (← hasInstance ``Repr declName) do
      elabCommand (← `(deriving instance Repr for $(mkCIdent declName)))
    unless (← hasInstance ``BEq declName) do
      elabCommand (← `(deriving instance BEq for $(mkCIdent declName)))
    unless (← hasInstance ``Plausible.Arbitrary declName) do
      elabCommand (← liftTermElabM <| mkArbitraryInstance declName fields)
    unless (← hasInstance ``Plausible.Shrinkable declName) do
      elabCommand (← `(instance : Plausible.Shrinkable $(mkCIdent declName) := {}))
    elabCommand (← liftTermElabM <| mkRoundTripSpec declName)
  return true

initialize
  registerDerivingHandler ``SchemaLang.WireCodec mkWireCodecHandler

end SchemaLang.Meta
