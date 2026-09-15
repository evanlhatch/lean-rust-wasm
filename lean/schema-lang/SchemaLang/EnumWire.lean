/-
# SchemaLang.EnumWire — `declare_enum_wire`: enum boilerplate, generated

Doctrine §6 ("boilerplate families are generated, not written — enum wire
codecs"): ONE command from a constructor list generates the whole enum
wire family, so the hand-rolled encode/decode/token triples cannot drift:

    declare_enum_wire Delivery where once | stream

generates, in the enclosing namespace:

(a) the enum inductive (`deriving Repr, BEq, DecidableEq, Inhabited`,
    the item-model derivation set) plus an `all` list (exhaustive
    witnesses) —
(b) the wire codec: the token spelling (`toToken`/`ofToken?` — the ONE
    spelling the snapshot codec and `@[schema_fn]` attr args consume)
    and the binary codec over `Codec.encEnum`/`Codec.decEnum?` with the
    round-trip laws proved (the Codec.lean append form, so per-field
    lemmas compose) —
(c) the plausible instances (`Arbitrary`/`Shrinkable` — the Gen!),
    tags 0..k-1 uniformly, shrinking to the first ctor —
(d) the PropSpec with its MANDATORY negative control (TestKit.PropSpec):
    the sweep pins `decode? ∘ encode = some`; the sabotaged sibling
    (`tag + 1` corruption) must be caught or the suite fails.

Placement: schema-lang, not codegen-core — the generated codec consumes
`SchemaLang.Codec`'s enum combinators, and the dogfood consumer is the
item model itself (`Item.lean`'s NullSem/Determinism/Delivery were the
three hand-rolled triples this command replaces).

The wire tags are the CONSTRUCTOR ORDER (0-based, closed at the
declaration): inserting a ctor appends a new tag only if done at the
end — reordering is a WIRE-BREAKING change (the same rule as the
versioned envelope's fingerprint; `BreakingMain` is the gate).

Ledger (sibling-lane maintenance): this module came from the
port-smalls lane; the Vortex-encodings lane applied a one-line fix
while landing Vortex/Batch — `tokArms`' lambda is now
`(fun (c, _) => …)`, destructuring `zipIdx`'s (elem, index) pair
order on v4.33 (the token arms read the CTOR, discarding the index).
-/

import Lean
import SchemaLang.Codec
import Plausible
import TestKit

namespace SchemaLang.EnumWire

open Lean Elab Command

/-- Elaborate ONE generated declaration (source text → parsed command →
    elabCommand). Parse errors are internal (the generator wrote them). -/
def elabGenerated (src : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e =>
      throwError "declare_enum_wire: internal: generated code failed to parse\n{e}"

/-- The generated declarations, in order (each entry is one command). -/
def generatedSources (n : String) (ctors : Array String) : Array String :=
  let k := ctors.size
  let first := ctors[0]!
  let indAlts := String.intercalate " " (ctors.toList.map (fun c => s!"| {c}"))
  let tokArms := String.intercalate "\n"
    ((ctors.toList.zipIdx).map (fun (c, _) => s!"  | .{c} => \"{c}\""))
  let tokParseArms := String.intercalate "\n"
    (ctors.toList.map (fun c => s!"  | \"{c}\" => some .{c}")) ++ "\n  | _ => none"
  let tagArms := String.intercalate "\n"
    ((ctors.toList.zipIdx).map (fun (c, i) => s!"  | .{c} => {i}"))
  let tagParseArms := String.intercalate "\n"
    ((ctors.toList.zipIdx).map (fun (c, i) => s!"  | {i} => some .{c}"))
      ++ s!"\n  | _ => none"
  let allLit := String.intercalate ", " (ctors.toList.map (fun c => s!".{c}"))
  let genArms := String.intercalate "\n"
    ((ctors.toList.zipIdx).map (fun (c, i) => s!"    | {i} => .{c}"))
      ++ s!"\n    | _ => .{first}"
  #[
  -- (a) the enum inductive + the exhaustive list
  s!"inductive {n} where\n  {indAlts}\nderiving Repr, DecidableEq, Inhabited",
  s!"def {n}.all : List {n} := [{allLit}]",
  -- (b) the token spelling (the ONE spelling — Snapshot + attr args)
  s!"def {n}.toToken : {n} → String\n{tokArms}",
  s!"def {n}.ofToken? : String → Option {n}\n{tokParseArms}",
  -- (b) the binary codec over Codec.encEnum/decEnum?
  s!"def {n}.toTag : {n} → Nat\n{tagArms}",
  s!"def {n}.ofTag? : Nat → Option {n}\n{tagParseArms}",
  s!"def {n}.encode : {n} → List UInt8\n  | e => SchemaLang.Codec.encEnum e.toTag",
  s!"def {n}.decode? : List UInt8 → Option ({n} × List UInt8)\n  | bs => SchemaLang.Codec.decEnum? {n}.ofTag? bs",
  -- the round-trip laws (the Codec append form + the plain form)
  s!"theorem {n}.ofTag_toTag : ∀ (e : {n}), {n}.ofTag? ({n}.toTag e) = some e := by\n  intro e\n  cases e <;> rfl",
  s!"theorem {n}.decode_encode_append (e : {n}) (rest : List UInt8) :\n    {n}.decode? ({n}.encode e ++ rest) = some (e, rest) :=\n  SchemaLang.Codec.decEnum_encEnum_append {n}.toTag {n}.ofTag? {n}.ofTag_toTag e rest",
  s!"theorem {n}.decode_encode (e : {n}) : {n}.decode? ({n}.encode e) = some (e, []) := by\n  simpa using {n}.decode_encode_append e []",
  -- (c) the plausible instances (the Gen) + the Bool round-trip predicate
  s!"def {n}.roundTrips (e : {n}) : Bool :=\n  ({n}.decode? ({n}.encode e)).map (·.1) == some e",
  s!"theorem {n}.roundTrips_true (e : {n}) : {n}.roundTrips e = true := by\n  cases e <;> simp [{n}.roundTrips, {n}.decode_encode]",
  s!"instance : Plausible.Arbitrary {n} where\n  arbitrary := do\n    let i ← Plausible.Gen.chooseNat\n    pure (match i % {k} with\n{genArms})",
  s!"instance : Plausible.Shrinkable {n} where\n  shrink e := if e == {n}.{first} then [] else [{n}.{first}]",
  -- (d) the PropSpec with the MANDATORY negative control
  s!"def {n}.wireSabotage (e : {n}) : Bool :=\n  {n}.ofTag? ({n}.toTag e + 1) == some e",
  s!"def {n}.wireSuite : LSpec.TestSeq :=\n  LSpec.checkPlausibleIO \"enum wire: decode? ∘ encode = some (round trip)\"\n    (∀ (e : {n}), {n}.roundTrips e = true)\n    .done \{ numInst := 256, randomSeed := some 20261104 }",
  s!"def {n}.wireControl : LSpec.TestSeq :=\n  LSpec.checkPlausibleIO \"sabotaged: tag+1 corruption (must be caught)\"\n    (∀ (e : {n}), {n}.wireSabotage e = true)\n    .done \{ numInst := 256, randomSeed := some 20261104 }",
  s!"def {n}.wirePropSpec : TestKit.PropSpec :=\n  \{ name := \"enum wire: {n} decode∘encode round trip\"\n  , suite := {n}.wireSuite\n  , control := {n}.wireControl\n  , controlName := \"tag+1 sabotage\" }"
  ]

/-- `declare_enum_wire <Name> where <ctor> | ... | <ctor>` — generate the
    enum inductive, its token spelling, its binary wire codec with the
    proved round-trip laws, the plausible instances, and the PropSpec
    with its mandatory negative control (module header: the family). -/
syntax (name := declareEnumWire) "declare_enum_wire " ident " where "
  ident (" | " ident)* : command

@[command_elab declareEnumWire]
def declareEnumWireImpl : CommandElab := fun stx => do
  let n := stx[1].getId.toString
  let mut ctors : Array String := #[stx[3].getId.toString]
  for rep in stx[4].getArgs do
    ctors := ctors.push rep[1].getId.toString
  if ctors.isEmpty then
    throwError "declare_enum_wire {n}: at least one constructor required"
  if (ctors.toList.eraseDups).length != ctors.size then
    throwError s!"declare_enum_wire {n}: duplicate constructor names"
  for src in generatedSources n ctors do
    elabGenerated src

end SchemaLang.EnumWire
