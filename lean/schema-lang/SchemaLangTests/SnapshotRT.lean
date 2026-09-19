/-
# Tests.SnapshotRT — the snapshot-codec differential support (fuzz-gap audit, gap #2)

The snapshot format has TWO hand-ported parsers (`SchemaLang.Snapshot`
— the format's authority — and `crates/steel-host/src/hostgen.rs`'s
Rust twin) and three inspection-visible drifts (empty `ty()` ref,
kebab-at-parse asymmetry, CRLF). This module is the SHARED support for
both consumers:

1. `Tests/Main.lean`'s `SnapshotRTPins` section — the Lean-side
   round-trip PropSpec (`parse ∘ render = id` over the full `Ty`
   vocabulary: option/result/list/future/stream/map/set/tensor, which
   the seeded `PropSweep` generator does NOT produce) plus the three
   drifts' regression pins;
2. the `snapshot-fixtures` exe (`SnapshotFixturesMain.lean`) — emits
   N seeded (snapshot-text, expected-item-dump) pairs to
   `crates/steel-host/tests/fixtures/snapshot_fixtures.txt`; the Rust
   differential (`tests/snapshot_differential.rs`) replays each pair
   through `hostgen::parse_snapshot`.

Ownership: schema-lang's snapshot-codec test lane. `SchemaLang/Snapshot.lean`
(the codec under test) is a read-only dependency — the drift FIXES land
there, but this module only observes. Deliberate exclusions: the
`PropSweep` name-resolution sweep keeps its OWN generator (its property
is resolution, not encoding — widening it would dilute both); the dump
format below deliberately does NOT reuse `Ty.toSnapshot` for types (an
independent spelling prevents a Rust `parse_ty_text` drift from
cancelling between the two sides of the differential).

Driving decision: seeded via plausible's `Gen` + a pinned seed (the
byte-tie law for generated fixtures — a regen is byte-identical), NOT a
hand list: the sweep found no Lean-side counterexample, so the random
vocabulary is the point (a hand list pins only what it names).
-/

import Lean
import SchemaLang
import Plausible
import TestKit

open Plausible SchemaLang TestKit

namespace SnapshotRT

/-! ## The full-vocabulary generator -/

/-- The name supply: alphanumeric (the `nameOk` gate's happy path) and
    deliberately MIXED-CASE — the kebab asymmetry's positive pins ride
    these names through render→parse and the Rust fixtures. -/
def nameSupply : List String :=
  ["alpha", "beta", "gamma", "OrderItem", "getUser"]

/-- Small field/case/param name supply (mixed case, same reason). -/
def fieldSupply : List String := ["id", "name", "qty", "unitPrice"]

/-- Pick a name from a supply. -/
def pickName (supply : List String) : Gen String := do
  let n ← Gen.chooseNat
  pure (supply[n % supply.length]?.getD "alpha")

/-- Scalar KEY leaves (the map/set key gate's positive vocabulary —
    exactly the `KeyTy` universe itself; no floats, no composites). -/
def genKeyLeaf : Gen KeyTy :=
  Gen.oneOfWithDefault (pure .bool)
    [pure .u8, pure .u16, pure .u32, pure .u64,
     pure .i8, pure .i16, pure .i32, pure .i64, pure .string]

/-- Leaf types: the closed scalars plus a named ref from the supply
    (`oneOfWithDefault`, not a bare modulo — the tail-branch starvation
    lesson, see `PropSweep.genTyLeaf`). -/
def genTyLeaf (supply : List String) : Gen Ty :=
  Gen.oneOfWithDefault (pure .bool)
    [pure .u8, pure .u16, pure .u32, pure .u64,
     pure .i8, pure .i16, pure .i32, pure .i64,
     pure .f32, pure .f64, pure .string, pure .bytes,
     do pure (.ty (← pickName supply))]

/-- Sized random `Ty` over the FULL closed vocabulary: option/result/
    list/future/stream wrap smaller types; map/set take key-gated
    scalars; tensor takes 0–3 dims over a smaller element. -/
def genTy (supply : List String) : Nat → Gen Ty
  | 0 => genTyLeaf supply
  | fuel + 1 => do
    let branch ← Gen.chooseNat
    match branch % 12 with
    | 0 => pure (.option (← genTy supply fuel))
    | 1 => pure (.result (← genTy supply fuel) (← genTy supply fuel))
    | 2 => pure (.list (← genTy supply fuel))
    | 3 => pure (.future (← genTy supply fuel))
    | 4 => pure (.stream (← genTy supply fuel))
    | 5 => pure (.map (← genKeyLeaf) (← genTy supply fuel))
    | 6 => pure (.set (← genKeyLeaf))
    | 7 => do
        let n ← Gen.chooseNat
        let dims ← (List.range (n % 4)).mapM fun _ => do
          pure ((← Gen.chooseNat) % 6)
        pure (.tensor dims (← genTy supply fuel))
    | _ => genTyLeaf supply

/-- A generated field. -/
def genField (supply : List String) (fuel : Nat) : Gen Field := do
  pure { name := (← pickName fieldSupply), ty := (← genTy supply fuel) }

/-- A generated func semantic contract (uniform over the 3×3×2 axis
    grid — the default triple appears at 1/18, so the `sem` line's
    present AND absent forms both generate). -/
def genSem : Gen FuncSem := do
  pure { nullSem := (← Plausible.Arbitrary.arbitrary (α := NullSem))
       , determinism := (← Plausible.Arbitrary.arbitrary (α := Determinism))
       , delivery := (← Plausible.Arbitrary.arbitrary (α := Delivery)) }

/-- A generated item: record / variant / func (with a generated
    `FuncSem`) / resource. -/
def genItem (supply : List String) (fuel : Nat) : Gen Item := do
  let branch ← Gen.chooseNat
  match branch % 4 with
  | 0 => pure (.record (← pickName supply)
      (← SchemaLang.genShortList (genField supply fuel) 3))
  | 1 => do
    let genCase : Gen VariantCase := do
      let c ← pickName fieldSupply
      let p ← Gen.chooseNat
      if p % 2 == 0 then pure (c, none)
      else pure (c, some (← genTy supply fuel))
    pure (.variant (← pickName supply) (← SchemaLang.genShortList genCase 3))
  | 2 => do
    let genParam : Gen (String × Ty) := do
      pure (← pickName fieldSupply, ← genTy supply fuel)
    pure (.func { name := (← pickName supply)
                , params := (← SchemaLang.genShortList genParam 2)
                , ret := (← genTy supply fuel)
                , sem := (← genSem) })
  | _ => pure (.resource (← pickName supply))

/-- The generated universe (bounded item count). -/
structure Universe where
  items : List Item
deriving Repr

instance : Arbitrary Universe where
  arbitrary := Gen.sized fun fuel => do
    pure ⟨← SchemaLang.genShortList (genItem nameSupply fuel) 5⟩

/-- Shrink one item: drop fields/cases/params (names never shrink —
    a failing name shrinks nowhere useful). -/
def shrinkOne : Item → List Item
  | .record n fs => .record n [] :: fs.mapIdx fun i _ => .record n (fs.eraseIdx i)
  | .variant n cs => .variant n [] :: cs.mapIdx fun i _ => .variant n (cs.eraseIdx i)
  | .func s => [.func { s with params := [] }]
  | .resource _ => []

/-- Shrink a universe: drop one item, or shrink one item in place. -/
def shrinkUniverse (u : Universe) : List Universe :=
  (u.items.mapIdx fun i _ => ⟨u.items.eraseIdx i⟩)
    ++ ((u.items.mapIdx fun i it =>
          (shrinkOne it).map fun it' =>
            ⟨u.items.take i ++ [it'] ++ u.items.drop (i + 1)⟩).flatten)

instance : Shrinkable Universe where
  shrink := shrinkUniverse

/-- Run a generator deterministically, purely (fixed seed and size). -/
def runGenPure (g : Gen α) (seed : Nat) (size : Nat) : Except Plausible.GenError α :=
  (ReaderT.run (StateT.run g (ULift.up (mkStdGen seed))) ⟨size⟩).map (·.1)

/-! ## The PropSpec: parse ∘ render = id (sweep + mandatory control) -/

/-- The property predicate: render then parse recovers the universe. -/
def roundTrips (items : List Item) : Bool :=
  match Snapshot.parse (Snapshot.render items) with
  | .ok got => got == items
  | .error _ => false

/-- The suite: 1000 instances, PINNED SEED — a CI failure replays
    byte-identically; the shrinker minimizes any counterexample. -/
def suite : TestSeq :=
  checkPlausibleIO "snapshot: parse ∘ render = id (full Ty vocabulary)"
    (∀ u : Universe, roundTrips u.items = true)
    .done { numInst := 1000, randomSeed := some 20261119 }

/-- The sabotaged sibling: an unrecognized line appended to the render —
    parse MUST reject it, so the (corrupted) round trip MUST fail. If
    parse silently DROPPED the bogus line instead, the corrupted text
    would still round-trip and this suite would pass — a vacuous control
    flags a deafness hole in the parser's error channel. -/
def corruptStillRoundTrips (items : List Item) : Bool :=
  match Snapshot.parse (Snapshot.render items ++ "bogus x\n") with
  | .ok got => got == items
  | .error _ => false

/-- The negative control (TestKit.PropSpec discipline): must FAIL. -/
def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: unrecognized line appended (must be caught)"
    (∀ u : Universe, corruptStillRoundTrips u.items = true)
    .done { numInst := 1000, randomSeed := some 20261119 }

/-- The property spec: sweep + its mandatory negative control. -/
def spec : TestKit.PropSpec :=
  { name := "snapshot: parse ∘ render round trip (full Ty vocabulary)"
  , suite := suite
  , control := controlSuite
  , controlName := "append-bogus-line" }

/-! ## The coverage witness (the generator must REACH every arm) -/

/-- All types appearing in a type, ALL constructors descended (unlike
    `PropSweep.tysOf`, which does not enter map/set/tensor). -/
partial def allTysOf (t : Ty) : List Ty :=
  t :: match t with
  | .option a | .list a | .future a | .stream a => allTysOf a
  | .result a b => allTysOf a ++ allTysOf b
  | .map _ v => allTysOf v  -- the key is a scalar (KeyTy) — no sub-tys
  | .set _ => []            -- the element is a scalar (KeyTy)
  | .tensor _ a => allTysOf a
  | _ => []

/-- All types appearing in an item. -/
def itemTys : Item → List Ty
  | .record _ fs => fs.flatMap fun f => allTysOf f.ty
  | .variant _ cs => (cs.filterMap (·.2)).flatMap allTysOf
  | .func s => (s.params.map (·.2)).flatMap allTysOf ++ allTysOf s.ret
  | .resource _ => []

/-- Does any func carry a NON-default semantic contract (the `sem`
    line's present form)? -/
def hasNonDefaultSem (items : List Item) : Bool :=
  items.any fun it =>
    match it with
    | .func s => s.sem != ({} : FuncSem)
    | _ => false

/-- Deterministic coverage witness (pinned seeds): across 24 fixed seeds
    the generator MUST reach every snapshot-relevant `Ty` constructor —
    map/set/tensor/result/stream especially (the audit's unexercised
    arms) — plus a non-default `sem` line. Without this, the sweep could
    pass while never rendering half the format. -/
def coverageChecks : CheckResult := do
  let us := (List.range 24).filterMap fun s =>
    match runGenPure (Plausible.Arbitrary.arbitrary (α := Universe)) (20261119 + s) 12 with
    | .ok u => some u.items
    | .error _ => none
  _ ← assertEq "generator produced samples" us.isEmpty false
  let allTys := us.flatten.flatMap itemTys
  _ ← assert (allTys.any fun t => match t with | .map .. => true | _ => false)
    "generator reaches map"
  _ ← assert (allTys.any fun t => match t with | .set _ => true | _ => false)
    "generator reaches set"
  _ ← assert (allTys.any fun t => match t with | .tensor .. => true | _ => false)
    "generator reaches tensor"
  _ ← assert (allTys.any fun t => match t with | .result .. => true | _ => false)
    "generator reaches result"
  _ ← assert (allTys.any fun t => match t with | .stream _ => true | _ => false)
    "generator reaches stream"
  _ ← assert (allTys.any fun t => match t with | .future _ => true | _ => false)
    "generator reaches future"
  _ ← assert (allTys.any fun t => match t with | .option _ => true | _ => false)
    "generator reaches option"
  _ ← assert (allTys.any fun t => match t with | .list _ => true | _ => false)
    "generator reaches list"
  _ ← assert (allTys.any fun t => match t with | .ty _ => true | _ => false)
    "generator reaches ty refs"
  _ ← assert (us.flatten.any (fun it => hasNonDefaultSem [it]))
    "generator reaches non-default sem"
  -- the zero-dims rendering pin (the empty-prefix corner)
  _ ← assertEq "zero-dim tensor renders the empty prefix"
    (Ty.tensor [] .u64).toSnapshot "tensor(u64)"
  .ok ()

/-! ## The fixture emission (the Rust differential's input) -/

/-- Number of fixture pairs. -/
def fixtureCount : Nat := 32

/-- The pinned fixture seed (the byte-tie law for generated fixtures). -/
def fixtureSeed : Nat := 20261119

/-- The fixture universes: deterministic seeded draws, each VERIFIED to
    round-trip before it can become a fixture. -/
def fixtureUniverses : Except String (List (List Item)) :=
  match (List.range fixtureCount).mapM fun s =>
      (runGenPure (Plausible.Arbitrary.arbitrary (α := Universe))
        (fixtureSeed + s) 12).map (·.items) with
  | .ok us => .ok us
  | .error _ => .error "snapshot fixtures: generator error (seed/size drift?)"

/-- One type → its EXPECTED-dump spelling — deliberately NOT
    `Ty.toSnapshot`: a fully-parenthesized S-expression with SPACED
    parens (`(map string u64)`), decoded by the Rust differential's own
    tiny token parser. An independent shape means a drift in EITHER
    side's snapshot-ty parser shows as a differential failure instead of
    cancelling. -/
def dumpTy : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "string" | .bytes => "bytes"
  | .option a => s!"( option {dumpTy a} )"
  | .result ok err => s!"( result {dumpTy ok} {dumpTy err} )"
  | .list a => s!"( list {dumpTy a} )"
  | .map k v => s!"( map {k.toSnapshot} {dumpTy v} )"
  | .set k => s!"( set {k.toSnapshot} )"
  | .future a => s!"( future {dumpTy a} )"
  | .stream a => s!"( stream {dumpTy a} )"
  | .tensor dims a =>
      s!"( tensor {String.join (dims.map fun d => s!"{d} ")}{dumpTy a} )"
  | .ty n => s!"( ref {n} )"

/-- One item → its EXPECTED dump lines: an independent spelling
    (`item record|variant|func|resource` headers, `fld`/`cs`/`p`
    members) over `dumpTy` types. Names VERBATIM — parse is lossless;
    the kebab-case asymmetry's pin is that the dump agrees. The `sem`
    line mirrors the snapshot's rule (present only when non-default). -/
def dumpItem : Item → List String
  | .record n fs =>
      s!"item record {n}" :: fs.map fun f => s!"fld {f.name} {dumpTy f.ty}"
  | .variant n cs =>
      s!"item variant {n}" :: cs.map fun (c, p) =>
        match p with
        | some t => s!"cs {c} {dumpTy t}"
        | none => s!"cs {c}"
  | .func s =>
      s!"item func {s.name}"
        :: s.params.map (fun (n, t) => s!"p {n} {dumpTy t}")
          ++ [s!"ret {dumpTy s.ret}"]
          ++ (if s.sem == ({} : FuncSem) then []
              else [s!"sem {s.sem.nullSem.toToken} {s.sem.determinism.toToken}"
                    ++ (if s.sem.delivery == (.stream : Delivery) then " stream" else "")])
  | .resource n => [s!"item resource {n}"]

/-- The fixture FILE: header + one block per pair. Each block:

    == u<i>
    snap:
    <the snapshot text — what BOTH parsers must agree on>
    expect:
    <the dump of what LEAN'S parser produced — the authority's answer>

    The dump is the parse OUTPUT (not the generator's input), so the
    Rust side compares `hostgen::parse_snapshot(snap)` against the
    authority's own parse of the same bytes. -/
def fixtureFile (us : List (List Item)) : Except String String := do
  let header := "# GENERATED by schema-lang's snapshot-fixtures exe — DO NOT EDIT\n\
    # seed 20261119 | count 32 | regen: just snapshot-fixtures (byte-identical)\n\
    # pair: `== u<i>` header, snapshot text after `snap:`, the dump of\n\
    # Lean's parse output after `expect:` (see Tests/SnapshotRT.lean)."
  let blocks ← (List.range us.length).mapM fun i => do
    let items := us[i]!
    let text := Snapshot.render items
    let got ← match Snapshot.parse text with
      | .ok got => .ok got
      | .error e => throw s!"snapshot fixture: the rendered text does not parse: {e}"
    unless got == items do
      throw "snapshot fixture: parse ∘ render ≠ id on a fixture universe"
    let dump := String.intercalate "\n" (got.flatMap dumpItem)
    pure s!"== u{i}\nsnap:\n{text}expect:\n{dump}\n"
  pure (header ++ "\n" ++ String.intercalate "\n" blocks)

end SnapshotRT
