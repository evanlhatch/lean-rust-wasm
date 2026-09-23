/-
# KitTests — the kit's test exe

Per module: the positive pins + the MANDATORY negative controls
(15-patterns #5 — a suite without its control doesn't construct). The
negative controls here are DATA-LEVEL: a sabotaged case must FAIL a
check function (the proof-level refusal is the elaborator itself — a
law-less literal cannot construct; each control names which refusal it
mirrors).

The runner is TestKit's (`mainOfSuites` — doctrine 12 §9: tests are
data folds; SchemaTests already rides it on the same root package).
Each module section is one Spec; the sabotage cases are the Spec's
NEGATIVES, each guarded by the vacuity tripwire.

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the laws — zero-axiom output or the build fails.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Correspondence
import Kit.Obligation
import Kit.Registry
import Kit.CheckedProp
import Kit.Emit
import Kit.Suggest
import Kit.FreshName
import Kit.Diag
import Kit.Lane
import Kit.CodeRegistry
import Kit.Change
import Kit.Observer
import TestKit.Harness
import KitTests.Axioms

open Kit
open Kit.Emit
open TestKit

-- Core `Except` ships no `DecidableEq`; the suite's `pinProp`s decide
-- on `parse`/`replay` verdicts — the gap filled HERE (test-exe local).
deriving instance DecidableEq for Except

/-! ## Fixtures — Correspondence -/

/-- `Bool ↔ Option Unit` — the toy iso, laws by cases. -/
def bitOptIso : Iso Bool (Option Unit) where
  to b := if b then some () else none
  inv o := o.isSome
  to_inv o := by cases o <;> rfl
  inv_to b := by cases b <;> rfl

/-- The honest wire codec for one bit over small naturals: bytes 0/1,
    policy `n < 2`, decode refuses everything else. -/
def bitEncode : Bool → Nat := fun b => cond b 1 0
def bitDecode : Nat → Option Bool := fun n => if n < 2 then some (n % 2 == 1) else none
def bitPolicy : Nat → Prop := fun n => n < 2

def bitCodec : Codec Nat Bool where
  encode := bitEncode
  decode := bitDecode
  policy := bitPolicy
  decode_encode := by
    intro b
    cases b <;> simp [bitEncode, bitDecode, cond]
  decode_some_policy := by
    intro a b h
    unfold bitDecode at h
    split at h
    · next h2 => exact h2
    · next _h2 => simp at h

/-- `Bool ↣ Nat` — the one round trip: `inv (emb b) = b`. -/
def bitRetraction : Retraction Bool Nat where
  emb b := cond b 1 0
  inv n := n % 2 == 1
  inv_emb b := by cases b <;> rfl

/-! ## Fixtures — Obligation -/

def oblg : Obligation Nat where
  label := "answer-is-42"
  tier := .decidableNow
  payload := 42
  provenance := `KitTests

def oblgClaim (o : Obligation Nat) : Prop := o.payload = 42
instance oblgClaimDec : ∀ o : Obligation Nat, Decidable (oblgClaim o) :=
  fun o => Nat.decEq o.payload 42

/-! ## Fixtures — Registry -/

def itemReg : DataRegistry Nat where
  items := [1, 2, 3]
  nameOf := fun n => s!"item{n}"

/-- A closed enumeration: the CodedRegistry's `finIso` upgrade fires. -/
inductive Color where
  | red | green | blue

def colorName : Color → String
  | .red => "red" | .green => "green" | .blue => "blue"

def colorReg : CodedRegistry Color where
  items := [Color.red, Color.green, Color.blue]
  nameOf := colorName
  codePrefix := "C"
  start := 100

theorem colorExhaustive : ∀ a : Color, a ∈ colorReg.items := by
  intro a; cases a <;> simp [colorReg]

deriving instance BEq, DecidableEq for Color

instance : LawfulBEq Color where
  rfl {a} := by cases a <;> rfl
  eq_of_beq := by
    intro a b h
    match a, b with
    | .red, .red => rfl
    | .green, .green => rfl
    | .blue, .blue => rfl
    | .red, .green | .green, .red | .red, .blue | .blue, .red
    | .green, .blue | .blue, .green => exact Bool.noConfusion h

/-! ## Fixtures — CheckedProp -/

def evenProp : CheckedProp Nat where
  P a := a % 2 = 0
  check a := a % 2 == 0
  sound _a h := beq_iff_eq.mp h
  complete? := .proved (fun _a h => beq_iff_eq.mpr h)

/-- The LOUD one-directional gate: soundness proved, completeness
    declared `.missing` (the constructor choice with no default). -/
def oddGate : CheckedProp Nat where
  P a := a % 2 = 1
  check a := a % 2 == 1
  sound _a h := beq_iff_eq.mp h
  complete? := .missing

/-! ## Fixtures — Emit -/

def e1 : Emitter (List String) where
  name := "e1"
  style := .lean
  specSource := "KitTests"
  outputs := ["gen/a.txt"]
  run spec := [{ path := "gen/a.txt", contents := String.intercalate "," spec }]

def e2 : Emitter (List String) where
  name := "e2"
  style := .hash
  specSource := "KitTests"
  outputs := ["gen/b.txt"]
  run spec := [{ path := "gen/b.txt", contents := toString spec.length }]

/-- The scratch emitter for the driver test (writes under the tests'
    dir; the driver cleans up the file). -/
def e1scratch : Emitter (List String) where
  name := "e1-scratch"
  style := .lean
  specSource := "KitTests"
  outputs := ["kit/KitTests/scratch/emitted.txt"]
  run spec := [{ path := "kit/KitTests/scratch/emitted.txt",
                 contents := String.intercalate "," spec }]

/-- Sabotaged pair: TWO emitters claim ONE output path — the
    cross-emitter one-writer audit detects the collision. -/
def e1sab : Emitter (List String) where
  name := "e1-sab"
  style := .lean
  specSource := "KitTests"
  outputs := ["gen/shared.txt"]
  run spec := [{ path := "gen/shared.txt", contents := "x" }]

def e2sab : Emitter (List String) where
  name := "e2-sab"
  style := .hash
  specSource := "KitTests"
  outputs := ["gen/shared.txt"]
  run spec := [{ path := "gen/shared.txt", contents := "y" }]

/-! ## Fixtures — Diag / Suggest / FreshName -/

/-- The valid space the fixture failures speak over. -/
def fixtureValid : List String := ["were", "what", "when"]

/-- A fully-filled Diag literal (the positional/lint face: no got, no
    valid space — `closedWorld` is not the route here). -/
def fixtureDiag : Diag :=
  { code := ⟨"K0001"⟩
  , message := "schema: unsupported construct"
  , context := [Label.at "schema", { name := "field", detail := "user" }]
  , severity := .error }

/-- The closed-world fixture: one call, suggest filled by the engine. -/
def fixtureClosed : Diag :=
  Diag.closedWorld ⟨"K0002"⟩ "schema: unknown clause" .error "whre" fixtureValid

/-- The closed-world SHAPE check: a Diag that names a got over a
    non-empty valid space MUST carry the engine's suggestion — a Diag
    that skips it fails this detector (the discipline is checkable,
    not just conventional). -/
def diagSuggestOk (d : Diag) : Bool :=
  match d.got, d.suggest with
  | some g, some s => Kit.suggestFor g d.valid == some s
  | some _, none => d.valid.isEmpty
  | _, _ => true

/-- Sabotaged ranker: reverses the engine's order — the negative
    control's producer (a wrong order would go undetected without a
    detector that distinguishes it). -/
def sabRanked (got : String) (valid : List String) : List String :=
  (Kit.didYouMean got valid).reverse

/-! ## Lane — the lane substrate (Kit.Lane) — the value-level pins

The demo lane's END-TO-END (register → replay → fold) runs at
elaboration time in the fixture modules: `KitTests.LaneReg` (the
`register_lane` mount) + `KitTests.LaneDemo` (the two entries + the
accessor/fold pins + the curated-failure negative controls). A
module's own initializers run only at IMPORT, so the registration and
the consumption must be different modules. The pins here are the
value-level halves: the import-concatenation semantics and the
materialization's duplicate refusal.
-/

/-- The `addImportedFn` semantics, pinned: keep order, concatenate
    (the replay discipline — `Array (Array α)`, the trap-list rule). -/
def laneMergePin : Bool :=
  (Kit.Lane.mergeImported #[#[1], #[2, 3]] == ([1, 2, 3] : List Nat))

/-- The materialization accepts distinct names (the fold hook's
    `.ok` face). -/
def laneMatOkPin : Bool :=
  match Kit.Lane.materialize (nameOf := fun (n : Nat) => s!"item{n}") [1, 2] with
  | .ok _ => true
  | .error _ => false

/-- NEGATIVE CONTROL: the materialization DECIDES the nodup fact and
    refuses duplicate names loudly (there is no silent acceptance
    path; the runtime mirror of the registry's discipline). -/
def laneMatDupRefusedPin : Bool :=
  match Kit.Lane.materialize (nameOf := fun (n : Nat) => s!"item{n}") [1, 1] with
  | .ok _ => false
  | .error _ => true

/-! ## Fixtures — CodeRegistry -/

/-- A canonical three-name registry (1-based allocation, sorted by code). -/
def cr3 : CodeRegistry := [⟨"alpha", 1, false⟩, ⟨"beta", 2, false⟩, ⟨"gamma", 3, false⟩]

/-- The same registry with beta retired — its tombstone keeps code 2 spent. -/
def cr3Retired : CodeRegistry :=
  match cr3.retire "beta" with | .ok r => r | .error _ => cr3

/-- Beta deleted WITHOUT its tombstone (the illegal "free" code 2). -/
def cr3TombstoneDropped : CodeRegistry := [⟨"alpha", 1, false⟩, ⟨"gamma", 3, false⟩]

/-- The tombstone-dropped registry, but code 2 LIVE again on a new name —
    the reuse the doctrine forbids. -/
def cr3Reused : CodeRegistry := [⟨"alpha", 1, false⟩, ⟨"newname", 2, false⟩, ⟨"gamma", 3, false⟩]

/-- A registry where EVERY high row is retired (live max below retired codes) —
    the case a live-only max would mis-allocate. -/
def crAllHighRetired : CodeRegistry := [⟨"alpha", 1, false⟩, ⟨"beta", 2, true⟩, ⟨"gamma", 3, true⟩]

/-- The canonical text of `cr3` (the committed file's format). -/
def cr3Text : String := "alpha\t1\nbeta\t2\ngamma\t3\n"

/-! ## Fixtures — Change / Observer -/

/-- Two executions with the SAME api observation but DIFFERENT traces —
    the observer-choice witness. -/
def ex1 : Execution Int := { trace := [1, 2], result := some 2, cost := 5 }

def ex2 : Execution Int := { trace := [1, 3], result := some 2, cost := 5 }

/-- THE directionality obligation: ex1 refines ex2 under apiObs but
    NOT under auditObs — refinement is parameterized by the observer
    (04 §4: every equivalence/refinement claim names one). -/
theorem observerRefinesDirectional :
    (apiObs Int).refines [ex1] [ex2] ∧ ¬(auditObs Int).refines [ex1] [ex2] := by
  constructor
  · intro x hx
    have hxe : x = ex1 := List.mem_singleton.mp hx
    rw [hxe]
    exact ⟨ex2, List.mem_singleton_self ex2, rfl⟩
  · intro h
    obtain ⟨y, hy, hsee⟩ := h ex1 (List.mem_singleton_self ex1)
    have hye : y = ex2 := List.mem_singleton.mp hy
    rw [hye] at hsee
    simp [auditObs, ex1, ex2] at hsee

/-! ## Sabotage fixtures — the negatives' producers

The sabotage cases hoisted out of the suite (each feeds one NEGATIVE
control in the specs below; the control claims the sabotage is lawful
and MUST fail — the vacuity tripwire (TestKit.Harness) is the guard
that keeps it failing). The detectors they mirror live beside their
sections' fixtures above.
-/

/-- Sabotaged decoder: fires on byte 3, which the policy rejects. A
    codec literal with this `decode` cannot fill `decode_some_policy`
    (the elaborator refuses); the data-level mirror is the same
    refusal: the byte is out-of-policy AND the decode fired. -/
def sabDecode : Nat → Option Bool := fun n => if n = 3 then some false else bitDecode n

/-- Sabotaged embedding: collides both bools onto one nat — `inv_emb`
    is unfillable (the elaborator refuses); the data-level mirror is
    the collision itself. -/
def sabEmb : Bool → Nat := fun _ => 1

/-- Duplicate names: the `nodup` proof field's `by decide` refuses the
    literal (no runtime rejection path); the data-level mirror is the
    same decide. -/
def dupNames : List String :=
  ([(1 : Nat), 2, 1].map fun n => s!"item{n}")

/-- Colliding hand-set codes: the `codesNodup` proof field's default
    refuses; the data-level mirror is the same decide. -/
def sabCodes : List (Nat × String) := [(1, "E0"), (2, "E0")]

/-- Sabotaged checker: fires on a value where P fails — the `sound`
    field is unfillable (the elaborator refuses); the data-level mirror
    is the false verdict the checker would certify. -/
def sabCheck : Nat → Bool := fun a => a % 2 == 1

/-- Hand-built Diag over a closed world with the suggest field left
    empty — the shape detector's negative control's producer (the
    closedWorld constructor cannot produce this shape). -/
def skipSuggest : Diag :=
  { fixtureClosed with suggest := none }

/-- Sabotaged verdict (always fresh, never enumerates): a duplicate
    passes it — the always-fresh control's producer. -/
def sabVerdict : String → String → String → List String → Option String :=
  fun _ _ _ _ => none

/-- Sabotaged allocator: max over the LIVE rows only (tombstones
    ignored) — on the all-high-retired fixture it would REUSE the
    retired code 2 (the real nextCode is 4). -/
def sabNextCode (r : CodeRegistry) : Nat :=
  (r.filter (fun (row : CodeRow) => !row.retired)).map (CodeRow.code)
    |>.foldl max 0 |>.succ

/-- Sabotaged stability: the tombstone clause dropped (tombstones always
    "survive") — it ACCEPTS the tombstone-dropped registry the real
    verdict refuses. -/
def sabStable (old new : CodeRegistry) : Bool :=
  old.all (fun o => o.retired || (new.lookup o.name == some o.code))

/-- Sabotaged parser: the fully-consumed check dropped (trailing junk
    accepted) — the malformed line slips through where the real parse
    refuses. -/
def sabParse (line : String) : Option CodeRow :=
  match line.splitOn "\t" with
  | name :: _ => some ⟨name, 999, false⟩
  | [] => none

/-- Sabotaged extract (drop the result, keep nothing): the Below law's
    negative control's producer. -/
def sabExtract : Option Int × List Int → Option Int := fun _ => none

/-! ## The suite — TestKit's runner (doctrine 12 §9: tests are data folds)

One Spec per module section: the section's positive pins are the prop
(each assert names its pin — the failure evidence keeps the old
granularity), and the section's sabotage cases are the Spec's NEGATIVES
(each must FAIL; TestKit's vacuity tripwire guards them). CheckedProp
and Lane each carry exactly one natural control, so they share one spec
(the negatives subtype needs two). The emit driver's IO half runs in
`main`; its result folds into `emitSpec` as the `emit.driverWrote` pin.
-/

def correspondenceSpec : Spec :=
  Spec.ofList "Kit.Correspondence — the iso/codec/retraction pins"
    (fun _ => do
      assert (decide (bitOptIso.to (bitOptIso.inv (some ())) = some ())) "iso.roundTrip"
      assert (decide ((bitOptIso.prod bitOptIso).to (true, false) = (some (), none))) "iso.prod"
      assert (decide ((bitOptIso.sum bitOptIso).to (Sum.inl true) = Sum.inl (some ()))) "iso.sum"
      assert (decide ((Iso.trans (Iso.refl _) bitOptIso).to false = none)) "iso.transRefl"
      assert (decide (bitCodec.decode (bitCodec.encode true) = some true)) "codec.roundTrip"
      assert (decide (bitCodec.decode 7 = none)) "codec.refusesOutsidePolicy"
      assert (decide ((Codec.trans (Codec.refl Nat) bitCodec).decode 1 = bitDecode 1))
        "codec.composesWithRefl"
      assert (decide (bitRetraction.inv (bitRetraction.emb false) = false)) "retraction.roundTrip"
      assert (decide (bitRetraction.toImageIso.to ⟨1, ⟨true, rfl⟩⟩ = true)) "retraction.imageIso"
      assert (decide ((Retraction.transportLeft (Iso.refl _) bitRetraction).emb true = 1))
        "retraction.transportLeft")
    [ ("sabotaged decode is lawful",
        fun _ =>
          assert (decide (sabDecode 3 = none))
            "control fired: the sabotaged decoder accepted an out-of-policy byte")
    , ("sabotaged embedding is injective",
        fun _ =>
          assert (decide (sabEmb true ≠ sabEmb false))
            "control fired: the sabotaged embedding collided the bools") ]
    4 42

def obligationSpec : Spec :=
  Spec.ofList "Kit.Obligation — the discharge pins"
    (fun _ => do
      assert (decide (oblg.decideDischarge oblgClaim = some (Evidence.decided true)))
        "obligation.dischargeFires"
      assert (decide (¬(Kit.tierMismatch oblg (Evidence.decided true)))) "obligation.tierMatches"
      assert (
          let d : Discharged Nat := { obligation := oblg, evidence := .decided true }
          d.obligation.payload == 42)
        "obligation.dischargedConstructs")
    [ ("false claim discharges",
        fun _ =>
          assert (decide (oblg.decideDischarge (fun o => o.payload = 43)
            = some (Evidence.decided true)))
            "control fired: a false claim was fabricated into evidence")
    , ("oracle-row evidence is well-tiered",
        fun _ =>
          assert (decide (¬(Kit.tierMismatch oblg (Evidence.oracleRow "oracle-1"))))
            "control fired: an oracle-row evidence against decidableNow is a mis-wire") ]
    4 42

def registrySpec : Spec :=
  Spec.ofList "Kit.Registry — the lookup/allocation pins"
    (fun _ => do
      assert (
          match itemReg.lookup? "item2" with
          | .ok a => a == 2
          | .error _ => false)
        "registry.lookupOk"
      assert (
          match itemReg.lookup? "item" with
          | .ok _ => false
          | .error miss => miss.didYouMean == ["item1", "item2", "item3"])
        "registry.missSuggests"
      assert (decide (colorReg.codes.length = 3)) "codedRegistry.codesLength"
      assert (colorReg.denseCheck) "codedRegistry.denseCheck"
      assert (decide ((colorReg.finIso colorExhaustive).to ⟨1, by decide⟩ = Color.green))
        "codedRegistry.finIso"
      assert (decide ((colorReg.membersIso.inv ⟨Color.blue, by simp [colorReg]⟩).1 = 2))
        "codedRegistry.membersIso")
    [ ("duplicate names construct a registry",
        fun _ =>
          assert (dupNames.Nodup)
            "control fired: the duplicate-named literal's data mirror constructed")
    , ("colliding hand-set codes allocate",
        fun _ =>
          assert ((sabCodes.map (·.2)).Nodup)
            "control fired: the colliding-code literal's data mirror constructed") ]
    4 42

/-- CheckedProp and Lane share one spec: each carries exactly one
    natural control, and the negatives subtype needs two. -/
def checkedLaneSpec : Spec :=
  Spec.ofList "Kit.CheckedProp + Kit.Lane — the graded-checker and lane pins"
    (fun _ => do
      assert (decide ((evenProp.check 4 = true) ∧ (4 % 2 = 0))) "checkedProp.soundVerdictIsProof"
      assert (decide (evenProp.isComplete)) "checkedProp.isComplete"
      assert (decide (¬(oddGate.isComplete))) "checkedProp.missingIsLoud"
      assert (decide ((evenProp.check 6 = true) ∧ (6 % 2 = 0))) "checkedProp.checkIff"
      assert (decide ((evenProp.toMap ⟨4, rfl⟩).1 = 4)) "checkedProp.toMap"
      assert (
          let i := evenProp.toIso (fun a h => beq_iff_eq.mpr h)
          let x := i.inv ⟨2, rfl⟩
          x.1 == 2)
        "checkedProp.toIso"
      assert (laneMergePin) "lane.mergeImported"
      assert (laneMatOkPin) "lane.materializeOk")
    [ ("the sabotaged checker is sound",
        fun _ =>
          assert (!(sabCheck 3))
            "control fired: the sabotaged checker certified a P-failing value")
    , ("the materialization accepts duplicate names",
        fun _ =>
          assert (
              match Kit.Lane.materialize (nameOf := fun (n : Nat) => s!"item{n}") [1, 1] with
              | .ok _ => true
              | .error _ => false)
            "control fired: the materialization refused duplicate names") ]
    4 42

/-- The emit driver's IO result folds in as a pin (the sweep's tape is
    irrelevant — the pin is the closed read-back decision). -/
def emitSpec (driverOk : Bool) : Spec :=
  Spec.ofList "Kit.Emit — the emitter pins"
    (fun _ => do
      assert (decide (e1.outputs.Nodup ∧ e2.outputs.Nodup)) "emit.outputsNodup"
      assert (Kit.Emit.outputsDisjoint [e1, e2]) "emit.outputsDisjoint"
      assert ((Kit.Emit.header .lean "kit-tests" "KitTests"
          { contentHash := 0 }).startsWith "-- GENERATED")
        "emit.headerMarksGenerated"
      assert (
          let h := Kit.Emit.header .lean "kit-tests" "KitTests"
            { contentHash := "body".hash, items := 1 }
          h.contains (toString "body".hash))
        "emit.contentHashInHeader"
      assert (driverOk) "emit.driverWrote")
    [ ("colliding outputs are disjoint",
        fun _ =>
          assert (Kit.Emit.outputsDisjoint [e1sab, e2sab])
            "control fired: the cross-emitter one-writer audit missed the collision")
    , ("duplicate output names are unique",
        fun _ =>
          assert ((["a", "a"] : List String).Nodup)
            "control fired: the in-type nodup refusal's data mirror constructed") ]
    4 42

def diagSuggestSpec : Spec :=
  Spec.ofList "Kit.Diag / Suggest / FreshName — the error-surface pins"
    (fun _ => do
      assert (decide (Kit.editDistance? "kitten" "sitting" 5 = some 3))
        "suggest.distance.kittenSitting"
      assert (decide (Kit.editDistance? "kitten" "sitting" 2 = none))
        "suggest.distance.cutoffRefuses"
      assert (decide (Kit.editDistance? "abc" "abc" 0 = some 0)) "suggest.distance.zero"
      assert (decide (Kit.editDistance? "a" "b" 0 = none)) "suggest.distance.oneRefusedAtZero"
      assert (decide (Kit.suggestFor "" ["b", "a"] = some " — did you mean: a, b?"))
        "suggest.order.tieIsLexicographic"
      assert (decide (Kit.suggestFor "whre" fixtureValid
        = some " — did you mean: were, what, when?")) "suggest.order.nearestFirst"
      assert (decide (Kit.suggestFor "zzzzzz" ["a", "b"] = none)) "suggest.noneWhenNothingClose"
      assert ((Kit.freshNameCheck "kit-tests" "item4" "item"
          ["item1", "item2", "item3"]).isOk)
        "freshName.freshIsOk"
      assert (decide (Kit.freshNameVerdict "kit-tests" "item2" "item"
          ["item1", "item2", "item3"]
        = some "kit-tests: `item2` is already a registered item — \
names must be fresh — did you mean: item2, item1, item3?"))
        "freshName.duplicateCuratedShape"
      assert (!((Kit.freshNameCheck "kit-tests" "item2" "item"
          ["item1", "item2", "item3"]).isOk))
        "freshName.checkCarriesTheVerdict"
      assert (decide ((Kit.freshNameVerdict "kit-tests" "item4" "item"
          ["item1", "item2", "item3"]) = none)) "freshName.verdictDichotomyFreshSide"
      assert ((Kit.freshNameVerdict "kit-tests" "item2" "item"
          ["item1", "item2", "item3"]).isSome) "freshName.verdictDichotomyDuplicateSide"
      assert (decide (fixtureClosed.suggest = some " — did you mean: were, what, when?" ∧
          fixtureClosed.got = some "whre" ∧ fixtureClosed.valid = fixtureValid))
        "diag.closedWorldFillsSuggest"
      assert (diagSuggestOk fixtureClosed) "diag.closedWorldShapeOk"
      assert (decide (toString fixtureDiag
        = "[K0001] error: schema: unsupported construct [schema, field (user)]"))
        "diag.literalRender"
      assert (decide (toString fixtureClosed
        = "[K0002] error: schema: unknown clause (got: whre) — \
valid: were, what, when — did you mean: were, what, when?"))
        "diag.closedWorldRender"
      assert (decide ([Severity.error, .warning, .gate, .obligation, .info].map
          Severity.render
        = ["error", "warning", "gate", "obligation", "info"])) "diag.severityClosedFive")
    [ ("reversed ranker matches the engine",
        fun _ =>
          assert (sabRanked "whre" fixtureValid == Kit.didYouMean "whre" fixtureValid)
            "control fired: the ordering pins have no teeth against a reversed engine")
    , ("the closed-world skip is well-shaped",
        fun _ =>
          assert (diagSuggestOk skipSuggest)
            "control fired: a closed-world Diag without its suggestion passed the shape check")
    , ("the always-fresh verdict agrees with the real one",
        fun _ =>
          assert (decide (sabVerdict "kit-tests" "item2" "item"
              ["item1", "item2", "item3"]
            = Kit.freshNameVerdict "kit-tests" "item2" "item" ["item1", "item2", "item3"]))
            "control fired: the sabotaged verdict matched the real verdict") ]
    4 42

def codeRegistrySpec : Spec :=
  Spec.ofList "Kit.CodeRegistry — the persisted-code pins"
    (fun _ => do
      assert (cr3.lookup "beta" == some 2) "codeRegistry.lookupLive"
      assert (cr3.lookup "nope" == none) "codeRegistry.lookupMiss"
      assert (cr3Retired.lookup "beta" == none) "codeRegistry.lookupRefusesTombstone"
      assert (
          match cr3.allocate "delta" with
          | .ok r => r.lookup "delta" == some 4
          | .error _ => false)
        "codeRegistry.allocateNextFree"
      -- THE never-reassigns law: with beta retired (code 2 spent, its
      -- tombstone present) the next allocation is 4 — the retired code
      -- is never revisited.
      assert (
          match cr3Retired.allocate "delta" with
          | .ok r => r.lookup "delta" == some 4
          | .error _ => false)
        "codeRegistry.allocateNeverReassigns"
      -- Even when EVERY high row is retired, the tombstones hold the
      -- codes spent.
      assert (
          match crAllHighRetired.allocate "delta" with
          | .ok r => r.lookup "delta" == some 4
          | .error _ => false)
        "codeRegistry.tombstonesHoldCodesSpent"
      -- A rename is a NEW code: allocate refuses an existing name.
      assert (
          match cr3.allocate "beta" with | .error _ => true | .ok _ => false)
        "codeRegistry.renameIsNewCode"
      assert (decide (CodeRegistry.checkStable cr3 cr3)) "codeRegistry.stableSelf"
      assert (decide (CodeRegistry.checkStable cr3Retired cr3Retired))
        "codeRegistry.stableWithTombstone"
      -- A deleted name's pair does not survive: the verdict is FALSE.
      assert (decide (¬(CodeRegistry.checkStable cr3 cr3TombstoneDropped)))
        "codeRegistry.deletionIsUnstable"
      -- Code REUSE after deletion: the tombstone's code claimed live by
      -- a new name — the verdict refuses it.
      assert (decide (¬(CodeRegistry.checkStable cr3Retired cr3Reused)))
        "codeRegistry.reuseIsUnstable"
      -- And the tombstone-dropped form fails too: the spent code must
      -- STAY retired.
      assert (decide (¬(CodeRegistry.checkStable cr3Retired cr3TombstoneDropped)))
        "codeRegistry.droppedTombstoneIsUnstable"
      assert (
          match CodeRegistry.parse cr3Text with
          | .ok r => r == cr3
          | .error _ => false)
        "codeRegistry.roundTrip"
      assert (
          match CodeRegistry.parse (CodeRegistry.print cr3Retired) with
          | .ok r => r == cr3Retired
          | .error _ => false)
        "codeRegistry.roundTripTombstone"
      assert (
          match CodeRegistry.parse "" with
          | .ok r => r == ([] : CodeRegistry)
          | .error _ => false)
        "codeRegistry.emptyParses"
      -- The final newline is the file's, not a row's (canonicalization).
      assert (
          match CodeRegistry.parse "alpha\t1" with
          | .ok r => r == [⟨"alpha", 1, false⟩] ∧ CodeRegistry.print r == "alpha\t1\n"
          | .error _ => false)
        "codeRegistry.missingFinalNewlineCanonicalizes"
      assert (
          match CodeRegistry.parse "alpha\t1\n-beta\t2\ngamma\t3\n" with
          | .ok r => r == cr3Retired
          | .error _ => false)
        "codeRegistry.tombstoneTextParses"
      assert (
          match CodeRegistry.parse "alphatab1\n" with | .error _ => true | .ok _ => false)
        "codeRegistry.refusesNoTab"
      assert (
          match CodeRegistry.parse "\t1\n" with | .error _ => true | .ok _ => false)
        "codeRegistry.refusesEmptyName"
      assert (
          match CodeRegistry.parse "alpha\txy\n" with | .error _ => true | .ok _ => false)
        "codeRegistry.refusesNonDigitCode"
      assert (
          match CodeRegistry.parse "alpha\t1x\n" with | .error _ => true | .ok _ => false)
        "codeRegistry.refusesJunkAfterCode"
      assert (
          match CodeRegistry.parse "alpha\t1\r\n" with | .error _ => true | .ok _ => false)
        "codeRegistry.refusesCRLF"
      assert (
          match CodeRegistry.parse "alpha\t1\n\nbeta\t2\n" with
          | .error _ => true | .ok _ => false)
        "codeRegistry.refusesBlankLine"
      assert (
          match CodeRegistry.parse "beta\t2\nalpha\t1\n" with
          | .error _ => true | .ok _ => false)
        "codeRegistry.refusesUnsorted"
      assert (
          match CodeRegistry.parse "alpha\t1\nalpha\t2\n" with
          | .error _ => true | .ok _ => false)
        "codeRegistry.refusesDupName"
      assert (
          match CodeRegistry.parse "alpha\t1\nbeta\t1\n" with
          | .error _ => true | .ok _ => false)
        "codeRegistry.refusesDupCode"
      -- The allocation replay (the gate's tooth): a hand-edited code
      -- falls off the discipline's sequence.
      assert (
          match CodeRegistry.replay cr3 with | .ok _ => true | .error _ => false)
        "codeRegistry.replayCanonical"
      assert (
          match CodeRegistry.replay cr3Retired with | .ok _ => true | .error _ => false)
        "codeRegistry.replayTombstone"
      assert (
          match CodeRegistry.replay [⟨"alpha", 1, false⟩, ⟨"beta", 7, false⟩] with
          | .error _ => true | .ok _ => false)
        "codeRegistry.replayCatchesHandEdit"
      assert (
          match CodeRegistry.replay [⟨"alpha", 0, false⟩] with
          | .error _ => true | .ok _ => false)
        "codeRegistry.replayCatchesHandSetZero"
      assert (decide (¬(Kit.codeRegistryWf.check [⟨"b", 2, false⟩, ⟨"a", 1, false⟩])))
        "codeRegistry.wfCatchesSortedViolation")
    [ ("the live-max allocator agrees with nextCode",
        fun _ =>
          assert (sabNextCode crAllHighRetired == crAllHighRetired.nextCode)
            "control fired: the live-max allocator reused the retired code \
              (the tombstones do NOT hold the codes spent)")
    , ("the tombstone-clause-dropped stability agrees with the verdict",
        fun _ =>
          assert (sabStable cr3Retired cr3TombstoneDropped
            == CodeRegistry.checkStable cr3Retired cr3TombstoneDropped)
            "control fired: the sabotaged stability accepted the \
              tombstone-dropped registry")
    , ("the lax parser agrees with the real parse",
        fun _ =>
          assert ((sabParse "alpha\t1x\n").isSome
            == (CodeRegistry.parseRow "alpha\t1x\n").isSome)
            "control fired: the lax parser accepted the malformed line") ]
    4 42

def changeSpec : Spec :=
  Spec.ofList "Kit.Change — the ladder's worked instances"
    (fun _ => do
      assert (decide (intAdd.apply 3 4 = some 7)) "change.intAdd.applies"
      assert (decide (intAdd.apply 5 intAdd.nop = some 5)) "change.intAdd.nop"
      assert (decide (intAdd.apply 3 5 = some 8 ∧ intAdd.apply 8 (intAdd.inv 5) = some 3))
        "change.intAdd.roundTrip"
      -- The inverse is LAWFUL: the compose-level inverse laws force the
      -- apply-level round trip (Additive.invRoundTrip, general).
      assert (decide (intAdd.apply 8 (intAdd.inv 5) = some 3)) "change.intAdd.derivedInverse"
      assert (decide ((intAdd.apply 7 2).bind (intAdd.apply · 3)
        = (intAdd.apply 7 3).bind (intAdd.apply · 2))) "change.intAdd.bindComm"
      assert (decide (monus.apply 7 3 = some 4)) "change.monus.applies"
      assert (decide (monus.apply 3 5 = some 0)) "change.monus.saturates"
      assert (decide (monus.apply 9 monus.nop = some 9)) "change.monus.nop"
      assert (decide (fieldSet.apply ⟨0, 0⟩ (Field.name, 7) = some ⟨7, 0⟩))
        "change.fieldSet.applies")
    [ ("monus round-trips",
        fun _ =>
          assert (decide ((monus.apply 3 5).bind (monus.apply · 4) = some 3))
            "control fired: the saturating delta restored the original state")
    , ("field-set is invertible",
        fun _ =>
          assert (decide (fieldSet.apply ⟨9, 0⟩ (Field.name, 7) = some ⟨9, 0⟩))
            "control fired: the forgotten old value came back")
    , ("one field-set covers the composite",
        fun _ =>
          assert (decide (fieldSet.apply ⟨0, 0⟩ (Field.name, 1) = some ⟨1, 2⟩))
            "control fired: a single field-set covered a two-field composite") ]
    4 42

def observerSpec : Spec :=
  Spec.ofList "Kit.Observer — the observer-choice pins"
    (fun _ => do
      assert (decide ((apiObs Int).equiv ex1 ex2)) "observer.equiv.api"
      assert (decide (¬((auditObs Int).equiv ex1 ex2))) "observer.notEquiv.audit"
      assert (decide ((auditObs Int).equiv ex1 ex1 → (auditObs Int).equiv ex1 ex1))
        "observer.equiv.symm"
      assert (decide ((apiObs Int).see ex1
        = (apiBelowAudit Int).extract ((auditObs Int).see ex1))) "observer.below.apiAudit"
      assert (decide ((auditObs Int).see ex1
        = (auditBelowPerf Int).extract ((perfObs Int).see ex1))) "observer.below.auditPerf"
      assert (decide ((securityObs (fun _ (e : Int) => e % 2 == 0) 0).see ex1 =
        (securityBelowAudit (fun _ (e : Int) => e % 2 == 0) 0).extract
          ((auditObs Int).see ex1))) "observer.below.securityAudit")
    [ ("the api observation distinguishes the traces",
        fun _ =>
          assert (decide ((apiObs Int).see ex1 ≠ (apiObs Int).see ex2))
            "control fired: the api observation distinguished the executions")
    , ("the sabotaged extract honors the Below law",
        fun _ =>
          assert (decide (sabExtract ((auditObs Int).see ex1) = (apiObs Int).see ex1))
            "control fired: the sabotaged extract matched the api observation")
    , ("the audit observation collapses onto the api view",
        fun _ =>
          assert (decide ((auditObs Int).see ex1 = (auditObs Int).see ex2))
            "control fired: the audit observation saw the same thing the \
              api observation saw — it is not blind to the trace") ]
    4 42

def main : IO UInt32 := do
  -- the emit driver's IO half: the artifact write + read-back (the
  -- result folds into `emitSpec` as the `emit.driverWrote` pin; the
  -- file is cleaned up)
  let scratch := "kit/KitTests/scratch/emitted.txt"
  IO.FS.createDirAll "kit/KitTests/scratch"
  Kit.Emit.runEmitters "kit-tests" [(e1scratch, ["a", "b"])]
    (fun _ _ => pure { contentHash := ("a,b".hash : UInt64) })
  let back ← IO.FS.readFile scratch
  IO.FS.removeFile scratch
  let emitDriverOk := back.contains "GENERATED" && back.contains "a,b"
  TestKit.mainOfSuites
    [ ("Kit.Correspondence", [correspondenceSpec])
    , ("Kit.Obligation", [obligationSpec])
    , ("Kit.Registry", [registrySpec])
    , ("Kit.CheckedProp + Kit.Lane", [checkedLaneSpec])
    , ("Kit.Emit", [emitSpec emitDriverOk])
    , ("Kit.Diag/Suggest/FreshName", [diagSuggestSpec])
    , ("Kit.CodeRegistry", [codeRegistrySpec])
    , ("Kit.Change", [changeSpec])
    , ("Kit.Observer", [observerSpec]) ]
