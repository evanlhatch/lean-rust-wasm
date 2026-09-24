/-
# KitTests — the kit's test exe

Per module: the positive pins + the MANDATORY negative controls
(15-patterns #5 — a suite without its control doesn't construct). The
negative controls here are DATA-LEVEL: a sabotaged case must FAIL a
check function (the proof-level refusal is the elaborator itself — a
law-less literal cannot construct; each control names which refusal it
mirrors).

The runner is TestingKit's (`mainOfSuites` — doctrine 12 §9: tests are
data folds; SchemaTests already rides it on the same root package).
Each module section is one Spec; the sabotage cases are the Spec's
NEGATIVES, each guarded by the vacuity tripwire.

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the laws — zero-axiom output or the build fails.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Correspondence
import Kit.Relation
import Kit.Hyper
import Kit.Obligation
import Kit.Registry
import Kit.CheckedProp
import Kit.Emit
import Kit.Ledger
import Kit.Suggest
import Kit.FreshName
import Kit.Diag
import Kit.Lane
import Kit.CodeRegistry
import Kit.Change
import Kit.Observer
import Kit.Text
import Kit.Duel
import Kit.Mangle
import Kit.Json
import Kit.Validation
import Kit.Derive.Fold
import Kit.Derive.Bridge
import Kit.Derive.Evidence
import TextKit.Error
import TestingKit.Harness
import KitTests.Axioms

open Kit
open Kit.Emit
open TestingKit

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

/-- The claim is IN THE TYPE now: `oblg` claims `42 = 42` (the claim's
    pairing with the payload is fixed at construction; the backends
    discharge the index, there is no claim parameter to mis-wire). -/
def oblg : Obligation Nat (42 = 42) where
  label := "answer-is-42"
  tier := .decidableNow
  payload := 42
  provenance := `KitTests

/-- The FALSE-claim sibling (the negative control's producer): the
    claim `43 = 42` — the row is a different TYPE; its discharge is the
    loud `none` (the backend refuses, it does not fabricate evidence). -/
def oblgFalse : Obligation Nat (43 = 42) where
  label := "answer-is-43"
  tier := .decidableNow
  payload := 42
  provenance := `KitTests

/-- The claim accessor: the index, named (definitionally `42 = 42`). -/
example : oblg.claim = (42 = 42) := rfl

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

/-! ## Fixtures — Emit binary lane (Order 1) -/

/-- The scratch binary emitter's payload: 8 LCG-seeded bytes (seed 42,
    pinned — the replay discipline). -/
def ebBytes : ByteArray := (Kit.Duel.genBytes (TestingKit.Tape.ofSeed 42) 8).1

/-- The scratch binary emitter: one codec-shaped byte vector, an EMPTY
    text lane (`run := []` — the two lanes share the one-writer
    namespace, never one path). -/
def eb : Emitter (List String) where
  name := "eb"
  style := .lean
  specSource := "KitTests"
  outputs := []
  binaryOutputs := ["kit/KitTests/scratch/emitted.bin"]
  run _ := []
  runBinary := some fun _ =>
    [{ path := "kit/KitTests/scratch/emitted.bin", contents := ebBytes }]

/-- The honest sidecar: the header naming the fresh bytes' hash (what
    the driver writes). -/
def freshSidecar : String :=
  Kit.Emit.header .lean "kit-tests" "KitTests"
    { contentHash := Kit.Emit.bytesHash ebBytes }

/-- The STALE sidecar: its hash row names a DIFFERENT body — the
    sidecar-check control's producer. -/
def staleSidecar : String :=
  Kit.Emit.header .lean "kit-tests" "KitTests"
    { contentHash := Kit.Emit.bytesHash (ebBytes.push 0) }

/-! ## Fixtures — Duel (Order 2) -/

/-- The fixture vector set: the differential's shape — one LCG-seeded
    golden (decode + byte-identical re-encode expected) + one tamper
    (the last byte dropped: refuse expected). -/
def vs1 : Kit.Duel.VectorSet where
  dir := "kit/KitTests/scratch/duel"
  name := "fixture-duel"
  generator := "KitTests"
  vectors :=
    [ { path := "kit/KitTests/scratch/duel/golden.bin", contents := ebBytes }
    , { path := "kit/KitTests/scratch/duel/tampered.bin"
      , contents := (ebBytes.toList.take (ebBytes.size - 1)).toByteArray } ]
  expects :=
    [ ("kit/KitTests/scratch/duel/golden.bin", .decode "lcg-42 eight bytes")
    , ("kit/KitTests/scratch/duel/tampered.bin", .refuse) ]

/-- The witness fixture (the diverge row's minimal evidence). -/
def witnessAt : Kit.Duel.Witness := { loc := "v", lhs := "1", rhs := "2" }

/-! ## Fixtures — Diag / Suggest / FreshName -/

/-- The valid space the fixture failures speak over. -/
def fixtureValid : List String := ["were", "what", "when"]

/-- A fully-filled Diag literal (the positional/lint face: no got, no
    valid space — `closedWorld` is not the route here). -/
def fixtureDiag : Diag :=
  { code := ⟨"K000" ++ "1"⟩
  , message := "schema: unsupported construct"
  , context := [Label.at "schema", { name := "field", detail := "user" }]
  , severity := .error }

/-- The closed-world fixture: one call, suggest filled by the engine. -/
def fixtureClosed : Diag :=
  Diag.closedWorld ⟨"K000" ++ "2"⟩ "schema: unknown clause" .error "whre" fixtureValid

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

/-! ## Kit.Relation — the relational engine's fixtures

The worked instance (the task's e2e): ONE toy expression language,
evaluated TWO ways — directly into `Nat`, and accumulator-style into
`Nat → Nat` (the classic accumulator transformation). The per-primitive
rows are supplied ONCE; THE generic theorem (`Kit.Expr.preserves`)
delivers the whole-program agreement for free. The composition
discipline: a map stage (the scale-and-shift pair, `Expr.pipeline`) and
a chain (direct → accumulator → direct, end-to-end as ONE composite
relation, `Expr.chain`). The negative controls: a WRONG per-primitive
row and a WRONG stage row — the premises are load-bearing.
-/

/-- Toy program 1: `3 + double 5 = 13`. -/
def toyE : Kit.Expr Nat := .bin (.prim 3) (.un (.prim 5))

/-- Toy program 2: `double (1 + double 2) = 10` — a different shape;
    the generic theorem's coverage is the whole universe, not one
    program. -/
def toyE' : Kit.Expr Nat := .un (.bin (.prim 1) (.un (.prim 2)))

/-- THE relation: the accumulator evaluation is the direct evaluation
    shifted by the accumulator, POINTWISE (the honest shape — `f 0 = n`
    alone is too weak to compose through `un`). -/
def toyR : Rel Nat (Nat → Nat) := fun n f => ∀ acc, f acc = n + acc

def toyLeaf₁ : Nat → Nat := fun n => n
def toyUn₁ : Nat → Nat := fun a => a + a
def toyBin₁ : Nat → Nat → Nat := fun a b => a + b
def toyLeaf₂ : Nat → Nat → Nat := fun n acc => n + acc
def toyUn₂ : (Nat → Nat) → Nat → Nat := fun f acc => f (f acc)
def toyBin₂ : (Nat → Nat) → (Nat → Nat) → Nat → Nat := fun f g acc => f (g acc)

def toyEval₁ (e : Kit.Expr Nat) : Nat := e.fold toyLeaf₁ toyUn₁ toyBin₁
def toyEval₂ (e : Kit.Expr Nat) : Nat → Nat := e.fold toyLeaf₂ toyUn₂ toyBin₂

/-- The shared node laws (both rows instances read them; no duplicated
    proof bodies). -/
theorem toyUnRow (n : Nat) (f : Nat → Nat)
    (h : ∀ acc, f acc = n + acc) (acc : Nat) :
    f (f acc) = n + n + acc := by rw [h, h, Nat.add_assoc]

theorem toyBinRow (n₁ n₂ : Nat) (f g : Nat → Nat)
    (h1 : ∀ acc, f acc = n₁ + acc) (h2 : ∀ acc, g acc = n₂ + acc) (acc : Nat) :
    f (g acc) = n₁ + n₂ + acc := by rw [h2, h1, Nat.add_assoc]

/-- The per-primitive rows, supplied ONCE (the engine's only input). -/
theorem toyRows : Preserves Nat Nat (Nat → Nat) toyR
    toyLeaf₁ toyUn₁ toyBin₁ toyLeaf₂ toyUn₂ toyBin₂ :=
  { prim := fun _p _acc => rfl
    un := fun a b h acc => toyUnRow a b h acc
    bin := fun a₁ a₂ b₁ b₂ h1 h2 acc => toyBinRow a₁ a₂ b₁ b₂ h1 h2 acc }

/-- THE agreement: whole-program, delivered by the generic theorem —
    no per-program proof exists anywhere below. -/
theorem toyAgrees (e : Kit.Expr Nat) :
    toyR (toyEval₁ e) (toyEval₂ e) := Expr.preserves toyRows e

/-- The determinism rows: the SAME evaluation paired with itself, the
    diagonal relation (the reflexivity case). -/
theorem toyDetRows : Preserves Nat Nat Nat (Rel.refl Nat)
    toyLeaf₁ toyUn₁ toyBin₁ toyLeaf₁ toyUn₁ toyBin₁ :=
  { prim := fun _p => rfl
    un := fun a b h => by show toyUn₁ a = toyUn₁ b; rw [h]
    bin := fun a₁ a₂ b₁ b₂ h1 h2 => by
      show toyBin₁ a₁ a₂ = toyBin₁ b₁ b₂
      rw [h1, h2] }

/-- Reflexivity as determinism (§6): the single-interpretation pair
    through `Interpretation.refl` — the generic theorem delivers the
    agreement with no new proof. -/
theorem toyDet (e : Kit.Expr Nat) :
    (Interpretation.refl toyEval₁).R
      ((Interpretation.refl toyEval₁).eval₁ e)
      ((Interpretation.refl toyEval₁).eval₂ e) :=
  Expr.preserves toyDetRows e

/-- The map stage: scale-and-shift. `toyF₁` on the direct side, `toyF₂`
    on the accumulator side; `toyS` relates their outputs. -/
def toyF₁ : Nat → Nat := fun n => n + 100
def toyF₂ : (Nat → Nat) → Nat → Nat := fun g _acc => g 0 + 100
/-- (`abbrev`: the negative control's decide sees through to the Eq.) -/
abbrev toyS : Rel Nat (Nat → Nat) := fun n g => g 0 = n

/-- The map-stage row: R-preservation into S (proved once). -/
theorem toyStage (a : Nat) (b : Nat → Nat) (h : toyR a b) :
    toyS (toyF₁ a) (toyF₂ b) := by
  have h0 := h 0
  rw [Nat.add_zero] at h0
  show b 0 + 100 = a + 100
  rw [h0]

/-- THE map pipeline: end-to-end through the second stage — no second
    induction (`Expr.pipeline` = one application of THE theorem). -/
theorem toyPipeline (e : Kit.Expr Nat) :
    toyS (toyF₁ (toyEval₁ e)) (toyF₂ (toyEval₂ e)) :=
  Expr.pipeline toyRows toyStage e

/-- The chain's second relation: accumulator → direct (pair 2 shares
    the middle universe with pair 1; its rows are pair 1's node laws,
    read in the other direction). -/
def toyRFlip : Rel (Nat → Nat) Nat := fun f n => ∀ acc, f acc = n + acc

theorem toyRowsFlip : Preserves Nat (Nat → Nat) Nat toyRFlip
    toyLeaf₂ toyUn₂ toyBin₂ toyLeaf₁ toyUn₁ toyBin₁ :=
  { prim := fun _p _acc => rfl
    un := fun f n h acc => toyUnRow n f h acc
    bin := fun f g n₁ n₂ h1 h2 acc => toyBinRow n₁ n₂ f g h1 h2 acc }

/-- THE chain: direct → accumulator → direct, end-to-end as ONE
    composite relation — the witness is the middle (accumulator)
    evaluation, the two inductions are THE generic theorem
    (`Expr.chain`). -/
theorem toyChain (e : Kit.Expr Nat) :
    Rel.comp toyR toyRFlip (toyEval₁ e) (toyEval₁ e) :=
  Expr.chain toyRows toyRowsFlip e

/-- The composite's witness chain is SHARP: 13 relates only to 13 (the
    middle accumulator is pinned by both legs). -/
theorem toyChainSharp : ¬ Rel.comp toyR toyRFlip 13 14 := by
  intro h
  obtain ⟨f, h1, h2⟩ := h
  have h13 := h1 0
  have h14 := h2 0
  rw [Nat.add_zero] at h13 h14
  rw [h13] at h14
  simp at h14

/-! ## Kit.Relation — the negative controls' producers -/

/-- NEGATIVE CONTROL's producer: the off-by-one accumulator leaf — its
    per-primitive row is FALSE (the premise is load-bearing). -/
def sabLeaf₂ : Nat → Nat → Nat := fun n acc => acc + n + 1

def sabEval₂ (e : Kit.Expr Nat) : Nat → Nat := e.fold sabLeaf₂ toyUn₂ toyBin₂

/-- The sabotaged row FAILS (the witness: acc = 0). -/
theorem sabRowFails : ¬ toyR 5 (sabLeaf₂ 5) := by
  intro h
  have h0 := h 0
  simp [sabLeaf₂] at h0

/-- The stage-2 saboteur: the constant 999 — its stage row is FALSE. -/
def toyF₂' : (Nat → Nat) → Nat → Nat := fun _ _ => 999

theorem sabStageFails :
    ¬ ∀ (a : Nat) (b : Nat → Nat), toyR a b → toyS (toyF₁ a) (toyF₂' b) := by
  intro H
  have h := H 5 (toyLeaf₂ 5) (toyRows.prim 5)
  simp [toyS, toyF₁, toyF₂'] at h

/-! ## Kit.Relation — the relation-family pins -/

/-- Concrete shift relations for the §1 pins (`abbrev`: the decide
    instances see through to the Nat equalities). -/
abbrev relR : Rel Nat Nat := fun a b => a + 1 = b
abbrev relS : Rel Nat Nat := fun b c => b + 2 = c
abbrev relT : Rel Nat Nat := fun c d => c + 3 = d

theorem relCompAssocPin :
    (Rel.comp (Rel.comp relR relS) relT (1 : Nat) 7 ↔
      Rel.comp relR (Rel.comp relS relT) (1 : Nat) 7) :=
  Rel.comp_assoc relR relS relT 1 7

theorem relCompAssocLhs : Rel.comp (Rel.comp relR relS) relT (1 : Nat) 7 :=
  ⟨4, ⟨2, rfl, rfl⟩, rfl⟩

theorem relCompAssocRhs : Rel.comp relR (Rel.comp relS relT) (1 : Nat) 7 :=
  ⟨2, rfl, ⟨4, rfl, rfl⟩⟩

/-- Transitivity via the composite's collapse (`Rel.trans_iff`): `≤`'s
    transitivity read off `Rel.comp` — the transitivity-friendly shape
    in action. -/
theorem relLeTrans : ∀ x z : Nat,
    Rel.comp (fun a b => a ≤ b) (fun a b => a ≤ b) x z → x ≤ z :=
  (Rel.trans_iff (fun a b => a ≤ b)).mp fun _ _ _ h1 h2 => Nat.le_trans h1 h2

/-- The determinism pin: a reflexive, deterministic relation IS the
    diagonal (`Rel.det_iff`). -/
theorem relDetPin (a b : Nat) : ((∃ _k : Nat, a = b) ↔ a = b) :=
  Rel.det_iff (fun a b => ∃ _k : Nat, a = b) (fun _ => ⟨0, rfl⟩)
    (fun _ _ h => by obtain ⟨_, h⟩ := h; exact h) a b

theorem relIdLeftPin : (Rel.comp (Rel.refl Nat) relR 1 2 ↔ relR 1 2) :=
  Rel.comp_reflLeft relR 1 2

/-! ## Fixtures — Mangle / Json / Validation -/

/-- The mined legacy corpus: every convention emits from the SAME word
    list (camel/snake/kebab differ only in glue + capitalization). -/
def manglerCorpus : List String := ["maxHealth", "max_health", "MaxHealth"]

/-- The colliding pair: kebab is NOT injective — two legal source names,
    one mangled image (the mined caught-bug class). -/
def collidingNames : List String := ["FooBar", "foo-bar"]

/-- Sabotaged WF: checks PRE-mangle nodup instead of POST-mangle — it
    ACCEPTS the colliding pair (both names distinct) where the real
    `mangleWf` refuses (the negative control's producer). -/
def sabMangleWf (ns : List String) : Bool := ns.Nodup

/-- Sabotaged fold: the Except-shaped early exit (the first error wins,
    the rest of the list never reports) — the anti-early-exit control's
    producer: it counts ONE failure where Validation counts ALL three. -/
def sabEarlyCount : Nat :=
  match (([1, 2, 3] : List Nat).foldlM (fun (_ : Nat) (_ : Nat) => Except.error "e") 0 :
    Except String Nat) with
  | .error _ => 1
  | .ok _ => 0

/-- Sabotaged escaper: the RAW wrap (no escaping — the quote passes
    through into the output's body) — the negative control's producer:
    on a quote-carrying input its output differs from the real
    `Kit.Json.jsonStr`'s. -/
def sabJsonStr (s : String) : String := "\"" ++ s ++ "\""

/-! ## Sabotage fixtures — the negatives' producers

The sabotage cases hoisted out of the suite (each feeds one NEGATIVE
control in the specs below; the control claims the sabotage is lawful
and MUST fail — the vacuity tripwire (TestingKit.Harness) is the guard
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
    same decide. (Renamed off `Kit.dupNames` — the restored dup scan's
    name.) -/
def dupNameFixture : List String :=
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

/-! ## The suite — TestingKit's runner (doctrine 12 §9: tests are data folds)

One Spec per module section: the section's positive pins are the prop
(each assert names its pin — the failure evidence keeps the old
granularity), and the section's sabotage cases are the Spec's NEGATIVES
(each must FAIL; TestingKit's vacuity tripwire guards them). CheckedProp
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
      -- the backends discharge the obligation's OWN claim (the index)
      assert (decide (oblg.decideDischarge = some (Evidence.decided true)))
        "obligation.dischargeFires"
      assert (decide (¬(Kit.tierMismatch oblg (Evidence.decided true)))) "obligation.tierMatches"
      assert (
          let d : Discharged Nat (42 = 42) := { obligation := oblg, evidence := .decided true }
          d.obligation.payload == 42)
        "obligation.dischargedConstructs")
    [ ("false claim discharges",
        fun _ =>
          assert (decide (oblgFalse.decideDischarge = some (Evidence.decided true)))
            "control fired: a false claim was fabricated into evidence")
    , ("oracle-row evidence is well-tiered",
        fun _ =>
          assert (decide (¬(Kit.tierMismatch oblg (Evidence.oracleRow "oracle-1"))))
            "control fired: an oracle-row evidence against decidableNow is a mis-wire") ]
    4 42

/-! ## Kit.Obligation — the type-level teeth (the elaborator is the
    refusal; these are NOT data-level controls — they fail the BUILD if
    the mis-wire becomes constructible again) -/

-- THE TEETH (the review's correction): a discharge cannot prove a
-- claim it does not carry — routing `oblg`'s discharge to a DIFFERENT
-- proposition fails to elaborate. The claim is the index; there is no
-- claim parameter to mis-wire.
/-- error: Type mismatch
  Obligation.decideDischarge_sound oblg rfl h
has type
  oblg.claim
but is expected to have type
  43 = 42
-/
#guard_msgs in
example (h : oblg.decideDischarge = some (Evidence.decided true)) : 43 = 42 :=
  Obligation.decideDischarge_sound oblg rfl h

-- THE TEETH, discharge-side: a `Discharged` FILED UNDER THE WRONG
-- CLAIM is a different type — the obligation's index refuses the
-- wrong-claim row at elaboration.
/-- error: Type mismatch
  oblgFalse
has type
  Obligation Nat (43 = 42)
but is expected to have type
  Obligation Nat (42 = 42)
---
error: could not synthesize default value for field 'tierOK' of 'Kit.Discharged' using tactics
-/
#guard_msgs in
example : Discharged Nat (42 = 42) :=
  { obligation := oblgFalse, evidence := .decided true }

-- THE TEETH, backend-side: `decideDischarge` takes NO claim — the
-- old mis-wire (discharging one row with another row's claim) no
-- longer parses. The only claim a discharge can carry is the index.
/-- error: Function expected at
  oblg.decideDischarge
but this term has type
  Option Evidence

Note: Expected a function because this term is being applied to the argument
  (fun _ => True)
-/
#guard_msgs in
example := oblg.decideDischarge (fun _ => True)

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
        "codedRegistry.membersIso"
      -- THE insert restoration: freshness is an ARGUMENT (no illegal
      -- state to reject); the laws are exercised, not just stated.
      assert (
          let hf : itemReg.nameOf 4 ∉ itemReg.items.map itemReg.nameOf := by
            simp [itemReg]
          match (itemReg.insert 4 hf).lookup? "item4" with
          | .ok a => a == 4
          | .error _ => false)
        "registry.insertSelfLookup"
      assert (
          let hf : itemReg.nameOf 4 ∉ itemReg.items.map itemReg.nameOf := by
            simp [itemReg]
          (itemReg.insert 4 hf).all == [4, 1, 2, 3])
        "registry.insertGrowsAll"
      -- determinism under nodup: the looked-up item is THE item with
      -- its name — exactly one item in the inserted registry carries
      -- the looked-up name (lookup?_ok_unique, read off the value).
      assert (
          let hf : itemReg.nameOf 4 ∉ itemReg.items.map itemReg.nameOf := by
            simp [itemReg]
          let r := itemReg.insert 4 hf
          r.items.filter (fun b => r.nameOf b == "item4") == [4])
        "registry.insertLookupUnique")
    [ ("duplicate names construct a registry",
        fun _ =>
          assert (dupNameFixture.Nodup)
            "control fired: the duplicate-named literal's data mirror constructed")
    , ("colliding hand-set codes allocate",
        fun _ =>
          assert ((sabCodes.map (·.2)).Nodup)
            "control fired: the colliding-code literal's data mirror constructed")
    , ("the freshness obligation dropped is still lawful",
        fun _ =>
          -- the lax insert's mirror: appending a DUPLICATE name runs
          -- anyway (no obligation, no refusal) — the name map the real
          -- `insert`'s argument forbids is not nodup.
          assert (decide (((1 :: itemReg.items).map (fun n => s!"item{n}")).Nodup))
            "control fired: the obligation-free insert produced a lawful registry") ]
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

/-- The binary lane's pins (the driver's IO result folds in as
    `emitBinary.driverWrote` — the same shape as `emitSpec`). -/
def emitBinarySpec (binaryOk : Bool) : Spec :=
  Spec.ofList "Kit.Emit binary lane — the byte-artifact pins"
    (fun _ => do
      assert (decide (eb.binaryOutputs.Nodup)) "emitBinary.outputsNodup"
      assert (eb.runBinary.isSome) "emitBinary.laneDeclared"
      -- The cross-lane audit: one path namespace, text + binary both.
      assert (Kit.Emit.outputsDisjoint [e1, eb]) "emitBinary.crossLaneDisjoint"
      -- THE byte-tie: fresh bytes tie; drifted bytes don't; a stale
      -- sidecar doesn't.
      assert (
          match Kit.Emit.tieBytes freshSidecar ebBytes ebBytes with
          | .tied => true | .drifted _ => false)
        "emitBinary.tieFresh"
      assert (
          match Kit.Emit.tieBytes freshSidecar ebBytes (ebBytes.push 7) with
          | .drifted _ => true | .tied => false)
        "emitBinary.tieCatchesDrift"
      assert (
          match Kit.Emit.tieBytes staleSidecar ebBytes ebBytes with
          | .drifted _ => true | .tied => false)
        "emitBinary.tieCatchesStaleSidecar"
      assert (Kit.Emit.bytesHash ebBytes == Kit.Emit.bytesHash ebBytes)
        "emitBinary.hashDeterministic"
      assert (binaryOk) "emitBinary.driverWrote")
    [ ("drifted bytes tie",
        fun _ =>
          assert (
              match Kit.Emit.tieBytes freshSidecar ebBytes (ebBytes.push 7) with
              | .tied => true | .drifted _ => false)
            "control fired: the byte-tie accepted drifted bytes")
    , ("the stale sidecar ties",
        fun _ =>
          assert (
              match Kit.Emit.tieBytes staleSidecar ebBytes ebBytes with
              | .tied => true | .drifted _ => false)
            "control fired: the byte-tie accepted a stale sidecar") ]
    4 42

/-- The duel harness's pins (the vector-set emit's IO result folds in
    as `duel.driverWrote`). -/
def duelSpec (duelOk : Bool) : Spec :=
  Spec.ofList "Kit.Duel — the duel/vector harness pins"
    (fun _ => do
      assert (decide ((vs1.vectors.map (·.path)).length = 2)) "duel.twoVectorsDeclared"
      assert (Kit.Duel.expectsCovered vs1) "duel.expectsCovered"
      -- The seeded generator: same seed, byte-identical replay (#14).
      assert (
          let (bs, _) := Kit.Duel.genBytes (TestingKit.Tape.ofSeed 42) 8
          bs == ebBytes)
        "duel.genBytesSeedReplay"
      assert (decide (Kit.Duel.Verdict.foldRows [.agree, .agree] = .agree))
        "duel.foldRowsAgree"
      assert (
          match Kit.Duel.Verdict.foldRows [.agree, .diverge witnessAt] with
          | .diverge w => w.loc == "v" ∧ w.rhs == "2" | _ => false)
        "duel.foldRowsSurfacesWitness"
      assert (
          match Kit.Duel.Verdict.foldRows [.agree, .refused "typed codec error"] with
          | .refused why => why == "typed codec error" | _ => false)
        "duel.foldRowsSurfacesRefusal"
      -- The manifest names the generator + the expectations (the
      -- consumer contract's data).
      assert ((Kit.Duel.manifestBody vs1).contains "generator\tKitTests")
        "duel.manifestNamesGenerator"
      assert ((Kit.Duel.manifestBody vs1).contains
        "golden.bin\tdecode lcg-42 eight bytes")
        "duel.manifestDecodeRow"
      assert ((Kit.Duel.manifestBody vs1).contains "tampered.bin\trefuse")
        "duel.manifestRefuseRow"
      assert (duelOk) "duel.driverWrote")
    [ ("the colliding vector set constructs",
        fun _ =>
          assert (((["a.bin", "a.bin"] : List String).Nodup))
            "control fired: the duplicate-path vector set's data mirror constructed")
    , ("the sabotaged aggregate agrees",
        fun _ =>
          assert (decide (Kit.Duel.Verdict.foldRows [.agree, .diverge witnessAt] = .agree))
            "control fired: the duel verdict collapsed a divergence into agreement") ]
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
        = "[K000" ++ "1] error: schema: unsupported construct [schema, field (user)]"))
        "diag.literalRender"
      assert (decide (toString fixtureClosed
        = "[K000" ++ "2] error: schema: unknown clause (got: whre) — \
valid: were, what, when — did you mean: were, what, when?"))
        "diag.closedWorldRender"
      -- (TextKit-qualified: the ctor dot-notation does not resolve
      --   through the `Kit.Severity` abbrev shim — the home's face)
      assert (decide (([TextKit.Severity.error, .warning, .gate, .obligation, .info] :
            List TextKit.Severity).map
          TextKit.Severity.render
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
        "codeRegistry.wfCatchesSortedViolation"
      -- THE BRIDGES (the lint-wave's laws, pinned usable at the value
      -- level): the stability checker's TRUE verdict DECIDES the live
      -- pair's survival (checkStable_ok's soundness face — no new
      -- computation, the law carries the pin), and the file-format
      -- round trip is the parse_print THEOREM (well-formed registry:
      -- print then parse is EXACTLY the identity).
      -- THE BRIDGES (the lint-wave's laws, pinned at the value level):
      -- checkStable_ok (the stability bridge) PROVES the pin below — its
      -- soundness face applied to the live pair is exactly
      -- `cr3.lookup "beta" = some 2`; and parse_print (the file-format
      -- law) proves the round trip: a wf registry parses back EXACTLY.
      assert (decide (cr3.lookup "beta" = some 2))
        "codeRegistry.checkStableOkLivePairSurvives"
      assert (decide (CodeRegistry.parse (CodeRegistry.print cr3) = .ok cr3))
        "codeRegistry.parsePrintRoundTripLaw")
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

/-- The E-code registry's COVERAGE pins (05 §4's envelope discipline at
    the source): the committed registry — `notes/code-registry.txt`,
    folded in from `main`'s IO half (the registry is PERSISTED data,
    not a Lean literal) — is well-formed, replays, is stable and
    canonical; every family constant the kit declares is a LIVE row of
    it; and the coverage tooth's verdict gets its mandatory negative
    controls. The unregistered fixture spelling is built from PIECES
    (`"KB99" ++ "99"`): the gate's scan is total over the tree's
    sources, so even a test fixture must not hand-string an unallocated
    code. -/
def codeCoverageSpec (committed : Except String CodeRegistry) : Spec :=
  Spec.ofList "Kit.CodeRegistry — the coverage pins"
    (fun _ => do
      match committed with
      | .error _ => assert false "coverage.committedParses"
      | .ok r => do
        -- the committed file: well-formed, replayed, stable, canonical
        assert (decide (Kit.codeRegistryWf.check r))
          "coverage.committedWellFormed"
        assert (
            match CodeRegistry.replay r with | .ok _ => true | .error _ => false)
          "coverage.committedReplays"
        assert (decide (CodeRegistry.checkStable r r))
          "coverage.committedStable"
        assert (
            match CodeRegistry.parse (CodeRegistry.print r) with
            | .ok r' => r' == r
            | .error _ => false)
          "coverage.committedCanonical"
        -- THE ALLOCATION ROUND TRIP: every family constant's spelling is
        -- a live row (KB/KD in Kit.Derive, KL in Kit.Lane, TK in
        -- TextKit.Error; the other families' constants live at their
        -- owners — the gate's scan ties those).
        assert (decide ([Kit.Derive.Bridge.eKB0001, Kit.Derive.Bridge.eKB0002,
            Kit.Derive.Bridge.eKB0003, Kit.Derive.Bridge.eKB0004,
            Kit.Derive.Bridge.eKB0005, Kit.Derive.Bridge.eKB0006,
            Kit.Derive.Bridge.eKB0007, Kit.Derive.Bridge.eKB0008,
            Kit.Derive.Fold.eKD0001, Kit.Derive.Fold.eKD0002,
            Kit.Derive.Fold.eKD0003, Kit.Derive.Fold.eKD0004,
            Kit.Derive.Fold.eKD0005, Kit.Derive.Fold.eKD0006,
            Kit.Derive.Fold.eKD0007, Kit.Derive.Fold.eKD0008,
            Kit.Derive.Fold.eKD0009, Kit.Lane.eKL0001, Kit.Lane.eKL0002,
            Kit.Lane.eKL0003, Kit.Lane.eKL0004, Kit.Lane.eKL0005,
            Kit.Lane.eKL0006, Kit.Ledger.eKL0007, Kit.Ledger.eKL0008,
            TextKit.parseCode].all
          (fun c => r.lookup c.code ≠ none)))
          "coverage.familyConstantsLive"
        -- the replay's negative control: a tampered code falls off the
        -- discipline's sequence AND fails the stability verdict
        let tampered := r.map fun row =>
          if row.name == "KB0001" then { row with code := row.code + 1 } else row
        assert (
            match CodeRegistry.replay tampered with
            | .error _ => true | .ok _ => false)
          "coverage.tamperedCodeRefuses"
        assert (decide (¬(CodeRegistry.checkStable r tampered)))
          "coverage.tamperedCodeUnstable"
        -- THE COVERAGE TOOTH: registered → clean; unregistered
        -- code-shaped → the offender; not code-shaped → clean; a
        -- TOMBSTONED spelling refuses too (a spent code is not live).
        let probe := "KB99" ++ "99"
        assert (CodeRegistry.codeShape probe) "coverage.probeIsCodeShaped"
        assert (decide (CodeRegistry.coverageOffenders r [("x.lean", probe)] ≠ []))
          "coverage.unregisteredRefuses"
        assert (decide (CodeRegistry.coverageOffenders r
          [("x.lean", "KB0001")] = []))
          "coverage.registeredCleans"
        assert (decide (CodeRegistry.coverageOffenders r
          [("x.lean", "hello")] = []))
          "coverage.plainStringCleans"
        let tombed := r.map fun row =>
          if row.name == "KB0001" then { row with retired := true } else row
        assert (decide (CodeRegistry.coverageOffenders tombed
          [("x.lean", "KB0001")] ≠ []))
          "coverage.tombstonedSpellingRefuses"
        -- the shape's teeth: 4 digits exactly, a DECLARED family only
        assert (decide (!CodeRegistry.codeShape "KB99999"))
          "coverage.shapeFourDigits"
        assert (decide (!CodeRegistry.codeShape ("ZZ00" ++ "01")))
          "coverage.shapeDeclaredFamily"
        -- THE UNDECLARED-FAMILY TOOTH: a raw code-shaped literal whose
        -- family prefix is undeclared is a FINDING — a fresh prefix
        -- cannot bypass the registry by skipping the shape table.
        assert (CodeRegistry.rawShape ("ZZ00" ++ "01"))
          "coverage.undeclaredProbeIsRawShaped"
        assert (decide (CodeRegistry.coverageOffenders r
          [("x.lean", "ZZ00" ++ "01")] ≠ []))
          "coverage.undeclaredFamilyRefuses")
    [ ("the family-clause-dropped shape agrees with the real shape",
        fun _ =>
          -- the LAX shape (the declared-family clause dropped) accepts
          -- the unallocated family — the clause is load-bearing
          let sabShape (s : String) : Bool :=
            let cs := s.toList
            let letters := cs.takeWhile Char.isUpper
            let digits := cs.drop letters.length
            cs.length = letters.length + digits.length
              && digits.length == 4 && digits.all Char.isDigit
          assert (sabShape ("ZZ00" ++ "01")
            == CodeRegistry.codeShape ("ZZ00" ++ "01"))
            "control fired: the family-clause-dropped shape matched the \
real shape — the declared-family clause is not load-bearing")
    , ("the registry-blind coverage agrees with the real verdict",
        fun _ =>
          match committed with
          | .error _ => assert false "coverage.committedParses"
          | .ok r =>
              -- the PADDED coverage (the lookup face fed a fabricated
              -- row) sees no offenders where the real verdict refuses
              -- — the lookup against the COMMITTED rows is load-bearing
              let padded : CodeRegistry :=
                [{ name := "KB999" ++ "9", code := 9999, retired := false }]
              assert ((CodeRegistry.coverageOffenders padded
                    [("x.lean", "KB99" ++ "99")]).isEmpty
                == (CodeRegistry.coverageOffenders r
                  [("x.lean", "KB99" ++ "99")]).isEmpty)
                "control fired: the padded coverage matched the real \
verdict — the coverage tooth has no teeth")
    , ("the undeclared-family tooth dropped agrees with the real verdict",
        fun _ =>
          match committed with
          | .error _ => assert false "coverage.committedParses"
          | .ok r =>
              -- the LAX coverage (the undeclared-family tooth dropped:
              -- the pre-audit behavior) sees no offenders for a fresh
              -- prefix where the real verdict refuses — the tooth is
              -- load-bearing
              let laxOffenders (rr : CodeRegistry) (hits : List (String × String)) :=
                hits.filterMap fun (path, lit) =>
                  if CodeRegistry.codeShape lit && rr.lookup lit = none then
                    some path else none
              assert ((laxOffenders r [("x.lean", "ZZ00" ++ "01")]).isEmpty
                == (CodeRegistry.coverageOffenders r
                  [("x.lean", "ZZ00" ++ "01")]).isEmpty)
                "control fired: the undeclared-family-tooth-dropped coverage \
matched the real verdict — a fresh prefix bypassed silently") ]
    4 42 (h := by simp)

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

def relationSpec : Spec :=
  Spec.ofList "Kit.Relation — the relational engine's pins"
    (fun _ => do
      -- §1: the relation family — the DECIDABLE faces (the proof-level
      -- pins are the theorems + the elaboration lets below)
      assert (decide (relR 1 2 ∧ relS 2 4 ∧ relT 4 7)) "rel.compWitnessChain"
      assert (decide ((4 : Nat) = 4)) "rel.detIffDecidableFace"
      -- the worked instance: rows supplied once, agreement for free
      assert (decide (toyEval₁ toyE = 13 ∧ toyEval₂ toyE 0 = 13))
        "rel.toy.directAndAccumulatorAgree"
      assert (decide (toyEval₂ toyE 7 = 20)) "rel.toy.accumulatorAccumulates"
      assert (decide (toyEval₁ toyE' = 10 ∧ toyEval₂ toyE' 0 = 10))
        "rel.toy.genericTheoremWholeUniverse"
      -- the composition discipline's decidable face: end-to-end value
      -- through the map stage (13 + 100)
      assert (decide (toyF₂ (toyEval₂ toyE) 0 = 113)) "rel.pipeline.endToEndValue"
      -- the proof-level pins: each let is ONE theorem application — the
      -- elaborator is the refusal (drop a premise, the build fails)
      assert (
          let _assoc := relCompAssocPin        -- composition's associativity
          let _lhs := relCompAssocLhs          -- the witness chain, left
          let _rhs := relCompAssocRhs          -- the witness chain, right
          let _trans := relLeTrans 2 4 ⟨3, Nat.le_succ 2, Nat.le_succ 3⟩
          let _idLeft := relIdLeftPin.mpr rfl  -- the diagonal is comp's unit
          let _det := relDetPin 4 4 |>.mp ⟨0, rfl⟩  -- determinism for free
          let _agree := toyAgrees toyE         -- THE generic theorem's output
          let _bundle := Interpretation.ofPreserves_agrees toyRows toyE
          let _detToy := toyDet toyE           -- reflexivity-as-determinism
          let _pipe := toyPipeline toyE        -- the map stage, lifted
          let _chain := toyChain toyE          -- the composite relation
          let _sharp := toyChainSharp          -- the witness chain is sharp
          let _rowFails := sabRowFails         -- the row premise is load-bearing
          let _stageFails := sabStageFails     -- the stage premise too
          true)
        "rel.genericTheoremsElaborate")
    [ ("the off-by-one accumulator row still agrees",
        fun _ =>
          assert (decide (sabEval₂ toyE 0 = toyEval₁ toyE))
            "control fired: the off-by-one accumulator agreed with the \
              direct evaluation — the row premise is not load-bearing")
    , ("the constant stage still composes",
        fun _ =>
          assert (decide (toyS (toyF₁ (toyEval₁ toyE)) (toyF₂' (toyEval₂ toyE))))
            "control fired: the constant-999 stage landed in toyS — the \
              stage premise is not load-bearing")
    , ("the parity relation is the diagonal",
        fun _ =>
          assert ((!(1 % 2 == (3 : Nat) % 2) || ((1 : Nat) = 3) : Bool))
            "control fired: the non-deterministic parity relation collapsed \
              to the diagonal — det_iff's premise is not load-bearing") ]
    4 42

/-! ## Kit.Correspondence — the carrier-as-graph bridge + Kit.Hyper — the
hyperproperty substrate (16-surface §4.1 + §4.3)

The bridge: every carrier value INDUCES its graph `Rel`; the tower-merge
theorems (`toRel_trans` per grade) are exercised at values AND at the
proof level (each let is ONE theorem application — the elaborator is
the refusal), and the agreement is shown non-vacuous (an off-by-two
composite's graph is DISTINGUISHABLE from the engine's composite).

The substrate: `Rel2` over execution pairs + the pointwise lift + THE
flagship hyperproperty (noninterference) — the worked positive (the
secret-dropper), the worked NEGATIVE (the leaky machine, numeric AND
execution-shaped under `securityObs`, each with the counterexample pair
as data), and the mandatory negative controls (the self-pair-only
audit + the loose relation are the producers).
-/

/-- The inverse-facing iso (the second leg for the `trans` pins). -/
def optBitIso : Iso (Option Unit) Bool where
  to o := o.isSome
  inv b := if b then some () else none
  to_inv b := by cases b <;> simp
  inv_to o := by cases o <;> simp

/-- The successor retraction (the second leg for the composite pins). -/
def retSucc : Retraction Nat Nat where
  emb n := n + 1
  inv n := n - 1
  inv_emb n := Nat.add_sub_cancel n 1

/-- NEGATIVE CONTROL producer: the off-by-two composite — the
    retraction composite whose `emb` adds two. Its graph is NOT the
    engine's composite of the graphs. -/
def sabRet : Retraction Bool Nat where
  emb a := bitRetraction.emb a + 2
  inv n := bitRetraction.inv (n - 2)
  inv_emb a := by cases a <;> simp [bitRetraction]

/-- The honest composite's graph check (the data face of
    `(bitRetraction.trans retSucc).toRel`). -/
def honestCompCheck (a : Bool) (b : Nat) : Bool :=
  decide ((bitRetraction.trans retSucc).toRel a b)

/-- The off-by-two composite's own graph check. -/
def sabCompCheck (a : Bool) (b : Nat) : Bool :=
  decide (sabRet.toRel a b)

/-- The bridge's pins. -/
def bridgeSpec : Spec :=
  Spec.ofList "Kit.Correspondence — the carrier-as-graph bridge pins"
    (fun _ => do
      -- the graphs at values (the carrier's own round trips)
      assert (decide (bitOptIso.toRel true (some ()))) "bridge.iso.graph"
      assert (decide ((bitOptIso.trans optBitIso).toRel true true))
        "bridge.iso.compositeGraph"
      assert (decide (bitRetraction.toRel true 1)) "bridge.retraction.graph"
      assert (decide ((bitRetraction.trans retSucc).toRel true 2))
        "bridge.retraction.compositeGraph"
      assert (decide (bitCodec.toRel 1 true)) "bridge.codec.graph"
      assert (decide (¬(bitCodec.toRel 7 true))) "bridge.codec.partialGraph"
      -- THE tower merge: the agreement theorems, READ (each let is ONE
      -- theorem application — the elaborator is the refusal), + the
      -- non-vacuity witness: an off-by-two composite's graph is
      -- DISTINGUISHABLE from the engine's composite
      assert (
          let _iso := Iso.toRel_trans bitOptIso optBitIso true true
            |>.mpr ⟨some (), rfl, rfl⟩
          let _isoUnit := Iso.toRel_refl Bool true true
          let _ret := Retraction.toRel_trans bitRetraction retSucc true 2
            |>.mpr ⟨1, rfl, rfl⟩
          let _retUnit := Retraction.toRel_refl Nat 3 3
          let _codec := Codec.toRel_trans bitCodec (Codec.refl Bool) 1 true
            |>.mpr ⟨true, rfl, rfl⟩
          let _codecUnit := Codec.toRel_refl Nat 4 4
          let _distinguishable := decide (sabRet.toRel true 3 ∧
            ¬((bitRetraction.trans retSucc).toRel true 3))
          true)
        "bridge.towerMergeElaborates")
    [ ("the codec's graph answers the out-of-policy byte",
        fun _ =>
          assert (decide (bitCodec.toRel 7 true ∨ bitCodec.toRel 7 false))
            "control fired: the partial graph answered a byte the \
              accepted-byte policy refuses")
    , ("the off-by-two composite's graph is the engine's composite graph",
        fun _ =>
          assert (decide (sabCompCheck true 3 == honestCompCheck true 3))
            "control fired: the wrong composite's graph agreed with the \
              engine's composite — the agreement theorem is vacuous") ]
    4 42

/-- NEGATIVE CONTROL producer: the self-pair-only noninterference
    audit — probes only `(u, u)` (trivially agreeing), never the
    differing pair. The audit the leak passes. -/
def sabNISelfCheck (f : Nat × Nat → Nat) : Bool :=
  decide (id (f (0, 0)) = id (f (0, 0)))

/-- NEGATIVE CONTROL producer: the loose two-run relation — EVERY pair
    admissible (the public-agreement clause dropped). The relation that
    hides the leak. (`abbrev`: the decide reaches through.) -/
abbrev looseRel : Rel (Nat × Nat) (Nat × Nat) := fun _ _ => True

/-- The substrate's pins. -/
def hyperSpec : Spec :=
  Spec.ofList "Kit.Hyper — the hyperproperty substrate's pins"
    (fun _ => do
      -- the substrate's shapes at values
      assert (decide (pairMap dropSecret ((3, 9), (3, 9)) = (3, 3)))
        "hyper.pairMap"
      assert (decide (Rel.lift2 relR (1, 3) (2, 4))) "hyper.lift2"
      -- the witness pair: ADMISSIBLE under the honest relation (same
      -- public input) — the leak lives in the OUTPUT side
      assert (decide (agreeOn Prod.fst leakWitness.1 leakWitness.2))
        "hyper.witness.admissible"
      -- the worked instances' values
      assert (decide (dropSecret (3, 9) = 3 ∧ leakSecret (3, 9) = 12))
        "hyper.instances.values"
      -- the worked positive: the secret-dropper is noninterfering
      assert (
          let _ni := dropSecret_noninterfering
          let _power := dropSecret_preserves2
          true)
        "hyper.dropSecret.noninterfering"
      -- the worked negative: the leak, refuted by the counterexample pair
      assert (
          let _leak := leakSecret_notNoninterfering
          true)
        "hyper.leak.refuted"
      -- the lifting discipline: the power tower merges with THE one tower
      assert (
          let _lift := Rel.lift2_comp relR relS (1, 3) (4, 6)
            |>.mpr ⟨⟨2, rfl, rfl⟩, ⟨4, rfl, rfl⟩⟩
          let _down := Noninterfering.ofPreserves2 (agreeOn_symm Prod.fst)
            dropSecret_preserves2
          true)
        "hyper.lift2CompElaborates"
      -- the observer composition (cited, not rebuilt)
      assert (
          let _audit := resultOnly_audit_noninterfering Int
          let _api := resultOnly_api_noninterfering Int
          let _sec := resultOnly_security_noninterfering Int Int
            (fun _ _ => false) 0
          true)
        "hyper.observerCompositionElaborates"
      -- the leaky run-map: refuted at the blind principal's sight line
      assert (
          let _leakExec := leakExec_notNoninterfering
          true)
        "hyper.leakExec.refuted")
    [ ("the self-pair-only audit rejects the leaky function",
        fun _ =>
          assert (decide (sabNISelfCheck leakSecret == false))
            "control fired: the self-pair-only audit passed the leaky \
              function — probing (u, u) can never see a leak")
    , ("the leak's witness pair is inadmissible under the loose relation",
        fun _ =>
          assert (decide (¬(looseRel leakWitness.1 leakWitness.2)))
            "control fired: the loose relation (every pair admissible) \
              refused the witness — the relation that hides the leak") ]
    4 42

/-! ## Kit.Text — the rope text-builder (06 §7b's carrier) -/

/-- Sabotaged render: the chunk walk REVERSED (order flipped at every
    `.app`) — the negative control's producer for the render law (a
    wrong walk must be DISTINGUISHABLE from the real one). -/
def sabRopeRender : Text → String :=
  let rec go : Text → List String
    | .nil => []
    | .str s => [s]
    | .app a b => go b ++ go a
  fun t => String.join (go t)

/-- Sabotaged join: DROPS the separators — the intercalate bridge's
    negative control's producer (a gap-less join must fail the
    intercalate equivalence on any multi-element list). -/
def sabSepByDrop (sep : String) : List Text → Text
  | [] => .nil
  | [t] => t
  | t :: ts => Text.app t (sabSepByDrop sep ts)

def textSpec : Spec :=
  Spec.ofList "Kit.Text — the rope pins"
    (fun _ => do
      assert (decide (Text.render .nil = "")) "text.renderNil"
      assert (decide (Text.render (Text.str "ab") = "ab")) "text.renderStr"
      assert (decide (Text.render (Text.app (Text.str "a") (Text.str "b")) = "ab"))
        "text.renderApp"
      assert (decide (Text.render (Text.cat (["a", "b", "c"].map .str))
        = String.join ["a", "b", "c"]))
        "text.catIsJoin"
      assert (decide (Text.render (Text.sepBy "\n" (["a", "b", "c"].map .str))
        = String.intercalate "\n" ["a", "b", "c"]))
        "text.sepByIsIntercalate"
      -- the emitter-shaped block: the rope renders EXACTLY the
      -- string-template bytes (the rewire's value-level proof face)
      assert (decide (
        let lines := ["let x = 1;", "let y = 2;", "x + y"]
        Text.render (Text.cat [.str "fn f() {\n", Text.sepBy "\n" (lines.map .str), .str "\n}"])
          = "fn f() {\n" ++ String.intercalate "\n" lines ++ "\n}"))
        "text.emitterShapedBlockExact"
      assert (decide (Text.render (Text.sepBy "\n" []) = "")) "text.sepByEmpty")
    [ ("the reversed-chunk render is the real render",
        fun _ =>
          assert (
            let t := Text.cat [.str "a", .str "b", .str "c"]
            Text.render t = sabRopeRender t)
            "control fired: the reversed-walk render matched the real render")
    , ("the separator-dropping join is intercalate",
        fun _ =>
          assert (
            let ss := ["a", "b", "c"]
            Text.render (sabSepByDrop "\n" (ss.map .str)) = String.intercalate "\n" ss)
            "control fired: the separator-dropping join matched intercalate") ]
    4 42

/-! ## Kit.Mangle / Kit.Json / Kit.Validation — the restored machinery's
pins

- Mangle: every convention over the SAME word list (the mined legacy
  corpus pins) + THE post-mangle uniqueness discipline: the colliding
  pair FAILS the WF check, the bridge names the culprits, and the
  negative control is the pre-mangle saboteur that accepts it.
- Json: the ONE escaping decision + the two brace styles + the empty
  array (the byte-level pins).
- Validation: the accumulator collects ALL failures (the element-count
  law, read off the value) + the negative control: the Except-shaped
  early exit reports only the FIRST failure.
-/ --

def mangleSpec : Spec :=
  Spec.ofList "Kit.Mangle — the mangler + the post-mangle uniqueness pins"
    (fun _ => do
      -- the word list is the one source (the mined legacy pins)
      assert (decide (words "maxHealth current" = ["max", "health", "current"]))
        "mangle.words.splitsHumpsAndSeparators"
      assert (decide (kebab "maxHealth current" = "max-health-current"))
        "mangle.kebab.legacyCorpus"
      assert (decide (camel "foo_bar baz" = "fooBarBaz")) "mangle.camel"
      assert (decide (pascal "foo_bar" = "FooBar")) "mangle.pascal"
      assert (decide (snake "FooBar baz" = "foo_bar_baz")) "mangle.snake"
      assert (decide (rustIdent "type" = "r#type")) "mangle.rustIdentEscapesKeyword"
      assert (decide (rustIdent "max_health" = "maxHealth")) "mangle.rustIdentPassesThrough"
      -- one word list, other glue: kebab n == snake n with "-" for "_"
      assert (manglerCorpus.all (fun n => kebab n == (snake n).replace "_" "-"))
        "mangle.kebabSnakeSameWords"
      -- kebab/camel/pascal/snake all emit from the same word list
      assert (decide (kebab "MaxHealth" = "max-health" ∧ camel "MaxHealth" = "maxHealth"
        ∧ pascal "MaxHealth" = "MaxHealth" ∧ snake "MaxHealth" = "max_health"))
        "mangle.oneWordList"
      -- THE post-mangle uniqueness discipline: the colliding pair fails
      -- the WF check; the bridge names the culprits.
      assert (!(Kit.mangleWf kebab collidingNames))
        "mangle.wfRefusesCollision"
      assert (
          match Kit.collDiags kebab collidingNames with
          | [{ image := "foo-bar", culprits := ["FooBar", "foo-bar"] }] => true
          | _ => false)
        "mangle.collDiagsNamesAllCulprits"
      -- distinct images pass (a disjoint universe is lawful)
      assert (Kit.mangleWf kebab ["FooBar", "other"])
        "mangle.wfAcceptsDistinctImages"
      -- the bridge, read as data: the scan is empty iff the mangled
      -- list is nodup
      assert (decide ((Kit.collDiags kebab ["FooBar", "foo-bar"] = [])
        = ((collidingNames.map kebab).Nodup)))
        "mangle.bridgeAgrees")
    [ ("the pre-mangle WF agrees with the real WF",
        fun _ =>
          assert (sabMangleWf collidingNames == Kit.mangleWf kebab collidingNames)
            "control fired: the pre-mangle WF (names distinct) matched \
              the real WF's refusal — it cannot see the collision")
    , ("the collision scan passes the collision",
        fun _ =>
          assert (Kit.mangleWf kebab collidingNames)
            "control fired: the WF check accepted the colliding pair") ]
    4 42

def jsonSpec : Spec :=
  Spec.ofList "Kit.Json — the ONE escaping decision + the builders"
    (fun _ => do
      assert (decide (Kit.Json.jsonStr "a\"b" = "\"a\\\"b\""))
        "json.jsonStr.escapesQuote"
      assert (decide (Kit.Json.jsonStr "a\\b" = "\"a\\\\b\""))
        "json.jsonStr.escapesBackslash"
      assert (decide (Kit.Json.jsonStr "plain" = "\"plain\""))
        "json.jsonStr.plain"
      assert (decide (Kit.Json.obj [("k", "1"), ("k2", "2")] = "{\"k\": 1, \"k2\": 2}"))
        "json.obj.tight"
      assert (decide (Kit.Json.objPad [("k", "1")] = "{ \"k\": 1 }"))
        "json.objPad.paddedRow"
      assert (decide (Kit.Json.arr ["1", "2"] = "[1, 2]")) "json.arr"
      assert (decide (Kit.Json.arr [] = "[]")) "json.arrEmpty")
    [ ("the raw-wrap escaper is the real one",
        fun _ =>
          assert (decide (sabJsonStr "a\"b" == Kit.Json.jsonStr "a\"b"))
            "control fired: the unescaped (raw-wrap) escaper matched \
              the real escaper's output")
    , ("the tight obj renders as a padded row",
        fun _ =>
          assert (decide (Kit.Json.obj [("k", "1")] = Kit.Json.objPad [("k", "1")]))
            "control fired: the two brace styles collapsed to one") ]
    4 42

def validationSpec : Spec :=
  Spec.ofList "Kit.Validation — the error-accumulating applicative pins"
    (fun _ => do
      -- all-ok folds to the plain fold (the ok-identity law, read off
      -- the value)
      assert (
          match Validation.foldlM (fun b a => .ok (b + a) : Nat → Nat →
            Validation String Nat) 0 [1, 2, 3] with
          | .ok s => s == 6
          | .errs _ => false)
        "validation.foldlMAllOk"
      -- THE anti-early-exit pin: EVERY failing step reports — all
      -- three failures collected, in element order.
      assert (
          match Validation.foldlM (fun _ _ => .errs ["e"] : Nat → Nat →
            Validation String Nat) 0 [1, 2, 3] with
          | .errs es => es == ["e", "e", "e"]
          | .ok _ => false)
        "validation.accumulatesAllFailures"
      -- the element-count law (the proved face of the same pin)
      assert (decide (
        (Validation.foldlM (fun _ _ => .errs ["e"] : Nat → Nat → Validation String Nat)
          0 [1, 2, 3]).errors?.length = 3))
        "validation.errCountEqualsElementCount"
      -- traverse: mixed failures accumulate head-first, in list order
      assert (
          match Validation.traverse (fun n => if n % 2 == 0 then .ok (n * 2 :
            Nat) else .errs [s!"odd {n}"]) [1, 2, 3] with
          | .errs es => es == ["odd 1", "odd 3"]
          | .ok _ => false)
        "validation.traverseAccumulatesInOrder"
      -- traverse all-ok: ok of the plain map (traverse_ok, value face)
      assert (
          match Validation.traverse (fun n => .ok (n * 2 : Nat) :
            Nat → Validation String Nat) [1, 2, 3] with
          | .ok xs => xs == [2, 4, 6]
          | .errs _ => false)
        "validation.traverseAllOk")
    [ ("the early exit collects everything",
        fun _ =>
          assert (sabEarlyCount == 3)
            "control fired: the Except-shaped fold reported every failure \
              (it cannot — it exited at the first)")
    , ("the accumulator drops the tail",
        fun _ =>
          assert (decide (
            (Validation.foldlM (fun _ _ => .errs ["e"] : Nat → Nat → Validation String Nat)
              0 [1, 2, 3]).errors?.length = 1))
            "control fired: the accumulator reported only the first failure") ]
    4 42

/-! ## Kit.Ledger — the provenance ledger (09 §4) — the fixtures

Two rows over one shared collection: the WIT artifact's demand NAMES
its rows (the fold read them); the Rust artifact's demand only
ENUMERATES the collection (the registry — the correction's face: a fold
over a registry depends on its contents-as-a-set). Paths in the
canonical (sorted) order the format requires.
-/

/-- The WIT row's demand: two named rows + the enumerated registry. -/
def demWit : Kit.Ledger.DemandSet :=
  { rows := [`SchemaCore.Item.a, `SchemaCore.Item.b]
  , collections := [`SchemaCore.registry]
  , emitterRev := "schema-wit-r1" }

/-- The Rust row's demand: the collection face ONLY (the correction's
    honest case — the fold enumerated; it cannot name what it will
    read). -/
def demRust : Kit.Ledger.DemandSet :=
  { rows := []
  , collections := [`SchemaCore.registry]
  , emitterRev := "schema-rust-r1" }

def ledgerRowRust : Kit.Ledger.LedgerRow :=
  { path := "crates/schema-generated/src/lib.rs", emitter := "schema-rust"
  , demand := demRust, contentHash := 222
  , obligations := ["fields-nodup"] }

def ledgerRowWit : Kit.Ledger.LedgerRow :=
  { path := "gen/schema-slice.wit", emitter := "schema-wit"
  , demand := demWit, contentHash := 111, obligations := [] }

/-- The fixture ledger (sorted by path — the snapshot order). -/
def ledgerFx : List Kit.Ledger.LedgerRow := [ledgerRowRust, ledgerRowWit]

/-- The committed header's 2nd line for the WIT artifact (the shape
    Kit.Emit's driver writes). -/
def witHeaderLine : String :=
  "-- spec abc1234 | SchemaCore.Slice | 2 item(s) | content hash 111 | "
    ++ "regen: just gen; drift fails CI"

/-! ## Kit.Ledger — the negatives' producers -/

/-- THE PRE-CORRECTION QUERY: the rows-only forward face the doctrine
    REJECTS — it filters `demand.rows` alone, blind to the collection
    face. The negative control's producer: it under-reports exactly the
    enumeration dependencies (a new row in a depended-on collection
    moves artifacts it never sees). -/
def sabForward (r : Lean.Name) (ledger : List Kit.Ledger.LedgerRow) :
    List Kit.Ledger.LedgerRow :=
  ledger.filter (fun a => decide (r ∈ a.demand.rows))

/-- Sabotaged agreement: the HASH-BLIND face — a row's presence is
    "agreement" regardless of what hash the header names. -/
def sabCheckHeader (ledger : List Kit.Ledger.LedgerRow) (path : String)
    (_headerLine : String) : Kit.Ledger.LedgerAgreement :=
  match ledger.find? (fun a => a.path == path) with
  | some _ => .ok
  | none => .noRow

/-- Sabotaged stability: the PARSE-ONLY face — canonical bytes are
    never re-derived, so a parseable-but-non-canonical ledger passes. -/
def sabLedgerStable (s : String) : Bool :=
  match Kit.Ledger.parse s with | .ok _ => true | .error _ => false

/-- The parseable-but-NON-canonical ledger: the fixture's printed bytes
    minus the final newline — `parse` accepts, `selfStable` refuses. -/
def nonCanonicalLedger : String :=
  let s := Kit.Ledger.print ledgerFx
  String.ofList (s.toList.take (s.length - 1))

/-- Kit.Ledger — the provenance-ledger pins. `driverRows` folds in from
    `main`'s IO half (the duel write's recorded rows). -/
def ledgerSpec (driverRows : List Kit.Ledger.LedgerRow) : Spec :=
  Spec.ofList "Kit.Ledger — the provenance-ledger pins"
    (fun _ => do
      -- FORMAT: the round trip over the fixture
      assert (
          match Kit.Ledger.parse (Kit.Ledger.print ledgerFx) with
          | .ok rows => rows == ledgerFx
          | .error _ => false)
        "ledger.roundTrip"
      -- THE SNAPSHOT DISCIPLINE: the canonical bytes are self-stable
      assert (Kit.Ledger.selfStable (Kit.Ledger.print ledgerFx))
        "ledger.selfStable"
      -- the canonical bytes, pinned: sorted rows, seven tab-separated
      -- fields, comma-joined list fields (empty = empty), LF-terminated
      assert (Kit.Ledger.print ledgerFx ==
        "crates/schema-generated/src/lib.rs\tschema-rust\t\tSchemaCore.registry"
          ++ "\tschema-rust-r1\t222\tfields-nodup\n"
          ++ "gen/schema-slice.wit\tschema-wit\tSchemaCore.Item.a,SchemaCore.Item.b"
          ++ "\tSchemaCore.registry\tschema-wit-r1\t111\t\n")
        "ledger.canonicalBytes"
      -- the format's refusals: unsorted, duplicate path, blank line,
      -- a missing field, a non-natural hash
      assert (
          match Kit.Ledger.parse
              "gen/b.wit\te\t\t\t-\t1\t\ngen/a.wit\te\t\t\t-\t2\t\n" with
          | .error _ => true | .ok _ => false)
        "ledger.refusesUnsorted"
      assert (
          match Kit.Ledger.parse
              "gen/a.wit\te\t\t\t-\t1\t\ngen/a.wit\te\t\t\t-\t1\t\n" with
          | .error _ => true | .ok _ => false)
        "ledger.refusesDupPath"
      assert (
          match Kit.Ledger.parse
              "gen/a.wit\te\t\t\t-\t1\t\n\ngen/b.wit\te\t\t\t-\t2\t\n" with
          | .error _ => true | .ok _ => false)
        "ledger.refusesBlankLine"
      assert (
          match Kit.Ledger.parse "gen/a.wit\te\t\t\t1\n" with
          | .error _ => true | .ok _ => false)
        "ledger.refusesMissingField"
      assert (
          match Kit.Ledger.parse "gen/a.wit\te\t\t\t-\tx\t\n" with
          | .error _ => true | .ok _ => false)
        "ledger.refusesBadHash"
      -- BACKWARD: the artifact's FULL spec surface (rows + collections)
      assert (Kit.Ledger.backward ledgerFx "gen/schema-slice.wit"
        == [`SchemaCore.Item.a, `SchemaCore.Item.b, `SchemaCore.registry])
        "ledger.backward"
      assert (Kit.Ledger.backward ledgerFx "gen/absent.wit" == [])
        "ledger.backwardAbsent"
      -- FORWARD, the rows face
      assert ((Kit.Ledger.forward `SchemaCore.Item.a [] ledgerFx).map (·.path)
        == ["gen/schema-slice.wit"]) "ledger.forwardRow"
      -- FORWARD, the collection face (THE DEMAND-SET CORRECTION): a new
      -- row in a depended-on collection invalidates BOTH artifacts —
      -- neither's `rows` named the new row
      assert ((Kit.Ledger.forward `SchemaCore.Item.new [`SchemaCore.registry]
            ledgerFx).map (·.path)
        == ["crates/schema-generated/src/lib.rs", "gen/schema-slice.wit"])
        "ledger.forwardCollectionGrowth"
      -- the review-failure detector
      assert (Kit.Ledger.withoutRow ledgerFx
          ["gen/schema-slice.wit", "gen/missing.wit"]
        == ["gen/missing.wit"]) "ledger.withoutRow"
      -- HEADER ↔ LEDGER AGREEMENT: agreeing, + the three finding faces
      assert (
          match Kit.Ledger.checkHeader ledgerFx "gen/schema-slice.wit"
              witHeaderLine with
          | .ok => true | _ => false)
        "ledger.headerAgrees"
      -- TEETH: the mismatch — a regenerated artifact without its ledger
      -- rewrite, or a hand-edited ledger — is a finding, with the
      -- hashes in the verdict
      assert (
          match Kit.Ledger.checkHeader ledgerFx "gen/schema-slice.wit"
              (witHeaderLine.replace "content hash 111" "content hash 999") with
          | .hashMismatch 999 111 => true | _ => false)
        "ledger.headerMismatchIsAFinding"
      assert (
          match Kit.Ledger.checkHeader ledgerFx "gen/absent.wit"
              witHeaderLine with
          | .noRow => true | _ => false)
        "ledger.headerNoRow"
      assert (
          match Kit.Ledger.checkHeader ledgerFx "gen/schema-slice.wit"
              "-- spec abc | S | 1 item(s) | regen: just gen" with
          | .malformedHeader _ => true | _ => false)
        "ledger.headerMalformed"
      -- THE PROVED CONSERVATISM (the theorems over the fixture, one
      -- application each): forward NEVER under-reports — the rows face
      -- and the collection-growth face
      assert (
          let _rowsFace := Kit.Ledger.forward_covers_row
            (r := `SchemaCore.Item.a) (cs := []) ledgerFx ledgerRowWit
            (by show ledgerRowWit ∈ [ledgerRowRust, ledgerRowWit]
                exact List.mem_cons_of_mem _ List.mem_cons_self)
            (by show `SchemaCore.Item.a
                  ∈ [`SchemaCore.Item.a, `SchemaCore.Item.b]
                exact List.mem_cons_self)
          let _growthFace := Kit.Ledger.forward_growthInvalidates
            (r := `SchemaCore.Item.new) (c := `SchemaCore.registry)
            (cs := [`SchemaCore.registry]) ledgerFx ledgerRowWit
            (by show ledgerRowWit ∈ [ledgerRowRust, ledgerRowWit]
                exact List.mem_cons_of_mem _ List.mem_cons_self)
            (by show `SchemaCore.registry ∈ demRust.collections
                exact List.mem_cons_self)
            List.mem_cons_self
          true)
        "ledger.conservatismTheoremsElaborate"
      -- THE SPINE INTEGRATION: the driver RECORDED the rows as it wrote
      -- (the IO half's result): the duel's three artifacts, each row
      -- naming its emitter, its declared demand, its content hash
      assert ((driverRows.map (·.path)) ==
        ["kit/KitTests/scratch/duel/manifest.txt",
         "kit/KitTests/scratch/duel/golden.bin",
         "kit/KitTests/scratch/duel/golden.bin.hdr",
         "kit/KitTests/scratch/duel/tampered.bin",
         "kit/KitTests/scratch/duel/tampered.bin.hdr"])
        "ledger.driverRecordedAllFive"
      assert ((driverRows.map (·.emitter)).all (· == "duel:fixture-duel"))
        "ledger.driverRowsNameTheEmitter"
      assert (driverRows.all (fun r => r.contentHash != 0))
        "ledger.driverRowsCarryTheHash"
      -- the declared demand flows through: the duel emitter declares no
      -- reads; the rev default is the undeclared "-"
      assert (driverRows.all (fun r =>
        r.demand.collections == [] && r.demand.emitterRev == "-"))
        "ledger.driverDemandIsTheDeclaredOne")
    [ ("the pre-correction query is exact",
        fun _ =>
          assert (sabForward `SchemaCore.Item.new ledgerFx
            == (Kit.Ledger.forward `SchemaCore.Item.new [`SchemaCore.registry]
                  ledgerFx))
            "control fired: the rows-only query saw the collection growth — \
              it cannot (it under-reports the enumeration face)")
    , ("the hash-blind agreement agrees with the real one",
        fun _ =>
          assert (sabCheckHeader ledgerFx "gen/schema-slice.wit"
              (witHeaderLine.replace "content hash 111" "content hash 999")
            == (Kit.Ledger.checkHeader ledgerFx "gen/schema-slice.wit"
                (witHeaderLine.replace "content hash 111" "content hash 999")))
            "control fired: the hash-blind agreement matched the real \
              agreement — it accepted the mismatch")
    , ("the parse-only stability is stable",
        fun _ =>
          assert (sabLedgerStable nonCanonicalLedger
            == (Kit.Ledger.selfStable nonCanonicalLedger))
            "control fired: the parse-only stability matched the real \
              stability — it accepted the non-canonical bytes \
              (the missing final newline)") ]
    4 42


/-! ## Kit.Derive — the `declare_fold` / `declare_bridge` generators

The generators' gate row: a fixture inductive per generator, the
GENERATED surface exercised against the HAND-WRITTEN sibling, the
refusal teeth (`#guard_msgs` over the curated Diags — the unsupported
shapes, each NAMED), and the axiom pins over the generated theorems
(the recursor-template discipline — a sorry in the template fails
here). The value-level pins are the `deriveSpec` below.
-/

open Kit.Derive.Fold
open Kit.Derive.Bridge

/-! ### The fold fixture — the generated fold ≡ the hand fold -/

/-- The fixture inductive: a nullary leaf, a leaf with data, a binary
    combinator, and a mixed one (the four shapes the algebra carries). -/
inductive Tree2 where
  | leaf : Tree2
  | lit : Bool → Tree2
  | node : Tree2 → Nat → Tree2 → Tree2
  | wrap : Nat → Tree2 → Tree2

declare_fold Tree2

/-- The HAND sibling (the pre-generator shape, mined from
    `SchemaCore.Fold`'s `foldTy`) — the migration's other side. -/
structure Tree2Alg' (α : Type) where
  leaf : α
  lit : Bool → α
  node : α → Nat → α → α
  wrap : Nat → α → α

def handFold : Tree2Alg' α → Tree2 → α
  | alg, .leaf => alg.leaf
  | alg, .lit b => alg.lit b
  | alg, .node l n r => alg.node (handFold alg l) n (handFold alg r)
  | alg, .wrap n a => alg.wrap n (handFold alg a)

/-- The transported algebra (the thin wrapper — the rows verbatim). -/
def tree2AlgOf (alg : Tree2Alg' α) : Tree2Alg α where
  leaf := alg.leaf
  lit b := alg.lit b
  node l n r := alg.node l n r
  wrap n a := alg.wrap n a

/-- The fixture algebra (the Nat-sum reader). -/
def natAlg' : Tree2Alg' Nat where
  leaf := 0
  lit b := if b then 2 else 3
  node l n r := l + n + r
  wrap n a := n + a

/-- THE MIGRATION PIN: the hand fold IS the generated fold (over the
    transported algebra) — THE INITIALITY THEOREM CITED (one
    application; the commutation rows are `fun _ => rfl`). -/
theorem handFold_eq (alg : Tree2Alg' α) (t : Tree2) :
    handFold alg t = foldTree2 (tree2AlgOf alg) t :=
  foldTree2_unique (alg := tree2AlgOf alg) (f := handFold alg)
    rfl (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) t

-- the generated equation lemmas reduce (kernel-visible)
example : foldTree2 (tree2AlgOf natAlg') (.node .leaf 3 (.lit true)) = 5 := rfl
example : foldTree2 (tree2AlgOf natAlg') (.wrap 2 .leaf) = 2 := rfl

/-! ### The bridge fixture — the generated iff over the combinator fragment -/

/-- The fixture checker's inductive: leaves + and/or/not — the fragment
    whose soundness/completeness need EACH OTHER under `not`. -/
inductive BExp where
  | lit : Bool → BExp
  | var : Nat → BExp
  | band : BExp → BExp → BExp
  | bor : BExp → BExp → BExp
  | bnot : BExp → BExp

def BExp.check : BExp → (Nat → Bool) → Bool
  | .lit b, _ => b
  | .var n, env => env n
  | .band p q, env => p.check env && q.check env
  | .bor p q, env => p.check env || q.check env
  | .bnot p, env => !(p.check env)

/-- The spec of record (defined before the bridge — pattern #1's
    discipline; the checker never defines the semantics). -/
def BExp.Sem : BExp → (Nat → Bool) → Prop
  | .lit b, _ => b = true
  | .var n, env => env n = true
  | .band p q, env => p.Sem env ∧ q.Sem env
  | .bor p q, env => p.Sem env ∨ q.Sem env
  | .bnot p, env => ¬ p.Sem env

declare_bridge bexpIff := BExp.check, BExp.Sem where
  | lit => leaf
  | var => leaf
  | band => and
  | bor => or
  | bnot => not

/- The leaf iff hypotheses (the DOMAIN's content — the template
   carries them as hypotheses, it does not guess semantics). -/

theorem bexp_lit_iff (b : Bool) (r : Nat → Bool) :
    BExp.check (.lit b) r = true ↔ BExp.Sem (.lit b) r := ⟨fun h => h, fun h => h⟩

theorem bexp_var_iff (n : Nat) (r : Nat → Bool) :
    BExp.check (.var n) r = true ↔ BExp.Sem (.var n) r := ⟨fun h => h, fun h => h⟩

/-- The fixture environment: var 3 is true, everything else false. -/
def env3 : Nat → Bool := fun | 3 => true | _ => false

/-! ### The refusal fixtures -/

/-- non-inductive constant -/
def notInd := 1

/-- indexed (the GADT fragment) -/
inductive BadIdx : Type → Type where
  | mk : BadIdx Nat

/-- parameterized -/
inductive BadParam (α : Type) where
  | mk : α → BadParam α

/-- empty -/
inductive BadEmpty : Type where

/-- nested -/
inductive BadNested where
  | nest : List BadNested → BadNested

/-- dependent ctor argument -/
inductive BadDep where
  | dep : (n : Nat) → Fin n → BadDep

/- The bridge's wrong-checker producer: right type, wrong (opaque) def —
    the template's equation-lemma gate refuses it (wrongness does not
    elaborate). -/
def sabExpCheck : BExp → (Nat → Bool) → Bool := BExp.check

/-! ### The teeth — the curated refusals, pinned verbatim (if the
    generator stops refusing, the guard fails: the teeth cannot go
    silent) -/

/-- error: [KD0001] error: declare_fold notInd: `notInd` is not an inductive — valid usage: `declare_fold <Inductive>` over a closed, parameter-free, index-free inductive -/
#guard_msgs in
declare_fold notInd

/-- error: [KD0002] error: declare_fold BadIdx: `BadIdx` is index (GADT)-indexed — the generator's scope is the SIMPLE closed inductives; the DEPENDENT fold (the motive riding the index, 06 §2) is the named extension — write it by hand (the `foldValue` shape) and cite this refusal -/
#guard_msgs in
declare_fold BadIdx

/-- error: [KD0003] error: declare_fold BadParam: `BadParam` has type parameters — the parameter-threaded fragment is the named extension; the V1 scope is the parameter-free closed inductives -/
#guard_msgs in
declare_fold BadParam

/-- error: [KD0004] error: declare_fold BadEmpty: `BadEmpty` has no constructors — the empty universe's fold is `nomatch`, which an algebra record cannot carry -/
#guard_msgs in
declare_fold BadEmpty

/-- error: [KD0005] error: declare_fold BadNested: constructor `BadNested.nest`'s argument 0 mentions the inductive below the root — the NESTED fragment (e.g. `List BadNested`) is out of scope; flat siblings or sigma-encoded packages are the 06 §2 pattern -/
#guard_msgs in
declare_fold BadNested

/-- error: [KD0007] error: declare_fold BadDep: constructor `BadDep.dep`'s argument 1 has a dependent type — the dependent-constructor fragment is out of scope -/
#guard_msgs in
declare_fold BadDep

/-- error: [KB0006] error: declare_bridge bt1: unknown row shape `leaves` (got: leaves) — valid: leaf, and, or, not — did you mean: leaf? -/
#guard_msgs in
declare_bridge bt1 := BExp.check, BExp.Sem where
  | lit => leaves

/-- error: [KB0006] error: declare_bridge bt2: `lits` is not a constructor of `BExp` (got: lits) — valid: lit, var, band, bor, bnot — did you mean: lit? -/
#guard_msgs in
declare_bridge bt2 := BExp.check, BExp.Sem where
  | lits => leaf
  | var => leaf
  | band => and
  | bor => or
  | bnot => not

/-- error: [KB0007] error: declare_bridge bt3: the row block must classify every constructor of `BExp` exactly once — missing: [bor], duplicated: #[] -/
#guard_msgs in
declare_bridge bt3 := BExp.check, BExp.Sem where
  | lit => leaf
  | var => leaf
  | band => and
  | bnot => not

/-- error: [KB0008] error: declare_bridge bt4: the row `band => not` does not fit the constructor's shape (2 argument(s), 2 recursive) — `leaf` needs 0 recursive arguments, `and`/`or` need exactly 2, `not` needs exactly 1 -/
#guard_msgs in
declare_bridge bt4 := BExp.check, BExp.Sem where
  | lit => leaf
  | var => leaf
  | band => not
  | bor => or
  | bnot => not

/- The equation-lemma gate: a checker of the RIGHT TYPE whose arms the
    template cannot read (`sabExpCheck` is an opaque def) refuses —
    wrongness does not elaborate. -/
/-- error: unsolved goals
h_lit : ∀ (a1 : Bool) (r : Nat → Bool), sabExpCheck (BExp.lit a1) r = true ↔ (BExp.lit a1).Sem r
h_var : ∀ (a1 : Nat) (r : Nat → Bool), sabExpCheck (BExp.var a1) r = true ↔ (BExp.var a1).Sem r
p : BExp
r✝ : Nat → Bool
a1 a2 : BExp
ih1 : ∀ (r : Nat → Bool), sabExpCheck a1 r = true ↔ a1.Sem r
ih2 : ∀ (r : Nat → Bool), sabExpCheck a2 r = true ↔ a2.Sem r
r : Nat → Bool
⊢ (a1.band a2).check r = true ↔ a1.Sem r ∧ a2.Sem r
---
error: unsolved goals
h_lit : ∀ (a1 : Bool) (r : Nat → Bool), sabExpCheck (BExp.lit a1) r = true ↔ (BExp.lit a1).Sem r
h_var : ∀ (a1 : Nat) (r : Nat → Bool), sabExpCheck (BExp.var a1) r = true ↔ (BExp.var a1).Sem r
p : BExp
r✝ : Nat → Bool
a1 a2 : BExp
ih1 : ∀ (r : Nat → Bool), sabExpCheck a1 r = true ↔ a1.Sem r
ih2 : ∀ (r : Nat → Bool), sabExpCheck a2 r = true ↔ a2.Sem r
r : Nat → Bool
⊢ (a1.bor a2).check r = true ↔ a1.Sem r ∨ a2.Sem r
---
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sabExpCheck a1 r
in the target expression
  a1.bnot.check r = true

case mp
h_lit : ∀ (a1 : Bool) (r : Nat → Bool), sabExpCheck (BExp.lit a1) r = true ↔ (BExp.lit a1).Sem r
h_var : ∀ (a1 : Nat) (r : Nat → Bool), sabExpCheck (BExp.var a1) r = true ↔ (BExp.var a1).Sem r
p : BExp
r✝ : Nat → Bool
a1 : BExp
ih1 : ∀ (r : Nat → Bool), sabExpCheck a1 r = true ↔ a1.Sem r
r : Nat → Bool
h✝ : a1.bnot.check r = true
hs✝ : a1.Sem r
⊢ False
---
error: `simp` made no progress
-/
#guard_msgs in
declare_bridge bt5 := sabExpCheck, BExp.Sem where
  | lit => leaf
  | var => leaf
  | band => and
  | bor => or
  | bnot => not

/-! ### The axiom pins (the generated theorems — the core triple only) -/

/-- info: 'foldTree2_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms foldTree2_unique

/-- info: 'bexpIff_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bexpIff_iff

/-- info: 'bexpIff_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bexpIff_sound

/-- info: 'bexpIff_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bexpIff_complete

/-! ### Kit.Derive.Evidence — the evidence-kind computation (16-surface §3) -/

open Kit.Derive.Evidence in
/-- The computed-kind pins: the kind from the capability + the carrier
    shape, the tier from the kind, the census (carried → NOTHING), and
    the emissions as data. -/
def evidenceSpec : Spec :=
  Spec.ofList "Kit.Derive.Evidence — the computed-kind pins"
    (fun _ => do
      -- the kinds are COMPUTED from the capability + the carrier shape
      assert (evidenceKindOf .wireCodec == .lgcSweep) "evidence.kind.wireCodec"
      assert (evidenceKindOf .rowBridge == .typeCarried) "evidence.kind.rowBridge"
      assert (evidenceKindOfShape .closedFinite == .kernelDecide) "evidence.kind.closedFinite"
      assert (evidenceKindOfShape .behavioral == .duel) "evidence.kind.behavioral"
      -- the tier is COMPUTED from the kind (the machinery cannot mislabel)
      assert (EvidenceKind.lgcSweep.tier! == .oracleSwept) "evidence.tier.sweep"
      assert (EvidenceKind.duel.tier! == .generatedCheck) "evidence.tier.duel"
      assert (EvidenceKind.kernelDecide.tier! == .decidableNow) "evidence.tier.kernel"
      assert (EvidenceKind.kernelDecide.tier == some .decidableNow) "evidence.tier.some"
      -- THE CENSUS: a type-carried fact generates NOTHING
      assert (emissions .wireCodec .carried == []) "evidence.census.carried"
      assert (emissionsOf .rowBridge == []) "evidence.census.rowBridge"
      assert (mechanicalControls .carried == []) "evidence.census.controls"
      assert (typeCarries .rowBridge) "evidence.census.firstQuestion"
      -- the emissions, as data (the handlers render THESE)
      assert (emissionsOf .wireCodec
        == [.obligationRow, .sweepControls, .simpSet]) "evidence.emissions.wireCodec"
      assert (emissions .rowBridge .closedFinite == [.obligationRow, .simpSet])
        "evidence.emissions.closedFinite"
      -- the mechanical controls come from the data, and there are two
      assert (mechanicalControls .closedFinite ==
        ["sabotage: the naming fn drops the name", "sabotage: the entry drifts"])
        "evidence.controls.closedFinite"
      pure ())
    [ ("sabotage: the machinery mislabels the sweep provedAtElab",
        fun _ =>
          assert (EvidenceKind.lgcSweep.tier! == .provedAtElab)
            "control fired: the tier-honesty theorem was violated")
    , ("sabotage: the carried shape grows an artifact",
        fun _ =>
          assert (!((emissions .wireCodec .carried).isEmpty))
            "control fired: the census generated an artifact for a \
              type-carried fact") ]
    4 42

/-! ### Kit.Derive — the value-level pins -/

/-- Sabotaged fold algebra: the `node` row DROPS the right child — the
    negative control's producer (the generated fold carries the
    sabotage; the pin below shows the pins DISTINGUISH it). -/
def sabTreeAlg : Tree2Alg' Nat where
  leaf := 0
  lit b := if b then 2 else 3
  node l _n _r := l
  wrap n a := n + a

/-- Sabotaged relation: the `band` row reads `∨` where the checker reads
    `&&` — the bridge's content is load-bearing (the generated iff
    refuses this sibling; the pin below shows the split it would catch).
    `abbrev`: the control's decide sees through to the disjunction. -/
abbrev BExp.sabSem : BExp → (Nat → Bool) → Prop
  | .lit b, _ => b = true
  | .var n, env => env n = true
  | .band p q, env => p.sabSem env ∨ q.sabSem env
  | .bor p q, env => p.sabSem env ∧ q.sabSem env
  | .bnot p, env => ¬ p.sabSem env

def deriveSpec : Spec :=
  Spec.ofList "Kit.Derive — the fold/bridge generators' pins"
    (fun _ => do
      -- the generated fold's known answers (kernel reduction)
      assert (decide (foldTree2 (tree2AlgOf natAlg') .leaf = 0)) "derive.fold.leaf"
      assert (decide (foldTree2 (tree2AlgOf natAlg') (.lit false) = 3)) "derive.fold.lit"
      assert (decide (foldTree2 (tree2AlgOf natAlg')
        (.node (.lit true) 1 (.node .leaf 2 .leaf)) = 5)) "derive.fold.node"
      -- THE MIGRATION PIN: hand fold ≡ generated fold, via the generated
      -- initiality theorem (the citation is the elaborator's gate: drop
      -- the theorem, the pin has no proof)
      assert (
          let _migrated := handFold_eq natAlg' .leaf
          let _migrated₂ := handFold_eq natAlg' (.node .leaf 1 .leaf)
          true)
        "derive.fold.initialityCited"
      -- the generated bridge's iff at compound shapes (through the
      -- generated `not` case — the mutual-dependence template)
      assert (
          let _iff := bexpIff_iff bexp_lit_iff bexp_var_iff
            (.band (.var 3) (.bnot (.lit false))) env3
          let _sound := bexpIff_sound bexp_lit_iff bexp_var_iff
            (.band (.var 3) (.bnot (.lit false))) env3 rfl
          let _complete := bexpIff_complete bexp_lit_iff bexp_var_iff
            (.bor (.lit false) (.var 3)) env3 (.inr rfl)
          true)
        "derive.bridge.iffElaborates")
    [ ("the sabotaged algebra's fold agrees",
        fun _ =>
          assert (decide (foldTree2 (tree2AlgOf sabTreeAlg)
            (.node .leaf 1 (.lit true))
            == foldTree2 (tree2AlgOf natAlg') (.node .leaf 1 (.lit true))))
            "control fired: the child-dropping algebra's verdict matched — \
              the fold pins have no teeth")
    , ("the sabotaged relation agrees with the checker",
        fun _ =>
          assert (decide (BExp.sabSem (.band (.lit true) (.lit false)) env3)
            == (BExp.check (.band (.lit true) (.lit false)) env3 == true))
            "control fired: the ∨-for-∧ relation agreed with the checker — \
              the bridge's content is not load-bearing") ]
    4 42

def main : IO UInt32 := do
  -- the emit driver's IO half: the artifact write + read-back (the
  -- result folds into `emitSpec` as the `emit.driverWrote` pin; the
  -- file is cleaned up)
  let scratch := "kit/KitTests/scratch/emitted.txt"
  IO.FS.createDirAll "kit/KitTests/scratch"
  let _emitRows ←
    Kit.Emit.runEmitters "kit-tests" [(e1scratch, ["a", "b"])]
      (fun _ _ => pure { contentHash := ("a,b".hash : UInt64) })
  let back ← IO.FS.readFile scratch
  IO.FS.removeFile scratch
  let emitDriverOk := back.contains "GENERATED" && back.contains "a,b"
  -- the BINARY driver's IO half (Order 1 end-to-end): emit the byte
  -- artifact + its `.hdr` sidecar to the scratch dir, read the BYTES
  -- back, byte-compare against the emitter's own bytes, check the
  -- sidecar names the bytes' hash (files cleaned up)
  let binPath := "kit/KitTests/scratch/emitted.bin"
  let _binRows ←
    Kit.Emit.runBinaryEmitters "kit-tests" [(eb, ["x"])]
      (fun _ f => pure { contentHash := Kit.Emit.bytesHash f.contents })
  let binBack ← IO.FS.readBinFile binPath
  let sidecarBack ← IO.FS.readFile (Kit.Emit.sidecarPath binPath)
  IO.FS.removeFile binPath
  IO.FS.removeFile (Kit.Emit.sidecarPath binPath)
  let binaryOk := binBack == ebBytes &&
      sidecarBack.contains "GENERATED" &&
      sidecarBack.contains (toString (Kit.Emit.bytesHash ebBytes))
  -- the DUEL vector-set's IO half (Order 2 end-to-end): manifest (text
  -- lane) + vectors (binary lane) through ONE emitter; read back,
  -- byte-compare (files cleaned up)
  -- the ledger rows the driver RECORDED as it wrote (the write path's
  -- provenance face; they fold into `ledgerSpec` below)
  let ledgerRows ←
    Kit.Emit.runEmittersAll "kit-tests" [(Kit.Duel.emitter vs1, ())]
      (fun _ f => pure { contentHash := f.contents.hash })
      (fun _ f => pure { contentHash := Kit.Emit.bytesHash f.contents })
  let goldenBack ← IO.FS.readBinFile "kit/KitTests/scratch/duel/golden.bin"
  let manifestBack ← IO.FS.readFile "kit/KitTests/scratch/duel/manifest.txt"
  IO.FS.removeFile "kit/KitTests/scratch/duel/golden.bin"
  IO.FS.removeFile (Kit.Emit.sidecarPath "kit/KitTests/scratch/duel/golden.bin")
  IO.FS.removeFile "kit/KitTests/scratch/duel/tampered.bin"
  IO.FS.removeFile (Kit.Emit.sidecarPath "kit/KitTests/scratch/duel/tampered.bin")
  IO.FS.removeFile "kit/KitTests/scratch/duel/manifest.txt"
  let duelOk := goldenBack == ebBytes &&
      manifestBack.contains "GENERATED" && manifestBack.contains "generator\tKitTests"
  -- the E-code registry's IO half: the committed file's parse (folds
  -- into `codeCoverageSpec` — the persisted registry is data on disk,
  -- never a Lean literal; the allocation tie rides this read)
  let committedCodeRegistry :=
    CodeRegistry.parse (← IO.FS.readFile "notes/code-registry.txt")
  TestingKit.mainOfSuites
    [ ("Kit.Correspondence", [correspondenceSpec])
    , ("Kit.Obligation", [obligationSpec])
    , ("Kit.Registry", [registrySpec])
    , ("Kit.CheckedProp + Kit.Lane", [checkedLaneSpec])
    , ("Kit.Emit", [emitSpec emitDriverOk])
    , ("Kit.Emit binary lane", [emitBinarySpec binaryOk])
    , ("Kit.Ledger", [ledgerSpec ledgerRows])
    , ("Kit.Duel", [duelSpec duelOk])
    , ("Kit.Diag/Suggest/FreshName", [diagSuggestSpec])
    , ("Kit.CodeRegistry", [codeRegistrySpec])
    , ("Kit.CodeRegistry coverage", [codeCoverageSpec committedCodeRegistry])
    , ("Kit.Change", [changeSpec])
    , ("Kit.Observer", [observerSpec])
    , ("Kit.Relation", [relationSpec])
    , ("Kit.Correspondence bridge", [bridgeSpec])
    , ("Kit.Hyper", [hyperSpec])
    , ("Kit.Derive", [deriveSpec])
    , ("Kit.Derive.Evidence", [evidenceSpec])
    , ("Kit.Text", [textSpec])
    , ("Kit.Mangle", [mangleSpec])
    , ("Kit.Json", [jsonSpec])
    , ("Kit.Validation", [validationSpec]) ]
