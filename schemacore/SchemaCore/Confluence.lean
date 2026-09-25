/-
# SchemaCore.Confluence — the coordination classifier (02 §8)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/02-data-plane.md §8 (invariant confluence:
can independently-valid updates merge without violating the invariant?
the lesson — COMMUTING OPERATIONS ≠ MERGED STATE PRESERVES THE
INVARIANT: two commuting withdrawals can jointly overdraw); notes/v3/
15-patterns.md #1 (relation + checker + bridge), #4 (the obligation as
data, Prop-indexed), #5 (the mandatory negative controls); notes/v3/
04-verification.md §6 (verdicts are ctors, never strings).

THE CLASSIFIER'S SHAPE — the four rows of 02 §8, per operation:

- `safeUnderMerge` — fires ONLY on the proved sufficient condition:
  the pair COMMUTES over the table (the update lane's `UpdateCompat`
  premise pack — derived reads vs writes, disjoint writes, the
  insert refusals, the insert/delete separation) AND the invariant is
  MERGE-CLOSED under each operation (`MergeSafe`: the operation's
  table effect preserves the invariant for EVERY table). BOTH
  conjuncts — the doctrine's lesson is exactly that the first alone
  decides nothing. The decidable sufficient condition
  (`Confluence.sufficient`) checks the commuting pack over the
  provided table + the honest MergeSafe premises (write-invisibility:
  the update writes no column the invariant reads — Law 2's
  neutrality — and insert-legality: the inserted literal satisfies
  the invariant); `MergeSafe.ofSufficient` is the PROVED bridge from
  the decidable condition to the general claim.
- `safeUnderPartition` — the declared-ownership face: the pair's
  write surfaces are disjoint (the partition is DECLARED, not
  derived) and the merged table checks. A PROVIDED-TABLE verdict:
  the general ∀-tables claim is NOT discharged by it — that is why
  the general safe row demands the proved condition instead.
- `requiresCoordination` — the counterexample shape EXISTS as data:
  each update applied ALONE preserves the invariant on the provided
  table, the merged application violates, and the violating rows come
  back (02 §1's discipline). The remedy is NAMED in the verdict.
- `unknown` — the honest open obligation: no proved condition, no
  witness on the provided table. The classifier says nothing rather
  than pretending.

THE COUNTEREXAMPLE DISCIPLINE — the overdraw witness (the doctrine's
own example) at the balance carrier (the check lane's `Pred` fragment
is u64-only; the witness's honest home is the Int balance under the
ADDITIVE merge — `Kit.Change.intAdd` is the Additive instance): the
two withdrawals COMMUTE (the additive merge is order-free) yet
jointly overdraw. `OverdrawWitness` carries the shape AS DATA
(base + two negative deltas), `isOverdraw` decides the shape,
`isOverdraw_sound` is the bridge, and `classifyWithdrawals` — the
carrier's classifier — REFUSES to call the doctrine's withdrawal
safe: `theOverdraw` lands on `requiresCoordination` (the escrow /
serialize remedy). `theOverdraw_lesson` pins the conjunction the
whole section exists for: commuting = true AND violating = true.

THE OBLIGATION INTEGRATION (15-patterns #4): the merged-application
preservation over the PROVIDED table is a closed decide — a
Prop-indexed `decidableNow` obligation, discharged by the kit's
backend with soundness + completeness. The GENERAL claim
(`MergeSafe`, ∀-tables) is the OPEN row: `openObligation` registers
it at tier `provedAtElab` — and the decide backend is UNTYPEABLE for
it (no `Decidable` instance over the ∀-rows quantifier exists), so a
decide-discharge cannot even be stated; the loud unknown is
structural, per the mis-wire rule (the claim is the index).

Honest exclusions (each names its reason — the leftover rule): the
keyed-delta face (`KeyPut`/`keyDeltaApply` already carries the
old-image serialize discipline — the classifier's escrow remedy
 NAMES it; a keyed classification is the first consumer's row);
additive merges of TABLE deltas (zset/'s carrier — the row-fragment
tables are lists, the additive rung is claimed nowhere here);
aggregates (the invariant is row-local `Pred` — a sum-over-table
invariant needs the datalog lane's fragment). The CALM connection
stays honest per the doctrine: monotone appends classify
safe-under-merge; the moment an update's guard reads what the merge
writes, the classification costs coordination — never a blanket
distributed-correctness claim.

The five questions (notes/v3/01-core.md): root = the confluence
question (02 §8) over the slice's discipline (the update lane's
updates × the check lane's invariants); carrier = `MergeVerdict` (the
closed four-row verdict, ctors never strings) + the Prop-indexed
`Obligation`; spine reading = none — the classifier READS the two
lanes' public surfaces, it accumulates nothing; ladder rung = the
obligations at `decidableNow` (the provided-table claims) with the
general claim at the loud `provedAtElab`-only row; gate row =
SchemaTests' confluenceSpec (the safe/overdraw/unknown pins + the
mandatory negative controls) + the axiom report.

Core-only (imports SchemaCore.Update + SchemaCore.Check + Kit.Change
— the cone rule).
-/

import Kit.Change
import SchemaCore.Update
import SchemaCore.Check

open Kit

namespace SchemaCore

/-! ## The verdict — the closed four-row vocabulary (02 §8) -/

/-- The coordination classifier's verdict, per operation pair.
    Constructors, never strings (04 §6); the coordination row NAMES
    the remedy (02 §8: serialize / partition / escrow /
    strengthen-precondition / change-conflict-policy). -/
inductive MergeVerdict where
  /-- The proved sufficient condition held: the pair commutes AND the
      invariant is merge-closed under each operation (for EVERY
      table). -/
  | safeUnderMerge
  /-- The declared-ownership partition: disjoint write surfaces and
      the provided merge checks. A PROVIDED-TABLE verdict. -/
  | safeUnderPartition
  /-- The counterexample shape exists (the witness is the violating
      rows, as data); the remedy is named. -/
  | requiresCoordination (remedy : String)
  /-- The honest open obligation: no proved condition, no witness on
      the provided table. The proof obligation remains open. -/
  | unknown
deriving BEq, Repr, DecidableEq

/-! ## The claims — the honest premise shape -/

/-- THE PRESERVATION PREMISE: the update's table effect preserves the
    invariant for EVERY table — the merge-closure conjunct of the
    safe-under-merge classification. This is the claim the sufficient
    condition earns, and the claim the overdraw witness REFUTES for a
    withdrawal. -/
def MergeSafe (ci : CheckItem) (u : UpdateItem ci.fields) : Prop :=
  ∀ rows : List (RowVals ci.fields), ci.holds rows → ci.holds (u.apply rows)

/-- THE CONFLUENCE PREMISE (the honest shape, 02 §8): the pair
    commutes over the table (the update lane's `UpdateCompat` pack)
    AND each operation is merge-closed for the invariant. BOTH —
    commuting alone is exactly the doctrine's non sequitur. -/
structure Confluent (ci : CheckItem) (u₁ u₂ : UpdateItem ci.fields)
    (rows : List (RowVals ci.fields)) : Prop where
  /-- The commuting discipline (the update lane's premise pack). -/
  comm : UpdateCompat u₁ u₂ rows
  /-- The invariant is merge-closed under u₁. -/
  safe₁ : MergeSafe ci u₁
  /-- The invariant is merge-closed under u₂. -/
  safe₂ : MergeSafe ci u₂

/-- The merged application preserves the invariant. -/
theorem Confluent.merge_preserves (c : Confluent ci u₁ u₂ rows)
    (h : ci.holds rows) : ci.holds (u₂.apply (u₁.apply rows)) :=
  c.safe₂ _ (c.safe₁ rows h)

/-- The merge is order-free (the commuting conjunct's payoff — the
    update lane's Law 5a; the insert blocks may swap, row order is
    unobservable). -/
theorem Confluent.merge_orderFree (c : Confluent ci u₁ u₂ rows) :
    (u₁.apply (u₂.apply rows)).Perm (u₂.apply (u₁.apply rows)) :=
  apply2_comm_perm c.comm

/-! ## The decidable sufficient condition + the bridge -/

/-- The WRITE-INVISIBILITY face: the update writes no column the
    invariant reads (Law 2's neutrality premise, decidable over the
    name lists). -/
def UpdateItem.writesAvoid {fs : List Field} (u : UpdateItem fs)
    (p : Pred fs) : Bool :=
  u.setNames.all (fun n => !(p.reads.contains n))

/-- The INSERT-LEGALITY face: no insert, or the inserted literal row
    satisfies the invariant (decidable on the literal — the guard's
    firing is irrelevant when the row itself is legal). Conservative:
    an insert row that fails the invariant fails the face even if the
    guard never fires — the honest feeds-`unknown` side. -/
def UpdateItem.insertLegal {fs : List Field} (u : UpdateItem fs)
    (p : Pred fs) : Bool :=
  match u.insert? with
  | none => true
  | some r => p.check r

/-- THE BRIDGE (pattern #1): the decidable faces EARN the general
    claim — write-invisible writes are neutral to the invariant
    (Law 2), a legal insert inserts a satisfying row, and deletion
    only shrinks a ∀-row-local claim. -/
theorem MergeSafe.ofSufficient {ci : CheckItem} {u : UpdateItem ci.fields}
    (hw : u.writesAvoid ci.pred = true) (hi : u.insertLegal ci.pred = true) :
    MergeSafe ci u := by
  have hne : ∀ n ∈ ci.pred.reads, ∀ c ∈ u.sets, n ≠ c.field.name := by
    intro n hn c hc hnc
    have hmem : c.field.name ∈ u.setNames := u.mem_setNames hc
    have hall := (List.all_eq_true.mp hw) c.field.name hmem
    rw [← hnc] at hall
    exact absurd hn (by simpa using hall)
  -- the Sat-level neutrality (Law 2 at the fold + the bridge, both ways)
  have hkey := ci.pred.check_applySets u.sets hne
  have satSwap : ∀ r : RowVals ci.fields,
      ci.pred.Sat (applySets u.sets r) ↔ ci.pred.Sat r := by
    intro r
    constructor
    · intro hs
      have hc : ci.pred.check (applySets u.sets r) = true :=
        (ci.pred.check_iff (applySets u.sets r)).mpr hs
      rw [hkey r] at hc
      exact (ci.pred.check_iff r).mp hc
    · intro hs
      have hc : ci.pred.check r = true := (ci.pred.check_iff r).mpr hs
      rw [← hkey r] at hc
      exact (ci.pred.check_iff (applySets u.sets r)).mp hc
  unfold MergeSafe
  intro rows hholds r hr
  unfold UpdateItem.apply at hr
  rcases List.mem_append.mp hr with hr | hr
  · -- the keep channel
    obtain ⟨r₀, hr₀, hkeep⟩ := List.mem_filterMap.mp hr
    unfold UpdateItem.keepRow at hkeep
    by_cases hv : validates u.guard r₀ = true
    · rw [if_pos hv] at hkeep
      by_cases hd : u.delete
      · rw [if_pos hd] at hkeep; exact absurd hkeep (by simp)
      · rw [if_neg hd] at hkeep
        have hrepl : r = applySets u.sets r₀ := (Option.some.inj hkeep).symm
        rw [hrepl]
        exact (satSwap r₀).mpr (hholds r₀ hr₀)
    · rw [if_neg hv] at hkeep
      rw [← Option.some.inj hkeep]
      exact hholds r₀ hr₀
  · -- the insert channel
    obtain ⟨r₀, hr₀, hnew⟩ := List.mem_filterMap.mp hr
    unfold UpdateItem.newRow at hnew
    by_cases hv : validates u.guard r₀ = true
    · rw [if_pos hv] at hnew
      unfold UpdateItem.insertLegal at hi
      rw [hnew] at hi
      exact (ci.pred.check_iff r).mp hi
    · rw [if_neg hv] at hnew
      exact absurd hnew (by simp)

/-! ## The commuting pack, decided over the provided table -/

/-- The `UpdateCompat` premise pack as a Bool over a PROVIDED table:
    every field is decidable here (the name lists + the guard verdicts
    over the concrete rows) — the checker's shadow of the pack. -/
def UpdateCompat.asBool {fs : List Field} (u₁ u₂ : UpdateItem fs)
    (rows : List (RowVals fs)) : Bool :=
  (u₁.reads.all fun n => !u₂.setNames.contains n)
    && (u₂.reads.all fun n => !u₁.setNames.contains n)
    && (u₁.setNames.all fun n => !u₂.setNames.contains n)
    && (rows.all fun r =>
          (u₁.newRow r).elim true (fun new => !(validates u₂.guard new)))
    && (rows.all fun r =>
          (u₂.newRow r).elim true (fun new => !(validates u₁.guard new)))
    && ((!u₁.insert?.isSome || !u₂.delete) || (rows.all fun r =>
          !(validates u₁.guard r) || !(validates u₂.guard r)))
    && ((!u₂.insert?.isSome || !u₁.delete) || (rows.all fun r =>
          !(validates u₂.guard r) || !(validates u₁.guard r)))

/-- The checker's shadow casts back: a `true` verdict IS the premise
    pack (pattern #1, one bridge, both directions' premise side). -/
theorem UpdateCompat.ofAsBool {fs : List Field} {u₁ u₂ : UpdateItem fs}
    {rows : List (RowVals fs)}
    (h : UpdateCompat.asBool u₁ u₂ rows = true) : UpdateCompat u₁ u₂ rows := by
  unfold asBool at h
  simp only [Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  obtain ⟨hni₁₂, hni₂₁, hdisj, href₁₂, href₂₁, hsep₁₂, hsep₂₁⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn hm
    have hval := hni₁₂ n hn
    have hct : u₂.setNames.contains n = true := List.contains_iff_mem.mpr hm
    rw [hct] at hval
    simp at hval
  · intro n hn hm
    have hval := hni₂₁ n hn
    have hct : u₁.setNames.contains n = true := List.contains_iff_mem.mpr hm
    rw [hct] at hval
    simp at hval
  · intro n hn hm
    have hval := hdisj n hn
    have hct : u₂.setNames.contains n = true := List.contains_iff_mem.mpr hm
    rw [hct] at hval
    simp at hval
  · exact href₁₂
  · exact href₂₁
  · intro his hdel r hr hv
    rcases Bool.or_eq_true_iff.mp hsep₁₂ with h0 | h0
    · rcases Bool.or_eq_true_iff.mp h0 with h0' | h0'
      · have hns : u₁.insert?.isSome = false := by simpa using h0'
        rw [hns] at his; simp at his
      · have hnd : u₂.delete = false := by simpa using h0'
        rw [hnd] at hdel; simp at hdel
    · have hval := (List.all_eq_true.mp h0) r hr
      rw [hv] at hval
      simp at hval
      cases hb : validates u₂.guard r with
      | false => rfl
      | true => rw [hb] at hval; simp at hval
  · intro his hdel r hr hv
    rcases Bool.or_eq_true_iff.mp hsep₂₁ with h0 | h0
    · rcases Bool.or_eq_true_iff.mp h0 with h0' | h0'
      · have hns : u₂.insert?.isSome = false := by simpa using h0'
        rw [hns] at his; simp at his
      · have hnd : u₁.delete = false := by simpa using h0'
        rw [hnd] at hdel; simp at hdel
    · have hval := (List.all_eq_true.mp h0) r hr
      rw [hv] at hval
      simp at hval
      cases hb : validates u₁.guard r with
      | false => rfl
      | true => rw [hb] at hval; simp at hval

/-- THE SUFFICIENT CONDITION (decidable): the pair commutes over the
    provided table AND each operation carries the proved MergeSafe
    faces — write-invisibility + insert-legality, both sides. -/
def Confluence.sufficient (ci : CheckItem) (u₁ u₂ : UpdateItem ci.fields)
    (rows : List (RowVals ci.fields)) : Bool :=
  UpdateCompat.asBool u₁ u₂ rows
    && u₁.writesAvoid ci.pred && u₂.writesAvoid ci.pred
    && u₁.insertLegal ci.pred && u₂.insertLegal ci.pred

/-- The sufficient condition's bridge: a `true` check IS the confluence
    premise — the classifier's safe row never rests on commutation
    alone. -/
theorem Confluence.sufficient_confluent (ci : CheckItem)
    (u₁ u₂ : UpdateItem ci.fields) (rows : List (RowVals ci.fields))
    (h : Confluence.sufficient ci u₁ u₂ rows = true) :
    Confluent ci u₁ u₂ rows := by
  have hc := h
  unfold sufficient at hc
  simp only [Bool.and_eq_true, and_assoc] at hc
  obtain ⟨hcomm, hw₁, hw₂, hi₁, hi₂⟩ := hc
  exact ⟨UpdateCompat.ofAsBool hcomm,
    MergeSafe.ofSufficient hw₁ hi₁, MergeSafe.ofSufficient hw₂ hi₂⟩

/-! ## The counterexample query (the witness comes back as data) -/

/-- THE COUNTEREXAMPLE QUERY over the provided table (02 §1's
    discipline): each update applied ALONE preserves the invariant,
    the MERGED application violates — the violating rows come back, in
    table order. Empty = no witness on this table (never a clean
    bill). -/
def Confluence.mergeCounterexample (ci : CheckItem)
    (u₁ u₂ : UpdateItem ci.fields) (rows : List (RowVals ci.fields)) :
    List (RowVals ci.fields) :=
  if ci.checkRows (u₁.apply rows)
      && ci.checkRows (u₂.apply rows)
      && !ci.checkRows (u₂.apply (u₁.apply rows)) then
    ci.violating (u₂.apply (u₁.apply rows))
  else []

/-- The declared-partition face: the pair's write surfaces are
    disjoint (the ownership partition is DECLARED, not derived). -/
def Confluence.partitioned (u₁ u₂ : UpdateItem fs) : Bool :=
  (u₁.setNames.all fun n => !u₂.setNames.contains n)
    && (u₂.setNames.all fun n => !u₁.setNames.contains n)

/-- THE CLASSIFIER (02 §8): the per-pair verdict over the slice's
    discipline. `safeUnderMerge` ONLY on the proved sufficient
    condition; the counterexample shape forces `requiresCoordination`
    with the remedy named; the disjoint-write partition face is the
    provided-table safe row; otherwise the honest `unknown`. -/
def Confluence.classify (ci : CheckItem) (u₁ u₂ : UpdateItem ci.fields)
    (rows : List (RowVals ci.fields)) : MergeVerdict :=
  if sufficient ci u₁ u₂ rows then
    .safeUnderMerge
  else if !(mergeCounterexample ci u₁ u₂ rows).isEmpty then
    .requiresCoordination
      "serialize the pair, escrow the shared column, or strengthen the \
        precondition — the guards read what the other writes"
  else if partitioned u₁ u₂
      && ci.checkRows (u₂.apply (u₁.apply rows)) then
    .safeUnderPartition
  else
    .unknown

/-! ## The counterexample discipline — the overdraw witness (the
      doctrine's own example, at the balance carrier) -/

/-- The non-negative-balance invariant, decided. (The check lane's
    `Pred` fragment is u64-only; the overdraw's honest home is the Int
    balance under the additive merge — `Kit.Change.intAdd` is the
    Additive instance. The row-fragment counterexample lives in the
    classifier above.) -/
def nonNegBal (bal : Int) : Bool := decide (0 ≤ bal)

/-- THE OVERDRAW WITNESS, as data: the shared base balance and two
    withdrawals (negative deltas) under the ADDITIVE merge — the
    merge in which deltas COMMUTE. -/
structure OverdrawWitness where
  /-- The shared base state. -/
  base : Int
  /-- The first withdrawal (a negative delta). -/
  w₁ : Int
  /-- The second withdrawal (a negative delta). -/
  w₂ : Int

namespace OverdrawWitness

/-- Individually valid #1: the first withdrawal alone preserves the
    non-negative balance. -/
def valid1 (w : OverdrawWitness) : Bool := nonNegBal (w.base + w.w₁)

/-- Individually valid #2. -/
def valid2 (w : OverdrawWitness) : Bool := nonNegBal (w.base + w.w₂)

/-- MERGE-CLOSURE: both withdrawals applied (the additive fold) still
    preserve the non-negative balance. -/
def mergedOK (w : OverdrawWitness) : Bool := nonNegBal (w.base + w.w₁ + w.w₂)

/-- The counterexample shape, as data: individually valid on both
    sides, jointly violating. -/
def isOverdraw (w : OverdrawWitness) : Bool :=
  w.valid1 && w.valid2 && !w.mergedOK

/-- The COMMUTING face: the additive merge is order-free (the deltas
    commute — `intAddCompose`'s law). This is the face that does NOT
    decide safety. -/
def commutes (w : OverdrawWitness) : Bool :=
  intAddCompose w.w₁ w.w₂ == intAddCompose w.w₂ w.w₁

/-- THE WITNESS'S BRIDGE (pattern #1): an `isOverdraw = true` verdict
    IS the doctrine's counterexample — both withdrawals individually
    valid, the merged state below zero. -/
theorem isOverdraw_sound (w : OverdrawWitness) (h : w.isOverdraw = true) :
    0 ≤ w.base + w.w₁ ∧ 0 ≤ w.base + w.w₂
      ∧ ¬(0 ≤ w.base + w.w₁ + w.w₂) := by
  simp only [isOverdraw, valid1, valid2, mergedOK, nonNegBal,
    Bool.and_eq_true] at h
  have h3 : decide (0 ≤ w.base + w.w₁ + w.w₂) = false := by
    simpa using h.2
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2,
    fun hc => absurd (decide_eq_true hc) (by rw [h3]; simp)⟩

/-- THE DOCTRINE'S OWN WITNESS: balance 50; withdraw 40; withdraw 30.
    Each withdrawal alone is fine; the additive merge overdraws. -/
def theOverdraw : OverdrawWitness := ⟨50, -40, -30⟩

/-- The witness's faces, kernel-pinned (the coverage discipline: every
    constructor's live witness). -/
example : theOverdraw.valid1 = true := by decide
example : theOverdraw.valid2 = true := by decide
example : theOverdraw.mergedOK = false := by decide
example : theOverdraw.commutes = true := by decide
example : theOverdraw.isOverdraw = true := by decide

/-- THE DOCTRINE'S LESSON, kernel-pinned: the two withdrawals COMMUTE
    (the additive merge's compose law) AND the merge violates. The
    conjunction is the whole point of 02 §8 — commutation does not
    decide merge-safety; the classifier's safe row demands BOTH the
    commuting face AND merge-closure. -/
theorem theOverdraw_lesson :
    theOverdraw.isOverdraw = true
      ∧ intAddCompose theOverdraw.w₁ theOverdraw.w₂
        = intAddCompose theOverdraw.w₂ theOverdraw.w₁ := by
  refine ⟨by decide, ?_⟩
  unfold intAddCompose
  decide

end OverdrawWitness

/-- The carrier's withdrawal classifier: the four rows, at the balance
    carrier. The commuting face is FREE (the additive merge always
    commutes), so the verdict rides merge-closure alone — the
    doctrine's asymmetry, executable. Individually invalid on both
    sides is NOT a confluence question (the transaction boundary
    refuses it); the classifier answers `unknown`, never a fabricated
    verdict. -/
def classifyWithdrawals (w : OverdrawWitness) : MergeVerdict :=
  if w.mergedOK then .safeUnderMerge
  else if w.isOverdraw then
    .requiresCoordination
      "escrow the balance (reserve the amount), or serialize the withdrawals"
  else .unknown

open OverdrawWitness in
/-- THE TEETH: the classifier REFUSES to call the doctrine's withdrawal
    safe — the overdraw witness forces the coordination verdict, with
    the remedy named (escrow: reserve the amount; or serialize). -/
example : classifyWithdrawals theOverdraw
    = MergeVerdict.requiresCoordination
        "escrow the balance (reserve the amount), or serialize the withdrawals" :=
  rfl

/-! ## The obligation integration (15-patterns #4) -/

/-- The confluence obligation's payload row. -/
inductive ConfluenceClaim where
  /-- The merged application preserves the named invariant. -/
  | mergePreserves (fs : List Field) (schemaRef : String) (name : String)

/-- THE MERGE OBLIGATION (15-patterns #4 at the indexed strength): over
    the PROVIDED table, the merged application's preservation is a
    closed decide — tier `decidableNow`; the claim index is the actual
    Prop, so a discharge proves the merged table's invariant, never a
    claim-shaped name. -/
def Confluence.mergeObligation (ci : CheckItem) (u₁ u₂ : UpdateItem ci.fields)
    (rows : List (RowVals ci.fields)) :
    Obligation ConfluenceClaim (ci.holds (u₂.apply (u₁.apply rows))) :=
  { label := s!"confluence/{ci.schemaRef}/{u₁.name}+{u₂.name}-merge-preserves"
    tier := .decidableNow
    payload := .mergePreserves ci.fields ci.schemaRef u₂.name
    provenance := `SchemaCore }

/-- THE DISCHARGE — the kit's decidableNow backend; `none` is the loud
    gap (a false claim or a mis-set tier; the backend refuses, it does
    not fabricate evidence). -/
def Confluence.dischargeMerge (ci : CheckItem) (u₁ u₂ : UpdateItem ci.fields)
    (rows : List (RowVals ci.fields)) : Option Evidence :=
  (mergeObligation ci u₁ u₂ rows).decideDischarge

/-- The discharge's SOUNDNESS — the kit backend's theorem, cited, at
    the indexed strength: the discharge proves THIS merge's claim. -/
theorem Confluence.dischargeMerge_sound (ci : CheckItem)
    (u₁ u₂ : UpdateItem ci.fields) (rows : List (RowVals ci.fields))
    (h : dischargeMerge ci u₁ u₂ rows = some (.decided true)) :
    ci.holds (u₂.apply (u₁.apply rows)) :=
  Obligation.decideDischarge_sound (mergeObligation ci u₁ u₂ rows) rfl h

/-- The discharge's COMPLETENESS — a true claim fires the backend. -/
theorem Confluence.dischargeMerge_complete (ci : CheckItem)
    (u₁ u₂ : UpdateItem ci.fields) (rows : List (RowVals ci.fields))
    (hc : ci.holds (u₂.apply (u₁.apply rows))) :
    dischargeMerge ci u₁ u₂ rows = some (.decided true) :=
  Obligation.decideDischarge_of_claim _ rfl hc

/-- THE OPEN ROW (the honest unknown's obligation face): the GENERAL
    preservation claim — for EVERY table, not the provided one. There
    is no `Decidable` instance over the ∀-rows quantifier, so the
    decide backend is UNTYPEABLE for this row; the tier is
    `provedAtElab` — its only honest discharge is a cited kernel
    theorem, and none is cited for an arbitrary pair. A fake discharge
    cannot be built: the claim is the index, and a `Discharged` row
    demands evidence of the matching tier. This is the loud unknown,
    as an obligation. -/
def Confluence.openObligation (ci : CheckItem) (u : UpdateItem ci.fields) :
    Obligation ConfluenceClaim (MergeSafe ci u) :=
  { label := s!"confluence/{ci.schemaRef}/{u.name}-merge-safe"
    tier := .provedAtElab
    payload := .mergePreserves ci.fields ci.schemaRef u.name
    provenance := `SchemaCore }

end SchemaCore
