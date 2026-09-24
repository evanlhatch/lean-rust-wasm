/-
# Inspector.WhatIf — the what-if inspector (08 #20: rewind/replay-with-modification)

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/08-capabilities.md #20 (the what-if
inspector — rewind/replay-with-modification over the journal: a
COMPOSITION of landed machinery, no new substrate) + notes/v3/01-core.md
§2 (the Change ladder: replay IS the I operator) +
notes/v3/03-bidirectional.md §7 (THE TRICHOTOMY: an EVENT is a
recorded occurrence with identity + causality — the what-if is a
HYPOTHETICAL, never a rewrite).

The composition (everything rides `SchemaCore.Event`):

- the REWIND — replay to a PREFIX: `rewindEvents` folds
  `log.take t`; `rewindEvents_eq_runStates` ties it to the landed
  `runStates` (the states ARE the partial integrals);
- the WHAT-IF — `whatIfJournal` replaces ONE event's recorded intent:
  the SAME occurrence (its `seq` is preserved —
  `whatIfJournal_seqs`), a NEW event stream (the original journal is
  untouched — the trichotomy's event-identity discipline: a what-if is
  a hypothetical, never a rewrite of history);
- the DIVERGENCE REPORT — `Report` carries the divergence AS DATA: the
  shared prefix state (BEFORE — identical on both sides by the prefix
  law `whatIfJournal_take_prefix` + `whatIfReport_prefix`), the two
  outcomes (AFTER), and the first divergence point
  (`firstDivergence?`'s side-by-side walk).

The laws (the honest discipline):

- `rewindEvents_eq_runStates` — the rewind IS the prefix's replay
  (over the landed `runStates`).
- `whatIfJournal_inRange` — the construction made explicit (take ++
  [the event with its intent replaced] ++ drop).
- `whatIfJournal_outOfRange` — a modification point past the end is
  the IDENTITY: no occurrence at t, nothing modified (the loud no-op
  is honest; there is no fabricated event).
- `whatIfJournal_take_prefix` — the what-if's rewind face IS the
  original's prefix: the divergence starts exactly at the modification
  point, nothing before it moved.
- `whatIfJournal_seqs` — occurrence identity survives the what-if
  (the trichotomy: the modified stream's events are the SAME
  occurrences with new recorded intent).
- `firstDivergenceAux_none` / `firstDivergence?_none` — the net-zero
  honesty: no divergence reported ⟹ the two outcomes render equal (a
  reported net-zero IS a net zero).
- `firstDivergenceAux_some` / `firstDivergence?_some` — the some-face
  faithfulness: a reported divergence at k ⟹ the two replays' states
  after event k render DIFFERENT, recomputable from the journals alone
  (the report never fabricates a divergence point).
- `whatIfReport_prefix` — the reported prefix state is BOTH sides'
  rewind.

The comparison surface: `renderTable` (the event lane's convention —
the `RowVals` GADT carries no BEq; the RENDER is the honest
comparison; `renderDelta` is its delta sibling).

The fixture (the committed honest data): a small two-field entity's
three-event journal + the worked what-if (event 1's update becomes a
different update — the divergence is AT 1) + the net-zero what-if
(event 1's update becomes the SAME update — no divergence).

The five questions (notes/v3/01-core.md): root = Change (01 §2)
crossed with the journal (03 §7's event face) — replay = I, the
what-if = a modified I over a NEW stream; carrier grade = none new —
`Report` is data over the landed `Journal`/`RowDelta`; spine reading =
the journal folds (Event.replayEvents), the what-if folds the modified
stream, the report reads the two folds side by side; ladder rung = rfl
construction equations + hand theorems over the landed fold (rung 6);
gate row = InspectorTests' what-if suite (the pins + the mandatory
negative controls) + the axiom pins (InspectorTests.Axioms).

Core-only: imports SchemaCore (the cone rule — the inspector is host
tooling, cone-high).
-/

import SchemaCore.Event
import SchemaCore.Pred

namespace Inspector.WhatIf

open SchemaCore

/-! ## The comparison surface (the render convention) -/

/-- Render a table (the event lane's comparison surface — `RowVals`
    carries no BEq; the GADT's index makes cross-shape comparison
    unrepresentable, so the RENDER is the honest comparison). -/
def renderTable {fs : List Field} (rows : List (RowVals fs)) : String :=
  String.intercalate ";" (rows.map (Pred.renderRow fs))

/-- Render a delta (`renderTable`'s sibling, for the intent lines). -/
def renderDelta {fs : List Field} : RowDelta fs → String
  | .insert r => "insert(" ++ Pred.renderRow fs r ++ ")"
  | .update r => "update(" ++ Pred.renderRow fs r ++ ")"
  | .remove k => "remove(" ++ toString k.val ++ ")"

/-! ## Small list helpers (the core ships no name) -/

/-- A prefix of `a ++ b` EXACTLY as long as `a` is `a` itself. -/
private theorem take_append_of_eq {α : Type} :
    ∀ (as bs : List α), (as ++ bs).take as.length = as
  | [], _ => rfl
  | a :: as, bs => by
      show (a :: (as ++ bs)).take (as.length + 1) = a :: as
      rw [List.take_cons (h := by omega)]
      simp only [Nat.add_sub_cancel]
      rw [take_append_of_eq as bs]

/-- One apply off the journal fold's front. -/
private theorem journalApply_cons {fs : List Field} (key : String)
    (d : RowDelta fs) (rest : List (RowDelta fs)) (rows : List (RowVals fs)) :
    journalApply key (d :: rest) rows
      = journalApply key rest (deltaApply key d rows) := by
  simp only [journalApply, List.foldl_cons]

/-! ## The rewind (replay to a prefix) -/

/-- THE REWIND: the state as of occurrence t — the replay of the
    journal's prefix (the partial integral; the landed `runStates`). -/
def rewindEvents {fs : List Field} (key : String) (s0 : List (RowVals fs))
    (log : Journal fs) (t : Nat) : List (RowVals fs) :=
  replayEvents key (log.take t) s0

/-- THE REWIND LAW: the rewind IS the prefix's replay — exactly the
    landed `runStates` at t (the states ARE the partial integrals). -/
theorem rewindEvents_eq_runStates {fs : List Field} (key : String)
    (s0 : List (RowVals fs)) (log : Journal fs) (t : Nat) :
    rewindEvents key s0 log t = runStates key s0 (journalDeltas log) t := by
  show journalApply key ((log.take t).map (·.delta)) s0
    = journalApply key ((log.map (·.delta)).take t) s0
  rw [List.map_take]

/-! ## The what-if journal (the NEW event stream) -/

/-- THE WHAT-IF JOURNAL: the original with event t's recorded intent
    replaced — the SAME occurrence (its `seq` survives), a NEW stream
    (the original is untouched — 03 §7: a what-if is a hypothetical,
    never a rewrite). Out of range = the identity (no occurrence at t,
    nothing modified). -/
def whatIfJournal {fs : List Field} (log : Journal fs) (t : Nat)
    (d : RowDelta fs) : Journal fs :=
  if h : t < log.length then
    log.take t ++ [{ log[t] with delta := d }] ++ log.drop (t + 1)
  else log

/-- The construction, in range: the modification is take ++ [the SAME
    occurrence with the replacement intent] ++ drop. -/
theorem whatIfJournal_inRange {fs : List Field} (log : Journal fs) (t : Nat)
    (d : RowDelta fs) (h : t < log.length) :
    whatIfJournal log t d
      = log.take t ++ [{ log[t] with delta := d }] ++ log.drop (t + 1) := by
  simp only [whatIfJournal, dif_pos h]

/-- Out of range, the modification is the IDENTITY — no occurrence at
    t, nothing modified (no fabricated event). -/
theorem whatIfJournal_outOfRange {fs : List Field} (log : Journal fs)
    (t : Nat) (d : RowDelta fs) (h : log.length ≤ t) :
    whatIfJournal log t d = log := by
  simp only [whatIfJournal,
    dif_neg (show ¬(t < log.length) from by omega)]

/-- THE PREFIX LAW: the what-if's rewind face IS the original's prefix
    — the divergence starts exactly at the modification point, nothing
    before it moved. -/
theorem whatIfJournal_take_prefix {fs : List Field} (log : Journal fs)
    (t : Nat) (d : RowDelta fs) (h : t < log.length) :
    (whatIfJournal log t d).take t = log.take t := by
  rw [whatIfJournal_inRange log t d h, List.append_assoc]
  have ht : (log.take t).length = t := by
    simp [List.length_take]
    omega
  have hta : (log.take t ++ ([{ log[t] with delta := d }]
      ++ log.drop (t + 1))).take (log.take t).length = log.take t :=
    take_append_of_eq _ _
  rw [ht] at hta
  exact hta

/-- THE EVENT-IDENTITY LAW (03 §7): occurrence identity survives the
    what-if — the modified stream's events are the SAME occurrences
    (`seq` for `seq`) with new recorded intent. -/
theorem whatIfJournal_seqs {fs : List Field} (log : Journal fs) (t : Nat)
    (d : RowDelta fs) :
    (whatIfJournal log t d).map (·.seq) = log.map (·.seq) := by
  by_cases h : t < log.length
  · rw [whatIfJournal_inRange log t d h]
    have key2 : log.map (·.seq)
        = (log.take t).map (·.seq)
            ++ log[t].seq :: (log.drop (t + 1)).map (·.seq) := by
      conv =>
        lhs
        rw [← List.take_append_drop t log, List.drop_eq_getElem_cons h,
          List.map_append, List.map_cons]
    rw [List.map_append, List.map_append, List.map_cons, key2]
    simp
  · rw [whatIfJournal_outOfRange log t d (by omega)]

/-- The replacement preserves the journal's length (the walk's
    equal-length premise — the what-if never adds or drops events). -/
theorem whatIfJournal_length {fs : List Field} (log : Journal fs) (t : Nat)
    (d : RowDelta fs) (h : t < log.length) :
    (whatIfJournal log t d).length = log.length := by
  rw [whatIfJournal_inRange log t d h, List.length_append, List.length_append,
    List.length_singleton, List.length_drop, List.length_take]
  omega

/-! ## The side-by-side walk (the divergence point) -/

/-- The side-by-side replay walk: both delta streams folded position-
    wise from the shared base, carried state; the first position whose
    rendered states differ is the DIVERGENCE POINT. One stream ending
    while the other continues is itself a divergence (the outcomes'
    shapes part). -/
def firstDivergenceAux {fs : List Field} (key : String) :
    Nat → List (RowVals fs) → List (RowVals fs) →
      List (RowDelta fs) → List (RowDelta fs) → Option Nat
  | t, sA, sB, [], [] =>
      if renderTable sA == renderTable sB then none else some t
  | t, sA, sB, dA :: restA, dB :: restB =>
      if renderTable (deltaApply key dA sA) == renderTable (deltaApply key dB sB) then
        firstDivergenceAux key (t + 1) (deltaApply key dA sA)
          (deltaApply key dB sB) restA restB
      else some t
  | t, _, _, _ :: _, [] => some t
  | t, _, _, [], _ :: _ => some t

/-- The walk's top level: both streams start at the shared base state. -/
def firstDivergence? {fs : List Field} (key : String) (s0 : List (RowVals fs))
    (dA dB : List (RowDelta fs)) : Option Nat :=
  firstDivergenceAux key 0 s0 s0 dA dB

/-! The walk's equations (the match's arms, stated once). -/

private theorem aux_nil_nil {fs : List Field} (key : String) (t : Nat)
    (sA sB : List (RowVals fs)) :
    firstDivergenceAux key t sA sB [] []
      = if renderTable sA == renderTable sB then none else some t :=
  rfl

private theorem aux_cons_cons {fs : List Field} (key : String) (t : Nat)
    (sA sB : List (RowVals fs)) (dA : RowDelta fs) (restA : List (RowDelta fs))
    (dB : RowDelta fs) (restB : List (RowDelta fs)) :
    firstDivergenceAux key t sA sB (dA :: restA) (dB :: restB)
      = if renderTable (deltaApply key dA sA) == renderTable (deltaApply key dB sB)
        then firstDivergenceAux key (t + 1) (deltaApply key dA sA)
              (deltaApply key dB sB) restA restB
        else some t :=
  rfl

private theorem aux_cons_nil {fs : List Field} (key : String) (t : Nat)
    (sA sB : List (RowVals fs)) (dA : RowDelta fs) (restA : List (RowDelta fs)) :
    firstDivergenceAux key t sA sB (dA :: restA) [] = some t :=
  rfl

private theorem aux_nil_cons {fs : List Field} (key : String) (t : Nat)
    (sA sB : List (RowVals fs)) (dB : RowDelta fs) (restB : List (RowDelta fs)) :
    firstDivergenceAux key t sA sB [] (dB :: restB) = some t :=
  rfl

/-- A reported divergence is never before the walk's start position. -/
theorem firstDivergenceAux_ge {fs : List Field} (key : String) :
    ∀ (t : Nat) (sA sB : List (RowVals fs)) (dA dB : List (RowDelta fs))
      (k : Nat),
      firstDivergenceAux key t sA sB dA dB = some k → t ≤ k := by
  intro t sA sB dA
  induction dA generalizing t sA sB with
  | nil =>
      intro dB k h
      cases dB with
      | nil =>
          rw [aux_nil_nil] at h
          split at h
          · simp at h
          · have htk : t = k := by simpa using h
            omega
      | cons dB' restB =>
          rw [aux_nil_cons] at h
          have htk : t = k := by simpa using h
          omega
  | cons d restA ih =>
      intro dB k h
      cases dB with
      | nil =>
          rw [aux_cons_nil] at h
          have htk : t = k := by simpa using h
          omega
      | cons d2 restB =>
          rw [aux_cons_cons] at h
          split at h
          · have hle := ih (t + 1) (deltaApply key d sA) (deltaApply key d2 sB)
              restB k h
            omega
          · have htk : t = k := by simpa using h
            omega

/-- THE NET-ZERO HONESTY (the walk's `none` face): no divergence
    reported ⟹ the two outcomes render equal — a reported net-zero IS
    a net zero. -/
theorem firstDivergenceAux_none {fs : List Field} (key : String) :
    ∀ (t : Nat) (sA sB : List (RowVals fs)) (dA dB : List (RowDelta fs)),
      firstDivergenceAux key t sA sB dA dB = none →
        (renderTable (journalApply key dA sA)
          == renderTable (journalApply key dB sB)) = true := by
  intro t sA sB dA
  induction dA generalizing t sA sB with
  | nil =>
      intro dB h
      cases dB with
      | nil =>
          rw [aux_nil_nil] at h
          split at h
          · next hEq => exact hEq
          · simp at h
      | cons _ _ =>
          rw [aux_nil_cons] at h
          simp at h
  | cons d restA ih =>
      intro dB h
      cases dB with
      | nil =>
          rw [aux_cons_nil] at h
          simp at h
      | cons d2 restB =>
          rw [aux_cons_cons] at h
          split at h
          · next hEq =>
              have h2 :=
                ih (t + 1) (deltaApply key d sA) (deltaApply key d2 sB) restB h
              rw [journalApply_cons, journalApply_cons]
              exact h2
          · simp at h

/-- The `none` face at the walk's top level. -/
theorem firstDivergence?_none {fs : List Field} (key : String)
    (s0 : List (RowVals fs)) (dA dB : List (RowDelta fs))
    (h : firstDivergence? key s0 dA dB = none) :
    (renderTable (replay key dA s0) == renderTable (replay key dB s0)) = true := by
  rw [firstDivergence?] at h
  simp only [replay]
  exact firstDivergenceAux_none key 0 s0 s0 dA dB h

/-- THE DIVERGENCE REPORT'S FAITHFULNESS (the walk's `some` face, over
    equal-length streams — the what-if's shape, `whatIfJournal_length`):
    a reported divergence at k means the two replays' states AFTER
    event k render DIFFERENT, and the reported states are honest
    replays of the journals' prefixes — the point is recomputable from
    the journals alone. -/
theorem firstDivergenceAux_some {fs : List Field} (key : String) :
    ∀ (t : Nat) (sA sB : List (RowVals fs)) (dA dB : List (RowDelta fs))
      (k : Nat),
      dA.length = dB.length →
      firstDivergenceAux key t sA sB dA dB = some k →
        ∃ (a b : List (RowVals fs)),
          (renderTable a == renderTable b) = false ∧
          a = journalApply key (dA.take (k - t + 1)) sA ∧
          b = journalApply key (dB.take (k - t + 1)) sB := by
  intro t sA sB dA
  induction dA generalizing t sA sB with
  | nil =>
      intro dB k hlen h
      cases dB with
      | nil =>
          rw [aux_nil_nil] at h
          split at h
          · simp at h
          · next hNe =>
              have hkt : t = k := by simpa using h
              have hf : (renderTable sA == renderTable sB) = false := by
                cases hEq : renderTable sA == renderTable sB with
                | false => rfl
                | true => exact absurd hEq hNe
              refine ⟨sA, sB, hf, ?_, ?_⟩
              · rw [hkt, show k - k + 1 = 1 from by omega]
                simp [journalApply]
              · rw [hkt, show k - k + 1 = 1 from by omega]
                simp [journalApply]
      | cons _ _ =>
          rw [aux_nil_cons] at h
          simp at hlen
  | cons d restA ih =>
      intro dB k hlen h
      cases dB with
      | nil =>
          rw [aux_cons_nil] at h
          simp at hlen
      | cons d2 restB =>
          have hrest : restA.length = restB.length := by
            simp only [List.length_cons] at hlen
            omega
          rw [aux_cons_cons] at h
          split at h
          · next =>
              have hge := firstDivergenceAux_ge key (t + 1)
                (deltaApply key d sA) (deltaApply key d2 sB) restA restB k h
              have ⟨a, b, hNe, hA, hB⟩ := ih (t + 1) (deltaApply key d sA)
                (deltaApply key d2 sB) restB k hrest h
              have hk : k - t + 1 = k - (t + 1) + 2 := by omega
              have hx : k - (t + 1) + 2 - 1 = k - (t + 1) + 1 := by omega
              refine ⟨a, b, hNe, ?_, ?_⟩
              · rw [hk, List.take_cons (h := by omega), hx, journalApply_cons]
                exact hA
              · rw [hk, List.take_cons (h := by omega), hx, journalApply_cons]
                exact hB
          · next hNe =>
              have hkt : t = k := by simpa using h
              have hf : (renderTable (deltaApply key d sA)
                    == renderTable (deltaApply key d2 sB)) = false := by
                cases hEq : renderTable (deltaApply key d sA)
                      == renderTable (deltaApply key d2 sB) with
                | false => rfl
                | true => exact absurd hEq hNe
              refine ⟨deltaApply key d sA, deltaApply key d2 sB, hf, ?_, ?_⟩
              · rw [hkt, show k - k + 1 = 1 from by omega]
                simp [journalApply]
              · rw [hkt, show k - k + 1 = 1 from by omega]
                simp [journalApply]

/-- The `some` face at the walk's top level (both streams start at the
    shared base; the reported states ARE the landed partial integrals —
    the `runStates` one tick past the reported point). -/
theorem firstDivergence?_some {fs : List Field} (key : String)
    (s0 : List (RowVals fs)) (dA dB : List (RowDelta fs)) (k : Nat)
    (hlen : dA.length = dB.length)
    (h : firstDivergence? key s0 dA dB = some k) :
    ∃ (a b : List (RowVals fs)),
      (renderTable a == renderTable b) = false ∧
      a = runStates key s0 dA (k + 1) ∧
      b = runStates key s0 dB (k + 1) := by
  rw [firstDivergence?] at h
  have ⟨a, b, hNe, hA, hB⟩ := firstDivergenceAux_some key 0 s0 s0 dA dB k hlen h
  refine ⟨a, b, hNe, ?_, ?_⟩
  · rw [hA, show k - 0 + 1 = k + 1 from by omega]
    rfl
  · rw [hB, show k - 0 + 1 = k + 1 from by omega]
    rfl

/-! ## The what-if report (the divergence as data) -/

/-- THE WHAT-IF REPORT: the divergence AS DATA — the modification's
    coordinates (the point + the replacement intent), the two journals
    (the original UNTOUCHED + the hypothetical NEW stream), the shared
    prefix state (BEFORE), the two outcomes (AFTER), and the first
    divergence point (`none` = the what-if is a net zero). -/
structure Report (fs : List Field) where
  /-- The original journal (untouched — the hypothetical never rewrites). -/
  original : Journal fs
  /-- The modified journal (the NEW event stream). -/
  modified : Journal fs
  /-- The modification point (the event whose intent is replaced). -/
  point : Nat
  /-- The replacement intent. -/
  replacement : RowDelta fs
  /-- The states BEFORE: the shared prefix state (the rewind to the point). -/
  prefixState : List (RowVals fs)
  /-- The original's outcome (the full replay's end). -/
  originalOutcome : List (RowVals fs)
  /-- The what-if's outcome. -/
  modifiedOutcome : List (RowVals fs)
  /-- The first divergence point (`none` = a net zero). -/
  divergesAt? : Option Nat

/-- Build the report: the two replays + the side-by-side walk over the
    two delta streams. Pure composition over the landed machinery. -/
def whatIfReport {fs : List Field} (key : String) (s0 : List (RowVals fs))
    (log : Journal fs) (t : Nat) (d : RowDelta fs) : Report fs :=
  let mod := whatIfJournal log t d
  { original := log
    modified := mod
    point := t
    replacement := d
    prefixState := rewindEvents key s0 log t
    originalOutcome := replayEvents key log s0
    modifiedOutcome := replayEvents key mod s0
    divergesAt? := firstDivergence? key s0 (journalDeltas log) (journalDeltas mod) }

/-- THE REPORT'S SHARED FACE: the reported prefix state is BOTH sides'
    rewind — equal by the prefix law (nothing before the modification
    point moved). -/
theorem whatIfReport_prefix {fs : List Field} (key : String)
    (s0 : List (RowVals fs)) (log : Journal fs) (t : Nat) (d : RowDelta fs)
    (h : t < log.length) :
    (whatIfReport key s0 log t d).prefixState
      = rewindEvents key s0 (whatIfJournal log t d) t := by
  show replayEvents key (log.take t) s0
    = replayEvents key ((whatIfJournal log t d).take t) s0
  rw [whatIfJournal_take_prefix log t d h]

/-- The report's rendering (pure; the CLI prints it). -/
def Report.render {fs : List Field} (r : Report fs) : String :=
  let outcome (rows : List (RowVals fs)) : String :=
    if rows.isEmpty then "(empty)" else renderTable rows
  let divLine :=
    match r.divergesAt? with
    | none =>
        "divergence: none — the what-if is a NET ZERO (the outcomes render equal)"
    | some k =>
        s!"divergence: first at event {k} — the states after event {k} differ"
  String.intercalate "\n"
    [ s!"what-if at event {r.point}: the recorded intent replaced with \
      {renderDelta r.replacement}"
    , s!"journal: {r.original.length} event(s); the hypothetical is a NEW \
      stream — the original is untouched (03 §7's event-identity discipline)"
    , s!"rewind (the shared prefix state before event {r.point}): \
      {outcome r.prefixState}"
    , divLine
    , s!"original outcome: {outcome r.originalOutcome}"
    , s!"what-if outcome: {outcome r.modifiedOutcome}" ]

/-! ## The fixture (the committed honest data) -/

/-- The entity's declaration: two fields, keyed on `id`. -/
def fixtureFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string }]

/-- The entity's row. -/
def fixtureRow (n : UInt64) (nm : String) : RowVals fixtureFields :=
  .cons (.u64 n) (.cons (.string nm) .nil)

/-- The base table. -/
def fixtureRows0 : List (RowVals fixtureFields) :=
  [fixtureRow 1 "ann", fixtureRow 2 "bob"]

/-- The fixture journal: three events, in occurrence order. -/
def fixtureJournal : Journal fixtureFields :=
  [ { seq := 0, delta := .insert (fixtureRow 3 "cat") }
  , { seq := 1, delta := .update (fixtureRow 2 "bob2") }
  , { seq := 2, delta := .remove ⟨.u64, .u64 1⟩ } ]

/-- THE WORKED WHAT-IF: event 1's intent becomes a DIFFERENT update —
    the divergence starts AT 1. -/
def fixtureReplacement : RowDelta fixtureFields := .update (fixtureRow 2 "bobby")

def fixtureWhatIf : Report fixtureFields :=
  whatIfReport "id" fixtureRows0 fixtureJournal 1 fixtureReplacement

/-- THE NET-ZERO WHAT-IF: event 1's intent becomes the SAME update —
    no divergence (the outcomes render equal). -/
def fixtureNetZero : Report fixtureFields :=
  whatIfReport "id" fixtureRows0 fixtureJournal 1 (.update (fixtureRow 2 "bob2"))

end Inspector.WhatIf
