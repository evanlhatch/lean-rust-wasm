/- # SchemaCore.Delta — the event-sourcing lane's shared delta variant

Owner: the event-sourcing lane agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/08-capabilities.md #7 (event sourcing —
delta variant + journal codec + replay + upcasters; the laws GENERATED
once at the shared type, never per record) + notes/v3/01-core.md §2
(the Change ladder — instances land at their highest HONEST rung) +
notes/v3/03-bidirectional.md §7 (the command/delta/event trichotomy:
Δ is the accepted NET change, never a command, never an event) +
notes/v3/02-data-plane.md §2 (the cone rule: core-only).

Provenance: mined from `legacy/lean/schema-lang/SchemaLang/Change.lean`
+ `EventSourced.lean` (ported fresh at the row layer):

- the ONE shared change variant — the legacy `Delta ρ κ` shape — is
  THIS tree's `SchemaCore.RowDelta` (Update.lean), REUSED by import:
  one type, three specializations (the update lane's rows, the
  journal's events, the wire's change enum). A second inductive here
  would be a parallel table (15-patterns' shield);
- the keyed-table semantics — the legacy `upsert`/`apply` (first key
  match replaces, else appends; remove erases the first match) — as
  `keyedUpsert`/`keyedErase`/`deltaApply`, restructured so the
  journal's witness position is DATA (an accumulator), never a
  `findIdx` lookup;
- the witnessed delta — the legacy `WDelta` + `patchW`/`validW`/
  `invertW` + `witnessOf`/`witnessOf_valid`/`apply_eq_patchW` — the
  journal records per event: position + OLD row + NEW row;
- `replay_snoc`'s home here is `journalApply_snoc` (Event.lean's
  `replay` is the same fold under the doctrine's name).

THE HONEST RUNG ANALYSIS (01-core §2 — this file's spine): one delta
variant, three carriers, three rungs.

1. the SINGLE delta is `Applicable` ONLY (`rowDeltaApplicable`) — one
   insert/update/remove cannot be the net of two (the update lane's
   `updateItem_notComposable` is the same shape at the language
   granularity; the control is not duplicated here);
2. the UNWITNESSED journal (`List (RowDelta fs)`) climbs to
   `WithIdentity` — deltas compose by append around the empty log —
   and STOPS: `journal_notReversible` PROVES no inverse exists. The
   doctrine's set-forgets-old-value example at the journal
   granularity: a remove of an absent key is a no-op, so two distinct
   states produce the same post-state under one log — a fixed inverse
   cannot restore both;
3. the WITNESSED journal (`List (WDelta fs)`) climbs to `Reversible`
   (`witnessedReversible`) — the witness RETAINS the old row, so the
   inverse (swap old/new, reverse the order) is lawful. The honesty
   carrier is the CHECKED patch `patchW?`: a lying witness REFUSES
   (the `KeyPut` discipline — the delta does not lie), which makes the
   round-trip law hold UNCONDITIONALLY, validity threading through the
   fold by construction.

The fusion bridges (`machines/Machines/Fusion.lean` — journal = D∘run,
replay = I∘journal) are the ADDITIVE (stream) face of this same
discipline; the keyed-table reading is the NONLINEAR fold (keyed upsert
is not a group operation), stated in Event.lean with the citation.

Named exclusions (the leftover rule, each with its reason): the
composite-position witness (a multi-row event needs a list of
witnesses — lands with the first batch event consumer); the wire-level
witness codec (the journal codec in Event.lean carries the deltas;
witness bytes follow the first rewind-wire consumer); the
`applyRowDelta` correspondence (the update lane's all-matches update
agrees with this first-match semantics under the `KeyCoherent` nodup
premises — Law 6's face — lands with the first consumer that needs the
two semantics tied).

The five questions (notes/v3/01-core.md): root = Change (01 §2) at the
row layer — the delta substrate the journal folds; carrier grade = the
ladder's OWN instances (`Applicable`/`WithIdentity`/`Reversible` — one
per carrier, rungs PROVED unclimbable where claimed); spine reading =
none — the lane rides the substrate the way Update.lean does; ladder
rung = the instances above (the Reversible round trip is a hand
theorem over the fold — rung 6), the keyed reductions are
`rfl`-reducible on concrete rows (rung 3); gate row = SchemaTests'
eventSourcedSpec (the rung pins + the negative controls) + the axiom
report (SchemaTests.Axioms).

Core-only (imports SchemaCore.Update + Kit.Change — the cone rule).
-/

import SchemaCore.Update
import Kit.Change

namespace SchemaCore

/-! ## The keyed-table semantics (the journal's reading of a delta) -/

/-- The key-image match: does `row`'s image under the declared key
    equal `k`? (Non-projecting rows match nothing — the refusal
    reading Update.lean's lowering uses, at the predicate level.) -/
def sameKeyImg {fs : List Field} (key : String) (row : RowVals fs)
    (k : FieldVal) : Bool :=
  match RowVals.project? fs row key with
  | some a => FieldVal.beq a k
  | none => false

/-- The row-pair key match (the upsert's gate). -/
def sameKey {fs : List Field} (key : String) (a b : RowVals fs) : Bool :=
  match RowVals.project? fs a key, RowVals.project? fs b key with
  | some x, some y => FieldVal.beq x y
  | _, _ => false

/-- Key-based upsert: replace the FIRST row whose key matches, else
    append (the legacy `upsert`, the Delta.lean lowering decision —
    v1 is full replacement). -/
def keyedUpsert {fs : List Field} (key : String) (r : RowVals fs) :
    List (RowVals fs) → List (RowVals fs)
  | [] => [r]
  | row :: rs =>
      if sameKey key row r then r :: rs else row :: keyedUpsert key r rs

/-- Key-based erase: drop the FIRST key-matching row (the legacy
    `remove` arm; v1 keyed tables are key-unique by construction —
    `insert` IS upsert, so reachable states never duplicate a key). -/
def keyedErase {fs : List Field} (key : String) (k : FieldVal) :
    List (RowVals fs) → List (RowVals fs)
  | [] => []
  | row :: rs =>
      if sameKeyImg key row k then rs else row :: keyedErase key k rs

/-- THE DELTA'S APPLICATION (the legacy `apply`): one journal delta on
    the keyed table. Total — `insert`/`update` ARE upsert, `remove`
    erases — the Option totality lives in the CHECKED carriers below,
    never here. -/
def deltaApply {fs : List Field} (key : String) (d : RowDelta fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  match d with
  | .insert r | .update r => keyedUpsert key r rows
  | .remove k => keyedErase key k rows

/-! ## Rung 2-3 — the unwitnessed journal: `WithIdentity`, not more -/

/-- The journal's application: the deltas in order (the I fold). -/
def journalApply {fs : List Field} (key : String) (log : List (RowDelta fs))
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  log.foldl (fun st d => deltaApply key d st) rows

theorem journalApply_snoc {fs : List Field} (key : String)
    (log : List (RowDelta fs)) (d : RowDelta fs) (rows : List (RowVals fs)) :
    journalApply key (log ++ [d]) rows
      = deltaApply key d (journalApply key log rows) := by
  simp only [journalApply, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- THE UNWITNESSED JOURNAL'S RUNG: `WithIdentity` — the log composes
    by append around the empty log, application respects it. NOT
    `Reversible` — `journal_notReversible` PROVES the climb unlawful
    (the delta forgets the old row). -/
def journalApplicable (key : String) {fs : List Field} :
    Kit.WithIdentity (List (RowVals fs)) (List (RowDelta fs)) where
  apply s d := some (journalApply key d s)
  compose a b := a ++ b
  assoc a b c := List.append_assoc a b c
  applyCompose s a b := by
    show some (journalApply key (a ++ b) s)
      = (some (journalApply key a s)).bind
          (fun x => some (journalApply key b x))
    simp [journalApply, List.foldl_append]
  nop := []
  composeNopLeft d := (List.nil_append d).symm
  composeNopRight d := List.append_nil d
  applyNop s := rfl

/-- Rung 1 for the SINGLE delta: `Applicable` — one insert/update/
    remove cannot be the net of two (the composition's unclimbability
    is `updateItem_notComposable`'s shape at the language granularity;
    the rung is stated so the single-delta carrier is tabled, not
    implied). -/
def rowDeltaApplicable (key : String) {fs : List Field} :
    Kit.Applicable (List (RowVals fs)) (RowDelta fs) where
  apply s d := some (deltaApply key d s)

/-! ## NEGATIVE CONTROL — the unwitnessed journal is NOT reversible

The control fixture is the UPDATE LANE'S counterexample schema
(`UpdateItem.cxFields`/`cxRow` — ONE copy; the dupDefBodies lint owns
the dedup). -/

/-- NEGATIVE CONTROL (the rung is real): NO inverse satisfies the
    round-trip law for the unwitnessed journal. The remove of an ABSENT
    key is a no-op: the distinct states `[x=5]` and `[x=5, x=9]` both
    land on `[x=5]` under the same log — and one fixed inverse cannot
    restore both (application is a function). The witnessed shape
    escapes exactly by RECORDING the old row. -/
theorem journal_notReversible :
    ¬ ∃ inv : List (RowDelta UpdateItem.cxFields) →
        List (RowDelta UpdateItem.cxFields),
      ∀ (s : List (RowVals UpdateItem.cxFields))
          (d : List (RowDelta UpdateItem.cxFields))
          (s' : List (RowVals UpdateItem.cxFields)),
        journalApply "x" d s = s' → journalApply "x" (inv d) s' = s := by
  rintro ⟨inv, h⟩
  have h1 : journalApply "x" [RowDelta.remove ⟨.u64, .u64 9⟩]
      [UpdateItem.cxRow 5] = [UpdateItem.cxRow 5] := rfl
  have h2 : journalApply "x" [RowDelta.remove ⟨.u64, .u64 9⟩]
      [UpdateItem.cxRow 5, UpdateItem.cxRow 9] = [UpdateItem.cxRow 5] := rfl
  have hA := h [UpdateItem.cxRow 5] [RowDelta.remove ⟨.u64, .u64 9⟩]
      [UpdateItem.cxRow 5] h1
  have hB := h [UpdateItem.cxRow 5, UpdateItem.cxRow 9]
      [RowDelta.remove ⟨.u64, .u64 9⟩] [UpdateItem.cxRow 5] h2
  -- both applications are of the SAME function at the SAME state
  have hcon : [UpdateItem.cxRow 5] = [UpdateItem.cxRow 5, UpdateItem.cxRow 9]
    := hA.symm.trans hB
  injection hcon with _ h'
  exact absurd h' (by simp)

/-! ## The witnessed delta (the old-retaining shape) -/

/-- THE WITNESSED DELTA (the legacy `WDelta`, at the row layer): the
    position, the OLD row (`none` = the key was absent), the NEW row
    (`none` = the row is gone). The old row is what makes the inverse
    LAWFUL — the whole point of the witnessed shape. -/
structure WDelta (fs : List Field) where
  /-- The position (the first key match, or the append position). -/
  idx : Nat
  /-- The recorded pre-image. -/
  old? : Option (RowVals fs)
  /-- The recorded post-image. -/
  new? : Option (RowVals fs)

/-- Inversion: swap old and new (rollback = the canon's undo row). -/
def invertW {fs : List Field} (d : WDelta fs) : WDelta fs :=
  ⟨d.idx, d.new?, d.old?⟩

/-- Patch by a witnessed delta: positional replace / erase / insert
    (matched on the delta directly — the laws need the literal
    constructor arms). -/
def patchW {fs : List Field} (rows : List (RowVals fs)) (d : WDelta fs) :
    List (RowVals fs) :=
  match d with
  | ⟨i, some _, some n⟩ => rows.set i n
  | ⟨i, some _, none⟩ => rows.eraseIdx i
  | ⟨i, none, some n⟩ => rows.insertIdx i n
  | ⟨_, none, none⟩ => rows

/-- The SHIFT: the witness's position rides a cons (the structural
    walk's step — the legacy `findIdx` restructured as data). -/
def shiftW {fs : List Field} (d : WDelta fs) : WDelta fs :=
  ⟨d.idx + 1, d.old?, d.new?⟩

/-- The shift's patch face: patching a cons at the shifted position is
    consing the patch (the four arms' cons equations). -/
theorem patchW_cons {fs : List Field} (row : RowVals fs)
    (rs : List (RowVals fs)) (d : WDelta fs) :
    patchW (row :: rs) (shiftW d) = row :: patchW rs d := by
  cases d with
  | mk i o n =>
      cases o <;> cases n <;> simp [patchW, shiftW]

/-- Validity as DATA: the recorded OLD row is exactly what's at the
    position (replace/erase), or the position is in append range
    (insert). The Bool face is what the CHECKED patch dispatches on —
    the Prop face is `validWb … = true`. -/
def validWb {fs : List Field} : List (RowVals fs) → WDelta fs → Bool
  | rows, ⟨i, some o, _⟩ =>
      match rows[i]? with
      | some r => rowBeq fs r o
      | none => false
  | rows, ⟨i, none, some _⟩ => decide (i ≤ rows.length)
  | _, ⟨_, none, none⟩ => true

/-- The validity bridge: a valid replace/erase witness recorded an old
    row that IS the row at the position. -/
theorem validWb_some_old {fs : List Field} {rows : List (RowVals fs)}
    {i : Nat} {o : RowVals fs} (h : validWb rows ⟨i, some o, none⟩ = true) :
    ∃ hlt : i < rows.length, rows[i]'hlt = o := by
  simp only [validWb] at h
  cases hget : rows[i]? with
  | none => rw [hget] at h; simp at h
  | some r =>
      rw [hget] at h
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
      exact ⟨hlt, heq.trans (rowBeq_eq _ r o h)⟩

/-- Validity survives inversion (the legacy `valid_invert`): the
    patched table presents exactly the recorded NEW row at the
    position. -/
theorem validWb_invert {fs : List Field} (rows : List (RowVals fs))
    (d : WDelta fs) (h : validWb rows d = true) :
    validWb (patchW rows d) (invertW d) = true := by
  cases d with
  | mk i o n =>
      cases o with
      | none =>
          cases n with
          | none => rfl
          | some n =>
              -- insert's invert is a replace by n at i
              have hi : i ≤ rows.length := by
                simpa [validWb] using h
              show validWb (rows.insertIdx i n) ⟨i, some n, none⟩ = true
              simp only [validWb, List.getElem?_insertIdx_self, if_pos hi]
              exact rowBeq_refl _ _
      | some o =>
          obtain ⟨hlt, _ho⟩ := validWb_some_old h
          cases n with
          | none =>
              -- erase's invert is an insert at i
              show validWb (rows.eraseIdx i) ⟨i, none, some o⟩ = true
              simp only [validWb, decide_eq_true_eq]
              rw [List.length_eraseIdx, if_pos hlt]
              omega
          | some n =>
              -- replace's invert replaces back
              show validWb (rows.set i n) ⟨i, some n, none⟩ = true
              simp only [validWb]
              rw [List.getElem?_set_self hlt]
              exact rowBeq_refl _ _

/-- Positional restore: re-inserting at `i` after erasing at `i` is
    `set i` (in bounds — out of bounds `insertIdx` appends where `set`
    is the identity). (Mined: the legacy's own diagonal lemma.) -/
theorem insertIdx_eraseIdx_eq_set (l : List α) (i : Nat) (a : α)
    (h : i < l.length) :
    (l.eraseIdx i).insertIdx i a = l.set i a := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < xs.length := by
        have : (x :: xs).length = xs.length + 1 := rfl
        omega
      show (x :: xs.eraseIdx i).insertIdx (i + 1) a = x :: xs.set i a
      rw [show (x :: xs.eraseIdx i).insertIdx (i + 1) a =
          x :: (xs.eraseIdx i).insertIdx i a from rfl]
      rw [ih i h']

/-- THE PATCH-INVERSE LAW (the legacy `correct_invert`): revert after
    apply is the identity ON VALID witnesses — the row at the position
    is exactly what the witness recorded. -/
theorem patchW_invert {fs : List Field} (rows : List (RowVals fs))
    (d : WDelta fs) (h : validWb rows d = true) :
    patchW (patchW rows d) (invertW d) = rows := by
  cases d with
  | mk i o n =>
      cases o with
      | none =>
          cases n with
          | none => rfl
          | some n =>
              show (rows.insertIdx i n).eraseIdx i = rows
              exact List.eraseIdx_insertIdx_self n
      | some o =>
          obtain ⟨hlt, ho⟩ := validWb_some_old h
          cases n with
          | none =>
              show (rows.eraseIdx i).insertIdx i o = rows
              rw [insertIdx_eraseIdx_eq_set _ _ _ hlt, ← ho,
                List.set_getElem_self hlt]
          | some n =>
              show (rows.set i n).set i o = rows
              rw [List.set_set, ← ho, List.set_getElem_self hlt]

/-! ## The witness (what the journal records per event) -/

/-- The witnessed upsert walk: the FIRST key match gives a replace
    witness (the old row recorded); no match gives an append witness.
    The position accumulator rides the walk — the legacy `witnessOf`'s
    row-carrying arms, restructured so the position is data. -/
def witnessUpsert {fs : List Field} (key : String) (r : RowVals fs) :
    List (RowVals fs) → WDelta fs
  | [] => ⟨0, none, some r⟩
  | row :: rs =>
      if sameKey key row r then ⟨0, some row, some r⟩
      else shiftW (witnessUpsert key r rs)

/-- The witnessed erase walk: the first key match gives the erase
    witness; no match gives the no-op witness. -/
def witnessErase {fs : List Field} (key : String) (k : FieldVal) :
    List (RowVals fs) → WDelta fs
  | [] => ⟨0, none, none⟩
  | row :: rs =>
      if sameKeyImg key row k then ⟨0, some row, none⟩
      else shiftW (witnessErase key k rs)

/-- THE WITNESS: the delta an event produces at a state — what the
    journal records per occurrence (the legacy `witnessOf`). -/
def witnessOf {fs : List Field} (key : String) (d : RowDelta fs)
    (rows : List (RowVals fs)) : WDelta fs :=
  match d with
  | .insert r | .update r => witnessUpsert key r rows
  | .remove k => witnessErase key k rows

/-- Firing IS patching (upsert face): the keyed upsert is the patch by
    the witnessed walk (the induction mirrors the legacy
    `upsert_eq_set`/`upsert_eq_append` pair, unified by the shift). -/
theorem keyedUpsert_eq_patchW {fs : List Field} (key : String)
    (r : RowVals fs) :
    ∀ (rows : List (RowVals fs)),
      keyedUpsert key r rows = patchW rows (witnessUpsert key r rows)
  | [] => rfl
  | row :: rs => by
      by_cases hc : sameKey key row r
      · simp only [keyedUpsert, witnessUpsert, if_pos hc, patchW]
        simp
      · simp only [keyedUpsert, witnessUpsert, if_neg hc]
        rw [patchW_cons, keyedUpsert_eq_patchW key r rs]

/-- Firing IS patching (erase face). -/
theorem keyedErase_eq_patchW {fs : List Field} (key : String)
    (k : FieldVal) :
    ∀ (rows : List (RowVals fs)),
      keyedErase key k rows = patchW rows (witnessErase key k rows)
  | [] => rfl
  | row :: rs => by
      by_cases hc : sameKeyImg key row k
      · simp only [keyedErase, witnessErase, if_pos hc, patchW]
        simp
      · simp only [keyedErase, witnessErase, if_neg hc]
        rw [patchW_cons, keyedErase_eq_patchW key k rs]

/-- **FIRING IS PATCHING** (the legacy `apply_eq_patchW`): applying a
    delta to the table IS patching the table by the delta the event
    records — the RewindableMachine.action_is_patch obligation's shape,
    discharged once here for every specialization. -/
theorem apply_eq_patchW {fs : List Field} (key : String) (d : RowDelta fs)
    (rows : List (RowVals fs)) :
    deltaApply key d rows = patchW rows (witnessOf key d rows) := by
  cases d with
  | insert r => exact keyedUpsert_eq_patchW key r rows
  | update r => exact keyedUpsert_eq_patchW key r rows
  | remove k => exact keyedErase_eq_patchW key k rows

/-- The shift carries validity (the walk's induction step): a witness
    valid for the suffix is valid for the cons, one position in. -/
theorem validWb_shift {fs : List Field} (row : RowVals fs)
    (rs : List (RowVals fs)) (d : WDelta fs) (h : validWb rs d = true) :
    validWb (row :: rs) (shiftW d) = true := by
  cases d with
  | mk i o n =>
      cases o with
      | none =>
          cases n with
          | none => rfl
          | some n =>
              have hi : i ≤ rs.length := by simpa [validWb] using h
              simp only [shiftW, validWb, decide_eq_true_eq]
              rw [List.length_cons]
              omega
      | some o =>
          simp only [validWb] at h ⊢
          cases hget : rs[i]? with
          | none => rw [hget] at h; simp at h
          | some r =>
              rw [hget] at h
              show (match (row :: rs)[i + 1]? with
                | some r' => rowBeq fs r' o
                | none => false) = true
              rw [List.getElem?_cons_succ, hget]
              exact h

/-- THE RECORDED DELTA IS VALID (the legacy `witnessOf_valid`): the
    witness an event produces is valid for the state that produced it —
    the RewindableMachine.deltaOf_valid obligation's shape. -/
theorem witnessUpsert_valid {fs : List Field} (key : String) (r : RowVals fs) :
    ∀ (rows : List (RowVals fs)), validWb rows (witnessUpsert key r rows)
  | [] => rfl
  | row :: rs => by
      by_cases hc : sameKey key row r
      · simp only [witnessUpsert, if_pos hc, validWb]
        simp [rowBeq_refl]
      · simp only [witnessUpsert, if_neg hc]
        exact validWb_shift row rs _ (witnessUpsert_valid key r rs)

/-- The erase walk's recorded witness is valid. -/
theorem witnessErase_valid {fs : List Field} (key : String) (k : FieldVal) :
    ∀ (rows : List (RowVals fs)), validWb rows (witnessErase key k rows)
  | [] => rfl
  | row :: rs => by
      by_cases hc : sameKeyImg key row k
      · simp only [witnessErase, if_pos hc, validWb]
        simp [rowBeq_refl]
      · simp only [witnessErase, if_neg hc]
        exact validWb_shift row rs _ (witnessErase_valid key k rs)

theorem witnessOf_valid {fs : List Field} (key : String) (d : RowDelta fs)
    (rows : List (RowVals fs)) : validWb rows (witnessOf key d rows) := by
  cases d with
  | insert r => exact witnessUpsert_valid key r rows
  | update r => exact witnessUpsert_valid key r rows
  | remove k => exact witnessErase_valid key k rows

/-! ## Rung 4 — the witnessed journal: `Reversible` (lawfully) -/

/-- THE CHECKED WITNESSED PATCH: it applies iff valid — a lying
    witness REFUSES, it never silently mispatches (the KeyPut
    discipline: the delta does not lie). The checked form is what
    makes the round-trip law hold UNCONDITIONALLY. -/
def patchW? {fs : List Field} (rows : List (RowVals fs)) (d : WDelta fs) :
    Option (List (RowVals fs)) :=
  if validWb rows d then some (patchW rows d) else none

theorem patchW?_of_valid {fs : List Field} (rows : List (RowVals fs))
    (d : WDelta fs) (h : validWb rows d = true) :
    patchW? rows d = some (patchW rows d) := by
  simp [patchW?, h]

/-- The witnessed journal's application: the patches in order, each
    checked — Kit.Change's ONE poison-fold (`optionFoldl`, the DRY
    sweep's consolidation; the Option accumulator is the fallibility
    carrier: a lying witness poisons the fold, never silently passes). -/
def witnessedApply (fs : List Field) (log : List (WDelta fs))
    (X : Option (List (RowVals fs))) : Option (List (RowVals fs)) :=
  X.bind fun r =>
    Kit.optionFoldl (fun (r : List (RowVals fs)) (w : WDelta fs) => patchW? r w)
      log r

/-- The one-step face (the fold's cons equation at the Option start). -/
theorem witnessedApply_cons (fs : List Field) (w : WDelta fs)
    (d : List (WDelta fs)) (X : Option (List (RowVals fs))) :
    witnessedApply fs (w :: d) X
      = witnessedApply fs d (X.bind (fun r => patchW? r w)) := by
  simp only [witnessedApply, Kit.optionFoldl_cons, Option.bind_assoc]

theorem witnessedApply_append (fs : List Field) (a b : List (WDelta fs))
    (X : Option (List (RowVals fs))) :
    witnessedApply fs (a ++ b) X
      = witnessedApply fs b (witnessedApply fs a X) := by
  rw [witnessedApply, witnessedApply, witnessedApply]
  simp only [Kit.optionFoldl_append, Option.bind_assoc]

theorem witnessedApply_none (fs : List Field) (d : List (WDelta fs)) :
    witnessedApply fs d none = none := by
  simp [witnessedApply]

/-- The single-step journal (the fold's one-element face). -/
theorem witnessedApply_single (fs : List Field) (w : WDelta fs)
    (X : Option (List (RowVals fs))) :
    witnessedApply fs [w] X = X.bind (fun r => patchW? r w) := by
  simp only [witnessedApply, Kit.optionFoldl]
  cases X <;> simp

/-- The witnessed journal's inverse: swap old and new, REVERSE the
    order (the legacy `invertW` lifted to the fold). -/
def witnessedInv (fs : List Field) (d : List (WDelta fs)) : List (WDelta fs) :=
  d.reverse.map invertW

/-- THE WITNESSED ROUND TRIP: applying the inverse journal undoes the
    journal — the fold-level `patchW_invert`, validity threaded by
    construction (each step's check proves the recorded old row). -/
theorem witnessedApply_reverse_inv (fs : List Field) :
    ∀ (d : List (WDelta fs)) (rows rows' : List (RowVals fs)),
      witnessedApply fs d (some rows) = some rows' →
      witnessedApply fs (d.reverse.map invertW) (some rows') = some rows := by
  intro d
  induction d with
  | nil =>
      intro rows rows' h
      rw [witnessedApply] at h ⊢
      simp only [Kit.optionFoldl_nil, Option.bind_some] at h ⊢
      exact h.symm
  | cons w d' ih =>
      intro rows rows' h
      rw [List.reverse_cons, List.map_append, witnessedApply_append,
        List.map_singleton, witnessedApply_single]
      rw [witnessedApply_cons, Option.bind_some] at h
      cases hp : patchW? rows w with
      | none =>
          rw [hp] at h
          rw [witnessedApply_none fs d'] at h
          exact absurd h (by simp)
      | some mid =>
          rw [hp] at h
          unfold patchW? at hp
          split at hp
          · next hv =>
              have hmid : mid = patchW rows w := Option.some.inj hp |>.symm
              rw [ih mid rows' h, Option.bind_some, hmid,
                patchW?_of_valid _ _ (validWb_invert rows w hv)]
              exact congrArg some (patchW_invert rows w hv)
          · exact absurd hp (by simp)

/-- THE REVERSIBLE RUNG on the witnessed journal carrier: the witness
    RETAINS the old value, so the inverse is LAWFUL — the honest climb
    the unwitnessed journal cannot make (`journal_notReversible` is the
    proved wall; the witnessed shape is its lawful resolution). -/
def witnessedReversible (fs : List Field) :
    Kit.Reversible (List (RowVals fs)) (List (WDelta fs)) where
  apply s d := witnessedApply fs d (some s)
  compose a b := a ++ b
  assoc a b c := List.append_assoc a b c
  applyCompose s a b := by
    show witnessedApply fs (a ++ b) (some s)
      = (witnessedApply fs a (some s)).bind
          (fun x => witnessedApply fs b (some x))
    rw [witnessedApply_append]
    cases X : witnessedApply fs a (some s) with
    | none => simp [witnessedApply_none]
    | some _ => rfl
  nop := []
  composeNopLeft d := (List.nil_append d).symm
  composeNopRight d := List.append_nil d
  applyNop s := rfl
  inv := witnessedInv fs
  roundTrip s d s' h := witnessedApply_reverse_inv fs d s s' h

end SchemaCore
