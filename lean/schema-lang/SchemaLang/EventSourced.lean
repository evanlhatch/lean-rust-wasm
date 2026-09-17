/-
# SchemaLang.EventSourced — the event-sourcing core (the canon row, Lean-side)

The canon row: **an event log = delta variant + journal codec + replay +
upcasters**. This module owns the TARGET-NEUTRAL core the
`@[event_sourced]` attribute (SchemaLang.Meta.EventSourced) specializes
per record; the `Meta` layer is syntax assembly — every LAW below is
proved once here, generically.

The delta variant IS the `SchemaLang.Delta` shape (the emitter lane's
`wit/delta.wit` + `delta_generated.rs`): `insert`/`update` carry the
full row, `remove` carries the key. One Lean inductive over abstract
row/key types — the per-record "derivation" is specialization, not
re-implementation (the emitter contract and this type are tied by
SHAPE: same ctors, same key convention — the first field, Delta.lean's
`Item.keyOf`).

Contents:

1. `Delta ρ κ` — the delta variant (event = patch = journal entry).
2. `upsert`/`apply`/`replay` — the keyed-table semantics; `replay` is
   the `I` operator (fold the event list to state). Law:
   `replay_snoc` (replay-after-append = one more apply).
3. `WDelta ρ` — the WITNESSED delta the journal records per event:
   position + old row + new row. `patchW`/`validW`/`invertW` carry a
   `Dbsp.ChangeInversion` instance (`wDeltaChangeInversion`) — the
   ChangeInversion row: `correct_invert` says revert-after-apply is the
   identity on valid deltas.
4. `witnessOf` — the delta an event produces at a state (first key
   match → replace/erase witness; no match → append/no-op witness).
   `apply_eq_patchW` (firing IS patching by the recorded delta) and
   `witnessOf_valid` (recorded deltas are valid) — the two
   `RewindableMachine` obligations.
5. `esMachine` — the generic `Machines.RewindableMachine` assembly.
   Every `@[event_sourced]` record gets a RewindableMachine by
   specialization; the ledger dogfood (W5.1 phase 2) constructs the
   first concrete instances (the review's pin-only island graduates).
6. The journal codec generics: `encDelta`/`decDelta?` (tag byte in
   ctor order — the EnumWire wire-breaking rule: reordering ctors is
   wire-breaking) + the append-form round trip, and
   `encJournal`/`decJournal?` over `Codec.encList`/`decList?`.
7. `unbox*` — the one-level `Value` projections for the flat-scalar
   fragment (the generated key codec's decode half).
8. THE WITNESS-GATED MIGRATION CHECKPOINT (W9.5 —
   notes/design-guest-verified.md §4 steps 3–5):
   `replayMigrated?` replays an upcast segment ONLY under a witness
   that ACCEPTS through the `WitnessCheck.verifyWitness` seam over the
   DERIVED decoded context (`migrationCtx` — built from the data under
   application, never caller-supplied). Refusal is loud, total, and
   classified: `MigrationRefusal` names the obligation's label + the
   class (`diverged` / `fuelExhausted`), the events are NOT applied,
   and there is no host fallback (owner decision 2). The soundness-
   cited wrapper is `replayMigrated?_ok`: acceptance returns the replay
   AND the claim's denotation over the derived context.

Deliberate exclusions (v1): diff generation (`Dbsp.Difference` — the
engine's job, same as Delta.lean), wire-level upcasting (the
Migration/Snapshot lane's versioned envelope; the attribute ships the
identity upcaster hook), key-uniqueness invariants (the machine's `Inv`
is `True`; the ledger's conservation law needs no uniqueness — it is a
sum over a fixed account universe).
-/

module

public import SchemaLang.CodecValue
public import SchemaLang.WitnessCheck
public import Dbsp.ChangeSpec
public import Machines.Rewind

@[expose] public section

namespace SchemaLang.EventSourced

open Dbsp (Change ChangeInversion)

/-! ## The delta variant -/

/-- The delta variant (the Delta.lean shape, as ONE Lean type over
    abstract row/key): `insert`/`update` carry the full row (v1 is full
    replacement), `remove` carries the key. Event = patch = journal
    entry = undo unit — the canon's delta row. -/
inductive Delta (ρ κ : Type) where
  | insert (row : ρ)
  | update (row : ρ)
  | remove (key : κ)
deriving Repr, BEq, DecidableEq

/-! ## Keyed-table semantics (replay = the I operator) -/

/-- Key-based upsert: replace the FIRST row whose key matches, else
    append. (`insert` and `update` share it — v1 is full replacement,
    the Delta.lean lowering decision.) -/
def upsert (key : ρ → κ) [BEq κ] (row : ρ) : List ρ → List ρ
  | [] => [row]
  | r :: rs => if key r == key row then row :: rs else r :: upsert key row rs

/-- Apply one event to the table. `remove` erases the FIRST
    key-matching row (v1 keyed tables are key-unique by construction —
    `insert` IS upsert, so machine-reachable states never duplicate a
    key; on such tables erase-first = filter). -/
def apply (key : ρ → κ) [BEq κ] (d : Delta ρ κ) (rows : List ρ) : List ρ :=
  match d with
  | .insert row | .update row => upsert key row rows
  | .remove k => rows.eraseIdx (rows.findIdx (fun r => key r == k))

/-- REPLAY — the `I` operator: fold the event list to state. The
    materialization/snapshot-reconstruction reading of the log. -/
def replay (key : ρ → κ) [BEq κ] (log : List (Delta ρ κ)) (init : List ρ) : List ρ :=
  log.foldl (fun st d => apply key d st) init

@[simp] theorem replay_nil (key : ρ → κ) [BEq κ] (init : List ρ) :
    replay key [] init = init := rfl

/-- THE REPLAY LAW (replay-after-append): replaying `log ++ [e]` IS one
    more apply after replaying `log` — the fold reading of `I` of an
    appended delta. -/
theorem replay_snoc (key : ρ → κ) [BEq κ] (log : List (Delta ρ κ))
    (e : Delta ρ κ) (init : List ρ) :
    replay key (log ++ [e]) init = apply key e (replay key log init) := by
  simp [replay, List.foldl_append]

/-! ## The witnessed delta (the ChangeInversion row) -/

/-- The witnessed delta the journal records per event: the position,
    the OLD row (none = the key was absent), the NEW row (none = the
    row is gone). Position-carrying so inversion is EXACT (an
    orderless delete+append could not restore the row's place). -/
structure WDelta (ρ : Type) where
  idx : Nat
  old : Option ρ
  new : Option ρ
deriving Repr, BEq, DecidableEq

/-- Patch by a witnessed delta: positional replace / erase / insert.
    (Matched on the delta directly — the tactic `match` in the law
    proofs needs the literal-constructor arms.) -/
def patchW (rows : List ρ) (d : WDelta ρ) : List ρ :=
  match d with
  | ⟨i, some _, some n⟩ => rows.set i n
  | ⟨i, some _, none⟩ => rows.eraseIdx i
  | ⟨i, none, some n⟩ => rows.insertIdx i n
  | ⟨_, none, none⟩ => rows

/-- Validity: a witnessed delta is meaningful for a table when the
    recorded OLD row is exactly what's at the position (replace/erase),
    or the position is in append range (insert). -/
def validW (rows : List ρ) (d : WDelta ρ) : Prop :=
  match d with
  | ⟨i, some o, some _⟩ => ∃ h : i < rows.length, rows[i]'h = o
  | ⟨i, some o, none⟩ => ∃ h : i < rows.length, rows[i]'h = o
  | ⟨i, none, some _⟩ => i ≤ rows.length
  | ⟨_, none, none⟩ => True

/-- Inversion: swap old and new (rollback = group subtraction, the
    canon's undo row). -/
def invertW (d : WDelta ρ) : WDelta ρ := ⟨d.idx, d.new, d.old⟩

/-- Positional restore: re-inserting at `i` after erasing at `i` is
    `set i` (in bounds — out of bounds, `insertIdx` appends where `set`
    is the identity). (Core has `List.insertIdx_eraseIdx` off-diagonal
    and `List.eraseIdx_insertIdx_self`; the diagonal this shape needs
    is proved here.) -/
theorem insertIdx_eraseIdx_eq_set (l : List ρ) (i : Nat) (a : ρ)
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

/-- The witnessed deltas form a change structure with inversion (the
    ChangeInversion row, instantiated at keyed tables).
    `correct_invert` IS the delta-inverse consistency law the attribute
    re-exports per record (`esDelta_inverse`, via
    `RewindableMachine.revert_left`). -/
instance wDeltaChangeInversion : ChangeInversion (List ρ) (WDelta ρ) where
  patch := patchW
  valid := validW
  invert := invertW
  valid_invert := by
    intro t dt hv
    match dt with
    | ⟨i, some o, some n⟩ =>
      -- the patched table has n at i
      obtain ⟨h, _⟩ := hv
      show ∃ h' : i < (t.set i n).length, (t.set i n)[i]'h' = n
      exact ⟨by rw [List.length_set]; exact h, List.getElem_set_self _⟩
    | ⟨i, some o, none⟩ =>
      -- erasing keeps i in append range
      obtain ⟨h, _⟩ := hv
      show i ≤ (t.eraseIdx i).length
      rw [List.length_eraseIdx, if_pos h]
      exact Nat.le_pred_of_lt h
    | ⟨i, none, some n⟩ =>
      -- the inserted table has n at i
      show ∃ h' : i < (t.insertIdx i n).length, (t.insertIdx i n)[i]'h' = n
      have hl : (t.insertIdx i n).length = t.length + 1 :=
        List.length_insertIdx_of_le_length hv _
      have hv' : i ≤ t.length := hv
      refine ⟨?_, List.getElem_insertIdx_self _⟩
      rw [hl]; omega
    | ⟨_, none, none⟩ => trivial
  correct_invert := by
    intro t dt hv
    match dt with
    | ⟨i, some o, some n⟩ =>
      -- replace, then replace back
      obtain ⟨h, ho⟩ := hv
      show (t.set i n).set i o = t
      rw [List.set_set, ← ho]
      exact List.set_getElem_self h
    | ⟨i, some o, none⟩ =>
      -- erase, then re-insert at i
      obtain ⟨h, ho⟩ := hv
      show (t.eraseIdx i).insertIdx i o = t
      rw [insertIdx_eraseIdx_eq_set _ _ _ h, ← ho]
      exact List.set_getElem_self h
    | ⟨i, none, some n⟩ =>
      -- insert, then erase at i
      show (t.insertIdx i n).eraseIdx i = t
      exact List.eraseIdx_insertIdx_self _
    | ⟨_, none, none⟩ => rfl

/-! ## The witness (what the journal records per event) -/

/-- The delta an event produces at a state: the first key match gives a
    replace/erase witness (the old row recorded); no match gives an
    append/no-op witness. -/
def witnessOf (key : ρ → κ) [BEq κ] (d : Delta ρ κ) (rows : List ρ) : WDelta ρ :=
  match d with
  | .insert row | .update row =>
      if h : rows.findIdx (fun r => key r == key row) < rows.length
      then ⟨rows.findIdx (fun r => key r == key row),
            some rows[rows.findIdx (fun r => key r == key row)], some row⟩
      else ⟨rows.length, none, some row⟩
  | .remove k =>
      if h : rows.findIdx (fun r => key r == k) < rows.length
      then ⟨rows.findIdx (fun r => key r == k),
            some rows[rows.findIdx (fun r => key r == k)], none⟩
      else ⟨rows.length, none, none⟩

/-- Upsert at a found key IS `set` at the found position. -/
theorem upsert_eq_set (key : ρ → κ) [BEq κ] (row : ρ) (rows : List ρ)
    (h : rows.findIdx (fun r => key r == key row) < rows.length) :
    upsert key row rows = rows.set (rows.findIdx (fun r => key r == key row)) row := by
  induction rows with
  | nil => simp at h
  | cons r rs ih =>
    cases hr : (key r == key row) with
    | true =>
      have h0 : (r :: rs).findIdx (fun r' => key r' == key row) = 0 := by
        rw [List.findIdx_cons]
        simp [hr]
      rw [h0]
      show (if key r == key row then row :: rs else r :: upsert key row rs) = row :: rs
      rw [if_pos hr]
    | false =>
      have hs : (r :: rs).findIdx (fun r' => key r' == key row) =
          rs.findIdx (fun r' => key r' == key row) + 1 := by
        rw [List.findIdx_cons]
        simp [hr]
      rw [hs] at h ⊢
      have h' : rs.findIdx (fun r' => key r' == key row) < rs.length := by
        have hlen : (r :: rs).length = rs.length + 1 := rfl
        omega
      have hih := ih h'
      show (if key r == key row then row :: rs else r :: upsert key row rs) =
        (r :: rs).set (rs.findIdx (fun r' => key r' == key row) + 1) row
      rw [if_neg (by simp [hr]), hih, List.set_cons_succ]

/-- Upsert at an absent key IS append. -/
theorem upsert_eq_append (key : ρ → κ) [BEq κ] (row : ρ) (rows : List ρ)
    (h : rows.findIdx (fun r => key r == key row) = rows.length) :
    upsert key row rows = rows ++ [row] := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    cases hr : (key r == key row) with
    | true =>
      have h0 : (r :: rs).findIdx (fun r' => key r' == key row) = 0 := by
        rw [List.findIdx_cons]
        simp [hr]
      rw [h0] at h
      simp at h  -- 0 = (r :: rs).length: contradiction
    | false =>
      have hs : (r :: rs).findIdx (fun r' => key r' == key row) =
          rs.findIdx (fun r' => key r' == key row) + 1 := by
        rw [List.findIdx_cons]
        simp [hr]
      rw [hs] at h
      have h' : rs.findIdx (fun r' => key r' == key row) = rs.length := by
        have hlen : (r :: rs).length = rs.length + 1 := rfl
        omega
      have hih := ih h'
      show (if key r == key row then row :: rs else r :: upsert key row rs) =
        (r :: rs) ++ [row]
      rw [if_neg (by simp [hr]), hih]
      rfl

/-- Firing an event IS patching the table by the recorded delta — the
    `RewindableMachine.action_is_patch` obligation, discharged once
    here for every event-sourced record. -/
theorem apply_eq_patchW (key : ρ → κ) [BEq κ] (d : Delta ρ κ) (rows : List ρ) :
    apply key d rows = patchW rows (witnessOf key d rows) := by
  cases d with
  | insert row =>
      show upsert key row rows = _
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == key row) < rows.length
      · rw [dif_pos h]
        show upsert key row rows = rows.set _ row
        exact upsert_eq_set key row rows h
      · rw [dif_neg h]
        have hi : rows.findIdx (fun r => key r == key row) = rows.length :=
          Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_gt h)
        show upsert key row rows = rows.insertIdx rows.length row
        rw [upsert_eq_append key row rows hi, List.insertIdx_length_self]
  | update row =>
      show upsert key row rows = _
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == key row) < rows.length
      · rw [dif_pos h]
        show upsert key row rows = rows.set _ row
        exact upsert_eq_set key row rows h
      · rw [dif_neg h]
        have hi : rows.findIdx (fun r => key r == key row) = rows.length :=
          Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_gt h)
        show upsert key row rows = rows.insertIdx rows.length row
        rw [upsert_eq_append key row rows hi, List.insertIdx_length_self]
  | remove k =>
      show rows.eraseIdx (rows.findIdx (fun r => key r == k)) = _
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == k) < rows.length
      · rw [dif_pos h]
        rfl
      · rw [dif_neg h]
        show rows.eraseIdx (rows.findIdx (fun r => key r == k)) = rows
        have hi : rows.findIdx (fun r => key r == k) = rows.length :=
          Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_gt h)
        rw [hi]
        exact List.eraseIdx_of_length_le (Nat.le_refl _)

/-- The recorded delta is valid for the state that produced it — the
    `RewindableMachine.deltaOf_valid` obligation, discharged once here. -/
theorem witnessOf_valid (key : ρ → κ) [BEq κ] (d : Delta ρ κ) (rows : List ρ) :
    validW rows (witnessOf key d rows) := by
  cases d with
  | insert row =>
      show validW rows (witnessOf key (.insert row) rows)
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == key row) < rows.length
      · rw [dif_pos h]; exact ⟨h, rfl⟩
      · rw [dif_neg h]; exact Nat.le_refl _
  | update row =>
      show validW rows (witnessOf key (.update row) rows)
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == key row) < rows.length
      · rw [dif_pos h]; exact ⟨h, rfl⟩
      · rw [dif_neg h]; exact Nat.le_refl _
  | remove k =>
      show validW rows (witnessOf key (.remove k) rows)
      simp only [witnessOf]
      by_cases h : rows.findIdx (fun r => key r == k) < rows.length
      · rw [dif_pos h]; exact ⟨h, rfl⟩
      · rw [dif_neg h]; trivial

/-! ## The machine -/

/-- THE EVENT-SOURCED MACHINE: a `Machines.RewindableMachine` whose
    labels are the delta variant, whose states are keyed tables, and
    whose journal deltas are the position witnesses. Every guard is
    `true` (v1: insert/update are upsert, remove is erase-first — total
    by construction), so `runLogged` over this machine never rejects.
    The rewind family (`rewind_runLogged`, `rewind_suffix` — rewind-K =
    undo-K) applies to every specialization. -/
def esMachine (key : ρ → κ) [BEq κ] : Machines.RewindableMachine where
  State := List ρ
  Label := Delta ρ κ
  Inv := fun _ => True
  event := fun d =>
    { guard := fun _ => true
    , action := fun s _ => apply key d s
    , safety := fun _ _ _ => trivial }
  Δ := WDelta ρ
  changeInv := wDeltaChangeInversion
  deltaOf := fun d s _ => witnessOf key d s
  action_is_patch := by
    intro d s _
    exact apply_eq_patchW key d s
  deltaOf_valid := by
    intro d s _
    exact witnessOf_valid key d s

/-! ## The journal codec (generics) -/

/-- The event codec: a tag byte in CTOR ORDER (0 insert / 1 update /
    2 remove — the EnumWire wire-breaking rule: reordering ctors is a
    wire-breaking change) followed by the payload. -/
def encDelta (encR : ρ → List UInt8) (encK : κ → List UInt8) :
    Delta ρ κ → List UInt8
  | .insert r => 0 :: encR r
  | .update r => 1 :: encR r
  | .remove k => 2 :: encK k

/-- The event decoder: the tag byte dispatches; unknown tags reject. -/
def decDelta? (decR : List UInt8 → Option (ρ × List UInt8))
    (decK : List UInt8 → Option (κ × List UInt8)) :
    List UInt8 → Option (Delta ρ κ × List UInt8)
  | 0 :: rest => (decR rest).map fun (r, rs) => (.insert r, rs)
  | 1 :: rest => (decR rest).map fun (r, rs) => (.update r, rs)
  | 2 :: rest => (decK rest).map fun (k, rs) => (.remove k, rs)
  | _ => none

/-- THE EVENT ROUND TRIP, append form: compose the row and key
    round trips through the tag dispatch. -/
theorem decDelta_encDelta_append (encR : ρ → List UInt8) (encK : κ → List UInt8)
    (decR : List UInt8 → Option (ρ × List UInt8))
    (decK : List UInt8 → Option (κ × List UInt8))
    (hR : ∀ (r : ρ) (rest : List UInt8), decR (encR r ++ rest) = some (r, rest))
    (hK : ∀ (k : κ) (rest : List UInt8), decK (encK k ++ rest) = some (k, rest))
    (d : Delta ρ κ) (rest : List UInt8) :
    decDelta? decR decK (encDelta encR encK d ++ rest) = some (d, rest) := by
  cases d <;> simp [encDelta, decDelta?, hR, hK]

/-- The journal codec: a length-prefixed list of events (the Codec
    combinator). -/
def encJournal (encR : ρ → List UInt8) (encK : κ → List UInt8)
    (log : List (Delta ρ κ)) : List UInt8 :=
  Codec.encList (encDelta encR encK) log

/-- The journal decoder. -/
def decJournal? (decR : List UInt8 → Option (ρ × List UInt8))
    (decK : List UInt8 → Option (κ × List UInt8)) (bs : List UInt8) :
    Option (List (Delta ρ κ) × List UInt8) :=
  Codec.decList? (decDelta? decR decK) bs

/-- THE JOURNAL ROUND TRIP, append form: the event log survives the
    wire — the codec law the per-record `esJournal_roundtrip` cites. -/
theorem decJournal_encJournal_append (encR : ρ → List UInt8) (encK : κ → List UInt8)
    (decR : List UInt8 → Option (ρ × List UInt8))
    (decK : List UInt8 → Option (κ × List UInt8))
    (hR : ∀ (r : ρ) (rest : List UInt8), decR (encR r ++ rest) = some (r, rest))
    (hK : ∀ (k : κ) (rest : List UInt8), decK (encK k ++ rest) = some (k, rest))
    (log : List (Delta ρ κ)) (rest : List UInt8) :
    decJournal? decR decK (encJournal encR encK log ++ rest) = some (log, rest) :=
  Codec.decList_encList_append (encDelta encR encK) (decDelta? decR decK)
    (fun d r => decDelta_encDelta_append encR encK decR decK hR hK d r) log rest

/-! ## The flat-scalar `Value` projections (the generated key codec's
    decode half; the boxing direction is the `Value` ctor itself) -/

def unboxBool : Value .bool → Bool | .bool b => b
def unboxU8 : Value .u8 → UInt8 | .u8 v => v
def unboxU16 : Value .u16 → UInt16 | .u16 v => v
def unboxU32 : Value .u32 → UInt32 | .u32 v => v
def unboxU64 : Value .u64 → UInt64 | .u64 v => v
def unboxI8 : Value .i8 → Int8 | .i8 v => v
def unboxI16 : Value .i16 → Int16 | .i16 v => v
def unboxI32 : Value .i32 → Int32 | .i32 v => v
def unboxI64 : Value .i64 → Int64 | .i64 v => v
def unboxString : Value .string → String | .string s => s

/-! ## The witness-gated migration checkpoint (W9.5 — design-guest-verified §4)

The consumer side of the fifth obligation tier: replaying an old log
through a migration is GATED on the migration's witness. The flow is
§4 steps 3–5 exactly, at the Lean-data level (the byte-level decode —
envelope version check, `decJournal?`, `decWitnessFor?` — is W9.1's
proved codec, exercised at the ledger dogfood): upcast the committed
segment, derive the decoded context from the MIGRATED data itself,
check the certificate through the `WitnessCheck.verifyWitness` seam,
and only then `replay`. ONE refusal path: bad witness, false claim,
unresolvable field, exhausted fuel — all refuse, loudly, naming the
obligation's label and the class; the events are not applied; no
silent skip, no host fallback (owner decision 2). -/

/-- The row a delta carries (insert/update: the full-row payload — the
    Delta.lean v1 lowering; remove carries a key, no post-row to
    certify). The migration checkpoint's decoded context ranges over
    exactly these. -/
def Delta.row? {ρ κ : Type} : Delta ρ κ → Option ρ
  | .insert r | .update r => some r
  | .remove _ => none

/-- THE REFUSAL (design §4 step 5's typed fault — the ONE refusal
    path): the obligation's label + the class. `diverged`: the
    certificate's claim does not hold of the derived decoded context
    (a tampered or stale witness, a false claim, an unresolvable field
    — `WitnessCheck.checkWitness_fuel_sufficient` proves the verdict is
    fuel-free at sufficient fuel, so this class is PERMANENT: no retry
    could change it). `fuelExhausted`: the artifact's shipped cap is
    below the checker's structural minimum (`WitnessCheck.fuelNeed`) —
    exhaustion IS refusal (§7.3), and
    `WitnessCheck.checkWitness_eq_false_of_fuel_lt` proves the
    exhausted run could not have accepted (the classes never blur). -/
inductive MigrationRefusal where
  | diverged (label : String)
  | fuelExhausted (label : String)

deriving Repr, BEq, DecidableEq

/-- The refusal, rendered LOUD: the obligation's label and the class,
    named (the operator-facing fault text — §4 step 5's "availability
    impact is observable, not silent"). -/
def MigrationRefusal.render : MigrationRefusal → String
  | .diverged label =>
      s!"migration REFUSED — obligation `{label}`: the witness's claim diverges \
        from the decoded segment (tampered/stale certificate, false claim, or \
        unresolvable field); the events are NOT applied"
  | .fuelExhausted label =>
      s!"migration REFUSED — obligation `{label}`: witness fuel exhausted (the \
        shipped cap is below the checker's structural minimum — §7.3: no retry, \
        a claim-shape finding); the events are NOT applied"

/-- The decoded context the checkpoint certifies against, DERIVED from
    the data under application — never caller-supplied (a witness
    checked against rows other than the ones under application is
    vacuous). `init` is the migrated BASE row (the chain claim's
    initial row — the segment's pre-state, shipped migrated); the
    log is the upcast segment's full-row payloads in order. -/
def migrationCtx {ρ₁ κ₁ ρ₂ κ₂ : Type} {fs : List Field} (rowOf : ρ₂ → RowVals fs)
    (upcast : Delta ρ₁ κ₁ → Delta ρ₂ κ₂) (init : ρ₂) (log : List (Delta ρ₁ κ₁)) :
    WitnessCheck.RowValsP :=
  ⟨fs, rowOf init, ((log.map upcast).filterMap Delta.row?).map rowOf⟩

/-- THE APPLY-GATE (design §4 steps 3–5): replay the migrated segment
    ONLY under an accepting witness. Upcast the committed (old-schema)
    log, derive the decoded context from the migrated data, classify
    the fuel against `WitnessCheck.fuelNeed`, check the certificate
    through THE SEAM (`WitnessCheck.verifyWitness` — the W9.6 mount
    point), and only then `replay`. Refusal is loud, total, and never
    downgraded (§7.1): the events are NOT applied and the verdict
    names the obligation's label + the class. -/
def replayMigrated? {ρ₁ κ₁ ρ₂ κ₂ : Type} {fs : List Field} (key : ρ₂ → κ₂)
    [BEq κ₂] (rowOf : ρ₂ → RowVals fs) (upcast : Delta ρ₁ κ₁ → Delta ρ₂ κ₂)
    (w : Witness.Witness) (init : ρ₂) (log : List (Delta ρ₁ κ₁))
    (state : List ρ₂) : Except MigrationRefusal (List ρ₂) :=
  if w.fuel < WitnessCheck.fuelNeed w.claim then .error (.fuelExhausted w.label)
  else if WitnessCheck.verifyWitness w (migrationCtx rowOf upcast init log) then
    .ok (replay key (log.map upcast) state)
  else .error (.diverged w.label)

/-- The fuel class, pinned: a below-minimum shipped cap refuses with
    `fuelExhausted`, naming the obligation — BEFORE any checking (the
    §7.3 exhaustion path). -/
theorem replayMigrated?_fuelExhausted {ρ₁ κ₁ ρ₂ κ₂ : Type} {fs : List Field}
    (key : ρ₂ → κ₂) [BEq κ₂] (rowOf : ρ₂ → RowVals fs)
    (upcast : Delta ρ₁ κ₁ → Delta ρ₂ κ₂) (w : Witness.Witness) (init : ρ₂)
    (log : List (Delta ρ₁ κ₁)) (state : List ρ₂)
    (h : w.fuel < WitnessCheck.fuelNeed w.claim) :
    replayMigrated? key rowOf upcast w init log state =
      .error (.fuelExhausted w.label) := by
  unfold replayMigrated?
  rw [if_pos h]

/-- The divergence class, pinned: sufficient fuel + a refusing seam
    verdict refuses with `diverged`, naming the obligation. -/
theorem replayMigrated?_diverged {ρ₁ κ₁ ρ₂ κ₂ : Type} {fs : List Field}
    (key : ρ₂ → κ₂) [BEq κ₂] (rowOf : ρ₂ → RowVals fs)
    (upcast : Delta ρ₁ κ₁ → Delta ρ₂ κ₂) (w : Witness.Witness) (init : ρ₂)
    (log : List (Delta ρ₁ κ₁)) (state : List ρ₂)
    (hf : ¬ w.fuel < WitnessCheck.fuelNeed w.claim)
    (hc : WitnessCheck.verifyWitness w (migrationCtx rowOf upcast init log) = false) :
    replayMigrated? key rowOf upcast w init log state =
      .error (.diverged w.label) := by
  unfold replayMigrated?
  rw [if_neg hf, if_neg (by simp [hc])]

/-- THE ACCEPTANCE THEOREM (the soundness-cited wrapper): an accepting
    gate returns the replay of the migrated segment AND the
    certificate's claim HOLDS over the derived decoded context — the
    applied rows are guest-certified per step (cites the seam's
    `WitnessCheck.verifyWitness_sound`; the compiled-reading bridge is
    `WitnessCheck.WHolds.chain_validates`). -/
theorem replayMigrated?_ok {ρ₁ κ₁ ρ₂ κ₂ : Type} {fs : List Field}
    (key : ρ₂ → κ₂) [BEq κ₂] (rowOf : ρ₂ → RowVals fs)
    (upcast : Delta ρ₁ κ₁ → Delta ρ₂ κ₂) (w : Witness.Witness) (init : ρ₂)
    (log : List (Delta ρ₁ κ₁)) (state : List ρ₂) (st : List ρ₂)
    (h : replayMigrated? key rowOf upcast w init log state = .ok st) :
    st = replay key (log.map upcast) state ∧
      WitnessCheck.WHolds w.claim (rowOf init)
        (migrationCtx rowOf upcast init log).log := by
  unfold replayMigrated? at h
  split at h
  · simp at h
  · split at h
    · rename_i _hfuel hcheck
      exact ⟨(Except.ok.inj h).symm,
        WitnessCheck.verifyWitness_sound _ _ hcheck⟩
    · simp at h

end SchemaLang.EventSourced

end -- @[expose] public section
