/-
# SchemaLang.Change — the ONE shared change variant (R1 consolidation)

THE canonical delta type of the whole stack: `EventSourced.Delta` —
`insert`/`update` carry the FULL row (v1 full replacement), `remove`
carries the key. Event = patch = journal entry = undo unit — the
canon's delta row. One inductive over abstract row/key types; the
per-record "derivation" is specialization, not re-implementation.

WHY A SEPARATE MODULE (the constraint-14 rule, notes/
w5-4-module-migration.md): the type + its keyed-table applicator must
sit in the import graph BELOW both consumers —

- `SchemaLang.EventSourced` (the journaling lane: replay, witnesses,
  codecs, the machine) — mathlib-carrying via Dbsp/Machines;
- `SchemaLang.Update2` (the update lane: the lowering correspondence
  `apply2_eq_foldDeltas` + the applicator bridge
  `applyRowDelta_eq_apply`) — whose closure must stay mathlib-FREE
  (it is publicly consumed by `Meta.Reflect`, hence by the legacy
  registries: a mathlib name leaked there collides with
  feature-flags' own `Flag`).

So the shared shape + the first-match keyed semantics live HERE
(zero imports, core-only), both lanes import this module, and the
FULL NAMES (`SchemaLang.EventSourced.Delta/apply/upsert/replay`) are
unchanged — the namespace rides the declaration site, not the file.

Deliberate exclusions: the witnessed deltas (`WDelta`), the journal
codec, and the machine stay in EventSourced (they need the Dbsp/
Machines cone); this file is the type + the `I`-operator fold and
nothing else.
-/

module

@[expose] public section

namespace SchemaLang.EventSourced

/-! ## The delta variant -/

/-- THE delta variant (the Delta.lean shape, as ONE Lean type over
    abstract row/key): `insert`/`update` carry the full row (v1 is full
    replacement), `remove` carries the key. Event = patch = journal
    entry = undo unit — the canon's delta row. THE canonical change
    variant (R1): the update lane's `RowDelta` (Update2.lean) is this
    type at `RowVals fs`/`FieldVal`; the emitted `dbsp::Change`
    contract (Delta.lean's emitter) is its Rust face. -/
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

end SchemaLang.EventSourced

end -- @[expose] public section
