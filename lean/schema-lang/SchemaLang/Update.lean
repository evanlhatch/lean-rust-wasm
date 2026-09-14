/-
# SchemaLang.Update — the update concept (SPEC-core §3, demoted to v1)

An update is the ONLY action concept: a NAMED, TOTAL, order-free batch
transformation of one table's rows. The flatland demotion:

- **The guard is part of the body** — a `VExpr .bool` over the table's
  fields; a row the guard refuses is untouched. There is no separate
  gate/trigger/rate machinery (SPEC §6's dissolution table).
- **The write is one column assignment** — the value expression is a
  `VExpr` of the WRITTEN COLUMN'S OWN TYPE (the GADT index: a string
  column cannot take a u64 expression — elaboration rejects it).
- **Reads are DERIVED, never declared** (SPEC §3): `readsOf` folds both
  expressions for their `.col` references. Nothing here is hand-listed.
- **Batch semantics** (SPEC law 1): `applyRow` consults only the
  ORIGINAL row — guard and value both read pre-update state; no
  cascade WITHIN an update. Cascade is across updates, at the tick.
- **The two-channel duality, pinned at the row level** (SPEC §4):
  `ColPath.set_commute_same` = later-wins (overwrite channels are NOT
  group elements — revert needs the old value); `ColPath.set_commute_disjoint`
  = disjoint-column updates commute in either order (the order-free
  composition law). Both are kernel-checked THERE, not asserted.

The enforcement ladder hook: `selfReading` — the DERIVED linearity
classification. An update whose value expression reads the written
column is nonlinear (its journal needs the old value); one that doesn't
is linear (delta-only). This is the flatland "old_values capture policy
is COMPUTED" — the derivation the review's "armed but unfired"
determinism machinery anticipated.

Execution substrate: `RowVals`/`ColPath`/`VExpr` (SchemaLang.Validate) —
the same row model the validators execute over, so the oracle reading
and the compiled reading share one semantics.
-/

import SchemaLang.Item
import Machines.Dsl
import SchemaLang.Validate

namespace SchemaLang

/-! ## Derived reads (the fold — never hand-listed) -/

/-- A read = a `.col` reference's name. THE derivation: every consumer
    (the tick's read/write graph, the journal's old-values policy, the
    docs) folds this — none may hand-list a column. -/
def VExpr.reads {fs : List Field} : {t : Ty} → VExpr fs t → List String
  | _, .col n _ => [n]
  | _, .lit _ => []
  | _, .gt a b => a.reads ++ b.reads
  | _, .eq a b => a.reads ++ b.reads
  | _, .and a b => a.reads ++ b.reads
  | _, .strlen e => e.reads

/-! ## The update item -/

/-- One update over table `fs`, writing field `f`. Indexed by BOTH —
    the value expression's type is the written column's type by
    construction. The write PATH rides (data, resolved by the
    registration command's `HasCol` instance search at elaboration —
    a write to a column NOT on the table has no instance and fails to
    elaborate; `Validate.lean`'s doctrine). -/
structure UpdateItem (fs : List Field) (f : Field) where
  /-- The update's name (load-bearing: provenance in the journal). -/
  name : String
  /-- The guard: rows failing it are untouched (part of the body —
      not a separate concept). -/
  guard : VExpr fs .bool
  /-- The new value for the written column. -/
  value : VExpr fs f.ty
  /-- The structural write path (the elaboration-checked extraction
      route — data, not a dictionary). -/
  writePath : ColPath f.name f.ty fs

/-- The DERIVED read set (guard + value, deduped, registration order). -/
def UpdateItem.reads {fs : List Field} {f : Field} (u : UpdateItem fs f) :
    List String :=
  (u.guard.reads ++ u.value.reads).eraseDups

/-- The DERIVED write set (one column — the written field). -/
def UpdateItem.writes {fs : List Field} {f : Field} (_u : UpdateItem fs f) :
    List String :=
  [f.name]

/-- The DERIVED linearity classification: does the value expression
    read the written column? `false` = linear (delta-only — the journal
    needs no old value); `true` = nonlinear (overwrite: the journal
    carries S0). COMPUTED, not declared — the capture policy's input. -/
def UpdateItem.selfReading {fs : List Field} {f : Field}
    (u : UpdateItem fs f) : Bool :=
  u.value.reads.contains f.name

/-! ## The write: `ColPath.set` -/

/-- Set the path's field to `v` — the structural write. Both the
    overwritten and the untouched fields ride the same constructor
    spine (no rebuild of unrelated fields). -/
def ColPath.set {n : String} {t : Ty} : {fs : List Field} →
    ColPath n t fs → RowVals fs → Value t → RowVals fs
  | _, .here, .cons _ vs, v => .cons v vs
  | _, .there p, .cons w vs, v => .cons w (p.set vs v)

/-- The row-level semantics: guard first (on the ORIGINAL row), then
    the value (ALSO from the original row — batch: no intra-update
    cascade), then the write. A refused row passes through untouched. -/
def UpdateItem.applyRow {fs : List Field} {f : Field}
    (u : UpdateItem fs f) (row : RowVals fs) : RowVals fs :=
  if validates u.guard row then
    u.writePath.set row (evalV u.value row)
  else row

/-- The batch semantics: TOTAL, order-free over the table (each row is
    independent — v1 updates read no other row; the map IS the
    order-freedom, structurally). -/
def UpdateItem.apply {fs : List Field} {f : Field}
    (u : UpdateItem fs f) (rows : List (RowVals fs)) : List (RowVals fs) :=
  rows.map u.applyRow

/-! ## The two-channel duality, pinned (SPEC §4) -/

/-- LATER-WINS (the overwrite channel): two writes to the SAME column
    compose by overwriting — the second survives. NOT a group (revert
    needs the old value — the journal carries S0 for self-reading
    updates, the `selfReading` policy). -/
theorem ColPath.set_commute_same {n : String} {t : Ty} : ∀ {fs : List Field}
    (p : ColPath n t fs) (row : RowVals fs) (v w : Value t),
    p.set (p.set row v) w = p.set row w := by
  intro fs p
  induction p with
  | here => intro row v w; cases row; simp [set]
  | there p ih =>
      intro row v w
      cases row with
      | cons a vs => simp only [set]; rw [ih vs v w]

/-- DISJOINT writes commute: two updates writing DIFFERENT columns
    (different column NAMES — the name determines the position, the
    HasCol priority) compose in either order. The order-free
    composition law the tick's cascade relies on. -/
theorem ColPath.set_commute_disjoint {n₁ n₂ : String} {t₁ t₂ : Ty} :
    ∀ {fs : List Field} (p₁ : ColPath n₁ t₁ fs) (p₂ : ColPath n₂ t₂ fs),
      n₁ ≠ n₂ → ∀ (row : RowVals fs) (v₁ : Value t₁) (v₂ : Value t₂),
        p₂.set (p₁.set row v₁) v₂ = p₁.set (p₂.set row v₂) v₁ := by
  intro fs
  induction fs with
  | nil => intro p₁ p₂ _; cases p₁ <;> cases p₂
  | cons f fs ih =>
      intro p₁ p₂ hne row v₁ v₂
      cases p₁ with
      | here =>
          cases p₂ with
          | here => exact absurd rfl hne
          | there _ => cases row; simp [set]
      | there p₁' =>
          cases p₂ with
          | here => cases row; simp [set]
          | there p₂' =>
              cases row with
              | cons a vs =>
                  simp only [set]
                  rw [ih p₁' p₂' hne vs v₁ v₂]
 
/-! ## The registered-update wrapper -/

/-- The registered-update wrapper: the table's fields + the written
    field + the update (the GADT indices ride the existentials — the
    registry is a plain list of these). -/
structure SomeUpdate where
  fields : List Field
  field : Field
  update : UpdateItem fields field

/-- Execute against a row whose field list CLAIMS to be the update's —
    the same guarded-cast discipline as `InvariantItem.checkOn` (data
    equality carries the proof; a foreign row refuses, `false`). -/
def SomeUpdate.applyRow (u : SomeUpdate) {fs : List Field}
    (row : RowVals fs) : RowVals fs :=
  if h : fs = u.fields then
    (h ▸ u.update.applyRow (h ▸ row) : RowVals fs)
  else row

/-! ## The tick — the four phases as a machine (SPEC §7, v1) -/

/-- The tick's phases: settle (external deltas + lifecycle) → cascade
    (the updates over changed rows, to fixpoint) → resolve (the declared
    deterministic function) → commit (the journal's two artifacts). v1:
    acyclic single-pass cascade (no SCC loops — the Dag is empty by
    construction, single-table updates) — the STAGE DISCIPLINE is what
    the machine pins. `stale` is the state no transition produces (the
    invariant excludes it — the non-vacuity witness, OrderMachine's
    pattern). -/
inductive TickState where
  | idle | settled | cascaded | resolved | committed | stale
deriving Repr, BEq, DecidableEq, Inhabited

-- (plain comment: doc comments cannot precede machine!)
machine! tick where
  State: TickState
  Inv: fun s => s ≠ .stale
  event: settle guard: (fun s => s = .idle) action: (fun _ _ => .settled)
  event: cascade guard: (fun s => s = .settled) action: (fun _ _ => .cascaded)
  event: resolve guard: (fun s => s = .cascaded) action: (fun _ _ => .resolved)
  event: commit guard: (fun s => s = .resolved) action: (fun _ _ => .committed)
  event: reset guard: (fun _ => true) action: (fun _ _ => .idle)

instance : DecidablePred tick.Inv := fun s =>
  match s with
  | .stale => isFalse (fun h => h rfl)
  | .idle => isTrue (fun h => TickState.noConfusion h)
  | .settled => isTrue (fun h => TickState.noConfusion h)
  | .cascaded => isTrue (fun h => TickState.noConfusion h)
  | .resolved => isTrue (fun h => TickState.noConfusion h)
  | .committed => isTrue (fun h => TickState.noConfusion h)

/-- The phase rank: idle 0 → settled 1 → cascaded 2 → resolved 3 →
    committed 4 (stale rides at 0 — unreachable). -/
def TickState.rank : TickState → Nat
  | .idle => 0 | .settled => 1 | .cascaded => 2
  | .resolved => 3 | .committed => 4 | .stale => 0

/-- Every non-reset transition strictly increases the rank (the tick is
    a DAG whose only cycles pass through `reset`). -/
theorem tick_rank_advances (s : TickState) (l : tick.Label)
    (hnr : l ≠ .reset) (w : (tick.event l).guard s = true) :
    s.rank < ((tick.event l).action s w).rank := by
  cases s <;> cases l <;>
    simp [tick, tick.spec, TickState.rank] at hnr w ⊢ <;>
    omega

theorem tick_rank_advances_tr (s s' : TickState) (l : tick.Label)
    (htr : tick.tr s l s') (hnr : l ≠ .reset) :
    s.rank < s'.rank := by
  obtain ⟨w, hact⟩ := htr
  have h := tick_rank_advances s l hnr w
  rw [hact] at h
  exact h

/-- Committed is terminal: only `reset` leaves it (a committed tick is
    history — the journal, not mutable state). -/
theorem tick_committed_only_reset (s s' : TickState) (l : tick.Label)
    (htr : tick.tr s l s') (hd : s = .committed) : l = .reset := by
  subst hd
  obtain ⟨w, hw⟩ := htr
  cases l <;> simp [tick, tick.spec] at w ⊢

/-- The phases fire strictly in order (the executable shadow). -/
theorem tick_reject_skip : tick.run .idle [.cascade] = none := rfl

theorem tick_happy : tick.run .idle [.settle, .cascade, .resolve, .commit]
    = some ([(.settle, .settled), (.cascade, .cascaded),
             (.resolve, .resolved), (.commit, .committed)], .committed) :=
  rfl

/-- The emitted table (the driver's data — the `Machine.matchArms`
    discipline). -/
def tickTrans : List (tick.Label × TickState × TickState) :=
  [ (.settle, .idle, .settled)
  , (.cascade, .settled, .cascaded)
  , (.resolve, .cascaded, .resolved)
  , (.commit, .resolved, .committed)
  , (.reset, .idle, .idle)
  , (.reset, .settled, .idle)
  , (.reset, .cascaded, .idle)
  , (.reset, .resolved, .idle)
  , (.reset, .committed, .idle)
  , (.reset, .stale, .idle) ]

/-- The structural reading (the emission theorem's subject). -/
def tickTableStep? : tick.Label → TickState → Option TickState
  | .settle, .idle => some .settled
  | .cascade, .settled => some .cascaded
  | .resolve, .cascaded => some .resolved
  | .commit, .resolved => some .committed
  | .reset, _ => some .idle
  | _, _ => none

/-- The emitted table IS the machine. -/
theorem tickTableStep?_eq_step? (e : tick.Label) (s : TickState) :
    tickTableStep? e s = tick.step? s e := by
  cases s <;> cases e <;> simp [tickTableStep?, tick, tick.spec]

end SchemaLang
