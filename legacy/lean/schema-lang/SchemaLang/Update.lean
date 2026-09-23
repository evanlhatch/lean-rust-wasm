/-
# SchemaLang.Update — the row-level law module (v2's substrate)

v1→v2 (the owner's canon row, 2026): `SchemaLang.Update2` is THE row
— a business rule / batch update is a `schema_update` on the v2
surface (multi-SET / INSERT / DELETE, keyed, six kernel-checked laws).
The v1 update surface (`UpdateItem`/`SomeUpdate`/`cascade2`/the
`UpdatePure`/`NonInterfering` class pair) was DELETE-AND-SUPERSEDED:
the cascade's composition laws now live at the v2 application
semantics (TickCascade cites `Update2.apply2_comm` through its
`Dbsp.DeltaSystem` instance), the authoring surface registers the v2
row for EVERY `schema_update` (`Meta.Register.Updates`), the emitter
consumes `update2ItemExt` (`Emit.GenCtx.updates2`), and the trace
oracle's batches ride `SomeUpdate2` (Trace.lean).

What remains here — the ROW LAYER, consumed by Update2:
- `VExpr.reads` — the DERIVED reads fold (the only folds' seed).
- `ColPath.set` — the structural write (the overwrite channel).
- The two-channel duality, pinned (SPEC §4): `set_commute_same`
  (later-wins) and `set_commute_disjoint` (disjoint columns commute
  in either order) — both kernel-checked HERE, consumed by Update2's
  `applySets_perm`.
- The reads-congruence family (write-locality + the raw/checked
  evaluators' neutrality): `get_set_neutral`,
  `evalV_set_neutral`, `evalRaw_set_neutral` — Update2's
  `evalV_applySets`/`validates_applySets`/`RowTmpl.eval_*` consume
  them. Moved from TickCascade at W8.3 (TickCascade drags
  Dbsp.Effects; Update2 stays mathlib-free).

Also still here (kept compiling, per the migration wave's scope): the
tick STAGE machine (`TickState` + `machine! tick` — SPEC §7, v1, the
four phases as a machine). It pins the stage discipline the emitter's
row-transform half compiles; it has no external consumers.
-/

module

public import SchemaLang.Item
public import Machines.Dsl
public import SchemaLang.Validate

@[expose] public section

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
  | _, .not e => e.reads

/-! ## The write: `ColPath.set` -/

/-- Set the path's field to `v` — the structural write. Both the
    overwritten and the untouched fields ride the same constructor
    spine (no rebuild of unrelated fields). -/
def ColPath.set {n : String} {t : Ty} : {fs : List Field} →
    ColPath n t fs → RowVals fs → Value t → RowVals fs
  | _, .here, .cons _ vs, v => .cons v vs
  | _, .there p, .cons w vs, v => .cons w (p.set vs v)

/-! ## The two-channel duality, pinned (SPEC §4) -/

/-- LATER-WINS (the overwrite channel): two writes to the SAME column
    compose by overwriting — the second survives. NOT a group (revert
    needs the old value — the journal carries S0 for self-reading
    updates). -/
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
 

/-! ## The reads-congruence family (moved from TickCascade at W8.3) -/

-- the row-level write-locality + reads-congruence lemmas live at the
-- ROW layer (they mention no cascade); TickCascade's composition laws
-- and Update2's v2 laws both consume them through this module. Names
-- unchanged. The `selfReading`/linearity derivation lives on the v2
-- surface now (`Update2Item`'s SET clauses: a clause whose value reads
-- its own column is nonlinear).

/-! ## The reads-membership simp family -/

@[simp] theorem VExpr.not_mem_reads_col {n m : String} {s : List Field} {t : Ty}
    {p : ColPath m t s} : n ∉ (VExpr.col m p).reads ↔ n ≠ m := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_lit {n : String} {s : List Field} (v : UInt64) :
    n ∉ (VExpr.lit v : VExpr s .u64).reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_gt {n : String} {s : List Field} (a b : VExpr s .u64) :
    n ∉ (VExpr.gt a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_eq {n : String} {s : List Field} (a b : VExpr s .u64) :
    n ∉ (VExpr.eq a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_and {n : String} {s : List Field} (a b : VExpr s .bool) :
    n ∉ (VExpr.and a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_strlen {n : String} {s : List Field} (e : VExpr s .string) :
    n ∉ (VExpr.strlen e).reads ↔ n ∉ e.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_not {n : String} {s : List Field} (e : VExpr s .bool) :
    n ∉ (VExpr.not e).reads ↔ n ∉ e.reads := by
  simp [VExpr.reads]

/-! ## Write locality -/

/-- A write to column `n₁` does not change ANY OTHER column's read. -/
theorem ColPath.get_set_neutral {n₁ n : String} {t₁ t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (p₁ : ColPath n₁ t₁ fs),
      n ≠ n₁ → ∀ (row : RowVals fs) (v : Value t₁),
        p.get (p₁.set row v) = p.get row := by
  intro fs
  induction fs with
  | nil => intro p _ _; cases p
  | cons f fs ih =>
      intro p p₁ hne row v
      cases p with
      | here =>
          cases p₁ with
          | here => exact absurd rfl hne
          | there p₁' => cases row; simp [ColPath.set, ColPath.get]
      | there p' =>
          cases p₁ with
          | here => cases row; simp [ColPath.set, ColPath.get]
          | there p₁' =>
              cases row with
              | cons a vs => simp only [ColPath.set]; exact ih p' p₁' hne vs v

/-- An expression whose reads avoid column `n₁` evaluates the same
    before and after a write to `n₁` (the reads-congruence). -/
theorem VExpr.evalV_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty} :
    ∀ {t : Ty} (e : VExpr fs t) (p₁ : ColPath n₁ t₁ fs) (_hne : n₁ ∉ e.reads)
      (row : RowVals fs) (v : Value t₁),
      evalV e (p₁.set row v) = evalV e row := by
  intro t e
  induction e with
  | col n p =>
      intro p₁ hne row v
      have hnn : n₁ ≠ n := by
        simpa using hne
      exact ColPath.get_set_neutral p p₁ hnn.symm row v
  | lit _ => intro _ _ _ _; rfl
  | gt a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | eq a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | and a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | «strlen» e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp [evalV, ih p₁ he row v]
  | not e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp [evalV, ih p₁ he row v]

/-- The RAW evaluator's congruence, at the GENERAL index (W3.4): an
    expression whose reads avoid column `n₁` evaluates the same before
    and after a write to `n₁`. The general `t` index is what unblocks
    `induction` — the fixed-index `.bool` slice barred it, forcing the
    old proof-carrying-def workaround (`evalBNeutral`; retired, with
    `evalU_set_neutral`, into this ONE theorem). The `strlen` case's
    operand is a field ref (the only `.string`-typed shape), so it
    closes by `cases` + `get_set_neutral`, no induction hypothesis. -/
theorem VExpr.evalRaw_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty} :
    ∀ {t : Ty} (e : VExpr fs t) (p₁ : ColPath n₁ t₁ fs) (_hne : n₁ ∉ e.reads)
      (row : RowVals fs) (v : Value t₁),
      evalRaw e (p₁.set row v) = evalRaw e row := by
  intro t e
  induction e with
  | col n p =>
      intro p₁ hne row v
      have hnn : n₁ ≠ n := by
        simpa using hne
      have := ColPath.get_set_neutral p p₁ hnn.symm row v
      simp only [evalRaw, this]
  | lit _ => intro _ _ _ _; rfl
  | gt a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | eq a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | and a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | «strlen» e _ih =>
      intro p₁ hne row v
      -- the operand is a field ref (the only `.string` shape)
      cases e with
      | col n p =>
          have hnn : n₁ ≠ n := by
            simpa using hne
          have := ColPath.get_set_neutral p p₁ hnn.symm row v
          simp only [evalRaw, this]
  | not e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [ih p₁ he row v]

/-! ## The tick — the four phases as a machine (SPEC §7, v1) -/

/-- The tick's phases: settle (external deltas + lifecycle) → cascade
    (the updates over changed rows, to fixpoint) → resolve (the declared
    deterministic function) → commit (the journal's two artifacts). v1:
    acyclic single-pass cascade (no SCC loops — the dependency graph is
    empty by construction, single-table updates) — the STAGE DISCIPLINE is what
    the machine pins. `stale` is the state no transition produces (the
    invariant excludes it — the non-vacuity witness, OrderMachine's
    pattern). -/
inductive TickState where
  | idle | settled | cascaded | resolved | committed | stale
deriving Repr, BEq, DecidableEq, Inhabited

-- (plain comment: doc comments cannot precede machine!)
/-- The phase rank: idle 0 → settled 1 → cascaded 2 → resolved 3 →
    committed 4 (stale rides at 0 — unreachable). -/
def TickState.rank : TickState → Nat
  | .idle => 0 | .settled => 1 | .cascaded => 2
  | .resolved => 3 | .committed => 4 | .stale => 0

machine! tick where
  State: TickState
  Inv: fun s => s ≠ .stale
  rank: TickState.rank rewind: reset
  event: settle guard: (fun s => s = .idle) action: (fun _ _ => .settled)
  event: cascade guard: (fun s => s = .settled) action: (fun _ _ => .cascaded)
  event: resolve guard: (fun s => s = .cascaded) action: (fun _ _ => .resolved)
  event: commit guard: (fun s => s = .resolved) action: (fun _ _ => .committed)
  event: reset guard: (fun _ => true) action: (fun _ _ => .idle)

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

end SchemaLang
