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
  /-- The volatile func references, as the registration's scan STORED
      them (`volatileSchemaFns` in `SchemaLang.Meta.Reflect` — the ONLY
      legitimate writer of this field; like `reads`, never hand-listed
      in spec data). The scan is the registration's first-line gate: a
      nonempty scan FAILS elaboration, so a registered row always
      carries `[]` — the field is the scan's decided fact, and
      `UpdatePure.volatileFree` reads it. Hand-constructed items (test
      mirrors, the registry default) default `[]` — pure by data. -/
  volatileRefs : List String := []

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

/-! ## The law classes — the COMPOSABLE purity/non-interference locks

Flatland TOOLKIT 4.1 doctrine: instance search IS proof assembly. The
registration's syntactic scan (`volatileSchemaFns`) stays the FIRST
line of defense — a `volatile` fn in a `schema_update` term fails at
the command. The classes are the COMPOSITION-level lock: `schema_update`
EMITS the `UpdatePure` instance at registration (the scan's decided
fact, discharged `rfl` against the stored `volatileRefs` — if the gate
ever stored a nonempty scan, the emitted proof FAILS to elaborate), and
consumers (`cascade2`) take legality as INSTANCE BINDERS — a composite
assembled from a volatile or interfering part is UNCONSTRUCTIBLE, no
re-scan at the firing site.

Scope (v1, honest): updates compose only through the CASCADE, so the
composition laws live at the cascade level — `cascade2`'s instance
binders ARE the `Pure g → Pure f → Pure (g ∘ f)` shape (legality of the
composite = the conjunction of the steps' instances, assembled by
search), and `NonInterfering.symm` is the pair-level composition law.
-/

/-- THE PURE LOCK: the update's terms reference only pure (non-volatile)
schema fns. The registration command constructs the instance (the scan
runs there); hand-written instances are `⟨rfl⟩` against the stored
data. -/
class UpdatePure (fs : List Field) (f : Field)
    (u : UpdateItem fs f) : Prop where
  /-- The stored volatile-ref set is empty (the scan's decided fact). -/
  volatileFree : u.volatileRefs = [] := by decide

/-- The REGISTRATION-ROUTE constructor: an item built by `mk` whose
    `volatileRefs` slot is literally `[]` is pure — the `rfl` reduces
    on the ctor with the binders still abstract. The `schema_update`
    command Qq-quotes this as the emitted instance's proof (W2.1): a
    statically elaborated proof can only discharge against a NAMED
    lemma — a raw `⟨rfl⟩` inside a quotation sees opaque antiquotes
    and cannot reduce. -/
theorem UpdatePure.emptyScan {fs : List Field} {f : Field} {n : String}
    {g : VExpr fs .bool} {v : VExpr fs f.ty} {p : ColPath f.name f.ty fs} :
    UpdatePure fs f (UpdateItem.mk n g v p []) :=
  ⟨rfl⟩

/-- THE NON-INTERFERENCE LOCK — literally `cascade_two_commute`'s
hypothesis set as ONE class: neither update's TERMS (guard or value)
read the other's written column, and the write columns differ. Every
fact rides the DERIVED reads (never hand-listed); concrete updates
discharge at construction via the slot's autoParam default (TOOLKIT
4.2's ladder, the `decide` rung — decidable membership over the derived
lists; the full ladder lives in `Proofkit.Ladder`). -/
class NonInterfering (fs : List Field) (f₁ f₂ : Field)
    (u₁ : UpdateItem fs f₁) (u₂ : UpdateItem fs f₂) : Prop where
  /-- The four non-membership facts + the distinct write columns. -/
  noOverlap :
    f₂.name ∉ u₁.guard.reads ∧ f₂.name ∉ u₁.value.reads
      ∧ f₁.name ∉ u₂.guard.reads ∧ f₁.name ∉ u₂.value.reads
      ∧ f₁.name ≠ f₂.name := by decide

/-- The class → `cascade_two_commute`'s hypotheses: the class IS the
hypothesis set — the extraction is the identity (the derived reads earn
the composition: no hand-listing, no re-derivation). -/
theorem NonInterfering.cascadeHyps {fs : List Field} {f₁ f₂ : Field}
    {u₁ : UpdateItem fs f₁} {u₂ : UpdateItem fs f₂}
    (h : NonInterfering fs f₁ f₂ u₁ u₂) :
    f₂.name ∉ u₁.guard.reads ∧ f₂.name ∉ u₁.value.reads
      ∧ f₁.name ∉ u₂.guard.reads ∧ f₁.name ∉ u₂.value.reads
      ∧ f₁.name ≠ f₂.name :=
  h.noOverlap

/-- Composition (pair level): non-interference is symmetric — the SAME
five facts, permuted (no new data, pure rearrangement). -/
instance NonInterfering.symm {fs : List Field} {f₁ f₂ : Field}
    {u₁ : UpdateItem fs f₁} {u₂ : UpdateItem fs f₂}
    [h : NonInterfering fs f₁ f₂ u₁ u₂] :
    NonInterfering fs f₂ f₁ u₂ u₁ where
  noOverlap :=
    ⟨h.noOverlap.2.2.1, h.noOverlap.2.2.2.1, h.noOverlap.1, h.noOverlap.2.1,
      Ne.symm h.noOverlap.2.2.2.2⟩

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

/-- THE FIRING SITE (the consumer the classes were built for): the
two-update cascade step, legality-locked. The instances are not
decorations — a cascade step assembled from a VOLATILE update or an
INTERFERING pair has no instance and CANNOT be constructed (instance
search fails; the syntactic scan's composition-level upgrade). The
instance binders are the composite purity law: legality of the whole =
the conjunction of the steps' instances, assembled by search. -/
def UpdateItem.cascade2 {fs : List Field} {f₁ f₂ : Field}
    (u₁ : UpdateItem fs f₁) (u₂ : UpdateItem fs f₂)
    [_hP₁ : UpdatePure fs f₁ u₁] [_hP₂ : UpdatePure fs f₂ u₂]
    [_hNI : NonInterfering fs f₁ f₂ u₁ u₂]
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  (rows.map u₂.applyRow).map u₁.applyRow

-- The composite's ORDER-FREEDOM (the law over the locked composite):
-- `cascade_two_commute` recovered STRUCTURALLY — its four
-- non-interference hypotheses come from the class field alone, via
-- `cascadeHyps` (the swap needs only the `symm` composition instance).
-- Stated in `Tests` — `cascade_two_commute` lives in `TickCascade`,
-- which imports THIS module (a theorem here would be an import cycle);
-- the Tests pin is the composition-level witness until the law moves
-- next to its consumer.

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
 

/-! ## The reads-congruence family (moved from TickCascade at W8.3) -/

-- the row-level write-locality + reads-congruence lemmas live at the
-- ROW layer (they mention no cascade); TickCascade's composition laws
-- and Update2's v2 laws both consume them through this module. The move
-- keeps Update2 mathlib-free (TickCascade drags Dbsp.Effects; the
-- feature-flags `Flag` collision lesson). Names unchanged.

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


/-! ## The registered-update wrapper -/

/-- The registered-update wrapper: the table's fields + the written
    field + the update (the GADT indices ride the existentials — the
    registry is a plain list of these). -/
structure SomeUpdate where
  fields : List Field
  field : Field
  update : UpdateItem fields field

-- W6.13 OPACITY DISCIPLINE (the schema-lang portion) — cedar's
-- proof-stability pattern: representation projections proofs should
-- never unfold are sealed so consumers go through the lemma interfaces.
-- The minimal safe step, `@[irreducible]` where NO consumer unfolds:
--
-- MARKED irreducible:
-- - `Validate.guardCastApply` — the cast-kit combinator; consumers are
--   the three registry eliminators below (compiled execution only) plus
--   its OWN lemma interface (`guardCastApply_self`/`_of_ne`, now
--   `simp only`-unfolded). No proof unfolds the raw `dite`.
-- - `SomeUpdate.applyRow` (below), `SomeUpdate.applyBatch` (Trace.lean),
--   `InvariantItem.checkOn` (Invariant.lean) — the existential wrappers'
--   eliminators; consumers are runtime asserts (irreducibility is an
--   elaborator hint — compiled code reduces regardless).
--
-- LEFT TRANSPARENT, with reason:
-- - `RowVals.cast` — its own interface lemmas (`cast_rfl` by `rfl`, the
--   `@[simp] cast_eq_cast` bridge to elaborator-inserted `▸`) must see
--   through it; sealing it breaks the bridge it names.
-- - `UpdateItem.applyRow`/`apply` — the cascade composition proofs
--   (Tests' `cascade_two_commute` pin, TickCascade) `simp [...]`-unfold
--   them BY DESIGN; their unfold set IS the proof interface.
-- - The structure projections (`SomeUpdate.fields/.field/.update`,
--   `SchemaInvariant.fields/.expr`, `InvariantItem.inv`) — per-projection
--   opacity needs the module system (`private`), the W5.4 step; the
--   emitters (Emit.Update/Emit.Invariant) are legitimate representation
--   consumers.
-- - `tickRows`/`tickTrace`/`runScenario` (Trace.lean) — the ORACLE;
--   replay consumers evaluate it and no lemma interface exists to hide
--   it behind yet.

/-- Execute against a row whose field list CLAIMS to be the update's —
    `guardCastApply` (Validate's cast kit, W3.6): the data equality
    carries the proof, the update's `applyRow` runs on the cast row,
    the result casts back; a foreign row passes through untouched.
    `@[irreducible]` (W6.13 — see the block above). -/
@[irreducible]
def SomeUpdate.applyRow (u : SomeUpdate) {fs : List Field}
    (row : RowVals fs) : RowVals fs :=
  guardCastApply row u.update.applyRow row

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

-- W7.3 phase 2: the `states:` clause is REMOVED — its generated
-- entourage (`tickStates`, `tickTrans`, `tickTableStep?` +
-- `tickTableStep?_eq_step?`, the `DecidablePred tick.Inv` instance) had
-- ZERO consumers (review finding, verified: no conformance battery
-- sweeps tick — unlike pipeline/orderMachine — and no emitter folds
-- its table). The machine itself (labels, the `rank:` theorems) is
-- untouched.
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

