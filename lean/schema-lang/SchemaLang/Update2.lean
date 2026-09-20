/-
# SchemaLang.Update2 — the update language v2 (W8.3)

v2 grows the `schema_update` surface (Meta.Reflect's command — the
syntax/elaborator half) from v1's single-column write to the canon
row's full shape (canon Part 3: "a business rule / batch update = a
`schema_update` (named, total, order-free; guard + write) — W8.3 grows
multi-column/insert/delete"):

- MULTI-COLUMN WRITES: a clause list `c₁ := e₁, c₂ := e₂, …`. Every
  value expression reads the ORIGINAL row (v1's batch law, now across
  the clause list — `applySets`'s fold evaluates every value at the
  fold's INPUT row); the writes apply SIMULTANEOUSLY (`applySets_perm`:
  with distinct column names — elaboration-checked — the clause order
  is unobservable).
- INSERT: `+ (e₁, …, eₙ)` — a FULL row, one expression per field in
  field order (no defaults, no partial rows), computed per GUARDED row
  (the INSERT-SELECT reading; the expressions read the guarded row's
  pre-update state). The inserted row's key is its value at the
  record's DECLARED key field (W8.2 — the command resolves
  `registeredKeyDecl?`; an insert/delete update on a keyless record is
  an ELABORATION error).
- DELETE: `-` — the guarded rows are removed (the row-level semantics
  is positional; the keyed reading is the lowering correspondence).

The batch law (v1, carried): guard, set values, and insert templates
ALL read pre-update state; no cascade WITHIN an update.

## The laws

1. `applySets_perm` — clause-order freedom WITHIN one update (distinct
   names), from `ColPath.set_commute_disjoint` by Perm induction.
2. `apply2_comm_perm` / `apply2_comm` — TWO updates compose in either
   order under `Update2Compat`, the honest "disjoint keys" premise:
   read/write non-interference (derived reads — never hand-listed),
   disjoint write columns, each side's guard refuses the other's
   inserts, and no row fires one side's insert while the other
   deletes. The general form is a PERMUTATION of the final table
   (inserts append in firing order — the tick already treats row order
   as unobservable, `Scenario.conforms`); with no inserts on either
   side it is plain EQUALITY. Same-key conflicts are OUTSIDE the
   premise: order-dependent by design (later-wins — the overwrite
   channel's row-level twin; the negative witness is pinned in Tests).
3. `apply2_eq_foldDeltas` — the LOWERING correspondence: the update's
   table effect IS the fold of its per-row deltas (`RowDelta` is the
   SHARED change variant — `EventSourced.Delta` at the schema row:
   insert/update carry the FULL row, remove carries the KEY image)
   applied through the keyed table semantics (`applyRowDelta`; the
   applicator bridge `applyRowDelta_eq_apply` proves it is the
   event-sourcing lane's keyed reading on key-unique tables). Premise:
   `KeyCoherent` — the key column is not written, every row projects
   its key, the key column's type is codec-closed (ONE fact — the
   lawful `FieldVal.beq`'s warranty, spread by `keyImgs_closed`), the
   key images are pairwise distinct (core `List.Nodup` — R5 collapsed
   the both-direction `nodup2` ball onto the codec's round-trip laws),
   insert keys fresh. Row level (`keepRow_eq_fold_patchKeep`,
   `newRow_eq_fold_patchNew`) is premise-light; the table fold carries
   coherence.
4. The OBLIGATION view: a keyed v2 update produces one obligation —
   key-uniqueness is PRESERVED on the pinned all-default singleton
   table (the invariant/key lane's default-row discipline) — tier
   computed (`decidableNow`), `Update2Obligation.discharge` with the
   soundness/completeness pair. A duplicate-key insert decides FALSE
   and REFUSES (the loud gap — Tests pins it).

Ownership: the update lane (this module + Meta.Reflect's command
half). Deliberate exclusions: emitter consumption (the byte-tie — no
emitter reads `update2ItemExt`; the v1 registry remains the emission
source); a `Dbsp.DeltaSystem` instance for v2 (the general law is a
permutation — the class's `patch` equality fits the no-insert
fragment; a follow-up); composite keys (W8.2's granularity);
cross-table updates (single-table, v1's scope).
-/

module

public import SchemaLang.Update
public import SchemaLang.Keys
public import SchemaLang.Change
public import CodegenCore

@[expose] public section

namespace SchemaLang

/-! ## The v2 data -/

/-- One SET clause of a v2 update: the written column (the name rides
    the field), the structural write path (the elaboration-checked
    extraction route — data, the `ColPath` doctrine), and the value
    expression typed at the COLUMN'S OWN type (the v1 GADT gate, per
    clause). -/
structure SetClause (fs : List Field) where
  field : Field
  path : ColPath field.name field.ty fs
  value : VExpr fs field.ty

/-- The insert template, as a GADT (the `RowVals` mirror): one value
    expression per field of the TARGET row, in field order. The
    template's expressions read the GUARDED row (the INSERT-SELECT
    reading — batch: pre-update state). A full row by construction:
    no defaults, no partial inserts. -/
inductive RowTmpl (fs : List Field) : List Field → Type where
  | nil : RowTmpl fs []
  | cons : {f : Field} → {gs : List Field} → VExpr fs f.ty → RowTmpl fs gs →
      RowTmpl fs (f :: gs)

/-- Evaluate the template against the source row (every field's
    expression reads the SAME pre-update row). -/
def RowTmpl.eval : {gs : List Field} → RowTmpl fs gs → RowVals fs → RowVals gs
  | _, .nil, _ => .nil
  | _, .cons e t, r => .cons (evalV e r) (t.eval r)

/-- The template's derived reads (the fold — never hand-listed). -/
def RowTmpl.reads : {gs : List Field} → RowTmpl fs gs → List String
  | _, .nil => []
  | _, .cons e t => e.reads ++ t.reads

/-- The v2 update item over table `fs`: the name, the record's schema
    name (provenance + key resolution), the guard, the SET clauses,
    and the optional row-level effects. `key?` is the record's
    DECLARED key field (W8.2), resolved at registration; insert/delete
    updates MUST be keyed (the elaboration gate), set-only updates
    adopt the declared key when one is registered (the obligation
    view reads it). `volatileRefs` is the registration scan's STORED
    fact (the `UpdateItem.volatileRefs` precedent — never
    hand-listed). -/
structure Update2Item (fs : List Field) where
  name : String
  record : String
  guard : VExpr fs .bool
  sets : List (SetClause fs)
  key? : Option String := none
  insert? : Option (RowTmpl fs fs) := none
  delete : Bool := false
  volatileRefs : List String := []

/-- The DERIVED write set (the SET clauses' columns; insert/delete are
    row-level effects, not column writes). -/
def Update2Item.setNames {fs : List Field} (u : Update2Item fs) : List String :=
  u.sets.map (fun c => c.field.name)

/-- The DERIVED read set (guard + set values + insert template,
    deduped — the `UpdateItem.reads` fold, extended). -/
def Update2Item.reads {fs : List Field} (u : Update2Item fs) : List String :=
  (u.guard.reads ++ u.sets.flatMap (fun c => c.value.reads)
    ++ (u.insert?.map RowTmpl.reads).getD []).eraseDups

/-- The DERIVED write set (the v1 `writes` reading). -/
def Update2Item.writes {fs : List Field} (u : Update2Item fs) : List String :=
  u.setNames

/-- THE PURE LOCK, v2 (the `UpdatePure` mirror): the registration's
    volatile scan stored `[]`. -/
class Update2Pure (fs : List Field) (u : Update2Item fs) : Prop where
  /-- The stored volatile-ref set is empty (the scan's decided fact). -/
  volatileFree : u.volatileRefs = [] := by decide

/-- The REGISTRATION-ROUTE constructor (the `UpdatePure.emptyScan`
    precedent): an item whose `volatileRefs` slot is literally `[]` is
    pure — the `rfl` reduces on the ctor with the binders abstract. -/
theorem Update2Pure.emptyScan {fs : List Field} {n rec : String}
    {g : VExpr fs .bool} {sets : List (SetClause fs)} {key? : Option String}
    {ins : Option (RowTmpl fs fs)} {del : Bool} :
    Update2Pure fs (Update2Item.mk n rec g sets key? ins del []) :=
  ⟨rfl⟩

/-- The registered-update wrapper (the `SomeUpdate` mirror). -/
structure SomeUpdate2 where
  fields : List Field
  update : Update2Item fields

/-- The registry-state inhabitant (the `SomeUpdate` default's
    pattern): SOME shape must witness the type; the empty-schema row
    is unreachable for registered data (the guard's `eq` of literals
    needs no column). Defined BEFORE the extension
    (`mkRegistryExt`'s seed — Meta.Reflect). -/
instance : Inhabited SomeUpdate2 :=
  ⟨{ fields := []
   , update := { name := "", record := ""
               , guard := .eq (.lit 0) (.lit 0), sets := [] } }⟩

/-! ## The semantics -/

/-- The simultaneous multi-write. BATCH by construction: the fold's
    value argument evaluates every clause's expression at `r` (the
    fold's INPUT row) — the accumulator only accumulates WRITES. -/
def applySets {fs : List Field} (sets : List (SetClause fs))
    (r : RowVals fs) : RowVals fs :=
  sets.foldl (fun acc c => c.path.set acc (evalV c.value r)) r

theorem applySets_nil {fs : List Field} (r : RowVals fs) :
    applySets [] r = r := rfl

/-- The surviving row (`none` = the guarded row is deleted). Guard and
    values read the ORIGINAL row. -/
def Update2Item.keepRow {fs : List Field} (u : Update2Item fs)
    (r : RowVals fs) : Option (RowVals fs) :=
  if validates u.guard r then
    if u.delete then none else some (applySets u.sets r)
  else some r

/-- The inserted row (`none` = no insert fired). -/
def Update2Item.newRow {fs : List Field} (u : Update2Item fs)
    (r : RowVals fs) : Option (RowVals fs) :=
  if validates u.guard r then u.insert?.map (·.eval r) else none

/-- The v2 batch semantics: TOTAL (every row is decided by the guard),
    kept rows in order, inserts appended at the end (DETERMINISTIC
    placement — the no-insert law's equality is list equality; the
    general law is a permutation). -/
def Update2Item.apply {fs : List Field} (u : Update2Item fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  rows.filterMap u.keepRow ++ rows.filterMap u.newRow

/-- Execute against a table whose field list CLAIMS to be the
    update's (the `SomeUpdate.applyRow` cast discipline, at the
    table): a matching table executes, a foreign one passes through. -/
@[irreducible]
def SomeUpdate2.apply (u : SomeUpdate2) {fs : List Field}
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  guardCastApply (F := fun fs => List (RowVals fs)) (G := fun fs => List (RowVals fs))
    rows u.update.apply rows

/-! ## The membership kit (derived sets earn the premises) -/

theorem Update2Item.mem_setNames {fs : List Field} {u : Update2Item fs}
    {c : SetClause fs} (hc : c ∈ u.sets) : c.field.name ∈ u.setNames :=
  List.mem_map_of_mem hc

-- (`++` is LEFT-associative in this toolchain: `G ++ S ++ I` parses
-- `(G ++ S) ++ I` — the membership proofs' Or-nestings follow THAT.)
theorem Update2Item.mem_reads_of_guard {fs : List Field} {u : Update2Item fs}
    {n : String} (h : n ∈ u.guard.reads) : n ∈ u.reads := by
  unfold Update2Item.reads
  exact List.mem_eraseDups.mpr
    (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))

theorem Update2Item.mem_reads_of_set {fs : List Field} {u : Update2Item fs}
    {c : SetClause fs} {n : String} (hc : c ∈ u.sets)
    (h : n ∈ c.value.reads) : n ∈ u.reads := by
  unfold Update2Item.reads
  exact List.mem_eraseDups.mpr (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨c, hc, h⟩)))))

theorem Update2Item.mem_reads_of_insert {fs : List Field} {u : Update2Item fs}
    {t : RowTmpl fs fs} {n : String} (hi : u.insert? = some t)
    (h : n ∈ t.reads) : n ∈ u.reads := by
  unfold Update2Item.reads
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  apply Or.inr
  rw [hi]
  exact h

/-! ## Law 1 — clause-order freedom WITHIN one update -/

/-- The fold's perm-invariance (generalized accumulator — the
    induction's motive). Values read `r₀` at every step, so the swap
    case is exactly `ColPath.set_commute_disjoint`. -/
theorem applySets_foldl_perm {fs : List Field} (r₀ : RowVals fs)
    {s₁ s₂ : List (SetClause fs)} (hp : s₁.Perm s₂)
    (hnd : (s₁.map fun c => c.field.name).Nodup) :
    ∀ (acc : RowVals fs),
      s₁.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc
        = s₂.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc := by
  induction hp with
  | nil => intro _; rfl
  | cons x _ ih =>
      intro acc
      simp only [List.foldl_cons]
      exact ih ((List.nodup_cons.mp hnd).2) (x.path.set acc (evalV x.value r₀))
  | swap x y l =>
      -- `Perm.swap x y l : (y :: x :: l) ~ (x :: y :: l)` — the motive's
      -- LHS is `y :: x :: l` (the Nodup premise rides it)
      have hne : x.field.name ≠ y.field.name := by
        rw [List.map_cons, List.map_cons, List.nodup_cons] at hnd
        intro he
        exact hnd.1 (List.mem_cons.mpr (Or.inl he.symm))
      intro acc
      have hcomm :
          x.path.set (y.path.set acc (evalV y.value r₀)) (evalV x.value r₀)
            = y.path.set (x.path.set acc (evalV x.value r₀)) (evalV y.value r₀) :=
        ColPath.set_commute_disjoint y.path x.path (fun h => hne h.symm) acc _ _
      simp only [List.foldl_cons]
      show List.foldl (fun a c => c.path.set a (evalV c.value r₀))
            (x.path.set (y.path.set acc (evalV y.value r₀)) (evalV x.value r₀)) l
        = List.foldl (fun a c => c.path.set a (evalV c.value r₀))
            (y.path.set (x.path.set acc (evalV x.value r₀)) (evalV y.value r₀)) l
      rw [hcomm]
  | trans hp₁ _ ih₁ ih₂ =>
      intro acc
      exact (ih₁ hnd acc).trans (ih₂ ((hp₁.map _).nodup_iff.mp hnd) acc)

/-- LAW 1: the SET clause order is unobservable (distinct column
    names — elaboration-checked at registration). -/
theorem applySets_perm {fs : List Field} {s₁ s₂ : List (SetClause fs)}
    (hp : s₁.Perm s₂) (hnd : (s₁.map fun c => c.field.name).Nodup)
    (r : RowVals fs) : applySets s₁ r = applySets s₂ r :=
  applySets_foldl_perm r hp hnd r

/-! ## Law 2 — neutrality under the multi-write -/

/-- An expression whose reads avoid every SET clause's column
    evaluates the same before and after the write fold (the
    `evalV_set_neutral` lift). -/
theorem evalV_applySets_neutral {fs : List Field} {r₀ : RowVals fs}
    {sets : List (SetClause fs)} {t : Ty} (e : VExpr fs t) :
    (∀ c ∈ sets, c.field.name ∉ e.reads) → ∀ (acc : RowVals fs),
      evalV e (sets.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc)
        = evalV e acc := by
  induction sets with
  | nil => intro _ _; rfl
  | cons c rest ih =>
      intro h acc
      simp only [List.foldl_cons]
      rw [ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) _]
      exact VExpr.evalV_set_neutral e c.path (h c (List.mem_cons_self)) acc _

/-- The corollary at the fold's own input row. -/
theorem evalV_applySets {fs : List Field} {sets : List (SetClause fs)}
    {t : Ty} (e : VExpr fs t) (h : ∀ c ∈ sets, c.field.name ∉ e.reads)
    (r : RowVals fs) : evalV e (applySets sets r) = evalV e r :=
  evalV_applySets_neutral e h r

/-- The raw reading's neutrality under the write fold. -/
theorem evalRaw_applySets_neutral {fs : List Field} {r₀ : RowVals fs}
    {sets : List (SetClause fs)} {t : Ty} (e : VExpr fs t) :
    (∀ c ∈ sets, c.field.name ∉ e.reads) → ∀ (acc : RowVals fs),
      evalRaw e (sets.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc)
        = evalRaw e acc := by
  induction sets with
  | nil => intro _ _; rfl
  | cons c rest ih =>
      intro h acc
      simp only [List.foldl_cons]
      rw [ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) _]
      exact VExpr.evalRaw_set_neutral e c.path (h c (List.mem_cons_self)) acc _

/-- The raw u64/bool lane, at the fold's input row (`evalB` is
    `evalRaw` specialized — the rewrite-friendly form). -/
theorem evalB_applySets {fs : List Field} {sets : List (SetClause fs)}
    (g : VExpr fs .bool) (h : ∀ c ∈ sets, c.field.name ∉ g.reads)
    (r : RowVals fs) : evalB g (applySets sets r) = evalB g r :=
  evalRaw_applySets_neutral (r₀ := r) (t := .bool) g h r

/-- The guard's verdict is stable under a write fold it doesn't read. -/
theorem validates_applySets {fs : List Field} {sets : List (SetClause fs)}
    (g : VExpr fs .bool) (h : ∀ c ∈ sets, c.field.name ∉ g.reads)
    (r : RowVals fs) : validates g (applySets sets r) = validates g r := by
  have hn := evalB_applySets (sets := sets) g h r
  show (evalB g (applySets sets r) == 1) = (evalB g r == 1)
  rw [hn]

/-- The template's set-neutrality (induction on the template). -/
theorem RowTmpl.eval_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty}
    {gs : List Field} (t : RowTmpl fs gs) (p₁ : ColPath n₁ t₁ fs)
    (hne : n₁ ∉ t.reads) (row : RowVals fs) (v : Value t₁) :
    t.eval (p₁.set row v) = t.eval row := by
  induction t with
  | nil => rfl
  | cons e t ih =>
      have ⟨he, ht⟩ : n₁ ∉ e.reads ∧ n₁ ∉ t.reads := by
        simpa [RowTmpl.reads] using hne
      show RowVals.cons (evalV e (p₁.set row v)) (t.eval (p₁.set row v))
        = RowVals.cons (evalV e row) (t.eval row)
      rw [VExpr.evalV_set_neutral e p₁ he row v, ih ht]

/-- The template's fold neutrality. -/
theorem RowTmpl.eval_applySets {fs : List Field} {r₀ : RowVals fs}
    {sets : List (SetClause fs)} {gs : List Field} (t : RowTmpl fs gs) :
    (∀ c ∈ sets, c.field.name ∉ t.reads) → ∀ (acc : RowVals fs),
      t.eval (sets.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc)
        = t.eval acc := by
  induction sets with
  | nil => intro _ _; rfl
  | cons c rest ih =>
      intro h acc
      simp only [List.foldl_cons]
      rw [ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) _]
      exact t.eval_set_neutral c.path (h c (List.mem_cons_self)) acc _

/-! ## Law 3 — two write folds with disjoint columns commute -/

/-- A step that commutes with every element of a fold pushes through
    the fold. -/
theorem foldl_step_push {fs : List Field}
    {f : RowVals fs → SetClause fs → RowVals fs}
    {s : List (SetClause fs)} {c : SetClause fs}
    (hc : ∀ c₂ ∈ s, ∀ a, f (f a c) c₂ = f (f a c₂) c) :
    ∀ a, s.foldl f (f a c) = f (s.foldl f a) c := by
  induction s with
  | nil => intro _; rfl
  | cons c₂ rest ih =>
      intro a
      simp only [List.foldl_cons]
      show rest.foldl f (f (f a c) c₂) = f (rest.foldl f (f a c₂)) c
      rw [hc c₂ (List.mem_cons_self) a]
      exact ih (fun c' hc' => hc c' (List.mem_cons_of_mem c₂ hc')) _

/-- Adjacent-block exchange for a fold of pairwise-commuting steps. -/
theorem foldl_append_comm_of_comm {fs : List Field}
    {f : RowVals fs → SetClause fs → RowVals fs}
    {s₁ s₂ : List (SetClause fs)}
    (hc : ∀ c₁ ∈ s₁, ∀ c₂ ∈ s₂, ∀ a, f (f a c₁) c₂ = f (f a c₂) c₁) :
    ∀ a, (s₁ ++ s₂).foldl f a = (s₂ ++ s₁).foldl f a := by
  induction s₁ with
  | nil => intro a; simp
  | cons c₁ s₁' ih =>
      intro a
      simp only [List.cons_append, List.foldl_cons]
      rw [ih (fun x hx => hc x (List.mem_cons_of_mem c₁ hx)) _]
      show (s₂ ++ s₁').foldl f (f a c₁) = (s₂ ++ c₁ :: s₁').foldl f a
      rw [List.foldl_append, List.foldl_append]
      show s₁'.foldl f (s₂.foldl f (f a c₁)) = s₁'.foldl f (f (s₂.foldl f a) c₁)
      rw [foldl_step_push (f := f) (s := s₂) (c := c₁)
        (fun c₂ hc₂ a' => hc c₁ (List.mem_cons_self) c₂ hc₂ a') a]

/-- Pointwise fold congruence (the value-reads rewrite). -/
theorem foldl_step_congr {fs : List Field} {s : List (SetClause fs)}
    {r x : RowVals fs}
    (h : ∀ c ∈ s, evalV c.value x = evalV c.value r) :
    ∀ a, s.foldl (fun a c => c.path.set a (evalV c.value x)) a
      = s.foldl (fun a c => c.path.set a (evalV c.value r)) a := by
  induction s with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro a
      simp only [List.foldl_cons]
      rw [h c (List.mem_cons_self)]
      exact ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) _

/-- LAW 3: two SET folds with DISJOINT columns and cross-neutral value
    reads commute. (THE unification marker: this family instantiates
    `CodegenCore.DisjointCommute` at the batch granularity — clause
    lists as mutations, column names as locations, name-inequality as
    disjointness; the landing belongs to the update lane's own
    follow-up. Read-only here — the lane was busy.) -/
theorem applySets_comm {fs : List Field} {s₁ s₂ : List (SetClause fs)}
    (hdisj : ∀ c₁ ∈ s₁, ∀ c₂ ∈ s₂, c₁.field.name ≠ c₂.field.name)
    (hval₂ : ∀ c₂ ∈ s₂, ∀ n ∈ c₂.value.reads, ∀ c₁ ∈ s₁,
      n ≠ c₁.field.name)
    (hval₁ : ∀ c₁ ∈ s₁, ∀ n ∈ c₁.value.reads, ∀ c₂ ∈ s₂,
      n ≠ c₂.field.name)
    (r : RowVals fs) :
    applySets s₁ (applySets s₂ r) = applySets s₂ (applySets s₁ r) := by
  have key : ∀ (sa sb : List (SetClause fs)),
      (∀ c ∈ sb, ∀ n ∈ c.value.reads, ∀ c' ∈ sa, n ≠ c'.field.name) →
      applySets sb (applySets sa r)
        = (sa ++ sb).foldl (fun a c => c.path.set a (evalV c.value r)) r := by
    intro sa sb h
    show sb.foldl (fun a c => c.path.set a (evalV c.value (applySets sa r)))
        (applySets sa r) = _
    rw [foldl_step_congr (r := r) (x := applySets sa r) (s := sb)
      (fun c hc => evalV_applySets c.value
        (fun c' hc' hn => h c hc _ hn c' hc' rfl) r) (applySets sa r)]
    show sb.foldl (fun a c => c.path.set a (evalV c.value r))
        (sa.foldl (fun a c => c.path.set a (evalV c.value r)) r) = _
    rw [← List.foldl_append]
  rw [key s₂ s₁ hval₁, key s₁ s₂ hval₂]
  exact (foldl_append_comm_of_comm (fun c₁ hc₁ c₂ hc₂ a =>
    ColPath.set_commute_disjoint c₁.path c₂.path (hdisj c₁ hc₁ c₂ hc₂) a _ _) r).symm

/-! ## Laws 4/5 — the two-update order-freedom -/

/-- THE ORDER-FREEDOM PREMISE (the honest "disjoint keys" form): two
    v2 updates over the same table compose in either order when

    - neither READS (guard, set values, insert template) a column the
      other WRITES (`ni₁₂`/`ni₂₁` — the derived read sets, never
      hand-listed);
    - their written columns are DISJOINT (`setDisj` — same-column
      writes are later-wins, `ColPath.set_commute_same`; excluded);
    - each side's guard REFUSES every row the other inserts
      (`refuse₁₂`/`refuse₂₁` — else the later update would process the
      other's fresh rows);
    - no row fires one side's INSERT while the other DELETES
      (`insertSep₁₂`/`insertSep₂₁` — a deleted row's insert never
      fires in the other order).

    Every field is decidable over a concrete table (the Tests'
    two-update fixture discharges them by `decide`). Same-key
    insert/delete conflicts VIOLATE the last two — order-dependent by
    design. -/
structure Update2Compat {fs : List Field} (u₁ u₂ : Update2Item fs)
    (rows : List (RowVals fs)) : Prop where
  /-- u₁'s reads avoid u₂'s written columns. -/
  ni₁₂ : ∀ n ∈ u₁.reads, n ∉ u₂.setNames
  /-- u₂'s reads avoid u₁'s written columns. -/
  ni₂₁ : ∀ n ∈ u₂.reads, n ∉ u₁.setNames
  /-- The written columns are disjoint. -/
  setDisj : ∀ n ∈ u₁.setNames, n ∉ u₂.setNames
  /-- u₂'s guard refuses every row u₁ inserts. -/
  refuse₁₂ : ∀ r ∈ rows,
    (u₁.newRow r).elim true (fun new => !validates u₂.guard new) = true
  /-- u₁'s guard refuses every row u₂ inserts. -/
  refuse₂₁ : ∀ r ∈ rows,
    (u₂.newRow r).elim true (fun new => !validates u₁.guard new) = true
  /-- No row fires u₁'s insert while u₂ deletes it. -/
  insertSep₁₂ : u₁.insert?.isSome → u₂.delete = true → ∀ r ∈ rows,
    validates u₁.guard r = true → validates u₂.guard r = false
  /-- No row fires u₂'s insert while u₁ deletes it. -/
  insertSep₂₁ : u₂.insert?.isSome → u₁.delete = true → ∀ r ∈ rows,
    validates u₂.guard r = true → validates u₁.guard r = false

/-- The premise pack is symmetric (the swap earns the swapped pack). -/
theorem Update2Compat.symm {fs : List Field} {u₁ u₂ : Update2Item fs}
    {rows : List (RowVals fs)} (c : Update2Compat u₁ u₂ rows) :
    Update2Compat u₂ u₁ rows where
  ni₁₂ := c.ni₂₁
  ni₂₁ := c.ni₁₂
  setDisj := fun n hn hn' => c.setDisj n hn' hn
  refuse₁₂ := c.refuse₂₁
  refuse₂₁ := c.refuse₁₂
  insertSep₁₂ := c.insertSep₂₁
  insertSep₂₁ := c.insertSep₁₂

namespace Update2Compat

variable {fs : List Field} {u₁ u₂ : Update2Item fs} {rows : List (RowVals fs)}

/-- u₂'s write fold is invisible to u₁'s guard (the neutrality lift). -/
theorem guard₁_set₂ (c : Update2Compat u₁ u₂ rows) (r : RowVals fs) :
    validates u₁.guard (applySets u₂.sets r) = validates u₁.guard r :=
  validates_applySets u₁.guard (fun _c₂ hc₂ hn =>
    c.ni₁₂ _ (u₁.mem_reads_of_guard hn) (u₂.mem_setNames hc₂)) r

/-- The symmetric guard neutrality. -/
theorem guard₂_set₁ (c : Update2Compat u₁ u₂ rows) (r : RowVals fs) :
    validates u₂.guard (applySets u₁.sets r) = validates u₂.guard r :=
  validates_applySets u₂.guard (fun _c₁ hc₁ hn =>
    c.ni₂₁ _ (u₂.mem_reads_of_guard hn) (u₁.mem_setNames hc₁)) r

/-- The write folds commute (Law 3, premises from the pack). -/
theorem sets_comm (c : Update2Compat u₁ u₂ rows) (r : RowVals fs) :
    applySets u₁.sets (applySets u₂.sets r)
      = applySets u₂.sets (applySets u₁.sets r) := by
  apply applySets_comm
  · intro c₁ hc₁ c₂ hc₂ heq
    exact c.setDisj _ (u₁.mem_setNames hc₁) (heq ▸ u₂.mem_setNames hc₂)
  · intro c₂ hc₂ n hn c₁ hc₁ heq
    exact c.ni₂₁ _ (u₂.mem_reads_of_set hc₂ hn) (heq ▸ u₁.mem_setNames hc₁)
  · intro c₁ hc₁ n hn c₂ hc₂ heq
    exact c.ni₁₂ _ (u₁.mem_reads_of_set hc₁ hn) (heq ▸ u₂.mem_setNames hc₂)

/-- u₁'s insert fires identically over u₂'s written row (guard +
    template both neutral). -/
theorem newRow_set₂ (c : Update2Compat u₁ u₂ rows) (r : RowVals fs) :
    u₁.newRow (applySets u₂.sets r) = u₁.newRow r := by
  unfold Update2Item.newRow
  rw [c.guard₁_set₂ r]
  cases hg : validates u₁.guard r with
  | false => rfl
  | true =>
      cases hi : u₁.insert? with
      | none => rfl
      | some t =>
          have ht : t.eval (applySets u₂.sets r) = t.eval r :=
            RowTmpl.eval_applySets t (fun c₂ hc₂ hn =>
              c.ni₁₂ _ (u₁.mem_reads_of_insert hi hn) (u₂.mem_setNames hc₂)) r
          simp [ht]

/-- The ROW-LEVEL composition law: the keep-channels commute. -/
theorem keepRow_bind_comm (c : Update2Compat u₁ u₂ rows) (r : RowVals fs) :
    (u₁.keepRow r).bind u₂.keepRow = (u₂.keepRow r).bind u₁.keepRow := by
  have g₂₁ := c.guard₂_set₁ r
  have g₁₂ := c.guard₁_set₂ r
  have scomm := c.sets_comm r
  unfold Update2Item.keepRow
  by_cases h₁ : validates u₁.guard r = true
  · by_cases h₂ : validates u₂.guard r = true
    · -- both fire: four delete-flag combinations
      have h₂' : validates u₂.guard (applySets u₁.sets r) = true := by
        rw [g₂₁]; exact h₂
      have h₁' : validates u₁.guard (applySets u₂.sets r) = true := by
        rw [g₁₂]; exact h₁
      cases hd₁ : u₁.delete <;> cases hd₂ : u₂.delete <;>
        simp [h₁, h₂, h₁', h₂', scomm]
    · -- u₂ refuses: both orders keep the row with u₁'s write applied
      have h₂' : ¬ validates u₂.guard (applySets u₁.sets r) = true := by
        rw [g₂₁]; exact h₂
      cases hd₁ : u₁.delete <;> simp [h₁, h₂, h₂']
  · by_cases h₂ : validates u₂.guard r = true
    · have h₁' : ¬ validates u₁.guard (applySets u₂.sets r) = true := by
        rw [g₁₂]; exact h₁
      cases hd₂ : u₂.delete <;> simp [h₁, h₂, h₁']
    · simp [h₁, h₂]

/-- The insert channel over the other's kept table = over the original
    (per row: a kept row is the ORIGINAL or a neutral write; a deleted
    row's insert is separated by `insertSep`). -/
theorem newRow_bind_keepRow (c : Update2Compat u₁ u₂ rows) (r : RowVals fs)
    (hr : r ∈ rows) :
    (u₂.keepRow r).bind u₁.newRow = u₁.newRow r := by
  unfold Update2Item.keepRow
  by_cases h₂ : validates u₂.guard r = true
  · by_cases hd₂ : u₂.delete = true
    · rw [if_pos h₂, if_pos hd₂]
      show (none : Option (RowVals fs)) = u₁.newRow r
      -- u₁'s insert cannot fire here (insertSep); the guard refuses
      unfold Update2Item.newRow
      by_cases h₁ : validates u₁.guard r = true
      · cases hi : u₁.insert? with
        | none => rw [if_pos h₁]; rfl
        | some t =>
            have hsep := c.insertSep₁₂ (by rw [hi]; rfl) hd₂ r hr h₁
            rw [hsep] at h₂
            exact absurd h₂ (by decide)
      · rw [if_neg h₁]
    · rw [if_pos h₂, if_neg hd₂]
      show (some (applySets u₂.sets r)).bind u₁.newRow = u₁.newRow r
      exact c.newRow_set₂ r
  · rw [if_neg h₂]
    rfl

/-- Nested filterMap as a per-element bind (the lift bridge). -/
theorem filterMap_filterMap {α β γ : Type _} {f : α → Option β}
    {g : β → Option γ} :
    ∀ l : List α, (l.filterMap f).filterMap g
      = l.filterMap (fun a => (f a).bind g) := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.filterMap_cons]
      cases h : f a with
      | none =>
          simpa [h] using ih
      | some b =>
          simp only [List.filterMap_cons]
          cases h' : g b with
          | none => simpa [h'] using ih
          | some cres => simp [h', ih]

/-- Pointwise filterMap congruence (core ships `filter_congr` only). -/
theorem filterMap_congr {α β : Type _} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The keep-channels commute at the table (Law 4's core). -/
theorem filterMap_keepRow_comm (c : Update2Compat u₁ u₂ rows) :
    (rows.filterMap u₂.keepRow).filterMap u₁.keepRow
      = (rows.filterMap u₁.keepRow).filterMap u₂.keepRow := by
  rw [filterMap_filterMap, filterMap_filterMap]
  exact filterMap_congr (fun r _ => (c.keepRow_bind_comm r).symm)

/-- u₁'s inserts over u₂'s kept table = over the original table. -/
theorem filterMap_newRow_keepRow (c : Update2Compat u₁ u₂ rows) :
    (rows.filterMap u₂.keepRow).filterMap u₁.newRow
      = rows.filterMap u₁.newRow := by
  rw [filterMap_filterMap]
  exact filterMap_congr (fun r hr => c.newRow_bind_keepRow r hr)

/-- A refused table passes the keep-channel untouched. -/
theorem filterMap_keepRow_eq_self_of_refused (u : Update2Item fs)
    {l : List (RowVals fs)}
    (h : ∀ x ∈ l, validates u.guard x = false) : l.filterMap u.keepRow = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : validates u.guard x = false := h x (List.mem_cons_self)
      rw [List.filterMap_cons,
        show u.keepRow x = some x from by
          unfold Update2Item.keepRow
          rw [show validates u.guard x = false from hx]
          rfl,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- A refused table fires no inserts. -/
theorem filterMap_newRow_eq_nil_of_refused (u : Update2Item fs)
    {l : List (RowVals fs)}
    (h : ∀ x ∈ l, validates u.guard x = false) : l.filterMap u.newRow = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  have hx' : validates u.guard x = false := h x hx
  unfold Update2Item.newRow
  rw [show validates u.guard x = false from hx']
  rfl

/-- No insert clause: the insert channel is empty. -/
theorem filterMap_newRow_eq_nil_of_insert_none (u : Update2Item fs)
    (h : u.insert? = none) (l : List (RowVals fs)) :
    l.filterMap u.newRow = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x _
  unfold Update2Item.newRow
  rw [h]
  cases validates u.guard x <;> rfl

/-- The other's inserts are refused (the `refuse` premise in list
    form). -/
theorem refused_newRows (c : Update2Compat u₁ u₂ rows) :
    ∀ x ∈ rows.filterMap u₂.newRow, validates u₁.guard x = false := by
  intro x hx
  obtain ⟨r, hr, hnr⟩ := List.mem_filterMap.mp hx
  have h := c.refuse₂₁ r hr
  rw [hnr] at h
  -- h : (!validates u₁.guard x) = true (the `Option.elim` reduces on
  -- the `some`)
  have h' : (!validates u₁.guard x) = true := h
  cases hb : validates u₁.guard x with
  | true => rw [hb] at h'; simp at h'
  | false => rfl

end Update2Compat

/-- The cons-through-append shuffle (the append-comm step). -/
theorem permConsAppend {α : Type _} (x : α) :
    ∀ (l₂ xs : List α), (x :: (l₂ ++ xs)).Perm (l₂ ++ x :: xs) := by
  intro l₂
  induction l₂ with
  | nil => intro _; exact List.Perm.refl _
  | cons y ys ih =>
      intro xs
      show (x :: y :: (ys ++ xs)).Perm (y :: (ys ++ x :: xs))
      exact (List.Perm.swap y x (ys ++ xs)).trans (List.Perm.cons y (ih xs))

/-- `l₁ ++ l₂ ~ l₂ ++ l₁` (core ships `Perm.append_left`/`append_right`
    but not append-commutativity). -/
theorem permAppendComm {α : Type _} :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).Perm (l₂ ++ l₁) := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, List.append_nil]
  | cons x xs ih =>
      show (x :: (xs ++ l₂)).Perm (l₂ ++ x :: xs)
      exact (List.Perm.cons x ih).trans (permConsAppend x l₂ xs)

/-- LAW 5a (the general form): compatible updates commute UP TO
    PERMUTATION of the final table (the insert blocks swap — row order
    is unobservable at the tick, `Scenario.conforms`). -/
theorem apply2_comm_perm {fs : List Field} {u₁ u₂ : Update2Item fs}
    {rows : List (RowVals fs)} (c : Update2Compat u₁ u₂ rows) :
    (u₁.apply (u₂.apply rows)).Perm (u₂.apply (u₁.apply rows)) := by
  have hkk := c.filterMap_keepRow_comm
  have hn₁ := c.filterMap_newRow_keepRow
  have hn₂ := c.symm.filterMap_newRow_keepRow
  have hk₁self := Update2Compat.filterMap_keepRow_eq_self_of_refused u₁
    c.refused_newRows
  have hn₁nil := Update2Compat.filterMap_newRow_eq_nil_of_refused u₁
    c.refused_newRows
  have hk₂self := Update2Compat.filterMap_keepRow_eq_self_of_refused u₂
    c.symm.refused_newRows
  have hn₂nil := Update2Compat.filterMap_newRow_eq_nil_of_refused u₂
    c.symm.refused_newRows
  unfold Update2Item.apply
  rw [List.filterMap_append, List.filterMap_append,
    List.filterMap_append, List.filterMap_append,
    hk₁self, hn₁nil, hk₂self, hn₂nil, hn₁, hn₂, hkk, List.append_nil,
    List.append_nil]
  -- goal: (K ++ N₂) ++ N₁ ~ (K ++ N₁) ++ N₂ (left-nested appends)
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ (permAppendComm _ _)

/-- LAW 5b (the sharp form): with no inserts on either side, compatible
    updates compute the SAME table in either order — plain equality. -/
theorem apply2_comm {fs : List Field} {u₁ u₂ : Update2Item fs}
    {rows : List (RowVals fs)} (c : Update2Compat u₁ u₂ rows)
    (h₁ : u₁.insert? = none) (h₂ : u₂.insert? = none) :
    u₁.apply (u₂.apply rows) = u₂.apply (u₁.apply rows) := by
  have hkk := c.filterMap_keepRow_comm
  have n₁nil := Update2Compat.filterMap_newRow_eq_nil_of_insert_none u₁ h₁ rows
  have n₂nil := Update2Compat.filterMap_newRow_eq_nil_of_insert_none u₂ h₂ rows
  unfold Update2Item.apply
  rw [List.filterMap_append, List.filterMap_append,
    List.filterMap_append, List.filterMap_append,
    Update2Compat.filterMap_keepRow_eq_self_of_refused u₁ c.refused_newRows,
    Update2Compat.filterMap_newRow_eq_nil_of_refused u₁ c.refused_newRows,
    Update2Compat.filterMap_keepRow_eq_self_of_refused u₂ c.symm.refused_newRows,
    Update2Compat.filterMap_newRow_eq_nil_of_refused u₂ c.symm.refused_newRows,
    c.filterMap_newRow_keepRow, c.symm.filterMap_newRow_keepRow,
    n₁nil, n₂nil, hkk]

/-! ## Law 6 — the lowering to THE SHARED DELTA (R1 consolidation) -/

/-- THE SHARED CHANGE VARIANT (R1): the update lane's old `RowDelta`
    inductive RETIRES onto the event-sourcing row's type —
    `EventSourced.Delta` (insert/update carry the full row, remove the
    key) at the schema row (`RowVals fs`, `FieldVal` keys). ONE
    inductive, three specializations (the event-sourcing lane's
    journals, the update lane's lowering, the emitter's
    `dbsp::Change` shape — Delta.lean's emitter emits the contract
    whose Lean side is THIS type). The constructor names resolve
    through the abbreviation. -/
abbrev RowDelta (fs : List Field) :=
  EventSourced.Delta (RowVals fs) FieldVal

/-- The keep-channel's patch reading (ChangeSpec's `patch`, at the
    row's Option): update REPLACES, remove DELETES, insert rides the
    other channel. -/
def RowDelta.patchKeep : RowDelta fs → Option (RowVals fs) → Option (RowVals fs)
  | .insert _, acc => acc
  | .update new, _ => some new
  | .remove _, _ => none

/-- The insert channel's patch reading: the last insert fired wins
    (a guarded row fires at most one). -/
def RowDelta.patchNew : RowDelta fs → Option (RowVals fs) → Option (RowVals fs)
  | .insert new, _ => some new
  | _, acc => acc

/-- THE LOWERING: one row → its deltas. A guard-refused row lowers to
    `[]` (untouched — the batch law). A guarded row lowers to its
    row-level effect (delete → `remove` of the key image; nonempty
    sets → `update` of the written row) followed by the insert. A
    delete whose key projection FAILS lowers to `[]` — the refusal
    reading (`guardCastApply`'s discipline: malformed data refuses
    rather than misreads; registration's gates make it unreachable
    for declared-key updates). -/
def Update2Item.lowerRow {fs : List Field} (u : Update2Item fs)
    (r : RowVals fs) : List (RowDelta fs) :=
  if validates u.guard r then
    (if u.delete then
        match u.key? with
        | some key =>
            match RowVals.project? fs r key with
            | some k => [.remove k]
            | none => []
        | none => []
      else if u.sets.isEmpty then []
      else [.update (applySets u.sets r)])
      ++ (u.insert?.map fun t => EventSourced.Delta.insert (t.eval r)).toList
  else []

/-- The ROW-LEVEL correspondence, keep channel: the surviving row IS
    the deltas' patch fold. Premise: a deleting update's key projects
    on this row (the remove delta needs the key image). -/
theorem keepRow_eq_fold_patchKeep {fs : List Field} (u : Update2Item fs)
    (key : String) (hk : u.key? = some key) (r : RowVals fs)
    (hproj : u.delete = true → validates u.guard r = true →
      ∃ k, RowVals.project? fs r key = some k) :
    u.keepRow r
      = (u.lowerRow r).foldl (fun acc d => d.patchKeep acc) (some r) := by
  by_cases hg : validates u.guard r = true
  · by_cases hd : u.delete = true
    · obtain ⟨k, hpk⟩ := hproj hd hg
      cases hi : u.insert? <;>
        simp [Update2Item.keepRow, Update2Item.lowerRow, hg, hd, hk, hpk, hi,
          RowDelta.patchKeep]
    · cases hs : u.sets with
      | nil =>
          cases hi : u.insert? <;>
            simp [Update2Item.keepRow, Update2Item.lowerRow, hg, hd, hs, hi,
              applySets, RowDelta.patchKeep]
      | cons chd ctl =>
          cases hi : u.insert? <;>
            simp [Update2Item.keepRow, Update2Item.lowerRow, hg, hd, hs, hi,
              RowDelta.patchKeep]
  · simp [Update2Item.keepRow, Update2Item.lowerRow, hg]

/-- The ROW-LEVEL correspondence, insert channel. -/
theorem newRow_eq_fold_patchNew {fs : List Field} (u : Update2Item fs)
    (key : String) (hk : u.key? = some key) (r : RowVals fs) :
    u.newRow r
      = (u.lowerRow r).foldl (fun acc d => d.patchNew acc) none := by
  by_cases hg : validates u.guard r = true
  · by_cases hd : u.delete = true
    · cases hpk : RowVals.project? fs r key <;>
        cases hi : u.insert? <;>
          simp [Update2Item.newRow, Update2Item.lowerRow, hg, hd, hk, hpk, hi,
            RowDelta.patchNew]
    · cases hs : u.sets with
      | nil =>
          cases hi : u.insert? <;>
            simp [Update2Item.newRow, Update2Item.lowerRow, hg, hd, hs, hi,
              RowDelta.patchNew]
      | cons chd ctl =>
          cases hi : u.insert? <;>
            simp [Update2Item.newRow, Update2Item.lowerRow, hg, hd, hs, hi,
              RowDelta.patchNew]
  · simp [Update2Item.newRow, Update2Item.lowerRow, hg]

/-! ### The keyed table semantics + the table-level correspondence -/

/-- The keyed table operation (Delta.lean's ChangeSpec reading at the
    table): `insert` appends the full row; `update` replaces the rows
    SHARING ITS KEY IMAGE (full replacement); `remove` drops the rows
    carrying the key image. Non-projecting rows refuse-by-identity
    (kept, unchanged). -/
def applyRowDelta (key : String) :
    {fs : List Field} → RowDelta fs → List (RowVals fs) → List (RowVals fs)
  | _, .insert r, rows => rows ++ [r]
  | _, .update r, rows => rows.map fun old =>
      match RowVals.project? _ old key with
      | some a =>
          match RowVals.project? _ r key with
          | some b => if a.beq b then r else old
          | none => old
      | none => old
  | _, .remove k, rows => rows.filter fun old =>
      match RowVals.project? _ old key with
      | some a => !a.beq k
      | none => true

/-- The key images of a table (the correspondence's working form —
    `KeyDecl.keyImages?`'s sibling without the mapM refusal: rows that
    don't project are SKIPPED). -/
def keyImgs (fs : List Field) (key : String) (rows : List (RowVals fs)) :
    List FieldVal :=
  rows.filterMap (fun r => RowVals.project? fs r key)

theorem keyImgs_append {fs : List Field} {key : String}
    (l₁ l₂ : List (RowVals fs)) :
    keyImgs fs key (l₁ ++ l₂) = keyImgs fs key l₁ ++ keyImgs fs key l₂ :=
  List.filterMap_append

theorem keyImgs_cons_of_some {fs : List Field} {key : String}
    {r : RowVals fs} {k : FieldVal} {rs : List (RowVals fs)}
    (h : RowVals.project? fs r key = some k) :
    keyImgs fs key (r :: rs) = k :: keyImgs fs key rs := by
  simp [keyImgs, h]

theorem mem_keyImgs_of_project? {fs : List Field} {key : String}
    {l : List (RowVals fs)} {r : RowVals fs} {k : FieldVal}
    (hr : r ∈ l) (h : RowVals.project? fs r key = some k) :
    k ∈ keyImgs fs key l :=
  List.mem_filterMap.mpr ⟨r, hr, h⟩

/-! ### The lawful key kit (R5) — the `nodup2` family retired

`FieldVal.beq` IS equality on codec-closed keys (Keys.lean's
`beq_eq_true_iff_eq`, riding the codec's decode-encode round trip), so
the correspondence's key premises speak CORE `List.Nodup` and `≠`: the
hand-rolled `nodup2` def, its append decomposition, and the
`A ++ k :: B` both-direction inversion pack are gone. The honest price
is the closure of the key images (`CodecClosed` — key types are `KeyTy`
scalars, the W8.1 discipline): ONE closed type fact
(`keyFieldType` — the key column's own type) seeds ALL of them, because
the key projection's TYPE is determined by the field list + column
name — never by the row. -/

/-- The key column's type: the first field named `key`'s type (an
    if-chain, so the reduction is stepwise); the `.bool` fallback is
    unreachable when any row projects (and harmless when none does). -/
def keyFieldType : List Field → String → Ty
  | [], _ => .bool
  | f :: fs, key => if f.name == key then f.ty else keyFieldType fs key

/-- The key projection's type is COLUMN-determined: any successful
    projection's type index is `keyFieldType` — never row-dependent. -/
theorem RowVals.project?_type {fs : List Field} {key : String}
    {x : RowVals fs} {v : FieldVal} (hp : RowVals.project? fs x key = some v) :
    v.1 = keyFieldType fs key := by
  induction fs with
  | nil =>
      cases x
      exact absurd hp (by simp [RowVals.project?])
  | cons f fs' ih =>
      cases x with
      | cons vx xs =>
          simp only [RowVals.project?] at hp
          by_cases hname : (f.name == key) = true
          · rw [if_pos hname] at hp
            have hv : ⟨f.ty, vx⟩ = v := Option.some.inj hp
            subst hv
            show (f.ty : Ty) = keyFieldType (f :: fs') key
            rw [keyFieldType, if_pos hname]
          · rw [if_neg hname] at hp
            rw [keyFieldType, if_neg hname]
            exact ih hp

/-- EVERY key image is codec-closed — the ONE closedness fact seeds
    them all (the projection's type is column-determined). -/
def keyImgs_closed {fs : List Field} {key : String}
    (hclTy : CodecClosed (keyFieldType fs key)) {L : List (RowVals fs)}
    {j : FieldVal} (hj : j ∈ keyImgs fs key L) : CodecClosed j.1 := by
  have hty : j.1 = keyFieldType fs key := by
    obtain ⟨row, _, hpj⟩ := List.mem_filterMap.mp hj
    exact RowVals.project?_type hpj
  rw [hty]
  exact hclTy

/-- The key projection is stable under a write fold that avoids the
    key column (the `project?`-level sibling of
    `ColPath.get_set_neutral`). -/
theorem ColPath.set_project?_neutral {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs)
      (v : Value t) (m : String), m ≠ n →
      RowVals.project? fs (p.set row v) m = RowVals.project? fs row m := by
  intro fs p
  induction p with
  | here =>
      intro row v m hm
      cases row with
      | cons a vs =>
          have hnm : n ≠ m := fun h => hm h.symm
          simp [ColPath.set, RowVals.project?, beq_false_of_ne hnm]
  | there p ih =>
      intro row v m hm
      cases row with
      | cons a vs =>
          show RowVals.project? _ (.cons a (p.set vs v)) m
            = RowVals.project? _ (.cons a vs) m
          simp only [RowVals.project?]
          split
          · rfl
          · exact ih vs v m hm

/-- The fold lift of the projection neutrality. -/
theorem project?_applySets {fs : List Field} {r₀ : RowVals fs}
    {sets : List (SetClause fs)} (m : String)
    (h : ∀ c ∈ sets, c.field.name ≠ m) :
    ∀ (acc : RowVals fs),
      RowVals.project? fs
          (sets.foldl (fun a c => c.path.set a (evalV c.value r₀)) acc) m
        = RowVals.project? fs acc m := by
  induction sets with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) _]
      exact ColPath.set_project?_neutral c.path acc _ m
        (fun he => h c (List.mem_cons_self) he.symm)

/-- `applySets` at the key column (the corollary form). -/
theorem project?_applySets' {fs : List Field} {sets : List (SetClause fs)}
    {m : String} (h : ∀ c ∈ sets, c.field.name ≠ m) (r : RowVals fs) :
    RowVals.project? fs (applySets sets r) m = RowVals.project? fs r m :=
  project?_applySets m h r

/-- `map` is the identity when every element is fixed. -/
theorem map_eq_self_of_forall {α : Type _} {f : α → α} {l : List α}
    (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, h x (List.mem_cons_self),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The update-delta's map over the working table replaces EXACTLY the
    source row (its key image): every other kept row's key is distinct
    (core `List.Nodup` — R5's lawful `FieldVal.beq`), the accumulated
    inserts are fresh. The statement's lambda is `applyRowDelta`'s
    update arm VERBATIM (the inner key match reduces via `hk'`). -/
theorem applyRowDelta_update_map {fs : List Field} (key : String)
    (K rest I : List (RowVals fs)) (r r' : RowVals fs) (k : FieldVal)
    (hk : RowVals.project? fs r key = some k)
    (hk' : RowVals.project? fs r' key = some k)
    (hnd : (keyImgs fs key (K ++ r :: rest)).Nodup)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hI : ∀ ik ∈ keyImgs fs key I,
      ∀ wk ∈ keyImgs fs key (K ++ r :: rest), ik ≠ wk) :
    applyRowDelta key (EventSourced.Delta.update r') (K ++ r :: rest ++ I)
      = K ++ r' :: rest ++ I := by
  show (K ++ r :: rest ++ I).map (fun old =>
      match RowVals.project? fs old key with
      | some a =>
          match RowVals.project? fs r' key with
          | some b => if a.beq b then r' else old
          | none => old
      | none => old) = _
  rw [keyImgs_append, keyImgs_cons_of_some hk] at hnd
  obtain ⟨hKnd, hRestNd, hcross⟩ := List.nodup_append.mp hnd
  -- hcross : ∀ a ∈ keyImgs K, ∀ b ∈ k :: keyImgs rest, a ≠ b
  have hself : k ∈ keyImgs fs key (K ++ r :: rest) := by
    rw [keyImgs_append, keyImgs_cons_of_some hk]
    exact List.mem_append_right _ List.mem_cons_self
  have hKne : ∀ a ∈ keyImgs fs key K, a ≠ k := fun a ha =>
    hcross a ha k List.mem_cons_self
  have hRestNe : ∀ a ∈ keyImgs fs key rest, a ≠ k := fun a ha hkeq =>
    (List.nodup_cons.mp hRestNd).1 (hkeq ▸ ha)
  have fixK : ∀ old ∈ K,
      (match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if a.beq b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := K) (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hKne a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))).1
        simp [hk', hae]
  have fixRest : ∀ old ∈ rest,
      (match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if a.beq b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := rest)
              (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hRestNe a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))).1
        simp [hk', hae]
  have fixI : ∀ old ∈ I,
      (match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if a.beq b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := I)
              (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hI a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k hself)).1
        simp [hk', hae]
  have fr : (match RowVals.project? fs r key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if a.beq b then r' else r
            | none => r
        | none => r) = r' := by
    simp [hk, hk', FieldVal.beq_refl]
  rw [List.map_append, map_eq_self_of_forall fixI, List.map_append,
    map_eq_self_of_forall fixK, List.map_cons, fr,
    map_eq_self_of_forall fixRest]

/-- The insert arm, as a rewrite lemma (the append). -/
theorem applyRowDelta_insert {fs : List Field} (key : String) (x : RowVals fs)
    (T : List (RowVals fs)) : applyRowDelta key (.insert x) T = T ++ [x] := rfl

/-- The remove-delta's filter over the working table drops EXACTLY the
    source row (the same Nodup kit, mirrored). -/
theorem applyRowDelta_remove_filter {fs : List Field} (key : String)
    (K rest I : List (RowVals fs)) (r : RowVals fs) (k : FieldVal)
    (hk : RowVals.project? fs r key = some k)
    (hnd : (keyImgs fs key (K ++ r :: rest)).Nodup)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hI : ∀ ik ∈ keyImgs fs key I,
      ∀ wk ∈ keyImgs fs key (K ++ r :: rest), ik ≠ wk) :
    applyRowDelta key (EventSourced.Delta.remove k) (K ++ r :: rest ++ I)
      = K ++ rest ++ I := by
  show (K ++ r :: rest ++ I).filter (fun old =>
      match RowVals.project? fs old key with
      | some a => !a.beq k
      | none => true) = _
  rw [keyImgs_append, keyImgs_cons_of_some hk] at hnd
  obtain ⟨hKnd, hRestNd, hcross⟩ := List.nodup_append.mp hnd
  have hself : k ∈ keyImgs fs key (K ++ r :: rest) := by
    rw [keyImgs_append, keyImgs_cons_of_some hk]
    exact List.mem_append_right _ List.mem_cons_self
  have hRestNe : ∀ a ∈ keyImgs fs key rest, a ≠ k := fun a ha hkeq =>
    (List.nodup_cons.mp hRestNd).1 (hkeq ▸ ha)
  have keepK : ∀ old ∈ K,
      (match RowVals.project? fs old key with
        | some a => !a.beq k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := K)
              (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hcross a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k
              List.mem_cons_self)).1
        simp [hae]
  have keepRest : ∀ old ∈ rest,
      (match RowVals.project? fs old key with
        | some a => !a.beq k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := rest)
              (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hRestNe a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))).1
        simp [hae]
  have keepI : ∀ old ∈ I,
      (match RowVals.project? fs old key with
        | some a => !a.beq k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : a.beq k = false :=
          (FieldVal.beq_false_pair_of_ne
            (keyImgs_closed hclTy (L := I)
              (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
            (keyImgs_closed hclTy hself)
            (hI a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k hself)).1
        simp [hae]
  have dropR : (match RowVals.project? fs r key with
        | some a => !a.beq k | none => true) = false := by
    simp [hk, FieldVal.beq_refl]
  rw [List.filter_append, List.filter_eq_self.mpr keepI,
    List.filter_append, List.filter_eq_self.mpr keepK, List.filter_cons, dropR,
    List.filter_eq_self.mpr keepRest]
  simp

theorem keyImgs_nil {fs : List Field} {key : String} :
    keyImgs fs key [] = [] := rfl

/-- The u64-key specialisation (the fixtures' shape): distinct u64 keys
    are beq-distinct (Keys.lean's lawful `FieldVal.beq` kit). -/
theorem FieldVal.beq_u64_ne {a b : UInt64} (h : a ≠ b) :
    FieldVal.beq ⟨.u64, .u64 a⟩ ⟨.u64, .u64 b⟩ = false :=
  FieldVal.beq_eq_false_of_ne (by
    intro heq
    obtain ⟨_, hv⟩ := Sigma.mk.inj heq
    exact h (Value.u64.inj (eq_of_heq hv))) CodecClosed.u64

/-- The keep-step's image transport: the processed row's image is the
    same whether it sits at the head of the suffix or at the end of
    the keeps (the key column is not written, so `r`'s and `r'`'s
    images coincide). -/
theorem mem_keyImgs_kept {fs : List Field} {key : String}
    {K rest : List (RowVals fs)} {r r' : RowVals fs} {k x : FieldVal}
    (hk : RowVals.project? fs r key = some k)
    (hk' : RowVals.project? fs r' key = some k) :
    x ∈ keyImgs fs key (K ++ r :: rest)
      ↔ x ∈ keyImgs fs key ((K ++ [r']) ++ rest) := by
  rw [keyImgs_append, keyImgs_cons_of_some hk]
  rw [keyImgs_append, keyImgs_append, keyImgs_cons_of_some hk', keyImgs_nil]
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_singleton,
    List.mem_cons]
  exact or_assoc.symm

/-- The delete-step's image transport (the suffix's images embed in
    the cons's). -/
theorem mem_keyImgs_shrunk {fs : List Field} {key : String}
    {K rest : List (RowVals fs)} {r : RowVals fs} {k x : FieldVal}
    (hk : RowVals.project? fs r key = some k) :
    x ∈ keyImgs fs key (K ++ rest) → x ∈ keyImgs fs key (K ++ r :: rest) := by
  intro h
  rw [keyImgs_append] at h
  rw [keyImgs_append, keyImgs_cons_of_some hk]
  rw [List.mem_append] at h ⊢
  exact h.elim Or.inl (fun h' => Or.inr (List.mem_cons_of_mem _ h'))

/-- The keep-step preserves `Nodup` of the key images (core
    `List.Nodup` — both sides' images are
    `keyImgs K ++ k :: keyImgs rest`, so this is the identity). -/
theorem nodup_keyImgs_kept {fs : List Field} {key : String}
    {K rest : List (RowVals fs)} {r r' : RowVals fs} {k : FieldVal}
    (hk : RowVals.project? fs r key = some k)
    (hk' : RowVals.project? fs r' key = some k)
    (h : (keyImgs fs key (K ++ r :: rest)).Nodup) :
    (keyImgs fs key ((K ++ [r']) ++ rest)).Nodup := by
  have h1 : keyImgs fs key (K ++ r :: rest)
      = keyImgs fs key K ++ k :: keyImgs fs key rest := by
    rw [keyImgs_append, keyImgs_cons_of_some hk]
  have h2 : keyImgs fs key ((K ++ [r']) ++ rest)
      = keyImgs fs key K ++ k :: keyImgs fs key rest := by
    rw [keyImgs_append, keyImgs_append, keyImgs_cons_of_some hk', keyImgs_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  rw [h1] at h
  rw [h2]
  exact h

/-- The delete-step preserves `Nodup` of the key images (the append
    decomposition repacked — one `List.nodup_append` round trip). -/
theorem nodup_keyImgs_shrunk {fs : List Field} {key : String}
    {K rest : List (RowVals fs)} {r : RowVals fs} {k : FieldVal}
    (hk : RowVals.project? fs r key = some k)
    (h : (keyImgs fs key (K ++ r :: rest)).Nodup) :
    (keyImgs fs key (K ++ rest)).Nodup := by
  rw [keyImgs_append, keyImgs_cons_of_some hk] at h
  obtain ⟨hA, hkB, hcross⟩ := List.nodup_append.mp h
  rw [keyImgs_append]
  exact List.nodup_append.mpr ⟨hA, (List.nodup_cons.mp hkB).2,
    fun a ha b hb => hcross a ha b (List.mem_cons_of_mem _ hb)⟩

/-- THE TABLE-LEVEL CORRESPONDENCE, generalized for the induction: the
    working table splits into processed keeps `K`, the unprocessed
    suffix `rest`, and accumulated inserts `I` (appended at the end —
    the deterministic placement). The key premises are the lawful kit:
    images codec-closed (ONE seed — `keyImgs_closed` spreads it),
    pairwise distinct (`Nodup`), inserted keys fresh (`≠`). -/
theorem foldDeltas_go {fs : List Field} (u : Update2Item fs)
    (key : String) (hkey : u.key? = some key)
    (himm : ∀ c ∈ u.sets, c.field.name ≠ key) :
    ∀ (K rest I : List (RowVals fs)),
      (∀ r ∈ rest, (RowVals.project? fs r key).isSome = true) →
      (∀ r ∈ rest, ∀ new, u.newRow r = some new → ∀ k',
        RowVals.project? fs new key = some k' →
        ∀ wk ∈ keyImgs fs key (K ++ rest), k' ≠ wk) →
      CodecClosed (keyFieldType fs key) →
      (keyImgs fs key (K ++ rest)).Nodup →
      (∀ ik ∈ keyImgs fs key I, ∀ wk ∈ keyImgs fs key (K ++ rest), ik ≠ wk) →
      (rest.flatMap u.lowerRow).foldl (fun t d => applyRowDelta key d t)
          (K ++ rest ++ I)
        = K ++ rest.filterMap u.keepRow ++ (I ++ rest.filterMap u.newRow) := by
  intro K rest I
  induction rest generalizing K I with
  | nil =>
      intro _ _ _ _ _
      simp [List.flatMap_nil, List.filterMap_nil, List.append_nil]
  | cons r rs ih =>
      intro hproj hfreshN hclTy hnd hI
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hproj r List.mem_cons_self)
      rw [List.flatMap_cons, List.foldl_append]
      -- the shrunk-range kit (every recursive call over `rs` rides it)
      have hprojS : ∀ r' ∈ rs, (RowVals.project? fs r' key).isSome = true :=
        fun r' hr' => hproj r' (List.mem_cons_of_mem r hr')
      have hfreshS : ∀ r' ∈ rs, ∀ new, u.newRow r' = some new → ∀ k',
          RowVals.project? fs new key = some k' →
          ∀ wk ∈ keyImgs fs key (K ++ rs), k' ≠ wk := by
        intro r' hr' new hn k' hp' wk hwk
        exact hfreshN r' (List.mem_cons_of_mem r hr') new hn k' hp' wk
          (mem_keyImgs_shrunk hk hwk)
      have hndS := nodup_keyImgs_shrunk hk hnd
      have hIS : ∀ ik ∈ keyImgs fs key I, ∀ wk ∈ keyImgs fs key (K ++ rs),
          ik ≠ wk := by
        intro ik hik wk hwk
        exact hI ik hik wk (mem_keyImgs_shrunk hk hwk)
      -- the K-extended kit (every keep/refuse-recursive call rides it;
      -- the written row's image is the source row's image)
      have hfreshK : ∀ r' ∈ rs, ∀ new, u.newRow r' = some new → ∀ k',
          RowVals.project? fs new key = some k' →
          ∀ wk ∈ keyImgs fs key ((K ++ [r]) ++ rs), k' ≠ wk := by
        intro r' hr' new hn k' hp' wk hwk
        exact hfreshN r' (List.mem_cons_of_mem r hr') new hn k' hp' wk
          ((mem_keyImgs_kept hk hk).mpr hwk)
      have hndK : (keyImgs fs key ((K ++ [r]) ++ rs)).Nodup :=
        nodup_keyImgs_kept hk hk hnd
      have hIK : ∀ ik ∈ keyImgs fs key I,
          ∀ wk ∈ keyImgs fs key ((K ++ [r]) ++ rs), ik ≠ wk := by
        intro ik hik wk hwk
        exact hI ik hik wk ((mem_keyImgs_kept hk hk).mpr hwk)
      by_cases hg : validates u.guard r = true
      · by_cases hd : u.delete = true
        · -- DELETE: the row leaves the keeps; the insert may still fire
          have hkr : u.keepRow r = none := by
            unfold Update2Item.keepRow
            rw [if_pos hg, if_pos hd]
          have hlow : u.lowerRow r
              = [EventSourced.Delta.remove k]
                  ++ (u.insert?.map fun t => EventSourced.Delta.insert (t.eval r)).toList := by
            simp [Update2Item.lowerRow, hg, hd, hkey, hk]
          rw [hlow]
          cases hi : u.insert? with
          | none =>
              have hnr : u.newRow r = none := by
                unfold Update2Item.newRow
                rw [if_pos hg, hi]
                rfl
              rw [Option.map_none, Option.toList_none, List.append_nil]
              simp only [List.foldl_cons, List.foldl_nil]
              rw [applyRowDelta_remove_filter key K rs I r k hk hnd hclTy hI]
              rw [ih K I hprojS hfreshS hclTy hndS hIS]
              simp only [List.filterMap_cons, hkr, hnr]
          | some t =>
              have hnr : u.newRow r = some (t.eval r) := by
                unfold Update2Item.newRow
                rw [if_pos hg, hi]
                rfl
              rw [Option.map_some, Option.toList_some]
              simp only [List.singleton_append, List.foldl_cons, List.foldl_nil]
              rw [applyRowDelta_remove_filter key K rs I r k hk hnd hclTy hI]
              rw [applyRowDelta_insert]
              have hT : (K ++ rs ++ I) ++ [t.eval r]
                  = (K ++ rs) ++ (I ++ [t.eval r]) := by
                simp only [List.append_assoc]
              rw [hT]
              -- the insert-extended I: the fresh image's ≠ against the
              -- shrunk table (the membership juggling, once)
              have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t.eval r]),
                  ∀ wk ∈ keyImgs fs key (K ++ rs), ik ≠ wk := by
                intro ik hik wk hwk
                rw [keyImgs_append] at hik
                rcases List.mem_append.mp hik with hik | hik
                · exact hI ik hik wk (mem_keyImgs_shrunk hk hwk)
                · cases hpk : RowVals.project? fs (t.eval r) key with
                  | none => simp [keyImgs, hpk] at hik
                  | some k' =>
                      have hsing : keyImgs fs key [t.eval r] = [k'] := by
                        have h1 := keyImgs_cons_of_some (rs := []) hpk
                        rw [keyImgs_nil] at h1
                        exact h1
                      rw [hsing, List.mem_singleton] at hik
                      rw [← hik] at hpk
                      exact hfreshN r List.mem_cons_self (t.eval r) hnr ik
                        hpk wk (mem_keyImgs_shrunk hk hwk)
              rw [ih K (I ++ [t.eval r]) hprojS hfreshS hclTy hndS hI1]
              simp only [List.filterMap_cons, hkr, hnr]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
        · -- KEEP (no delete): the update-delta fires when sets nonempty
          have hkr : u.keepRow r = some (applySets u.sets r) := by
            unfold Update2Item.keepRow
            rw [if_pos hg, if_neg hd]
          cases hs : u.sets with
          | nil =>
              have hkr' : u.keepRow r = some r := by
                rw [hkr]; rw [hs]; rfl
              have hlow : u.lowerRow r
                  = (u.insert?.map fun t => EventSourced.Delta.insert (t.eval r)).toList := by
                simp [Update2Item.lowerRow, hg, hd, hs]
              rw [hlow]
              cases hi : u.insert? with
              | none =>
                  have hnr : u.newRow r = none := by
                    unfold Update2Item.newRow
                    rw [if_pos hg, hi]
                    rfl
                  rw [Option.map_none, Option.toList_none]
                  simp only [List.foldl_nil]
                  have hT : (K ++ r :: rs) ++ I = (K ++ [r]) ++ rs ++ I := by
                    simp only [List.append_assoc, List.cons_append,
                      List.nil_append]
                  rw [hT]
                  rw [ih (K ++ [r]) I hprojS hfreshK hclTy hndK hIK]
                  simp only [List.filterMap_cons, hkr', hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
              | some t =>
                  have hnr : u.newRow r = some (t.eval r) := by
                    unfold Update2Item.newRow
                    rw [if_pos hg, hi]
                    rfl
                  rw [Option.map_some, Option.toList_some]
                  simp only [List.foldl_cons, List.foldl_nil]
                  rw [applyRowDelta_insert]
                  have hT : (K ++ r :: rs ++ I) ++ [t.eval r]
                      = (K ++ [r]) ++ rs ++ (I ++ [t.eval r]) := by
                    simp only [List.append_assoc, List.cons_append,
                      List.nil_append]
                  rw [hT]
                  have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t.eval r]),
                      ∀ wk ∈ keyImgs fs key ((K ++ [r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    rw [keyImgs_append] at hik
                    rcases List.mem_append.mp hik with hik | hik
                    · exact hI ik hik wk ((mem_keyImgs_kept hk hk).mpr hwk)
                    · cases hpk : RowVals.project? fs (t.eval r) key with
                      | none => simp [keyImgs, hpk] at hik
                      | some k' =>
                          have hsing : keyImgs fs key [t.eval r] = [k'] := by
                            have h1 := keyImgs_cons_of_some (rs := []) hpk
                            rw [keyImgs_nil] at h1
                            exact h1
                          rw [hsing, List.mem_singleton] at hik
                          rw [← hik] at hpk
                          exact hfreshN r List.mem_cons_self (t.eval r) hnr
                            ik hpk wk ((mem_keyImgs_kept hk hk).mpr hwk)
                  rw [ih (K ++ [r]) (I ++ [t.eval r]) hprojS hfreshK hclTy
                    hndK hI1]
                  simp only [List.filterMap_cons, hkr', hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
          | cons chd ctl =>
              -- the written row
              have hk' : RowVals.project? fs (applySets u.sets r) key
                  = some k := by
                rw [project?_applySets' himm]; exact hk
              have hlow : u.lowerRow r
                  = [EventSourced.Delta.update (applySets u.sets r)]
                      ++ (u.insert?.map fun t =>
                        EventSourced.Delta.insert (t.eval r)).toList := by
                simp [Update2Item.lowerRow, hg, hd, hs]
              rw [hlow]
              cases hi : u.insert? with
              | none =>
                  have hnr : u.newRow r = none := by
                    unfold Update2Item.newRow
                    rw [if_pos hg, hi]
                    rfl
                  rw [Option.map_none, Option.toList_none, List.append_nil]
                  simp only [List.foldl_cons, List.foldl_nil]
                  rw [applyRowDelta_update_map key K rs I r (applySets u.sets r) k
                    hk hk' hnd hclTy hI]
                  have hT : (K ++ applySets u.sets r :: rs) ++ I
                      = (K ++ [applySets u.sets r]) ++ rs ++ I := by
                    simp only [List.append_assoc,
                      List.cons_append, List.nil_append]
                  rw [hT]
                  have hfreshK' : ∀ r' ∈ rs, ∀ new, u.newRow r' = some new →
                      ∀ k'', RowVals.project? fs new key = some k'' →
                        ∀ wk ∈ keyImgs fs key
                          ((K ++ [applySets u.sets r]) ++ rs), k'' ≠ wk := by
                    intro r' hr' new hn k'' hp' wk hwk
                    exact hfreshN r' (List.mem_cons_of_mem r hr') new hn k''
                      hp' wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  have hndK' : (keyImgs fs key
                      ((K ++ [applySets u.sets r]) ++ rs)).Nodup :=
                    nodup_keyImgs_kept hk hk' hnd
                  have hIK' : ∀ ik ∈ keyImgs fs key I,
                      ∀ wk ∈ keyImgs fs key
                        ((K ++ [applySets u.sets r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    exact hI ik hik wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  rw [ih (K ++ [applySets u.sets r]) I hprojS hfreshK'
                    hclTy hndK' hIK']
                  simp only [List.filterMap_cons, hkr, hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
              | some t =>
                  have hnr : u.newRow r = some (t.eval r) := by
                    unfold Update2Item.newRow
                    rw [if_pos hg, hi]
                    rfl
                  rw [Option.map_some, Option.toList_some]
                  simp only [List.singleton_append, List.foldl_cons,
                    List.foldl_nil]
                  rw [applyRowDelta_update_map key K rs I r (applySets u.sets r) k
                    hk hk' hnd hclTy hI]
                  rw [applyRowDelta_insert]
                  have hT : (K ++ (applySets u.sets r) :: rs ++ I) ++ [t.eval r]
                      = (K ++ [applySets u.sets r]) ++ rs ++ (I ++ [t.eval r]) := by
                    simp only [List.append_assoc, List.cons_append, List.nil_append]
                  rw [hT]
                  have hfreshK' : ∀ r' ∈ rs, ∀ new, u.newRow r' = some new →
                      ∀ k'', RowVals.project? fs new key = some k'' →
                        ∀ wk ∈ keyImgs fs key
                          ((K ++ [applySets u.sets r]) ++ rs), k'' ≠ wk := by
                    intro r' hr' new hn k'' hp' wk hwk
                    exact hfreshN r' (List.mem_cons_of_mem r hr') new hn k''
                      hp' wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  have hndK' : (keyImgs fs key
                      ((K ++ [applySets u.sets r]) ++ rs)).Nodup :=
                    nodup_keyImgs_kept hk hk' hnd
                  have hIK' : ∀ ik ∈ keyImgs fs key I,
                      ∀ wk ∈ keyImgs fs key
                        ((K ++ [applySets u.sets r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    exact hI ik hik wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t.eval r]),
                      ∀ wk ∈ keyImgs fs key
                        ((K ++ [applySets u.sets r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    rw [keyImgs_append] at hik
                    rcases List.mem_append.mp hik with hik | hik
                    · exact hI ik hik wk ((mem_keyImgs_kept hk hk').mpr hwk)
                    · cases hpk : RowVals.project? fs (t.eval r) key with
                      | none => simp [keyImgs, hpk] at hik
                      | some k' =>
                          have hsing : keyImgs fs key [t.eval r] = [k'] := by
                            have h1 := keyImgs_cons_of_some (rs := []) hpk
                            rw [keyImgs_nil] at h1
                            exact h1
                          rw [hsing, List.mem_singleton] at hik
                          rw [← hik] at hpk
                          exact hfreshN r List.mem_cons_self (t.eval r) hnr
                            ik hpk wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  rw [ih (K ++ [applySets u.sets r]) (I ++ [t.eval r])
                    hprojS hfreshK' hclTy hndK' hI1]
                  simp only [List.filterMap_cons, hkr, hnr]
                  simp only [List.append_assoc, List.cons_append, List.nil_append]
      · -- guard refuses: the row is untouched, no deltas
        have hkr : u.keepRow r = some r := by
          unfold Update2Item.keepRow
          rw [if_neg hg]
        have hnr : u.newRow r = none := by
          unfold Update2Item.newRow
          rw [if_neg hg]
        have hlow : u.lowerRow r = [] := by
          simp [Update2Item.lowerRow, hg]
        rw [hlow, List.foldl_nil]
        have hT : (K ++ r :: rs) ++ I = (K ++ [r]) ++ rs ++ I := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [hT]
        rw [ih (K ++ [r]) I hprojS hfreshK hclTy hndK hIK]
        simp only [List.filterMap_cons, hkr, hnr]
        simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The correspondence premise bundle (registration-checkable on
    data): the key column is not written; every row projects its key;
    the key column's type is codec-closed (ONE fact — the lawful
    `FieldVal.beq`'s round-trip warranty, spread over every image by
    `keyImgs_closed`); the images are pairwise distinct (core
    `List.Nodup` — R5 collapsed the both-direction `nodup2` ball); the
    inserted rows' keys are fresh against every table row. The bundle
    is Type-valued (the `CodecClosed` seed is data, not a Prop). -/
structure KeyCoherent {fs : List Field} (u : Update2Item fs) (key : String)
    (rows : List (RowVals fs)) where
  /-- The update carries the declared key (the elaboration gate). -/
  keyOf : u.key? = some key
  /-- Key immutability: no SET clause writes the key column (a key
      change is a delete+insert — the event-sourcing reading). -/
  keyImmutable : ∀ c ∈ u.sets, c.field.name ≠ key
  /-- Every row projects its key. -/
  proj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true
  /-- The key column's type is codec-closed (the key type's `KeyTy`
      discipline — the lawful `FieldVal.beq`'s warranty). -/
  imgClosed : CodecClosed (keyFieldType fs key)
  /-- Key images pairwise distinct (core `List.Nodup`). -/
  nodup : (keyImgs fs key rows).Nodup
  /-- Insert keys fresh against every table row's key. -/
  fresh : ∀ r ∈ rows, ∀ new, u.newRow r = some new → ∀ k',
    RowVals.project? fs new key = some k' →
    ∀ wk ∈ keyImgs fs key rows, k' ≠ wk

/-- LAW 6 (the lowering correspondence): the update's table effect IS
    the fold of its per-row deltas through the keyed table semantics —
    the SHARED delta shape (`EventSourced.Delta` at the schema row:
    insert/update carry the full row, remove carries the key image)
    applied by `applyRowDelta`. Under `KeyCoherent`, the positional
    batch semantics (`Update2Item.apply`) and the delta fold coincide. -/
theorem apply2_eq_foldDeltas {fs : List Field} (u : Update2Item fs)
    (key : String) (rows : List (RowVals fs)) (h : KeyCoherent u key rows) :
    u.apply rows
      = (rows.flatMap u.lowerRow).foldl (fun t d => applyRowDelta key d t)
          rows := by
  have hgo := foldDeltas_go u key h.keyOf h.keyImmutable [] rows []
    h.proj
    (by
      intro r hr new hn k' hp' wk hwk
      rw [List.nil_append] at hwk
      exact h.fresh r hr new hn k' hp' wk hwk)
    h.imgClosed
    (by rw [List.nil_append]; exact h.nodup)
    (by
      intro ik hik wk _
      rw [keyImgs_nil] at hik
      exact (List.not_mem_nil hik).elim)
  -- hgo : foldl … (([] ++ rows) ++ []) = [] ++ keeps ++ ([] ++ news)
  have htable : ([] ++ rows) ++ [] = rows := by
    rw [List.nil_append, List.append_nil]
  rw [htable] at hgo
  rw [hgo]
  simp [Update2Item.apply, List.nil_append]

/-! ### The applicator bridge (R1: ONE delta, ONE keyed reading)

The update lane's keyed applicator (`applyRowDelta`: update REPLACES
every key-matching row, remove DROPS them, insert APPENDS) and the
event-sourcing lane's (`EventSourced.apply`: insert/update UPSERT the
first match, remove erases the first) are the SAME keyed reading on
key-unique tables — the correspondence the W8.3 lowering law rides:
one shared Delta, two equivalent applicators. -/

/-- The shared-Delta key view of a row (the event-sourcing lane's key
    function at the schema row). The `none` default never fires under
    `KeyCoherent.proj`. -/
def esKeyOf (fs : List Field) (key : String) (r : RowVals fs) : FieldVal :=
  match RowVals.project? fs r key with
  | some k => k
  | none => ⟨.bool, .bool false⟩

theorem esKeyOf_eq_image {fs : List Field} {key : String} {r : RowVals fs}
    {k : FieldVal} (h : RowVals.project? fs r key = some k) :
    esKeyOf fs key r = k := by
  simp [esKeyOf, h]

/-- The remove arm's bridge: first-erase = drop-every-match, on
    key-unique tables. -/
theorem applyRowDelta_remove_eq_apply {fs : List Field} (key : String)
    (k : FieldVal) (rows : List (RowVals fs))
    (hproj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hnd : (keyImgs fs key rows).Nodup) :
    EventSourced.apply (esKeyOf fs key) (EventSourced.Delta.remove k) rows
      = applyRowDelta key (EventSourced.Delta.remove k) rows := by
  show rows.eraseIdx (rows.findIdx (fun x => esKeyOf fs key x == k))
    = rows.filter (fun old =>
        match RowVals.project? fs old key with
        | some a => !a.beq k | none => true)
  revert hproj
  revert hnd
  induction rows with
  | nil => intro _ _; rfl
  | cons r rs ih =>
      intro hnd hproj
      obtain ⟨ar, har⟩ :=
        Option.isSome_iff_exists.mp (hproj r List.mem_cons_self)
      have himgs : keyImgs fs key (r :: rs) = ar :: keyImgs fs key rs :=
        keyImgs_cons_of_some har
      rw [himgs] at hnd
      have hprojS : ∀ x ∈ rs, (RowVals.project? fs x key).isSome = true :=
        fun x hx => hproj x (List.mem_cons_of_mem r hx)
      have hndS : (keyImgs fs key rs).Nodup := (List.nodup_cons.mp hnd).2
      by_cases hhead : ar = k
      · -- the head IS the (unique) match: erase at 0; the tail stays
        have hpr : (fun x => esKeyOf fs key x == k) r = true := by
          simp only [esKeyOf_eq_image har, hhead]
          exact FieldVal.beq_refl _
        have hp' : (fun old =>
            match RowVals.project? fs old key with
            | some a => !a.beq k | none => true) r = false := by
          simp [har, hhead, FieldVal.beq_refl]
        have hkeep : ∀ old ∈ rs,
            (fun old =>
              match RowVals.project? fs old key with
              | some a => !a.beq k | none => true) old = true := by
          intro old ho
          show (match RowVals.project? fs old key with
              | some a => !a.beq k | none => true) = true
          cases hp2 : RowVals.project? fs old key with
          | none => rfl
          | some a =>
              have hmemA : a ∈ keyImgs fs key rs :=
                List.mem_filterMap.mpr ⟨old, ho, hp2⟩
              have hne : a ≠ k := by
                intro heq
                rw [heq] at hmemA
                have h2 : k ∈ keyImgs fs key rs := hmemA
                rw [← hhead] at h2
                exact (List.nodup_cons.mp hnd).1 h2
              have hae : a.beq k = false :=
                (FieldVal.beq_false_pair_of_ne
                  (keyImgs_closed hclTy hmemA)
                  (keyImgs_closed hclTy (by
                    rw [himgs, ← hhead]; exact List.mem_cons_self))
                  hne).1
              simp [hae]
        rw [List.findIdx_cons]
        simp only [hpr, cond_true, List.eraseIdx_cons_zero]
        rw [List.filter_cons_of_neg
          (p := fun old =>
            match RowVals.project? fs old key with
            | some a => !a.beq k | none => true)
          (a := r) (by simp [hp'])]
        rw [List.filter_eq_self.mpr hkeep]
      · -- head ≠ match: the head stays; the tail recurses
        have hmemAr : ar ∈ keyImgs fs key (r :: rs) := by
          rw [himgs]; exact List.mem_cons_self
        have hpr : (fun x => esKeyOf fs key x == k) r = false := by
          simp only [esKeyOf_eq_image har]
          exact FieldVal.beq_eq_false_of_ne hhead (keyImgs_closed hclTy hmemAr)
        have hp' : (fun old =>
            match RowVals.project? fs old key with
            | some a => !a.beq k | none => true) r = true := by
          simp [har, FieldVal.beq_eq_false_of_ne hhead
            (keyImgs_closed hclTy hmemAr)]
        rw [List.findIdx_cons]
        simp only [hpr, cond_true, List.eraseIdx_cons_succ]
        rw [List.filter_cons_of_pos
          (p := fun old =>
            match RowVals.project? fs old key with
            | some a => !a.beq k | none => true)
          (a := r) hp']
        exact congrArg (fun l => r :: l) (ih hndS hprojS)

/-- The update arm's bridge: first-match-upsert = replace-every-match,
    on key-unique tables with the written key PRESENT. -/
theorem applyRowDelta_update_eq_apply {fs : List Field} (key : String)
    (r' : RowVals fs) (k : FieldVal) (rows : List (RowVals fs))
    (hrr' : RowVals.project? fs r' key = some k)
    (hproj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hnd : (keyImgs fs key rows).Nodup)
    (hak : k ∈ keyImgs fs key rows) :
    EventSourced.apply (esKeyOf fs key) (EventSourced.Delta.update r') rows
      = applyRowDelta key (EventSourced.Delta.update r') rows := by
  show EventSourced.upsert (esKeyOf fs key) r' rows
    = rows.map (fun old =>
        match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if a.beq b then r' else old
            | none => old
        | none => old)
  revert hak
  revert hproj
  revert hnd
  induction rows with
  | nil =>
      intro _ _ hak
      rw [keyImgs_nil] at hak
      exact (List.not_mem_nil hak).elim
  | cons r rs ih =>
      intro hnd hproj hak
      obtain ⟨ar, har⟩ :=
        Option.isSome_iff_exists.mp (hproj r List.mem_cons_self)
      have himgs : keyImgs fs key (r :: rs) = ar :: keyImgs fs key rs :=
        keyImgs_cons_of_some har
      rw [himgs] at hnd
      have hprojS : ∀ x ∈ rs, (RowVals.project? fs x key).isSome = true :=
        fun x hx => hproj x (List.mem_cons_of_mem r hx)
      have hndS : (keyImgs fs key rs).Nodup := (List.nodup_cons.mp hnd).2
      rw [EventSourced.upsert, List.map_cons]
      by_cases hhead : ar = k
      · -- the head row IS the match: upsert replaces it in place
        have hbeq : (esKeyOf fs key r == esKeyOf fs key r') = true := by
          rw [esKeyOf_eq_image har, esKeyOf_eq_image hrr', hhead]
          exact FieldVal.beq_refl _
        have hArmR : (match RowVals.project? fs r key with
            | some a =>
                match RowVals.project? fs r' key with
                | some b => if a.beq b then r' else r
                | none => r
            | none => r) = r' := by
          simp [har, hrr', hhead, FieldVal.beq_refl]
        have htail : ∀ old ∈ rs,
            (match RowVals.project? fs old key with
              | some a =>
                  match RowVals.project? fs r' key with
                  | some b => if a.beq b then r' else old
                  | none => old
              | none => old) = old := by
          intro old ho
          cases hp2 : RowVals.project? fs old key with
          | none => rfl
          | some a =>
              have hmemA : a ∈ keyImgs fs key rs :=
                List.mem_filterMap.mpr ⟨old, ho, hp2⟩
              have hne : a ≠ k := by
                intro heq
                rw [heq] at hmemA
                have h2 : k ∈ keyImgs fs key rs := hmemA
                rw [← hhead] at h2
                exact (List.nodup_cons.mp hnd).1 h2
              have hae : a.beq k = false :=
                (FieldVal.beq_false_pair_of_ne
                  (keyImgs_closed hclTy hmemA)
                  (keyImgs_closed hclTy hak) hne).1
              simp [hrr', hae]
        rw [if_pos hbeq, hArmR, map_eq_self_of_forall htail]
      · -- head ≠ match: upsert descends; the map fixes the head
        have hmemAr : ar ∈ keyImgs fs key (r :: rs) := by
          rw [himgs]; exact List.mem_cons_self
        have haeHead : ar.beq k = false :=
          (FieldVal.beq_false_pair_of_ne (keyImgs_closed hclTy hmemAr)
            (keyImgs_closed hclTy hak) hhead).1
        have hbeq : (esKeyOf fs key r == esKeyOf fs key r') = false := by
          rw [esKeyOf_eq_image har, esKeyOf_eq_image hrr']
          exact haeHead
        have hArmR : (match RowVals.project? fs r key with
            | some a =>
                match RowVals.project? fs r' key with
                | some b => if a.beq b then r' else r
                | none => r
            | none => r) = r := by
          simp [har, hrr', haeHead]
        have hakS : k ∈ keyImgs fs key rs := by
          have hak2 : k ∈ ar :: keyImgs fs key rs := by rw [← himgs]; exact hak
          rcases List.mem_cons.mp hak2 with heq | hm
          · exact absurd heq.symm hhead
          · exact hm
        rw [if_neg (by simp [hbeq]), hArmR, ih hndS hprojS hakS]

/-- The insert arm's bridge: a FRESH key means no row matches, so the
    upsert is the append. -/
theorem applyRowDelta_insert_eq_apply {fs : List Field} (key : String)
    (r' : RowVals fs) (k : FieldVal) (rows : List (RowVals fs))
    (hrr' : RowVals.project? fs r' key = some k)
    (hproj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hfresh : ∀ j ∈ keyImgs fs key rows, j ≠ k) :
    EventSourced.apply (esKeyOf fs key) (EventSourced.Delta.insert r') rows
      = applyRowDelta key (EventSourced.Delta.insert r') rows := by
  show EventSourced.upsert (esKeyOf fs key) r' rows = rows ++ [r']
  have hfind : rows.findIdx (fun x => esKeyOf fs key x == esKeyOf fs key r')
      = rows.length := by
    rw [List.findIdx_eq_length_of_false]
    intro r hr
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hproj r hr)
    show (esKeyOf fs key r == esKeyOf fs key r') = false
    rw [esKeyOf_eq_image hj, esKeyOf_eq_image hrr']
    exact FieldVal.beq_eq_false_of_ne
      (hfresh j (List.mem_filterMap.mpr ⟨r, hr, hj⟩))
      (keyImgs_closed hclTy (List.mem_filterMap.mpr ⟨r, hr, hj⟩))
  rw [EventSourced.upsert_eq_append (esKeyOf fs key) r' rows hfind]

/-- THE APPLICATOR CORRESPONDENCE (R1): the update lane's keyed
    applicator IS the event-sourcing lane's keyed semantics on
    key-unique tables — insert appends (fresh key), update replaces
    the one match (present key), remove drops the one match. The
    per-variant premises are `KeyCoherent`'s, split by arm. -/
theorem applyRowDelta_eq_apply {fs : List Field} (key : String)
    (d : RowDelta fs) (rows : List (RowVals fs))
    (hproj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true)
    (hclTy : CodecClosed (keyFieldType fs key))
    (hnd : (keyImgs fs key rows).Nodup)
    (hd : match d with
      | .insert r => ∃ k, RowVals.project? fs r key = some k
          ∧ ∀ j ∈ keyImgs fs key rows, j ≠ k
      | .update r => ∃ k, RowVals.project? fs r key = some k
          ∧ k ∈ keyImgs fs key rows
      | .remove _ => True) :
    EventSourced.apply (esKeyOf fs key) d rows = applyRowDelta key d rows := by
  cases d with
  | insert r =>
      obtain ⟨k, hk, hf⟩ := hd
      exact applyRowDelta_insert_eq_apply key r k rows hk hproj hclTy hf
  | update r =>
      obtain ⟨k, hk, hmem⟩ := hd
      exact applyRowDelta_update_eq_apply key r k rows hk hproj hclTy hnd hmem
  | remove k =>
      exact applyRowDelta_remove_eq_apply key k rows hproj hclTy hnd

/-! ## The obligation view (W7.1's substrate, the keys-lane shape) -/

/-- The fact a keyed v2 update records: key-uniqueness is PRESERVED by
    the update's table effect. -/
inductive Update2Claim where
  | keyUnique (fs : List Field) (u : Update2Item fs) (key : String)

/-- The update-lane obligation: the kit's shape at the update row
    (`abbrev` — reducible, the kit discipline). -/
abbrev Update2Obligation := CodegenCore.Obligation Update2Claim

/-- The computed tier: preservation claims are decidable row-data
    predicates over the pinned table — the `decidableNow` rung. -/
def Update2Claim.tierOf : Update2Claim → CodegenCore.Obligation.Tier :=
  fun _ => .decidableNow

/-- The obligation VIEW of one registered v2 update (additive — the
    `KeyDecl.obligations` precedent): a KEYED update carries one
    obligation — its table effect preserves key-uniqueness. -/
def Update2Item.obligations {fs : List Field} (u : Update2Item fs) :
    List Update2Obligation :=
  match u.key? with
  | none => []
  | some key =>
      [{ label := s!"{u.record}.{u.name}-preserves-unique({key})"
       , tier := Update2Claim.tierOf (.keyUnique fs u key)
       , payload := .keyUnique fs u key
       , provenance := u.record.toName }]

/-- All update obligations of a registered set (the enumeration the
    tests pin). -/
def update2Obligations (us : List SomeUpdate2) : List Update2Obligation :=
  us.flatMap (fun s => s.update.obligations)

/-- The decidableNow CLAIM at the update lane: on the pinned
    ALL-DEFAULT SINGLETON table (the invariant/key lane's default-row
    discipline — the one table the lane can materialize from the
    declaration alone), IF the table's keys are unique THEN the
    post-update table's keys are unique (`KeyDecl.uniqueOn` — the
    W8.2 authority — on both sides). The antecedent makes vacuous
    guards (the default row refuses) honest: the claim still exercises
    the wiring. A duplicate-key insert decides FALSE → the backend
    REFUSES (the loud gap). -/
def Update2Obligation.decidableClaim (o : Update2Obligation) : Prop :=
  match o.payload with
  | .keyUnique fs u key =>
      match SchemaLang.defaultRow? fs with
      | some row =>
          (if KeyDecl.uniqueOn ⟨u.record, fs, key, []⟩ [row] then
              KeyDecl.uniqueOn ⟨u.record, fs, key, []⟩ (u.apply [row])
            else true) = true
      | none => False

/-- The claim IS decidable: valued default rows reduce it to Bool
    equations over computed tables. (Named explicitly — the
    anonymous-instance auto-name collides cross-module, the
    `keyClaimDecidable` precedent.) -/
instance update2ClaimDecidable (o : Update2Obligation) :
    Decidable o.decidableClaim := by
  unfold Update2Obligation.decidableClaim
  cases hp : o.payload with
  | keyUnique fs u key =>
      show Decidable (match SchemaLang.defaultRow? fs with
        | some row =>
            (if KeyDecl.uniqueOn ⟨u.record, fs, key, []⟩ [row] then
                KeyDecl.uniqueOn ⟨u.record, fs, key, []⟩ (u.apply [row])
              else true) = true
        | none => False)
      cases hd : SchemaLang.defaultRow? fs <;> infer_instance

/-- THE DISCHARGE (the keys-lane shape): only the `decidableNow` rung
    is an update-lane assignment; the kernel's `decide` over
    `decidableClaim` is the evidence. `none` = the loud gap. (The
    decidableNow backend is the KIT's — `decideDischarge`.) -/
def Update2Obligation.discharge (o : Update2Obligation) :
    Option CodegenCore.Obligation.Evidence :=
  CodegenCore.Obligation.decideDischarge Update2Obligation.decidableClaim o

/-- SOUNDNESS: a `.decided true` verdict means the claim HOLDS (the
    kernel's `decide` validated the preservation predicate on the
    pinned table — `of_decide_eq_true`; no new trust base). Routes
    through the kit's `decideDischarge_sound` — the proof object is
    shared. -/
theorem Update2Obligation.discharge_decidableNow_sound (o : Update2Obligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim :=
  CodegenCore.Obligation.decideDischarge_sound _ _ ht h

/-- COMPLETENESS: a true claim discharges to the `.decided true`
    evidence — the backend FIRES on the claims it can decide. -/
theorem Update2Obligation.discharge_decidableNow_of_claim (o : Update2Obligation)
    (ht : o.tier = .decidableNow) (h : o.decidableClaim) :
    o.discharge = some (.decided true) :=
  CodegenCore.Obligation.decideDischarge_of_claim _ _ ht h

end SchemaLang
