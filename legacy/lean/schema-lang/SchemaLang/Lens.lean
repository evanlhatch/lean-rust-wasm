/-
# SchemaLang.Lens — the lawful-lens core (the schema-path law class)

PROVENANCE: the CSLib lawful-lens proposal's naming — `get_set` /
`set_get` / `set_set` / `over` — is used verbatim for the four vanilla
lens laws. The TWO EXTRAS are OURS (the DeltaSystem-flavored pair
vanilla lenses do not carry): `put_comm` (distinct-put commutation —
two writes to DIFFERENT targets compose in either order) and
`put_read_neutral` (put-read neutrality — a write does not disturb any
OTHER target's read). Both are quantified over a path-level
`Distinct` relation; at a FIXED target they degenerate (same-target
composition is `set_set`'s business).

The class is over a path type `P`, a container `C`, and the DEPENDENT
value family `A : P → Type` — the schema lane's payloads are
type-indexed (`ColPath n t fs` reads a `Value t`), so the vanilla
`A : Type` lens shape does not fit (the delta-lens generalization is
the honest one; `over` stays at a fixed `p`, where `A p` is constant).

Design decisions:
- `over` is a DEF over `get`/`put` (read-modify-write — the ONLY
  mutation surface the class admits: `put_eq_over` shows every `put`
  is `over`'s constant rewriter). The class carries no free-floating
  `over` data to keep lawful.
- `Distinct : P → P → Prop` is a class FIELD (not a parameter): the
  binary laws' content lives at the instance, where the relation is
  named (`ColPath`'s is name inequality).

The INSTANCE for `Validate.ColPath` (over the name-carrying sigma
`SomeColPath fs` — one `P` per schema, names as data) cites the
existing row-level law layer, which IS the proofs' content:
- `get_set` ← `ColPath.lens_get_set` (NEW — no existing lemma; the
  write-spine/gate-spine duality makes it a two-case induction),
- `set_get` ← `ColPath.lens_set_get` (NEW — same shape; LOUD NOTE: no
  prior lemma in Update/Update2 pinned it — the journal lane never
  needed it because revert reads the journal, not the row),
- `set_set` ← `ColPath.set_commute_same` (Update — later-wins),
- `put_comm` ← `ColPath.set_commute_disjoint` (Update — the
  order-free composition law the tick's cascade relies on),
- `put_read_neutral` ← `ColPath.get_set_neutral` (Update — write
  locality).

THE ABSORPTION MAP (documented follow-up — NOT this order): the six
existing lemma families re-point to the class (consumers cite the
class laws; the lemmas become the instance's named shadows):
1. `VExpr.evalV_set_neutral` (Update) → `put_read_neutral` lift at
   the boxed evaluator,
2. `VExpr.evalRaw_set_neutral` (Update) → same lift, raw lane,
3. `RowTmpl.eval_set_neutral` (Update2) → same lift, templates,
4. `ColPath.set_project?_neutral` (Update2) → `put_read_neutral` at
   the name-keyed projection (`RowVals.project?`),
5. `project?_applySets` (Update2) → the fold lift of 4,
6. `validates_applySets` (Update2) → the verdict corollary of the
   evaluator lift (`validates = evalB == 1`).
Order: 4 before 5 (5 cites 4); 6 after 5; 1–3 independent. Already
cited HERE (not follow-up work): `set_commute_same` → `set_set`,
`set_commute_disjoint` → `put_comm`, `get_set_neutral` →
`put_read_neutral`.

The CASEPRISM bundle (the variant lane, `Validate`'s VCase family):
`payloadOf` (the match) + `inject` (the ctor) + the prism law
(try∘build — `evalCase_here_sound` IS its here-instance, cited) + the
miss law (an unfired arm's read is `none` — the 0-analog
`HasPayload.miss` never leaks through a fired read). Instances derive
from `HasPayload` — the honest-NONE rule (a NONE-payload case has no
accessor BY CONSTRUCTION) is inherited, not restated.

Deliberate exclusions: no `Traversal`/`Setter` grades (one target per
path, by construction); no `revert` law (overwrite channels are not
group elements — the journal carries S0, `set_commute_same`'s doc);
no raw-lane prism (`evalCase` is SPEC-level only — the Phase-3
compiled-lane decision). Ownership: this module (the lens core); the
row layer's law lemmas stay in Update/Update2 until the absorption
lands.
-/

module

public import SchemaLang.Validate
public import SchemaLang.Update

-- The shared delta/lens law shape (`DisjointCommute`): the instance
-- below cites it. Kit is core-only — safe on the public surface
-- (W5.4 constraint 14).
public import CodegenCore.Kit

@[expose] public section

namespace SchemaLang

/-! ## The lawful-lens class -/

/-- The lawful schema-path class: a path type `P` reading/writing a
    container `C` at a (dependent) value family `A` — the family is a
    FIELD (not a parameter): it is determined by the instance, so the
    elaborator resolves `get`/`put` from the path and container types
    alone (the plain-parameter shape leaves a metavariable in instance
    search — the dependent family cannot be a search key). The four
    vanilla laws carry the CSLib-proposal naming; the two delta-flavored
    extras (`put_comm`, `put_read_neutral`) quantify over the path-level
    `Distinct` relation. -/
class SchemaPath (P : Type) (C : Type) where
  /-- The (dependent) value family the paths read and write. -/
  A : P → Type
  /-- The read: the path's value out of the container. -/
  get : (p : P) → C → A p
  /-- The put: write the path's value into the container. -/
  put : (p : P) → C → A p → C
  /-- Two paths name DIFFERENT targets (the delta pair's side
      condition; at a fixed target the relation is simply empty). -/
  Distinct : P → P → Prop
  /-- Put then get = the value (the van Laarhoven `get_set`). -/
  get_set : ∀ (p : P) (c : C) (a : A p), get p (put p c a) = a
  /-- Put the gotten = identity on this target's container. -/
  set_get : ∀ (p : P) (c : C), put p c (get p c) = c
  /-- Put-put collapses (later-wins at the same target). -/
  set_set : ∀ (p : P) (c : C) (a b : A p), put p (put p c a) b = put p c b
  /-- DISTINCT-put commutation (OURS, the delta-flavored pair's first
      half): two writes to different targets compose in either order. -/
  put_comm : ∀ (p q : P) (c : C) (a : A p) (b : A q), Distinct p q →
    put q (put p c a) b = put p (put q c b) a
  /-- PUT-READ NEUTRALITY (OURS, the second half): a write does not
      disturb any OTHER target's read. -/
  put_read_neutral : ∀ (p q : P) (c : C) (a : A p), Distinct p q →
    get q (put p c a) = get q c

/-! ### `over` — read-modify-write, the only mutation surface -/

/-- Read-modify-write: `put p c (f (get p c))`. THE only mutation
    surface a lawful path admits — every `put` IS an `over`
    (`put_eq_over`), so consumers write `over` and the laws carry. -/
def SchemaPath.over {P : Type} {C : Type}
    [inst : SchemaPath P C] (p : P) (f : inst.A p → inst.A p) (c : C) : C :=
  inst.put p c (f (inst.get p c))

/-- `over`'s constant rewriter IS the put — the only-mutation-surface
    pin (definitional). -/
theorem SchemaPath.put_eq_over {P : Type} {C : Type}
    [inst : SchemaPath P C] (p : P) (c : C) (a : inst.A p) :
    inst.put p c a = inst.over p (fun _ => a) c := rfl

/-- `over` the identity is the identity (rides `set_get`). -/
theorem SchemaPath.over_id {P : Type} {C : Type}
    [inst : SchemaPath P C] (p : P) (c : C) :
    inst.over p id c = c := inst.set_get p c

/-- `over` reads back the rewritten value (rides `get_set`). -/
theorem SchemaPath.over_get {P : Type} {C : Type}
    [inst : SchemaPath P C] (p : P) (f : inst.A p → inst.A p) (c : C) :
    inst.get p (inst.over p f c) = f (inst.get p c) :=
  inst.get_set p c (f (inst.get p c))

/-! ## The `ColPath` instance -/

/-! The class needs ONE path type per schema; `ColPath n t fs` bakes
    the name into its type, so the instance rides the name-carrying
    sigma (the `abbrev` rule — reducible, instance search sees it). -/

/-- Every `ColPath` over a FIXED schema, as one type: name + type +
    path. The lens class's `P` for the row lane. -/
abbrev SomeColPath (fs : List Field) : Type :=
  Σ (_n : String) (_t : Ty), ColPath _n _t fs

/-- `get_set` at the row lane: put then get = the value. NEW PROOF
    (no prior lemma — see the header's LOUD NOTE): the two-case
    induction follows the constructor spine `set` shares with `get`. -/
theorem ColPath.lens_get_set {n : String} {t : Ty} : ∀ {fs : List Field}
    (p : ColPath n t fs) (row : RowVals fs) (v : Value t),
    p.get (p.set row v) = v := by
  intro fs p
  induction p with
  | here => intro row _v; cases row; rfl
  | there p ih =>
      intro row v
      cases row with
      | cons w vs => simp only [ColPath.set, ColPath.get]; exact ih vs v

/-- `set_get` at the row lane: put the gotten = identity. NEW PROOF
    (no prior lemma — the journal lane never needed it: revert reads
    the journal, not the row; see the header). -/
theorem ColPath.lens_set_get {n : String} {t : Ty} : ∀ {fs : List Field}
    (p : ColPath n t fs) (row : RowVals fs),
    p.set row (p.get row) = row := by
  intro fs p
  induction p with
  | here => intro row; cases row; rfl
  | there p ih =>
      intro row
      cases row with
      | cons w vs =>
          simp only [ColPath.set, ColPath.get]
          exact congrArg (RowVals.cons w) (ih vs)

/-- THE INSTANCE: the row lane's lawful schema path. Each law field
    cites the existing lemma that IS its content (the header's map):
    `set_set` ← `set_commute_same`, `put_comm` ←
    `set_commute_disjoint`, `put_read_neutral` ← `get_set_neutral`;
    `get_set`/`set_get` are the two new spines. `Distinct` = name
    inequality (the name determines the position — the HasCol
    priority). -/
instance instSchemaPathSomeColPath (fs : List Field) :
    SchemaPath (SomeColPath fs) (RowVals fs) where
  A p := Value p.2.1
  get p row := p.2.2.get row
  put p row v := p.2.2.set row v
  Distinct p q := p.1 ≠ q.1
  get_set := by
    intro ⟨_, _, p⟩ row v
    exact ColPath.lens_get_set p row v
  set_get := by
    intro ⟨_, _, p⟩ row
    exact ColPath.lens_set_get p row
  set_set := by
    intro ⟨_, _, p⟩ row v w
    exact ColPath.set_commute_same p row v w
  put_comm := by
    intro ⟨n₁, _, p₁⟩ ⟨n₂, _, p₂⟩ row v₁ v₂ hne
    exact ColPath.set_commute_disjoint p₁ p₂ hne row v₁ v₂
  put_read_neutral := by
    intro ⟨n₁, _, p₁⟩ ⟨n₂, _, p₂⟩ row v hne
    exact ColPath.get_set_neutral p₂ p₁ (Ne.symm hne) row v

/-! ## THE unification — a lens PATH is a delta LOCATION

`put_comm` and `Dbsp.DeltaSystem.disjoint_commutes` are the SAME law
at two granularities; the shared structure is
`CodegenCore.DisjointCommute` — one location per mutation, a
disjointness relation, write-disjoint mutations commute. The lens
instantiates it at a write = a path + its (dependent) value (the
sigma `Mut` below), location = the path, `Disjoint` = `Distinct`, and
the law field CITES `put_comm` — the existing theorem IS the proof.

`put_read_neutral` stays LENS-SIDE (the honest judgment): the shared
structure has no READ surface — a delta system is write-only by
design (`Dbsp.Effects`' header: sound in one way) — so
read-neutrality has no honest instance at the delta granularity; it
does not factor into `DisjointCommute`. -/

/-- The lens's mutation type: a write = a path + its (dependent)
    value. An abbrev (the abbrev rule — reducible, so the
    `DisjointCommute` instance's type resolves against it). -/
abbrev SchemaPath.Mut {P : Type} {C : Type} [inst : SchemaPath P C] :
    Type := Σ p : P, inst.A p

/-- THE unification: the lawful lens IS a `DisjointCommute` — the
    delta law at the path granularity. The law field cites `put_comm`
    (no re-proof). -/
instance instDisjointCommuteOfSchemaPath {P : Type} {C : Type}
    [inst : SchemaPath P C] :
    CodegenCore.DisjointCommute C P inst.Mut where
  apply s m := inst.put m.1 s m.2
  loc m := m.1
  Disjoint := inst.Distinct
  disjoint_commutes m₁ m₂ hd s := inst.put_comm m₁.1 m₂.1 s m₁.2 m₂.2 hd

/-! ## The `CasePrism` bundle (the variant lane) -/

/-- Inject the payload at the path's position (the prism's BUILD: the
    ctor spine, pure data — the `payloadOf` walk's inverse). -/
def CasePath.inject {n : String} {t : Ty} :
    {cs : List VariantCase} → CasePath n t cs → Value t → VRow cs
  | _, .here, v => .here v
  | _, .there q, v => .there (q.inject v)

/-- The try∘build law at the path level: inject then extract recovers
    (the structural half of the prism law — the eval-level half is
    `evalCase_here_sound`, cited at `CasePrism.eval_inject`). -/
theorem CasePath.inject_payloadOf {n : String} {t : Ty} :
    ∀ {cs : List VariantCase} (q : CasePath n t cs) (v : Value t),
      q.payloadOf (q.inject v) = some v := by
  intro cs q
  induction q with
  | here => intro v; rfl
  | there q ih =>
      intro v
      simp only [inject, CasePath.payloadOf]
      exact ih v

/-- The miss law at the path level: an UNFIRED arm's read is `none` —
    the evaluator's 0-analog fallback (`HasPayload.miss`) only fires on
    genuinely-unfired rows. -/
theorem CasePath.payloadOf_miss {n : String} {t : Ty} :
    ∀ {cs : List VariantCase} (q : CasePath n t cs) (row : VRow cs),
      VRow.isName row n = false → q.payloadOf row = none := by
  intro cs q
  induction q with
  | here =>
      intro row h
      cases row with
      | here _ =>
          -- the fired tag IS this arm — `isName` answers true, the
          -- miss hypothesis is contradictory
          exfalso
          simp only [VRow.isName, beq_self_eq_true] at h
          exact absurd h (by simp)
      | there _ => rfl
  | there q ih =>
      intro row h
      cases row with
      | here _ => rfl
      | there r => exact ih r h

/-- The lawful prism over the variant lane (`Validate`'s VCase
    family): `payloadOf` (the match) + `inject` (the ctor) + the
    try∘build law + the miss law. The CSLib-proposal naming, applied
    to the second expression family. -/
class CasePrism (cs : List VariantCase) (n : String) (t : Ty) where
  /-- The match: the row's payload at this arm, `some` iff fired. -/
  payloadOf : VRow cs → Option (Value t)
  /-- The ctor: build a row firing THIS arm with the payload. -/
  inject : Value t → VRow cs
  /-- try∘build: inject then extract recovers the payload. -/
  prism_law : ∀ (v : Value t), payloadOf (inject v) = some v
  /-- miss: an unfired arm's read is `none` (the 0-analog
      `HasPayload.miss` never leaks through a fired read). -/
  miss_law : ∀ (row : VRow cs), VRow.isName row n = false →
    payloadOf row = none

/-- The prism instance: derives from `HasPayload` (the accessor's
    evidence) — the honest-NONE rule is inherited (a NONE-payload case
    has no `HasPayload`, hence no prism, BY CONSTRUCTION). -/
instance instCasePrismOfHasPayload {cs : List VariantCase} {n : String}
    {t : Ty} [h : HasPayload cs n t] : CasePrism cs n t where
  payloadOf := fun row => h.path.payloadOf row
  inject := fun v => h.path.inject v
  prism_law := fun v => CasePath.inject_payloadOf h.path v
  miss_law := fun row hr => CasePath.payloadOf_miss h.path row hr

/-- The eval-level citation (the header's map): `evalCase_here_sound`'s
    payload conjunct IS the prism law's here-instance — the prism law
    at the EVALUATOR, not just the path walk. -/
theorem CasePrism.eval_inject {cs : List VariantCase} {n : String}
    (p : Value .u64) :
    evalCase (VCase.payload (cs := (n, some .u64) :: cs) n) (.here p) = p :=
  (evalCase_here_sound n cs p).2

end SchemaLang
