/-
# SchemaCore.Update — the update lane: SET/INSERT/DELETE over declared keys

Owner: the update lane agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §2 (the Change ladder — the
updates ride it), notes/v3/02-data-plane.md §5 (commands are relations;
the three realization paths — here: DERIVE, the update's relation
structurally determines its output, so the evaluation is the
realization), notes/v3/08-capabilities.md #3 (Updates v2: multi-set/
insert/delete over declared keys, total, order-free under disjoint keys
— proved once, cited), notes/v3/03-bidirectional.md §7 (the
trichotomy: a COMMAND is requested intent, a DELTA is the accepted net
change — the evaluation realizes the command as a delta; validity is
checked at the transaction boundary, not per row).

Provenance: mined from
`legacy/lean/schema-lang/SchemaLang/Update2.lean` (W8.3), ported at the
slice's model size (records-only items, literal values, `Pred` guards):

- the ColPath write spine — the structural write path (data, GADT), its
  projection neutrality and its disjoint-commutation law;
- the update language: SET clauses (a written column + a typed value) +
  INSERT (a full literal row) + DELETE, under a `Pred` guard — the
  legacy `Update2Item` surface narrowed to what the new tree's items
  support (records-only; no VExpr — SET values are LITERALS of the
  column's own type, so the batch law's read set is the GUARD's, derived
  by `Pred.reads`, never hand-listed);
- the TOTAL evaluation (every row is decided by the guard; no cascade
  within an update — guard, values, and the insert row all read the
  PRE-update state);
- the laws, proved at the new substrate:
  1. `applySets_perm` — clause-order freedom within one update (distinct
     names), Perm induction over `ColPath.set_commute_disjoint`;
  2. the neutrality family — a write fold avoids every column a
     predicate reads, so the predicate's verdict is unchanged;
  3. `applySets_comm` — two write folds with disjoint columns commute;
  4. `apply2_comm_perm` / `apply2_comm` — TWO updates compose in either
     order under `UpdateCompat` (the honest disjoint-keys premise pack:
     derived reads vs writes, disjoint writes, each side's guard refuses
     the other's inserts, no insert-while-delete) — a permutation of the
     final table in general, plain equality with no inserts;
  5. the delta-lowering — the update's table effect IS the fold of its
     per-row `RowDelta`s through the keyed applicator `applyRowDelta`,
     under `KeyCoherent` (the key immutable, keys project, images
     pairwise distinct, inserts fresh);
  6. the Change-ladder instances (Kit.Change): the update language lands
     at `Applicable` ONLY — `updateItem_notComposable` PROVES no
     composition exists (a single guard/delete pair cannot be the net of
     two guard-channels — the doctrine's set-forgets-old-value example
     at the update granularity); the COMMUTING rung lands on the keyed
     delta carrier `KeyDelta` (the old-retaining checked put — 03 §7's
     replacement = −old +new at the canonical keyed meaning: the row-set
     is a function from key to row), with `Disjoint` explicit;
- the lane's mount: the WF checker + the curated Diag envelope (the SU
  family, allocated from the persisted registry) + the Prop-indexed
  obligation view (a keyed update's table effect preserves key
  uniqueness on the pinned all-default singleton — the kit's
  decidableNow backend).

Deliberate exclusions (the leftover rule, each names its reason): the
`schema_update` elaboration command — no consumer yet (the lane's data +
eval + laws are the honest minimal; the command surface lands with its
first emitted surface); the ZSet/additive rung for TABLES — a list table
is an order-dependent bag, not the canonical Z-set (zset/'s carrier);
the additive rung is claimed nowhere here; composite keys (v1: single
field keys, the Keys lane's granularity); cross-table updates.

The five questions (notes/v3/01-core.md): root = Change (01 §2) riding
the Universe's rows — the update is the data plane's operational half
(03 §7); carrier = the GADT write path (a write to a missing or
mistyped column is UNCONSTRUCTIBLE — the ColPath index) + the
Prop-indexed obligation (Kit.Obligation); spine reading = none — the
lane rides the substrate (Kit.Change, SchemaCore.Keys) the way keys
does; ladder rung = `Applicable` for the language (PROVED not
composable), `Commuting` for the keyed delta (Disjoint explicit), the
obligations at `decidableNow`; gate row = SchemaTests' updateSpec (the
order-freedom pin + the SAME-key later-wins counterexample + the
neutrality pins + the mandatory negative controls) + the axiom report.

Core-only (imports SchemaCore.Keys + SchemaCore.Pred — the cone rule).
-/

import SchemaCore.Keys
import SchemaCore.Pred
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace SchemaCore

/-! ## The write spine — ColPath -/

/-- The structural write path: the column named `n` carrying type `t`,
    found positionally in the field list. A write to a column that does
    not exist, or exists at another type, is UNCONSTRUCTIBLE — the path
    IS the evidence (the legacy `ColPath` doctrine, ported). -/
inductive ColPath (n : String) (t : Ty) : List Field → Type where
  | /-- The column is the head field. -/
    here : {fs : List Field} → ColPath n t (⟨n, t⟩ :: fs)
  | /-- The column is deeper in the field list. -/
    there : {f : Field} → {fs : List Field} → ColPath n t fs →
      ColPath n t (f :: fs)

/-- THE WRITE: replace the path's column value, all else untouched
    (positional — the row's shape is the path's index). -/
def ColPath.set {n : String} {t : Ty} : {fs : List Field} →
    ColPath n t fs → RowVals fs → Value t → RowVals fs
  | _, .here, .cons _ vs, v => .cons v vs
  | _, .there p, .cons a vs, v => .cons a (p.set vs v)

/-- A name inequality as a Bool pin (the write-spine lemmas' small
    step; core ships the contrapositive `not_eq_of_beq_eq_false`). -/
theorem String.beq_false_of_ne' {a b : String} (h : a ≠ b) :
    (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => exact absurd (eq_of_beq hb) h

/-- The projection is INVISIBLE to a write at another column: setting
    column `n` leaves the projection at `m ≠ n` unchanged (the legacy
    `ColPath.set_project?_neutral`). -/
theorem ColPath.set_project?_neutral {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs) (v : Value t)
      (m : String), m ≠ n →
      RowVals.project? fs (p.set row v) m = RowVals.project? fs row m := by
  intro fs p
  induction p with
  | here =>
      intro row v m hm
      cases row with
      | cons a vs =>
          have hnm : n ≠ m := fun h => hm h.symm
          simp only [ColPath.set, RowVals.project?, String.beq_false_of_ne' hnm]
          rfl
  | there p ih =>
      intro row v m hm
      cases row with
      | cons a vs =>
          simp only [ColPath.set, RowVals.project?]
          split
          · rfl
          · exact ih vs v m hm

/-- THE DISJOINT COMMUTATION: two writes at distinct columns commute —
    the write spine's order-freedom kernel (the legacy
    `ColPath.set_commute_disjoint`). -/
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
                  simp only [ColPath.set]
                  rw [ih p₁' p₂' (fun h => hne (by
                    rw [h])) vs v₁ v₂]

/-! ## The update language -/

/-- One SET clause: the written column (the name rides the field), the
    structural write path (the ColPath spine — existence + type are the
    INDEX, not a checker pass), and the value typed at the column's OWN
    type (the GADT gate — a mistyped write is unconstructible). The
    legacy `SetClause` narrowed to literal values (the new tree has no
    VExpr — the honest minimal the items support). -/
structure SetClause (fs : List Field) where
  field : Field
  path : ColPath field.name field.ty fs
  value : Value field.ty

/-- The update item over table `fs`: the record's registry name (the
    provenance + key-resolution face), the name, the guard, the SET
    clauses, the row-level effects, and the record's DECLARED key field
    (resolved at registration; insert/delete updates MUST be keyed —
    the WF rung below, the legacy elaboration gate's runtime face). -/
structure UpdateItem (fs : List Field) where
  record : String
  name : String
  guard : Pred fs
  sets : List (SetClause fs)
  delete : Bool := false
  insert? : Option (RowVals fs) := none
  key? : Option String := none

/-- The DERIVED write set (the SET clauses' columns; insert/delete are
    row-level effects, not column writes). -/
def UpdateItem.setNames {fs : List Field} (u : UpdateItem fs) : List String :=
  u.sets.map (fun c => c.field.name)

/-- The DERIVED read set (the guard's columns — the batch law: values
    are literals, so the guard is the only reader; deduped). -/
def UpdateItem.reads {fs : List Field} (u : UpdateItem fs) : List String :=
  u.guard.reads.eraseDups

/-- The guard's verdict (the legacy `validates`, at the Pred checker). -/
def validates {fs : List Field} (g : Pred fs) (r : RowVals fs) : Bool :=
  g.check r

/-! ## The semantics — total, batch -/

/-- The simultaneous multi-write. BATCH by construction: the values are
    literals, so the fold's accumulator only accumulates writes — and
    the guard's read set is the derived `reads` (the batch law's
    read-set face). -/
def applySets {fs : List Field} (sets : List (SetClause fs))
    (r : RowVals fs) : RowVals fs :=
  sets.foldl (fun acc c => c.path.set acc c.value) r

/-- The surviving row (`none` = the guarded row is deleted). The guard
    reads the ORIGINAL row (no cascade within an update). -/
def UpdateItem.keepRow {fs : List Field} (u : UpdateItem fs)
    (r : RowVals fs) : Option (RowVals fs) :=
  if validates u.guard r then
    if u.delete then none else some (applySets u.sets r)
  else some r

/-- The inserted row (`none` = no insert fired). The insert row is a
    FULL literal row (records-only narrowing — the legacy INSERT-SELECT
    template's expression lanes have no consumer here), computed at the
    GUARDED row's pre-update state (it is constant — the honest
    degenerate case of the template reading). -/
def UpdateItem.newRow {fs : List Field} (u : UpdateItem fs)
    (r : RowVals fs) : Option (RowVals fs) :=
  if validates u.guard r then u.insert? else none

/-- The batch semantics: TOTAL (every row is decided by the guard),
    kept rows in order, inserts appended at the end (DETERMINISTIC
    placement — the no-insert law's equality is list equality; the
    general law is a permutation). -/
def UpdateItem.apply {fs : List Field} (u : UpdateItem fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  rows.filterMap u.keepRow ++ rows.filterMap u.newRow

/-- The membership kit (the derived sets earn the premises). -/
theorem UpdateItem.mem_setNames {fs : List Field} {u : UpdateItem fs}
    {c : SetClause fs} (hc : c ∈ u.sets) : c.field.name ∈ u.setNames :=
  List.mem_map_of_mem hc

theorem UpdateItem.mem_reads_of_guard {fs : List Field} {u : UpdateItem fs}
    {n : String} (h : n ∈ u.guard.reads) : n ∈ u.reads :=
  List.mem_eraseDups.mpr h

/-! ## Law 1 — clause-order freedom within one update -/

/-- The fold's perm-invariance (generalized accumulator — the
    induction's motive). Values are literals, so the swap case is
    exactly `ColPath.set_commute_disjoint`. -/
theorem applySets_foldl_perm {fs : List Field}
    {s₁ s₂ : List (SetClause fs)} (hp : s₁.Perm s₂)
    (hnd : (s₁.map fun c => c.field.name).Nodup) :
    ∀ (_r₀ acc : RowVals fs),
      s₁.foldl (fun a c => c.path.set a c.value) acc
        = s₂.foldl (fun a c => c.path.set a c.value) acc := by
  induction hp with
  | nil => intro _ _; rfl
  | cons x _ ih =>
      intro r₀ acc
      simp only [List.foldl_cons]
      exact ih ((List.nodup_cons.mp hnd).2) r₀
        (x.path.set acc x.value)
  | swap x y l =>
      -- `Perm.swap x y l : (y :: x :: l) ~ (x :: y :: l)` — the motive's
      -- LHS is `y :: x :: l` (the Nodup premise rides it)
      have hne : x.field.name ≠ y.field.name := by
        rw [List.map_cons, List.map_cons, List.nodup_cons] at hnd
        intro he
        exact hnd.1 (List.mem_cons.mpr (Or.inl he.symm))
      intro r₀ acc
      have hcomm :
          x.path.set (y.path.set acc y.value) x.value
            = y.path.set (x.path.set acc x.value) y.value :=
        ColPath.set_commute_disjoint y.path x.path (fun h => hne h.symm) acc _ _
      simp only [List.foldl_cons]
      show List.foldl (fun a c => c.path.set a c.value)
            (x.path.set (y.path.set acc y.value) x.value) l
        = List.foldl (fun a c => c.path.set a c.value)
            (y.path.set (x.path.set acc x.value) y.value) l
      rw [hcomm]
  | trans hp₁ _ ih₁ ih₂ =>
      intro r₀ acc
      exact (ih₁ hnd r₀ acc).trans (ih₂ ((hp₁.map _).nodup_iff.mp hnd) r₀ acc)

/-- LAW 1: the SET clause order is unobservable (distinct column
    names — the WF rung's dup-set gate refuses the rest). -/
theorem applySets_perm {fs : List Field} {s₁ s₂ : List (SetClause fs)}
    (hp : s₁.Perm s₂) (hnd : (s₁.map fun c => c.field.name).Nodup)
    (r : RowVals fs) : applySets s₁ r = applySets s₂ r :=
  applySets_foldl_perm hp hnd r r

/-! ## Law 2 — the neutrality family -/

/-- A predicate's verdict is INVISIBLE to a write at a column it does
    not read (the legacy `evalV_set_neutral` family, at the Pred
    checker — the atomic arms ride `ColPath.set_project?_neutral`). -/
theorem Pred.check_set_neutral {fs : List Field} (p : Pred fs)
    (c : SetClause fs) (hne : ∀ n ∈ p.reads, n ≠ c.field.name) :
    ∀ (row : RowVals fs),
      p.check (c.path.set row c.value) = p.check row := by
  induction p with
  | lit b => intro row; rfl
  | u64EqLit n v =>
      intro row
      simp only [Pred.check, ColPath.set_project?_neutral c.path row c.value n
        (hne n (List.mem_cons_self))]
  | u64GtLit n v =>
      intro row
      simp only [Pred.check, ColPath.set_project?_neutral c.path row c.value n
        (hne n (List.mem_cons_self))]
  | u64Eq a b =>
      intro row
      simp only [Pred.check, ColPath.set_project?_neutral c.path row c.value a
        (hne a (List.mem_cons_self)),
        ColPath.set_project?_neutral c.path row c.value b
        (hne b (List.mem_cons_of_mem a (List.mem_cons_self)))]
  | strEqLit n s =>
      intro row
      simp only [Pred.check, ColPath.set_project?_neutral c.path row c.value n
        (hne n (List.mem_cons_self))]
  | and p q ihp ihq =>
      intro row
      simp only [Pred.check]
      rw [ihp (fun n hn => hne n (List.mem_append.mpr (Or.inl hn))) row,
        ihq (fun n hn => hne n (List.mem_append.mpr (Or.inr hn))) row]
  | or p q ihp ihq =>
      intro row
      simp only [Pred.check]
      rw [ihp (fun n hn => hne n (List.mem_append.mpr (Or.inl hn))) row,
        ihq (fun n hn => hne n (List.mem_append.mpr (Or.inr hn))) row]
  | not p ih =>
      intro row
      simp only [Pred.check]
      rw [ih hne row]

/-- The neutrality at the FOLD: a write fold whose columns the
    predicate never reads leaves the verdict (the legacy
    `validates_applySets`, batch form). -/
theorem Pred.check_applySets {fs : List Field} (p : Pred fs) :
    ∀ (sets : List (SetClause fs)),
      (∀ n ∈ p.reads, ∀ c ∈ sets, n ≠ c.field.name) →
      ∀ (row : RowVals fs),
        p.check (applySets sets row) = p.check row := by
  intro sets
  induction sets with
  | nil => intro _ row; rfl
  | cons c rest ih =>
      intro h row
      show p.check (applySets rest (c.path.set row c.value)) = p.check row
      rw [ih (fun n hn c' hc' => h n hn c' (List.mem_cons_of_mem c hc'))
        (c.path.set row c.value)]
      exact p.check_set_neutral c (fun n hn => h n hn c (List.mem_cons_self)) row

/-! ## Law 3 — two write folds with disjoint columns commute -/

/-- A step that commutes with every element of a fold pushes through
    the fold (generic — reused by the keyed delta's commutation). -/
theorem foldl_step_push {α β : Type} {f : β → α → β}
    {s : List α} {c : α}
    (hc : ∀ c₂ ∈ s, ∀ b, f (f b c) c₂ = f (f b c₂) c) :
    ∀ b, s.foldl f (f b c) = f (s.foldl f b) c := by
  induction s with
  | nil => intro _; rfl
  | cons c₂ rest ih =>
      intro b
      simp only [List.foldl_cons]
      show rest.foldl f (f (f b c) c₂) = f (rest.foldl f (f b c₂)) c
      rw [hc c₂ (List.mem_cons_self) b]
      exact ih (fun c' hc' => hc c' (List.mem_cons_of_mem c₂ hc')) _

/-- Adjacent-block exchange for a fold of pairwise-commuting steps
    (generic). -/
theorem foldl_append_comm {α β : Type} {f : β → α → β}
    {s₁ s₂ : List α}
    (hc : ∀ c₁ ∈ s₁, ∀ c₂ ∈ s₂, ∀ b, f (f b c₁) c₂ = f (f b c₂) c₁) :
    ∀ b, (s₁ ++ s₂).foldl f b = (s₂ ++ s₁).foldl f b := by
  induction s₁ with
  | nil => intro b; simp
  | cons c₁ s₁' ih =>
      intro b
      simp only [List.cons_append, List.foldl_cons]
      rw [ih (fun x hx => hc x (List.mem_cons_of_mem c₁ hx)) (f b c₁)]
      show (s₂ ++ s₁').foldl f (f b c₁) = (s₂ ++ c₁ :: s₁').foldl f b
      rw [List.foldl_append, List.foldl_append]
      show s₁'.foldl f (s₂.foldl f (f b c₁))
        = s₁'.foldl f (f (s₂.foldl f b) c₁)
      rw [foldl_step_push (f := f) (s := s₂) (c := c₁)
        (fun c₂ hc₂ b' => hc c₁ (List.mem_cons_self) c₂ hc₂ b') b]

/-- LAW 3: two SET folds with DISJOINT columns commute (the legacy
    `applySets_comm` — the value-read premises are gone: the values are
    literals, so disjoint names are the whole premise). -/
theorem applySets_comm {fs : List Field} {s₁ s₂ : List (SetClause fs)}
    (hdisj : ∀ c₁ ∈ s₁, ∀ c₂ ∈ s₂, c₁.field.name ≠ c₂.field.name)
    (r : RowVals fs) :
    applySets s₁ (applySets s₂ r) = applySets s₂ (applySets s₁ r) := by
  have key : ∀ (sa sb : List (SetClause fs)),
      applySets sb (applySets sa r)
        = (sa ++ sb).foldl (fun a c => c.path.set a c.value) r := by
    intro sa sb
    show sb.foldl (fun a c => c.path.set a c.value) (applySets sa r) = _
    rw [show applySets sa r = sa.foldl (fun a c => c.path.set a c.value) r
      from rfl]
    rw [← List.foldl_append]
  rw [key s₂ s₁, key s₁ s₂]
  exact ((foldl_append_comm (f := fun a c => c.path.set a c.value)
    (fun c₁ hc₁ c₂ hc₂ b =>
      ColPath.set_commute_disjoint c₁.path c₂.path (hdisj c₁ hc₁ c₂ hc₂) b _ _)) r).symm

/-! ## Laws 4/5 — the two-update order-freedom -/

/-- THE ORDER-FREEDOM PREMISE (the honest "disjoint keys" form): two
    updates over the same table compose in either order when

    - neither's GUARD reads a column the other WRITES (`ni₁₂`/`ni₂₁` —
      the DERIVED read set `UpdateItem.reads`, never hand-listed);
    - their written columns are DISJOINT (`setDisj` — same-column
      writes are later-wins, `ColPath.set_commute_same`; excluded);
    - each side's guard REFUSES every row the other inserts
      (`refuse₁₂`/`refuse₂₁` — else the later update would process the
      other's fresh rows);
    - no row fires one side's INSERT while the other DELETES
      (`insertSep₁₂`/`insertSep₂₁` — a deleted row's insert never
      fires in the other order).

    Every field is decidable over a concrete table. Same-key conflicts
    VIOLATE the last two — order-dependent by design (later-wins; the
    negative witness is pinned in SchemaTests). -/
structure UpdateCompat {fs : List Field} (u₁ u₂ : UpdateItem fs)
    (rows : List (RowVals fs)) : Prop where
  /-- u₁'s reads avoid u₂'s written columns. -/
  ni₁₂ : ∀ n ∈ u₁.reads, n ∉ u₂.setNames
  /-- u₂'s reads avoid u₁'s written columns. -/
  ni₂₁ : ∀ n ∈ u₂.reads, n ∉ u₁.setNames
  /-- The written columns are disjoint. -/
  setDisj : ∀ n ∈ u₁.setNames, n ∉ u₂.setNames
  /-- u₂'s guard refuses every row u₁ inserts. -/
  refuse₁₂ : ∀ r ∈ rows,
    (u₁.newRow r).elim true (fun new => !(validates u₂.guard new)) = true
  /-- u₁'s guard refuses every row u₂ inserts. -/
  refuse₂₁ : ∀ r ∈ rows,
    (u₂.newRow r).elim true (fun new => !(validates u₁.guard new)) = true
  /-- No row fires u₁'s insert while u₂ deletes it. -/
  insertSep₁₂ : u₁.insert?.isSome → u₂.delete = true → ∀ r ∈ rows,
    validates u₁.guard r = true → validates u₂.guard r = false
  /-- No row fires u₂'s insert while u₁ deletes it. -/
  insertSep₂₁ : u₂.insert?.isSome → u₁.delete = true → ∀ r ∈ rows,
    validates u₂.guard r = true → validates u₁.guard r = false

/-- The premise pack is symmetric (the swap earns the swapped pack). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem UpdateCompat.symm {fs : List Field} {u₁ u₂ : UpdateItem fs}
    {rows : List (RowVals fs)} (c : UpdateCompat u₁ u₂ rows) :
    UpdateCompat u₂ u₁ rows where
  ni₁₂ := c.ni₂₁
  ni₂₁ := c.ni₁₂
  setDisj := fun n hn hn' => c.setDisj n hn' hn
  refuse₁₂ := c.refuse₂₁
  refuse₂₁ := c.refuse₁₂
  insertSep₁₂ := c.insertSep₂₁
  insertSep₂₁ := c.insertSep₁₂

-- The premise pack's fields: the projection theorems the structure's
-- Prop-face auto-generates — the pack's API (its laws read them; a
-- downstream pack consumer reads them), never cited by name outside.
attribute [nolint linter.guestlang.zeroCitation "public API: the UpdateCompat premise pack's field (the laws' premises, read by the pack's consumers)"]
  UpdateCompat.ni₁₂ UpdateCompat.ni₂₁ UpdateCompat.setDisj
  UpdateCompat.refuse₁₂ UpdateCompat.refuse₂₁
  UpdateCompat.insertSep₁₂ UpdateCompat.insertSep₂₁

namespace UpdateCompat

variable {fs : List Field} {u₁ u₂ : UpdateItem fs} {rows : List (RowVals fs)}

/-- u₂'s write fold is invisible to u₁'s guard (the neutrality lift). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem guard₁_set₂ (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs) :
    validates u₁.guard (applySets u₂.sets r) = validates u₁.guard r := by
  show u₁.guard.check (applySets u₂.sets r) = u₁.guard.check r
  exact u₁.guard.check_applySets u₂.sets
    (fun n hn c₂ hc₂ hne => c.ni₁₂ n (u₁.mem_reads_of_guard hn)
      (hne ▸ u₂.mem_setNames hc₂)) r

/-- The symmetric guard neutrality. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem guard₂_set₁ (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs) :
    validates u₂.guard (applySets u₁.sets r) = validates u₂.guard r := by
  show u₂.guard.check (applySets u₁.sets r) = u₂.guard.check r
  exact u₂.guard.check_applySets u₁.sets
    (fun n hn c₁ hc₁ hne => c.ni₂₁ n (u₂.mem_reads_of_guard hn)
      (hne ▸ u₁.mem_setNames hc₁)) r

/-- The write folds commute (Law 3, premises from the pack). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem sets_comm (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs) :
    applySets u₁.sets (applySets u₂.sets r)
      = applySets u₂.sets (applySets u₁.sets r) := by
  apply applySets_comm
  intro c₁ hc₁ c₂ hc₂ heq
  exact c.setDisj _ (u₁.mem_setNames hc₁) (heq ▸ u₂.mem_setNames hc₂)

/-- u₁'s insert fires identically over u₂'s written row (the guard is
    neutral; the insert row is the literal). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem newRow_set₂ (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs) :
    u₁.newRow (applySets u₂.sets r) = u₁.newRow r := by
  unfold UpdateItem.newRow
  rw [c.guard₁_set₂ r]

/-- The ROW-LEVEL composition law: the keep-channels commute. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem keepRow_bind_comm (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs) :
    (u₁.keepRow r).bind u₂.keepRow = (u₂.keepRow r).bind u₁.keepRow := by
  have g₂₁ := c.guard₂_set₁ r
  have g₁₂ := c.guard₁_set₂ r
  have scomm := c.sets_comm r
  unfold UpdateItem.keepRow
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
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem newRow_bind_keepRow (c : UpdateCompat u₁ u₂ rows) (r : RowVals fs)
    (hr : r ∈ rows) :
    (u₂.keepRow r).bind u₁.newRow = u₁.newRow r := by
  unfold UpdateItem.keepRow
  by_cases h₂ : validates u₂.guard r = true
  · by_cases hd₂ : u₂.delete = true
    · rw [if_pos h₂, if_pos hd₂]
      show (none : Option (RowVals fs)) = u₁.newRow r
      -- u₁'s insert cannot fire here (insertSep); the guard refuses
      unfold UpdateItem.newRow
      by_cases h₁ : validates u₁.guard r = true
      · cases hi : u₁.insert? with
        | none => rw [if_pos h₁]
        | some t =>
            have hsep := c.insertSep₁₂ (by rw [hi]; rfl) hd₂ r hr h₁
            rw [hsep] at h₂
            exact absurd h₂ (by decide)
      · rw [if_neg h₁]
    · rw [if_pos h₂, if_neg hd₂]
      show u₁.newRow (applySets u₂.sets r) = u₁.newRow r
      rw [c.newRow_set₂ r]
  · rw [if_neg h₂]
    rfl

/-- Nested filterMap as a per-element bind (the lift bridge). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_filterMap {α β γ : Type} {f : α → Option β}
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
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_congr {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The keep-channels commute at the table (Law 4's core). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_keepRow_comm (c : UpdateCompat u₁ u₂ rows) :
    (rows.filterMap u₂.keepRow).filterMap u₁.keepRow
      = (rows.filterMap u₁.keepRow).filterMap u₂.keepRow := by
  rw [filterMap_filterMap, filterMap_filterMap]
  exact filterMap_congr (fun r _ => (c.keepRow_bind_comm r).symm)

/-- u₁'s inserts over u₂'s kept table = over the original table. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_newRow_keepRow (c : UpdateCompat u₁ u₂ rows) :
    (rows.filterMap u₂.keepRow).filterMap u₁.newRow
      = rows.filterMap u₁.newRow := by
  rw [filterMap_filterMap]
  exact filterMap_congr (fun r hr => c.newRow_bind_keepRow r hr)

/-- A refused table passes the keep-channel untouched. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_keepRow_eq_self_of_refused (u : UpdateItem fs)
    {l : List (RowVals fs)}
    (h : ∀ x ∈ l, validates u.guard x = false) : l.filterMap u.keepRow = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : validates u.guard x = false := h x (List.mem_cons_self)
      rw [List.filterMap_cons,
        show u.keepRow x = some x from by
          unfold UpdateItem.keepRow
          rw [show validates u.guard x = false from hx]
          rfl,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- A refused table fires no inserts. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_newRow_eq_nil_of_refused (u : UpdateItem fs)
    {l : List (RowVals fs)}
    (h : ∀ x ∈ l, validates u.guard x = false) : l.filterMap u.newRow = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  have hx' : validates u.guard x = false := h x hx
  unfold UpdateItem.newRow
  rw [show validates u.guard x = false from hx']
  rfl

/-- No insert clause: the insert channel is empty. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem filterMap_newRow_eq_nil_of_insert_none (u : UpdateItem fs)
    (h : u.insert? = none) (l : List (RowVals fs)) :
    l.filterMap u.newRow = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x _
  unfold UpdateItem.newRow
  rw [h]
  cases validates u.guard x <;> rfl

/-- The other's inserts are refused (the `refuse` premise in list
    form). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: the update-commutativity law stack — consumed via `apply2_comm` (pinned by SchemaTests.Main's renameRestockCompat witness)"]
theorem refused_newRows (c : UpdateCompat u₁ u₂ rows) :
    ∀ x ∈ rows.filterMap u₂.newRow, validates u₁.guard x = false := by
  intro x hx
  obtain ⟨r, hr, hnr⟩ := List.mem_filterMap.mp hx
  have h := c.refuse₂₁ r hr
  rw [hnr] at h
  -- h : (!(validates u₁.guard x)) = true (the `Option.elim` reduces on
  -- the `some`)
  have h' : (!(validates u₁.guard x)) = true := h
  cases hb : validates u₁.guard x with
  | true => rw [hb] at h'; simp at h'
  | false => rfl

end UpdateCompat

/-- The cons-through-append shuffle (the append-comm step). -/
theorem permConsAppend {α : Type} (x : α) :
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
theorem permAppendComm {α : Type} :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).Perm (l₂ ++ l₁) := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, List.append_nil]
  | cons x xs ih =>
      show (x :: (xs ++ l₂)).Perm (l₂ ++ x :: xs)
      exact (List.Perm.cons x ih).trans (permConsAppend x l₂ xs)

/-- LAW 5a (the general form): compatible updates commute UP TO
    PERMUTATION of the final table (the insert blocks swap — row order
    is unobservable at the tick's reading). -/
theorem apply2_comm_perm {fs : List Field} {u₁ u₂ : UpdateItem fs}
    {rows : List (RowVals fs)} (c : UpdateCompat u₁ u₂ rows) :
    (u₁.apply (u₂.apply rows)).Perm (u₂.apply (u₁.apply rows)) := by
  have hkk := c.filterMap_keepRow_comm
  have hn₁ := c.filterMap_newRow_keepRow
  have hn₂ := c.symm.filterMap_newRow_keepRow
  have hk₁self := UpdateCompat.filterMap_keepRow_eq_self_of_refused u₁
    c.refused_newRows
  have hn₁nil := UpdateCompat.filterMap_newRow_eq_nil_of_refused u₁
    c.refused_newRows
  have hk₂self := UpdateCompat.filterMap_keepRow_eq_self_of_refused u₂
    c.symm.refused_newRows
  have hn₂nil := UpdateCompat.filterMap_newRow_eq_nil_of_refused u₂
    c.symm.refused_newRows
  unfold UpdateItem.apply
  rw [List.filterMap_append, List.filterMap_append,
    List.filterMap_append, List.filterMap_append,
    hk₁self, hn₁nil, hk₂self, hn₂nil, hn₁, hn₂, hkk, List.append_nil,
    List.append_nil]
  -- goal: (K ++ N₂) ++ N₁ ~ (K ++ N₁) ++ N₂ (left-nested appends)
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ (permAppendComm _ _)

/-- LAW 5b (the sharp form): with no inserts on either side, compatible
    updates compute the SAME table in either order — plain equality. -/
theorem apply2_comm {fs : List Field} {u₁ u₂ : UpdateItem fs}
    {rows : List (RowVals fs)} (c : UpdateCompat u₁ u₂ rows)
    (h₁ : u₁.insert? = none) (h₂ : u₂.insert? = none) :
    u₁.apply (u₂.apply rows) = u₂.apply (u₁.apply rows) := by
  have hkk := c.filterMap_keepRow_comm
  have n₁nil := UpdateCompat.filterMap_newRow_eq_nil_of_insert_none u₁ h₁ rows
  have n₂nil := UpdateCompat.filterMap_newRow_eq_nil_of_insert_none u₂ h₂ rows
  unfold UpdateItem.apply
  rw [List.filterMap_append, List.filterMap_append,
    List.filterMap_append, List.filterMap_append,
    UpdateCompat.filterMap_keepRow_eq_self_of_refused u₁ c.refused_newRows,
    UpdateCompat.filterMap_newRow_eq_nil_of_refused u₁ c.refused_newRows,
    UpdateCompat.filterMap_keepRow_eq_self_of_refused u₂ c.symm.refused_newRows,
    UpdateCompat.filterMap_newRow_eq_nil_of_refused u₂ c.symm.refused_newRows,
    c.filterMap_newRow_keepRow, c.symm.filterMap_newRow_keepRow,
    n₁nil, n₂nil, hkk]

/-! ## Law 6 — the lowering to the shared delta -/

/-- THE SHARED ROW DELTA: the update lane's change variant at the row —
    insert/update carry the FULL row, remove carries the KEY image
    (the legacy `RowDelta`, at the slice's single source — the
    event-sourcing lane's sibling does not exist yet in this tree, so
    the inductive is defined HERE, its one home). This is the
    trichotomy's DELTA face: the accepted NET change per row. -/
inductive RowDelta (fs : List Field) : Type where
  | /-- The full row arrives. -/
    insert : RowVals fs → RowDelta fs
  | /-- The full written row replaces the rows sharing its key image. -/
    update : RowVals fs → RowDelta fs
  | /-- The key image of the removed row. -/
    remove : FieldVal → RowDelta fs

/-- The keep-channel's patch reading: update REPLACES, remove DELETES,
    insert rides the other channel. -/
def RowDelta.patchKeep {fs : List Field} :
    RowDelta fs → Option (RowVals fs) → Option (RowVals fs)
  | .insert _, acc => acc
  | .update new, _ => some new
  | .remove _, _ => none

/-- The insert channel's patch reading: the last insert fired wins
    (a guarded row fires at most one). -/
def RowDelta.patchNew {fs : List Field} :
    RowDelta fs → Option (RowVals fs) → Option (RowVals fs)
  | .insert new, _ => some new
  | _, acc => acc

/-- THE LOWERING: one row → its deltas. A guard-refused row lowers to
    `[]` (untouched — the batch law). A guarded row lowers to its
    row-level effect (delete → `remove` of the key image; nonempty
    sets → `update` of the written row) followed by the insert. A
    delete whose key projection FAILS lowers to `[]` — the refusal
    reading (malformed data refuses rather than misreads; the WF rungs
    make it unreachable for declared-key updates). -/
def UpdateItem.lowerRow {fs : List Field} (u : UpdateItem fs)
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
      ++ (u.insert?.map RowDelta.insert).toList
  else []

/-! ### The keyed table semantics + the lawful key kit -/

/-- The keyed table operation: `insert` appends the full row; `update`
    replaces the rows SHARING ITS KEY IMAGE (full replacement);
    `remove` drops the rows carrying the key image. Non-projecting rows
    refuse-by-identity (kept, unchanged). -/
def applyRowDelta (key : String) :
    {fs : List Field} → RowDelta fs → List (RowVals fs) → List (RowVals fs)
  | _, .insert r, rows => rows ++ [r]
  | _, .update r, rows => rows.map fun old =>
      match RowVals.project? _ old key with
      | some a =>
          match RowVals.project? _ r key with
          | some b => if FieldVal.beq a b then r else old
          | none => old
      | none => old
  | _, .remove k, rows => rows.filter fun old =>
      match RowVals.project? _ old key with
      | some a => !FieldVal.beq a k
      | none => true

/-- The key images of a table (rows that don't project are SKIPPED). -/
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

theorem keyImgs_nil {fs : List Field} {key : String} :
    keyImgs fs key [] = [] := rfl

/-- The BEQ-FALSE direction of the lawful equality (the legacy
    `FieldVal.beq_eq_false_pair_of_ne` — the new beq is UNCONDITIONALLY
    lawful, so the codec-closure hypotheses are gone). -/
theorem FieldVal.beq_false_of_ne {a b : FieldVal} (h : a ≠ b) :
    a.beq b = false := by
  cases hb : a.beq b with
  | false => rfl
  | true => exact absurd ((FieldVal.beq_eq_true_iff_eq a b).mp hb) h

/-- `map` is the identity when every element is fixed. -/
theorem map_eq_self_of_forall {α : Type} {f : α → α} {l : List α}
    (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, h x (List.mem_cons_self),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The update-delta's map over the working table replaces EXACTLY the
    source row (its key image): every other kept row's key is distinct
    (the lawful `FieldVal.beq`), the accumulated inserts are fresh. The
    statement's lambda is `applyRowDelta`'s update arm VERBATIM. -/
theorem applyRowDelta_update_map {fs : List Field} (key : String)
    (K rest I : List (RowVals fs)) (r r' : RowVals fs) (k : FieldVal)
    (hk : RowVals.project? fs r key = some k)
    (hk' : RowVals.project? fs r' key = some k)
    (hnd : (keyImgs fs key (K ++ r :: rest)).Nodup)
    (hI : ∀ ik ∈ keyImgs fs key I,
      ∀ wk ∈ keyImgs fs key (K ++ r :: rest), ik ≠ wk) :
    applyRowDelta key (RowDelta.update r') (K ++ r :: rest ++ I)
      = K ++ r' :: rest ++ I := by
  show (K ++ r :: rest ++ I).map (fun old =>
      match RowVals.project? fs old key with
      | some a =>
          match RowVals.project? fs r' key with
          | some b => if FieldVal.beq a b then r' else old
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
            | some b => if FieldVal.beq a b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hKne a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
        simp [hk', hae]
  have fixRest : ∀ old ∈ rest,
      (match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if FieldVal.beq a b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hRestNe a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
        simp [hk', hae]
  have fixI : ∀ old ∈ I,
      (match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if FieldVal.beq a b then r' else old
            | none => old
        | none => old) = old := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hI a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k hself)
        simp [hk', hae]
  have fr : (match RowVals.project? fs r key with
        | some a =>
            match RowVals.project? fs r' key with
            | some b => if FieldVal.beq a b then r' else r
            | none => r
        | none => r) = r' := by
    simp [hk, hk', FieldVal.beq_refl]
  rw [List.map_append, map_eq_self_of_forall fixI, List.map_append,
    map_eq_self_of_forall fixK, List.map_cons, fr,
    map_eq_self_of_forall fixRest]

/-- The insert arm, as a rewrite lemma (the append). -/
theorem applyRowDelta_insert {fs : List Field} (key : String)
    (x : RowVals fs) (T : List (RowVals fs)) :
    applyRowDelta key (RowDelta.insert x) T = T ++ [x] := rfl

/-- The remove-delta's filter over the working table drops EXACTLY the
    source row (the same Nodup kit, mirrored). -/
theorem applyRowDelta_remove_filter {fs : List Field} (key : String)
    (K rest I : List (RowVals fs)) (r : RowVals fs) (k : FieldVal)
    (hk : RowVals.project? fs r key = some k)
    (hnd : (keyImgs fs key (K ++ r :: rest)).Nodup)
    (hI : ∀ ik ∈ keyImgs fs key I,
      ∀ wk ∈ keyImgs fs key (K ++ r :: rest), ik ≠ wk) :
    applyRowDelta key (RowDelta.remove k) (K ++ r :: rest ++ I)
      = K ++ rest ++ I := by
  show (K ++ r :: rest ++ I).filter (fun old =>
      match RowVals.project? fs old key with
      | some a => !FieldVal.beq a k
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
        | some a => !FieldVal.beq a k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hcross a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k
              List.mem_cons_self)
        simp [hae]
  have keepRest : ∀ old ∈ rest,
      (match RowVals.project? fs old key with
        | some a => !FieldVal.beq a k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hRestNe a (List.mem_filterMap.mpr ⟨old, ho, hp⟩))
        simp [hae]
  have keepI : ∀ old ∈ I,
      (match RowVals.project? fs old key with
        | some a => !FieldVal.beq a k | none => true) = true := by
    intro old ho
    cases hp : RowVals.project? fs old key with
    | none => rfl
    | some a =>
        have hae : FieldVal.beq a k = false :=
          FieldVal.beq_false_of_ne
            (hI a (List.mem_filterMap.mpr ⟨old, ho, hp⟩) k hself)
        simp [hae]
  have dropR : (match RowVals.project? fs r key with
        | some a => !FieldVal.beq a k | none => true) = false := by
    simp [hk, FieldVal.beq_refl]
  rw [List.filter_append, List.filter_eq_self.mpr keepI,
    List.filter_append, List.filter_eq_self.mpr keepK, List.filter_cons,
    dropR, List.filter_eq_self.mpr keepRest]
  simp

/-! ### The correspondence's transport kit -/

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

/-- The keep-step preserves `Nodup` of the key images. -/
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

/-- The key projection is stable under a write fold that avoids the
    key column (the `project?`-level sibling of the neutrality family —
    the fold lift). -/
theorem project?_applySets {fs : List Field}
    {sets : List (SetClause fs)} (m : String)
    (h : ∀ c ∈ sets, c.field.name ≠ m) :
    ∀ (acc : RowVals fs),
      RowVals.project? fs
          (sets.foldl (fun a c => c.path.set a c.value) acc) m
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
theorem applySets_project?_key {fs : List Field} {sets : List (SetClause fs)}
    {key : String} (h : ∀ c ∈ sets, c.field.name ≠ key) (r : RowVals fs) :
    RowVals.project? fs (applySets sets r) key = RowVals.project? fs r key := by
  show RowVals.project? fs (sets.foldl (fun a c => c.path.set a c.value) r) key = _
  rw [project?_applySets (m := key) h r]

/-! ### The table-level correspondence -/

/-- THE TABLE-LEVEL CORRESPONDENCE, generalized for the induction: the
    working table splits into processed keeps `K`, the unprocessed
    suffix `rest`, and accumulated inserts `I` (appended at the end —
    the deterministic placement). The key premises are the lawful kit:
    images pairwise distinct (`Nodup` over the lawful beq), inserted
    keys fresh (`≠`). -/
theorem foldDeltas_go {fs : List Field} (u : UpdateItem fs)
    (key : String) (hkey : u.key? = some key)
    (himm : ∀ c ∈ u.sets, c.field.name ≠ key) :
    ∀ (K rest I : List (RowVals fs)),
      (∀ r ∈ rest, (RowVals.project? fs r key).isSome = true) →
      (∀ r ∈ rest, ∀ new, u.newRow r = some new → ∀ k',
        RowVals.project? fs new key = some k' →
        ∀ wk ∈ keyImgs fs key (K ++ rest), k' ≠ wk) →
      (keyImgs fs key (K ++ rest)).Nodup →
      (∀ ik ∈ keyImgs fs key I, ∀ wk ∈ keyImgs fs key (K ++ rest), ik ≠ wk) →
      (rest.flatMap u.lowerRow).foldl (fun t d => applyRowDelta key d t)
          (K ++ rest ++ I)
        = K ++ rest.filterMap u.keepRow ++ (I ++ rest.filterMap u.newRow) := by
  intro K rest I
  induction rest generalizing K I with
  | nil =>
      intro _ _ _ _
      simp [List.flatMap_nil, List.filterMap_nil, List.append_nil]
  | cons r rs ih =>
      intro hproj hfreshN hnd hI
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
            unfold UpdateItem.keepRow
            rw [if_pos hg, if_pos hd]
          have hlow : u.lowerRow r
              = [RowDelta.remove k]
                  ++ (u.insert?.map fun t => RowDelta.insert t).toList := by
            simp [UpdateItem.lowerRow, hg, hd, hkey, hk]
          rw [hlow]
          cases hi : u.insert? with
          | none =>
              have hnr : u.newRow r = none := by
                unfold UpdateItem.newRow
                rw [if_pos hg, hi]
              rw [Option.map_none, Option.toList_none, List.append_nil]
              simp only [List.foldl_cons, List.foldl_nil]
              rw [applyRowDelta_remove_filter key K rs I r k hk hnd hI]
              rw [ih K I hprojS hfreshS hndS hIS]
              simp only [List.filterMap_cons, hkr, hnr]
          | some t =>
              have hnr : u.newRow r = some t := by
                unfold UpdateItem.newRow
                rw [if_pos hg, hi]
              rw [Option.map_some, Option.toList_some]
              simp only [List.singleton_append, List.foldl_cons, List.foldl_nil]
              rw [applyRowDelta_remove_filter key K rs I r k hk hnd hI]
              rw [applyRowDelta_insert]
              have hT : (K ++ rs ++ I) ++ [t]
                  = (K ++ rs) ++ (I ++ [t]) := by
                simp only [List.append_assoc]
              rw [hT]
              -- the insert-extended I: the fresh image's ≠ against the
              -- shrunk table (the membership juggling, once)
              have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t]),
                  ∀ wk ∈ keyImgs fs key (K ++ rs), ik ≠ wk := by
                intro ik hik wk hwk
                rw [keyImgs_append] at hik
                rcases List.mem_append.mp hik with hik | hik
                · exact hI ik hik wk (mem_keyImgs_shrunk hk hwk)
                · cases hpk : RowVals.project? fs t key with
                  | none => simp [keyImgs, hpk] at hik
                  | some k' =>
                      have hsing : keyImgs fs key [t] = [k'] := by
                        have h1 := keyImgs_cons_of_some (rs := []) hpk
                        rw [keyImgs_nil] at h1
                        exact h1
                      rw [hsing, List.mem_singleton] at hik
                      rw [← hik] at hpk
                      exact hfreshN r List.mem_cons_self t hnr ik
                        hpk wk (mem_keyImgs_shrunk hk hwk)
              rw [ih K (I ++ [t]) hprojS hfreshS hndS hI1]
              simp only [List.filterMap_cons, hkr, hnr]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
        · -- KEEP (no delete): the update-delta fires when sets nonempty
          have hkr : u.keepRow r = some (applySets u.sets r) := by
            unfold UpdateItem.keepRow
            rw [if_pos hg, if_neg hd]
          cases hs : u.sets with
          | nil =>
              have hkr' : u.keepRow r = some r := by
                rw [hkr]; rw [hs]; rfl
              have hlow : u.lowerRow r
                  = (u.insert?.map fun t => RowDelta.insert t).toList := by
                simp [UpdateItem.lowerRow, hg, hd, hs]
              rw [hlow]
              cases hi : u.insert? with
              | none =>
                  have hnr : u.newRow r = none := by
                    unfold UpdateItem.newRow
                    rw [if_pos hg, hi]
                  rw [Option.map_none, Option.toList_none]
                  simp only [List.foldl_nil]
                  have hT : (K ++ r :: rs) ++ I = (K ++ [r]) ++ rs ++ I := by
                    simp only [List.append_assoc, List.cons_append,
                      List.nil_append]
                  rw [hT]
                  rw [ih (K ++ [r]) I hprojS hfreshK hndK hIK]
                  simp only [List.filterMap_cons, hkr', hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
              | some t =>
                  have hnr : u.newRow r = some t := by
                    unfold UpdateItem.newRow
                    rw [if_pos hg, hi]
                  rw [Option.map_some, Option.toList_some]
                  simp only [List.foldl_cons, List.foldl_nil]
                  rw [applyRowDelta_insert]
                  have hT : (K ++ r :: rs ++ I) ++ [t]
                      = (K ++ [r]) ++ rs ++ (I ++ [t]) := by
                    simp only [List.append_assoc, List.cons_append,
                      List.nil_append]
                  rw [hT]
                  have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t]),
                      ∀ wk ∈ keyImgs fs key ((K ++ [r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    rw [keyImgs_append] at hik
                    rcases List.mem_append.mp hik with hik | hik
                    · exact hI ik hik wk ((mem_keyImgs_kept hk hk).mpr hwk)
                    · cases hpk : RowVals.project? fs t key with
                      | none => simp [keyImgs, hpk] at hik
                      | some k' =>
                          have hsing : keyImgs fs key [t] = [k'] := by
                            have h1 := keyImgs_cons_of_some (rs := []) hpk
                            rw [keyImgs_nil] at h1
                            exact h1
                          rw [hsing, List.mem_singleton] at hik
                          rw [← hik] at hpk
                          exact hfreshN r List.mem_cons_self t hnr
                            ik hpk wk ((mem_keyImgs_kept hk hk).mpr hwk)
                  rw [ih (K ++ [r]) (I ++ [t]) hprojS hfreshK hndK hI1]
                  simp only [List.filterMap_cons, hkr', hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
          | cons chd ctl =>
              -- the written row
              have hk' : RowVals.project? fs (applySets u.sets r) key
                  = some k := by
                rw [applySets_project?_key himm r]; exact hk
              have hlow : u.lowerRow r
                  = [RowDelta.update (applySets u.sets r)]
                      ++ (u.insert?.map fun t =>
                        RowDelta.insert t).toList := by
                simp [UpdateItem.lowerRow, hg, hd, hs]
              rw [hlow]
              cases hi : u.insert? with
              | none =>
                  have hnr : u.newRow r = none := by
                    unfold UpdateItem.newRow
                    rw [if_pos hg, hi]
                  rw [Option.map_none, Option.toList_none, List.append_nil]
                  simp only [List.foldl_cons, List.foldl_nil]
                  rw [applyRowDelta_update_map key K rs I r (applySets u.sets r)
                    k hk hk' hnd hI]
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
                    hndK' hIK']
                  simp only [List.filterMap_cons, hkr, hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
              | some t =>
                  have hnr : u.newRow r = some t := by
                    unfold UpdateItem.newRow
                    rw [if_pos hg, hi]
                  rw [Option.map_some, Option.toList_some]
                  simp only [List.singleton_append, List.foldl_cons,
                    List.foldl_nil]
                  rw [applyRowDelta_update_map key K rs I r (applySets u.sets r)
                    k hk hk' hnd hI]
                  rw [applyRowDelta_insert]
                  have hT : (K ++ (applySets u.sets r) :: rs ++ I) ++ [t]
                      = (K ++ [applySets u.sets r]) ++ rs ++ (I ++ [t]) := by
                    simp only [List.append_assoc, List.cons_append,
                      List.nil_append]
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
                  have hI1 : ∀ ik ∈ keyImgs fs key (I ++ [t]),
                      ∀ wk ∈ keyImgs fs key
                        ((K ++ [applySets u.sets r]) ++ rs), ik ≠ wk := by
                    intro ik hik wk hwk
                    rw [keyImgs_append] at hik
                    rcases List.mem_append.mp hik with hik | hik
                    · exact hI ik hik wk ((mem_keyImgs_kept hk hk').mpr hwk)
                    · cases hpk : RowVals.project? fs t key with
                      | none => simp [keyImgs, hpk] at hik
                      | some k' =>
                          have hsing : keyImgs fs key [t] = [k'] := by
                            have h1 := keyImgs_cons_of_some (rs := []) hpk
                            rw [keyImgs_nil] at h1
                            exact h1
                          rw [hsing, List.mem_singleton] at hik
                          rw [← hik] at hpk
                          exact hfreshN r List.mem_cons_self t hnr
                            ik hpk wk ((mem_keyImgs_kept hk hk').mpr hwk)
                  rw [ih (K ++ [applySets u.sets r]) (I ++ [t])
                    hprojS hfreshK' hndK' hI1]
                  simp only [List.filterMap_cons, hkr, hnr]
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]
      · -- guard refuses: the row is untouched, no deltas
        have hkr : u.keepRow r = some r := by
          unfold UpdateItem.keepRow
          rw [if_neg hg]
        have hnr : u.newRow r = none := by
          unfold UpdateItem.newRow
          rw [if_neg hg]
        have hlow : u.lowerRow r = [] := by
          simp [UpdateItem.lowerRow, hg]
        rw [hlow, List.foldl_nil]
        have hT : (K ++ r :: rs) ++ I = (K ++ [r]) ++ rs ++ I := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [hT]
        rw [ih (K ++ [r]) I hprojS hfreshK hndK hIK]
        simp only [List.filterMap_cons, hkr, hnr]
        simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The correspondence premise bundle (WF-checkable on data): the key
    column is not written; every row projects its key; the images are
    pairwise distinct (core `List.Nodup` over the LAWFUL beq — no codec
    closure needed); the inserted rows' keys are fresh against every
    table row. -/
structure KeyCoherent {fs : List Field} (u : UpdateItem fs) (key : String)
    (rows : List (RowVals fs)) where
  /-- The update carries the declared key (the WF rung). -/
  keyOf : u.key? = some key
  /-- Key immutability: no SET clause writes the key column (a key
      change is a delete+insert — the event-sourcing reading). -/
  keyImmutable : ∀ c ∈ u.sets, c.field.name ≠ key
  /-- Every row projects its key. -/
  proj : ∀ r ∈ rows, (RowVals.project? fs r key).isSome = true
  /-- Key images pairwise distinct (core `List.Nodup`). -/
  nodup : (keyImgs fs key rows).Nodup
  /-- Insert keys fresh against every table row's key. -/
  fresh : ∀ r ∈ rows, ∀ new, u.newRow r = some new → ∀ k',
    RowVals.project? fs new key = some k' →
    ∀ wk ∈ keyImgs fs key rows, k' ≠ wk

/-- LAW 6 (the lowering correspondence): the update's table effect IS
    the fold of its per-row deltas through the keyed table semantics —
    insert/update carry the full row, remove carries the key image —
    applied by `applyRowDelta`. Under `KeyCoherent`, the positional
    batch semantics (`UpdateItem.apply`) and the delta fold coincide.
    (03 §7: the delta is the NET change — it erases intermediate
    history; the Z-set's canonical form is zset/'s carrier — the
    additive rung is claimed for the GROUP there, not for
    order-dependent list tables here.) -/
theorem apply2_eq_foldDeltas {fs : List Field} (u : UpdateItem fs)
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
  simp [UpdateItem.apply, List.nil_append]

/-! ## The Change-ladder instances (Kit.Change, 01-core §2) -/

/-- The update language's ladder instance: `Applicable` — the honest
    rung. The application is TOTAL (the guard decides every row), so
    the Option is the degenerate honest one. NOT composable — proved
    below; a set forgets the old value, the doctrine's own example at
    the update granularity (01-core §2). -/
def updateApplicable {fs : List Field} :
    Kit.Applicable (List (RowVals fs)) (UpdateItem fs) where
  apply := fun rows u => some (u.apply rows)

/- The two-update counterexample fixture (fields `x : u64`): u₁ writes
    x := 1 under the guard x = 0; u₂ DELETES the rows the write did not
    touch. -/
namespace UpdateItem

/-- The one-field schema of the counterexample. -/
def cxFields : List Field := [{ name := "x", ty := .u64 }]

/-- The row `[x = n]` (the counterexample's one-column row). -/
def cxRow (n : UInt64) : RowVals cxFields := .cons (.u64 n) .nil

/-- u₁: guarded write (x = 0 ⊢ x := 1). -/
def cxUpdate : UpdateItem cxFields where
  record := "Cx"
  name := "write"
  guard := .u64EqLit "x" 0
  sets := [{ field := { name := "x", ty := .u64 }
             path := ColPath.here
             value := .u64 1 }]

/-- u₂: guarded delete (¬(x = 1) ⊢ delete) — the rows the write did
    not touch. -/
def cxDelete : UpdateItem cxFields where
  record := "Cx"
  name := "purge"
  guard := .not (.u64EqLit "x" 1)
  sets := []
  delete := true

end UpdateItem

/-- A singleton's filterMap is the Option's list form (the channel
    case-analysis's step). -/
theorem filterMap_singleton {α β : Type} (f : α → Option β) (a : α) :
    List.filterMap f [a] = (f a).toList := by
  rw [List.filterMap_cons]
  cases f a <;> rfl

/-- NEGATIVE CONTROL (the rung is real): NO `compose : UpdateItem →
    UpdateItem → UpdateItem` satisfies the `Composable` law — one
    guard/delete pair cannot be the net of TWO guard channels (the
    composed item has ONE guard and ONE delete flag; the sequence needs
    both). The `Composable` law field is unconstructible at this Δ. -/
theorem updateItem_notComposable :
    ¬ ∃ compose : UpdateItem UpdateItem.cxFields →
              UpdateItem UpdateItem.cxFields →
              UpdateItem UpdateItem.cxFields,
      ∀ s a b, updateApplicable.apply s (compose a b)
        = (updateApplicable.apply s a).bind
            (fun t => updateApplicable.apply t b) := by
  rintro ⟨wfn, h⟩
  obtain ⟨w, hw⟩ : ∃ w, w = wfn UpdateItem.cxUpdate UpdateItem.cxDelete :=
    ⟨_, rfl⟩
  -- the composed item's behavior IS the sequence's
  have hseq : ∀ s : List (RowVals UpdateItem.cxFields),
      UpdateItem.apply w s
        = UpdateItem.cxDelete.apply (UpdateItem.cxUpdate.apply s) := by
    intro s
    have hs := h s UpdateItem.cxUpdate UpdateItem.cxDelete
    simp only [updateApplicable, Option.bind_some, Option.some.injEq] at hs
    rw [hw]
    exact hs
  -- the sequence's behavior on the two pinned rows (all concrete)
  have rhs0 : UpdateItem.cxDelete.apply
        (UpdateItem.cxUpdate.apply [UpdateItem.cxRow 0])
      = [UpdateItem.cxRow 1] := by rfl
  have rhs5 : UpdateItem.cxDelete.apply
        (UpdateItem.cxUpdate.apply [UpdateItem.cxRow 5])
      = [] := by rfl
  have w0 := hseq [UpdateItem.cxRow 0]
  have w5 := hseq [UpdateItem.cxRow 5]
  rw [rhs0] at w0
  rw [rhs5] at w5
  -- both sides' channels as Option.toList singletons
  simp only [UpdateItem.apply, filterMap_singleton] at w0 w5
  -- [x=5] vanishes: BOTH channels are empty on it
  rw [List.append_eq_nil_iff] at w5
  obtain ⟨hk5, hn5⟩ := w5
  have hk5' : w.keepRow (UpdateItem.cxRow 5) = none :=
    Option.toList_eq_nil_iff.mp hk5
  have hn5' : w.newRow (UpdateItem.cxRow 5) = none :=
    Option.toList_eq_nil_iff.mp hn5
  -- keepRow [x=5] = none forces the guard TRUE and the delete flag TRUE
  have hk5g : validates w.guard (UpdateItem.cxRow 5) = true := by
    unfold UpdateItem.keepRow at hk5'
    by_cases hg : validates w.guard (UpdateItem.cxRow 5) = true
    · exact hg
    · rw [if_neg hg] at hk5'
      exact absurd hk5' (by simp)
  have hd5 : w.delete = true := by
    unfold UpdateItem.keepRow at hk5'
    rw [if_pos hk5g] at hk5'
    by_cases hd : w.delete = true
    · exact hd
    · rw [if_neg hd] at hk5'
      exact absurd hk5' (by simp)
  -- the delete channel's emptiness fixes insert? = none
  have hins : w.insert? = none := by
    unfold UpdateItem.newRow at hn5'
    rw [if_pos hk5g] at hn5'
    exact hn5'
  -- [x=0] survives AS the written row — the channel combinations
  cases hk0 : w.keepRow (UpdateItem.cxRow 0) with
  | none =>
      cases hn0 : w.newRow (UpdateItem.cxRow 0) with
      | none => rw [hk0, hn0] at w0; simp at w0
      | some b =>
          rw [hk0, hn0] at w0
          simp at w0
          -- the insert channel fired on [x=0] — but insert? is none
          unfold UpdateItem.newRow at hn0
          split at hn0
          · rw [hins] at hn0
            exact absurd hn0 (by simp)
          · exact absurd hn0 (by simp)
  | some b =>
      cases hn0 : w.newRow (UpdateItem.cxRow 0) with
      | none =>
          rw [hk0, hn0] at w0
          simp at w0
          -- keepRow [x=0] = some [x=1]: guard fired, delete FALSE
          rw [w0] at hk0
          have hd0 : w.delete = false := by
            unfold UpdateItem.keepRow at hk0
            by_cases hg : validates w.guard (UpdateItem.cxRow 0) = true
            · rw [if_pos hg] at hk0
              by_cases hd : w.delete = true
              · rw [hd] at hk0
                exact absurd hk0 (by simp)
              · rw [if_neg hd] at hk0
                exact Bool.of_not_eq_true hd
            · rw [if_neg hg] at hk0
              -- some [x=0] = some [x=1]: the refuted row equality
              have h9 := Option.some.inj hk0
              have h10 := RowVals.cons.inj h9
              simp only [Value.u64.injEq] at h10
              exact absurd h10 (by decide)
          rw [hd5] at hd0
          exact absurd hd0 (by simp)
      | some b' =>
          rw [hk0, hn0] at w0
          simp [List.cons_append] at w0

/-! ## The keyed delta — the COMMUTING rung's honest carrier -/

/-- Row equality: position-wise `Value.beq` (the keyed delta's check
    surface — RowVals carries no BEq instance; the GADT's index makes
    cross-shape comparison unrepresentable). -/
def rowBeq : (fs : List Field) → RowVals fs → RowVals fs → Bool
  | [], .nil, .nil => true
  | f :: fs, .cons a as, .cons b bs => Value.beq f.ty a b && rowBeq fs as bs

theorem rowBeq_refl : ∀ (fs : List Field) (r : RowVals fs),
    rowBeq fs r r = true
  | [], .nil => rfl
  | f :: fs, .cons a as => by
      simp only [rowBeq]
      rw [Value.beq_refl f.ty a, rowBeq_refl fs as]
      rfl

theorem rowBeq_eq : ∀ (fs : List Field) (r r' : RowVals fs),
    rowBeq fs r r' = true → r = r'
  | [], .nil, .nil, _ => rfl
  | f :: fs, .cons a as, .cons b bs, h => by
      simp only [rowBeq, Bool.and_eq_true] at h
      rw [Value.beq_eq f.ty a b h.1, rowBeq_eq fs as bs h.2]

/-- The keyed put: the OLD-RETAINING delta (03 §7's replacement =
    −old +new at one key). The old image is what makes the inverse
    lawful — a plain set forgets it. -/
structure KeyPut (fs : List Field) where
  /-- The key the put writes at. -/
  key : FieldVal
  /-- The pre-image the put expects (the check's face). -/
  old? : Option (RowVals fs)
  /-- The post-image the put writes (`none` = the key vacates). -/
  new? : Option (RowVals fs)

/-- The canonical keyed state (the Keys lane's law: the row-set is a
    FUNCTION from key to row — `KeyDecl.uniqueOn`'s meaning). -/
abbrev KeyState (fs : List Field) := FieldVal → Option (RowVals fs)

/-- Option-level row-image comparison. -/
def optRowBeq {fs : List Field} :
    Option (RowVals fs) → Option (RowVals fs) → Bool
  | none, none => true
  | some a, some b => rowBeq fs a b
  | _, _ => false

theorem optRowBeq_refl {fs : List Field} (o : Option (RowVals fs)) :
    optRowBeq o o = true := by
  cases o with
  | none => rfl
  | some r => exact rowBeq_refl _ r

theorem optRowBeq_eq {fs : List Field} {o o' : Option (RowVals fs)}
    (h : optRowBeq o o' = true) : o = o' := by
  cases o with
  | none =>
      cases o' with
      | none => rfl
      | some _ => simp [optRowBeq] at h
  | some r =>
      cases o' with
      | none => simp [optRowBeq] at h
      | some r' => exact congrArg _ (rowBeq_eq _ r r' h)

/-- The put's effect, as data: write the new image AT the key,
    everything else untouched. -/
def KeyPut.upd (p : KeyPut fs) (st : KeyState fs) : KeyState fs :=
  fun k => if FieldVal.beq k p.key = true then p.new? else st k

/-- THE CHECKED KEYED PUT: it applies iff the state at the key IS the
    put's old image (the delta does not lie — 03 §7's command/delta
    boundary: a lying delta REFUSES, it never silently misapplies). -/
def KeyPut.apply (p : KeyPut fs) (st : KeyState fs) : Option (KeyState fs) :=
  if optRowBeq (st p.key) p.old? then
    some (p.upd st)
  else none

/-- The put's application at an OPTION state (the fold's step — the
    Option is the fallibility carrier, never a command's refusal). -/
def KeyPut.applyO (p : KeyPut fs) (X : Option (KeyState fs)) :
    Option (KeyState fs) :=
  X.bind (KeyPut.apply p)

/-- The put's inverse: swap the old and new images (the delta RETAINS
    the old information — that is the whole point). -/
def KeyPut.inv (p : KeyPut fs) : KeyPut fs :=
  { key := p.key, old? := p.new?, new? := p.old? }

theorem KeyPut.apply_iff (p : KeyPut fs) (st : KeyState fs) :
    p.apply st = some (p.upd st) ↔ optRowBeq (st p.key) p.old? = true := by
  constructor
  · intro h
    by_cases hc : optRowBeq (st p.key) p.old? = true
    · exact hc
    · rw [KeyPut.apply, if_neg (fun hc2 => hc hc2)] at h
      exact absurd h (by simp)
  · intro h
    rw [KeyPut.apply, if_pos h]

theorem KeyPut.apply_none_iff (p : KeyPut fs) (st : KeyState fs) :
    p.apply st = none ↔ optRowBeq (st p.key) p.old? = false := by
  constructor
  · intro h
    by_cases hc : optRowBeq (st p.key) p.old? = true
    · rw [KeyPut.apply, if_pos hc] at h
      exact absurd h (by simp)
    · exact Bool.of_not_eq_true hc
  · intro h
    rw [KeyPut.apply, if_neg (by
      intro hc
      rw [h] at hc
      exact absurd hc (by simp))]

theorem KeyPut.upd_apply_other (p : KeyPut fs) (st : KeyState fs)
    (k : FieldVal) (hk : FieldVal.beq k p.key = false) :
    p.upd st k = st k := by
  show (if FieldVal.beq k p.key = true then p.new? else st k) = st k
  rw [if_neg (by intro hc; rw [hc] at hk; exact absurd hk (by simp))]

/-- The put writes AT its key (the beq-refl step, extracted). -/
theorem KeyPut.upd_at_key (p : KeyPut fs) (st : KeyState fs) :
    p.upd st p.key = p.new? := by
  show (if FieldVal.beq p.key p.key = true then p.new? else st p.key) = p.new?
  rw [if_pos (FieldVal.beq_refl p.key)]

/-- THE SINGLE-PUT ROUND TRIP: applying the inverse undoes the put
    (exactly — the old image is restored at the key, everything else
    was never touched). -/
theorem KeyPut.apply_inv (p : KeyPut fs) (st : KeyState fs) (st' : KeyState fs)
    (h : p.apply st = some st') :
    (KeyPut.inv p).apply st' = some st := by
  have hchk : optRowBeq (st p.key) p.old? = true := by
    by_cases hchk : optRowBeq (st p.key) p.old? = true
    · exact hchk
    · rw [(p.apply_none_iff st).mpr (Bool.of_not_eq_true hchk)] at h
      exact absurd h (by simp)
  have hst' : st' = p.upd st := by
    have h2 : p.apply st = some (p.upd st) := (p.apply_iff st).mpr hchk
    exact Option.some.inj (h2.symm.trans h).symm
  have hsp : st p.key = p.old? := optRowBeq_eq hchk
  -- the inverse's check passes (the state at the key IS the new image)
  have hchk2 : optRowBeq (st' (KeyPut.inv p).key) (KeyPut.inv p).old? = true := by
    rw [hst']
    simp only [KeyPut.inv]
    rw [KeyPut.upd_at_key]
    exact optRowBeq_refl _
  rw [KeyPut.apply, if_pos hchk2]
  apply congrArg some
  funext k
  show (if FieldVal.beq k p.key = true then p.old? else st' k) = st k
  by_cases hkeq : FieldVal.beq k p.key = true
  · rw [if_pos hkeq, (FieldVal.beq_eq_true_iff_eq k p.key).mp hkeq, ← hsp]
  · have hkf : FieldVal.beq k p.key = false :=
      FieldVal.beq_false_of_ne (fun h => hkeq ((FieldVal.beq_eq_true_iff_eq _ _).mpr h))
    rw [if_neg hkeq, hst', p.upd_apply_other st k hkf]

/-- THE SINGLE-PUT SWAP: two puts at distinct keys commute — the
    writes touch disjoint key positions, and each put's check reads
    only its own key (the other's write is invisible to it). -/
theorem KeyPut.apply_swap (p q : KeyPut fs) (st : KeyState fs)
    (hne : p.key ≠ q.key) :
    (p.apply st).bind q.apply = (q.apply st).bind p.apply := by
  -- the checks transport across the other's put (each reads its own key)
  have hpq : optRowBeq ((q.upd st) p.key) p.old?
      = optRowBeq (st p.key) p.old? := by
    rw [q.upd_apply_other st p.key (FieldVal.beq_false_of_ne hne)]
  have hqp : optRowBeq ((p.upd st) q.key) q.old?
      = optRowBeq (st q.key) q.old? := by
    rw [p.upd_apply_other st q.key
      (FieldVal.beq_false_of_ne (fun h => hne h.symm))]
  by_cases hp : optRowBeq (st p.key) p.old? = true
  · rw [(p.apply_iff st).mpr hp, Option.bind_some]
    by_cases hq : optRowBeq (st q.key) q.old? = true
    · rw [(q.apply_iff (p.upd st)).mpr (by rw [hqp]; exact hq),
        (q.apply_iff st).mpr hq, Option.bind_some,
        (p.apply_iff (q.upd st)).mpr (by rw [hpq]; exact hp)]
      apply congrArg some
      funext k
      show q.upd (p.upd st) k = p.upd (q.upd st) k
      by_cases hkq : FieldVal.beq k q.key = true
      · have kq : k = q.key := (FieldVal.beq_eq_true_iff_eq k q.key).mp hkq
        rw [kq, KeyPut.upd_at_key,
          p.upd_apply_other (q.upd st) q.key
            (FieldVal.beq_false_of_ne (fun h => hne h.symm)),
          KeyPut.upd_at_key]
      · by_cases hkp : FieldVal.beq k p.key = true
        · have kp : k = p.key := (FieldVal.beq_eq_true_iff_eq k p.key).mp hkp
          rw [kp,
            q.upd_apply_other (p.upd st) p.key
              (FieldVal.beq_false_of_ne (fun h => hne (kp ▸ h))),
            KeyPut.upd_at_key, KeyPut.upd_at_key]
        · rw [q.upd_apply_other (p.upd st) k
              (FieldVal.beq_false_of_ne (fun h => hkq ((FieldVal.beq_eq_true_iff_eq _ _).mpr h))),
            p.upd_apply_other st k
              (FieldVal.beq_false_of_ne (fun h => hkp ((FieldVal.beq_eq_true_iff_eq _ _).mpr h))),
            p.upd_apply_other (q.upd st) k
              (FieldVal.beq_false_of_ne (fun h => hkp ((FieldVal.beq_eq_true_iff_eq _ _).mpr h))),
            q.upd_apply_other st k
              (FieldVal.beq_false_of_ne (fun h => hkq ((FieldVal.beq_eq_true_iff_eq _ _).mpr h)))]
    · rw [(q.apply_none_iff (p.upd st)).mpr
          (by rw [hqp]; exact Bool.of_not_eq_true hq),
        (q.apply_none_iff st).mpr (Bool.of_not_eq_true hq),
        Option.bind_none]
  · rw [(p.apply_none_iff st).mpr (Bool.of_not_eq_true hp), Option.bind_none]
    by_cases hq : optRowBeq (st q.key) q.old? = true
    · rw [(q.apply_iff st).mpr hq, Option.bind_some,
        (p.apply_none_iff (q.upd st)).mpr
          (by rw [hpq]; exact Bool.of_not_eq_true hp)]
    · rw [(q.apply_none_iff st).mpr (Bool.of_not_eq_true hq),
        Option.bind_none]

/-- The keyed delta: a LIST of puts (the delta's sequential face;
    same-key puts compose by later-wins). -/
abbrev KeyDelta (fs : List Field) := List (KeyPut fs)

/-- The keyed delta's application: the puts in order, each checked —
    the OPTION state is the fallibility carrier (a lying put's refusal
    poisons the whole fold). -/
def keyDeltaApply (d : KeyDelta fs) (X : Option (KeyState fs)) :
    Option (KeyState fs) :=
  d.foldl (fun acc p => KeyPut.applyO p acc) X

/-- The append law: the delta sequence's composition IS the fold over
    the concatenated list. -/
theorem keyDeltaApply_append (a b : KeyDelta fs) (X : Option (KeyState fs)) :
    keyDeltaApply (a ++ b) X = keyDeltaApply b (keyDeltaApply a X) := by
  simp only [keyDeltaApply, List.foldl_append]

/-- The fold never revives a poisoned (none) accumulator. -/
theorem keyDeltaApply_none (d : KeyDelta fs) :
    keyDeltaApply d none = none := by
  induction d with
  | nil => rfl
  | cons p d' ih =>
      show keyDeltaApply d' (KeyPut.applyO p none) = none
      rw [show KeyPut.applyO p none = none from rfl, ih]

/-- The bind-start law (the applyCompose field's shape). -/
theorem keyDeltaApply_bind_start (b : KeyDelta fs) (X : Option (KeyState fs)) :
    X.bind (fun s => keyDeltaApply b (some s)) = keyDeltaApply b X := by
  cases X with
  | none => rw [keyDeltaApply_none]; rfl
  | some st => rfl

/-- THE SINGLE-PUT SWAP at the Option level (the point-lifted
    commutation the fold-level laws ride). -/
theorem KeyPut.applyO_swap (p q : KeyPut fs) (hne : p.key ≠ q.key)
    (X : Option (KeyState fs)) :
    (KeyPut.applyO p X).bind (KeyPut.apply q)
      = (KeyPut.applyO q X).bind (KeyPut.apply p) := by
  cases X with
  | none => rfl
  | some st =>
      show (KeyPut.apply p st).bind (KeyPut.apply q)
        = (KeyPut.apply q st).bind (KeyPut.apply p)
      exact p.apply_swap q st hne

/-- A single put pushes through a fold of puts it is disjoint from. -/
theorem keyDeltaApply_pushSingle (p : KeyPut fs) (b : KeyDelta fs)
    (X : Option (KeyState fs)) (hd : ∀ q ∈ b, p.key ≠ q.key) :
    keyDeltaApply b (KeyPut.applyO p X) = KeyPut.applyO p (keyDeltaApply b X) := by
  induction b generalizing X with
  | nil => simp [keyDeltaApply, KeyPut.applyO]
  | cons q b' ih =>
      show keyDeltaApply b' ((KeyPut.applyO p X).bind (KeyPut.apply q))
        = KeyPut.applyO p (keyDeltaApply b' (X.bind (KeyPut.apply q)))
      rw [KeyPut.applyO_swap p q (hd q (List.mem_cons_self)) X]
      exact ih (X.bind (KeyPut.apply q))
        (fun q' hq' => hd q' (List.mem_cons_of_mem _ hq'))

/-- THE ORDER-FREEDOM LAW at the keyed delta: disjoint key sets mean
    neither delta reads nor writes what the other touches — the folds
    commute (the Commuting rung's law, proved once here). -/
theorem keyDeltaApply_swap (a b : KeyDelta fs) (X : Option (KeyState fs))
    (hd : ∀ p ∈ a, ∀ q ∈ b, p.key ≠ q.key) :
    keyDeltaApply b (keyDeltaApply a X) = keyDeltaApply a (keyDeltaApply b X) := by
  induction a generalizing X with
  | nil => simp [keyDeltaApply]
  | cons p a' ih =>
      have h1 := ih (KeyPut.applyO p X)
        (fun p' hp' q hq => hd p' (List.mem_cons_of_mem _ hp') q hq)
      have h2 := keyDeltaApply_pushSingle p b X
        (fun q hq => hd p (List.mem_cons_self) q hq)
      calc keyDeltaApply b (keyDeltaApply a' (KeyPut.applyO p X))
          = keyDeltaApply a' (keyDeltaApply b (KeyPut.applyO p X)) := h1
        _ = keyDeltaApply a' (KeyPut.applyO p (keyDeltaApply b X)) := by
              rw [h2]
        _ = keyDeltaApply (p :: a') (keyDeltaApply b X) := rfl

/-- The reversed-put-list delta undoes the delta (the fold round trip). -/
theorem keyDeltaApply_reverse_inv :
    ∀ (d : KeyDelta fs) (st st' : KeyState fs),
      keyDeltaApply d (some st) = some st' →
      keyDeltaApply (d.reverse.map KeyPut.inv) (some st') = some st := by
  intro d
  induction d with
  | nil =>
      intro st st' h
      simp only [keyDeltaApply, List.foldl_nil] at h ⊢
      exact congrArg some (Option.some.inj h).symm
  | cons p d ih =>
      intro st st' h
      have h2 : keyDeltaApply d (KeyPut.apply p st) = some st' := h
      cases hp : KeyPut.apply p st with
      | none =>
          rw [hp] at h2
          rw [keyDeltaApply_none] at h2
          exact absurd h2 (by simp)
      | some Z =>
          rw [hp] at h2
          have hrev : (p :: d).reverse.map KeyPut.inv
              = d.reverse.map KeyPut.inv ++ [KeyPut.inv p] := by
            simp [List.reverse_cons, List.map_append]
          rw [hrev, keyDeltaApply_append, ih Z st' h2]
          have hfin : KeyPut.apply (KeyPut.inv p) Z = some st :=
            p.apply_inv st Z hp
          simpa [keyDeltaApply, KeyPut.applyO] using hfin

/-- THE COMMUTING RUNG (01-core §2's fifth rung) on the keyed delta
    carrier: the old-retaining checked put — 03 §7's replacement =
    −old +new at the canonical keyed meaning (the row-set is a function
    from key to row, the Keys lane's law). The `Disjoint` predicate is
    EXPLICIT and the law holds only under it. The rung requires
    Reversible — honest exactly because the put retains the old image
    (a plain SET forgets it; `updateItem_notComposable` is the
    language-level face of the same information loss, and the ZSet's
    additive rung is the group-level reading of the same discipline). -/
def keyDeltaCommuting (fs : List Field) :
    Kit.Commuting (KeyState fs) (KeyDelta fs) where
  apply st d := keyDeltaApply d (some st)
  compose a b := a ++ b
  assoc a b c := List.append_assoc a b c
  applyCompose st a b := by
    rw [keyDeltaApply_append]
    exact (keyDeltaApply_bind_start b _).symm
  nop := []
  composeNopLeft d := (List.nil_append d).symm
  composeNopRight d := List.append_nil d
  applyNop st := rfl
  inv d := d.reverse.map KeyPut.inv
  roundTrip st d st' h := keyDeltaApply_reverse_inv d st st' h
  Disjoint a b := ∀ p ∈ a, ∀ q ∈ b, p.key ≠ q.key
  commute st a b hd := by
    show (keyDeltaApply a (some st)).bind
          (fun s' => keyDeltaApply b (some s'))
      = (keyDeltaApply b (some st)).bind
          (fun s' => keyDeltaApply a (some s'))
    rw [keyDeltaApply_bind_start, keyDeltaApply_bind_start]
    exact keyDeltaApply_swap a b (some st) hd

/-! ## The lane's mount — the WF checker, the Diag envelope, the obligation
    view (12 §2's recipe: item + mount + the WF legality + the obligation
    view; the registration (`schema_update`'s command surface) stays out —
    no consumer yet, the leftover rule) -/

/-- The update-lane E-codes (allocated from the PERSISTED registry:
    notes/code-registry.txt, the SU family — never a bare string). -/
def eSU0001 : Kit.ECode := ⟨"SU0001"⟩
def eSU0002 : Kit.ECode := ⟨"SU0002"⟩
def eSU0003 : Kit.ECode := ⟨"SU0003"⟩

/-- The declared key of the record resolving a name (the key-resolution
    rung's lookup — the Keys lane's declaration set, ONE reading). -/
def keyDeclFor (decls : List KeyDecl) (record key : String) : Option KeyDecl :=
  decls.find? (fun d => d.record == record && d.key == key)

/-- The update's WF diagnostics (the rung cascade; empty = well formed):

    1. the DUP-SET rung — two SET clauses on one column (the order-
       freedom premise, refused at the data level — SU0001);
    2. the KEYED rung — insert/delete without a declared key (the legacy
       elaboration gate's runtime face — SU0002);
    3. the KEY-RESOLUTION rung — `key?` names no declared key of the
       record (SU0003, closed-world over the record's declared keys). -/
def updateDiags (u : UpdateItem fs) (decls : List KeyDecl) : List Kit.Diag :=
  (if u.setNames.Nodup then [] else
      [Kit.Diag.closedWorld eSU0001
        s!"update: `{u.record}.{u.name}` writes a column twice — distinct \
          SET-clause names are the order-freedom premise (Law 1)"
        .error (u.setNames.head!) u.setNames.eraseDups])
    ++ (if u.delete || u.insert?.isSome then
        (match u.key? with
        | none => [Kit.Lane.usageDiag eSU0002
            s!"update: `{u.record}.{u.name}` deletes or inserts without a \
              declared key — the keyed rung refuses (a keyless row-level \
              effect is unrepresentable over the keys lane)"]
        | some k =>
            match keyDeclFor decls u.record k with
            | none => [Kit.Diag.closedWorld eSU0003
                s!"update: `{u.record}.{u.name}` keys on `{k}` — no \
                  declared key of `{u.record}` matches"
                .error k ((decls.filter (fun d => d.record == u.record)).map
                  (·.key))]
            | some _ => [])
      else [])

/-- The update's WF relation (the Prop side of the cascade). -/
structure UpdateWf (u : UpdateItem fs) (decls : List KeyDecl) : Prop where
  /-- The SET-clause names are distinct (Law 1's premise). -/
  setNodup : u.setNames.Nodup
  /-- A row-level effect carries a DECLARED key. -/
  keyed : (u.delete = true ∨ u.insert?.isSome = true) →
    ∃ k kd, u.key? = some k ∧ keyDeclFor decls u.record k = some kd

/-- The Bool-or's transport (the keyed rung's condition, once). -/
theorem boolOr_true {a b : Bool} (h : a = true ∨ b = true) :
    (a || b) = true := by
  cases a with
  | true => simp
  | false =>
      cases h with
      | inl h' => simp at h'
      | inr h' => rw [h']; simp

theorem boolOr_false {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
      rw [Bool.false_or] at h
      exact Or.inr h

/-- THE WF BRIDGE (pattern #1): the checker never lies in either
direction. -/
theorem updateDiags_eq_nil_iff {fs : List Field} (u : UpdateItem fs)
    (decls : List KeyDecl) : updateDiags u decls = [] ↔ UpdateWf u decls := by
  simp only [updateDiags, List.append_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_cases hnd : u.setNames.Nodup
      · exact hnd
      · rw [if_neg hnd] at h1
        exact absurd h1 (by simp)
    · intro hcon
      rw [if_pos (boolOr_true hcon)] at h2
      cases hu : u.key? with
      | none => simp [hu] at h2
      | some k =>
          cases hd2 : keyDeclFor decls u.record k with
          | none => simp [hu, hd2] at h2
          | some kd => exact ⟨k, kd, rfl, hd2⟩
  · rintro ⟨hnd, hkey⟩
    refine ⟨?_, ?_⟩
    · rw [if_pos hnd]
    · by_cases hr : u.delete = true ∨ u.insert?.isSome = true
      · rw [if_pos (boolOr_true hr)]
        obtain ⟨k, kd, hu, hkd⟩ := hkey hr
        simp [hu, hkd]
      · rw [if_neg (fun hc => hr (boolOr_false hc))]

/-! ## The obligation view (what a keyed update MEANS, as data) -/

/-- The update-lane claim. -/
inductive UpdateClaim where
  | /-- The update's table effect preserves key-uniqueness. -/
    keyUnique (fs : List Field) (u : UpdateItem fs) (key : String)

/-- The uniqueness reading of the update's record (the Keys lane's
    `uniqueOn` at the update's own record name). -/
def UpdateItem.kdUnique (u : UpdateItem fs) (key : String)
    (rows : List (RowVals fs)) : Bool :=
  KeyDecl.uniqueOn { record := u.record, fields := fs, key := key } rows

/-- THE CLAIM: the keyed update's table effect preserves key-uniqueness
    on the pinned ALL-DEFAULT SINGLETON table (the one table
    materializable from the declaration alone — the Keys lane's
    default-row discipline; the antecedent keeps vacuous guards
    honest). -/
def UpdateItem.keyUniqueProp (u : UpdateItem fs) (key : String) : Prop :=
  match defaultRow? fs with
  | none => False
  | some row =>
      (if u.kdUnique key [row] then u.kdUnique key (u.apply [row])
        else true) = true

/-- The claim's decidability (the row-data predicate reduces). -/
instance updateClaimDecidable {fs : List Field} (u : UpdateItem fs)
    (key : String) : Decidable (u.keyUniqueProp key) := by
  unfold UpdateItem.keyUniqueProp
  cases hd : defaultRow? fs with
  | none => infer_instance
  | some row => infer_instance

/-- The Prop-INDEXED obligation (15-patterns #4 at the indexed
    strength): the claim IS the type index — a discharge proves the
    ACTUAL preservation property, never a claim-shaped name. -/
def UpdateItem.uniqueObligation (u : UpdateItem fs) (key : String) :
    Kit.Obligation UpdateClaim (u.keyUniqueProp key) :=
  { label := s!"update/{u.record}/{u.name}-preserves-unique({key})"
    tier := .decidableNow
    payload := .keyUnique fs u key
    provenance := `SchemaCore }

/-- THE DISCHARGE — the kit's decidableNow backend; `none` is the loud
    gap (the backend refuses, it does not fabricate evidence). -/
def UpdateItem.dischargeUnique (u : UpdateItem fs) (key : String) :
    Option Kit.Evidence :=
  (u.uniqueObligation key).decideDischarge

/-- The discharge's SOUNDNESS — the kit backend's theorem, cited. -/
theorem UpdateItem.dischargeUnique_sound {fs : List Field} (u : UpdateItem fs)
    (key : String) (h : u.dischargeUnique key = some (.decided true)) :
    u.keyUniqueProp key :=
  Kit.Obligation.decideDischarge_sound (u.uniqueObligation key) rfl h

/-- The discharge's COMPLETENESS — a true claim fires the backend. -/
theorem UpdateItem.dischargeUnique_complete {fs : List Field}
    (u : UpdateItem fs) (key : String) (hc : u.keyUniqueProp key) :
    u.dischargeUnique key = some (.decided true) :=
  Kit.Obligation.decideDischarge_of_claim (u.uniqueObligation key) rfl hc

end SchemaCore
