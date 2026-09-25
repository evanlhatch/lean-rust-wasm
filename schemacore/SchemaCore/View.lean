/-
# SchemaCore.View — the writable-views lane: relational lenses over keyed tables

Owner: the writable-views agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/02-data-plane.md §7 ("The bidirectional
problem: edit the view → which base changes follow? Relational lenses:
view + update policy + laws (read-after-write returns the requested
view; an unchanged view preserves the source). Derive the writable
fragment from keys/dependencies; expose ambiguity precisely (an
aggregate edit with many base preimages refuses or demands a
policy).") + notes/v3/03-bidirectional.md §2 (the complement lens:
"The OldModel retains what the surface can't express" — the
unprojected columns are the complement, and the frame law pins their
survival) + notes/v3/15-patterns.md #1 (relation + executable checker
+ the proved bridge).

What lands here:

- `ViewDef` — THE VIEW IS A QUERY: the selection (`Pred`, the schema's
  OWN predicate fragment, consumed read-only) + the projection over
  the base table's rows. The projection's column data is the
  writeback-TYPED twin of `Query.Expr.Cols`: the read-side column data
  lives cone-high (the `query/` package imports `SchemaCore`), so the
  writable lane's columns carry the update lane's write PATH
  (`ColPath` — a write to a missing or mistyped column is
  unconstructible) instead of a bare position. The view row schema is
  COMPUTED (`vfields`).
- `ColPath.get` + its laws — the write spine's reader (read your own
  write / write what you read / another column's write is invisible),
  proved ONCE here; `get_project?` ties the reader to the Keys lane's
  name-keyed projection under nodup names.
- THE WRITABLE FRAGMENT, derived honestly: a view edit is writable
  when the projection is KEY-RESPECTING (`ViewCoherent.keyMem` — the
  declared key column rides the projection), the columns' names are
  distinct (read-after-write's premise), and the selection reads only
  the key (the verdict-stability premise). THE EDIT MAPS BACK UNIQUELY
  VIA THE KEY'S DETERMINACY: the preimage fiber (the selected rows
  carrying the edited key image) has at most one element under the
  CHECKED `uniqueOn` — `filter_matches_le_one` is that theorem, the
  Keys lane's `uniqueOn_determines` consumed, never re-proved.
- THE AMBIGUITY DISCIPLINE: the classifier `viewPut` is TOTAL and the
  refusals CARRY the ambiguity as data — `noPreimage k` (the edited
  key image names no selected base row) and `ambiguous n` (n base
  preimages: a violated uniqueness makes the key no longer determine
  the row — the aggregate-edit-many-preimages case, named with its
  count; the non-key-respecting projection's edit refuses the same
  way, over the projection's full-row fiber `viewFiber`). A refusal
  never fabricates a base row.
- THE LENS (`ViewLens` + `keyedViewLens`) — the view/update pair as
  the honest carrier, with the laws as FIELDS riding their honest
  premises: `get_put` (read-after-write: an applied edit's view
  returns the requested row — `viewPut_get`) and `put_get`
  (unchanged-view preservation: the edit that writes back what the
  view read restores the table EXACTLY — `viewPut_preserves`, the
  singleton-fiber premise discharged by the determinacy). NOT a
  `Kit.Iso` and not a `Kit.Retraction`: the view cannot express the
  base's complement columns, so no round trip is total — the grade's
  honesty IS the partiality.
- THE COMPLEMENT LENS (03 §2): `vwrite_project?_neutral` — every
  column the view does not project survives the writeback untouched;
  the base retains what the surface can't express.
- THE DELTA INTEGRATION: the applied edit's verdict carries the base
  DELTA as the update lane's shared `RowDelta` (`RowDelta.update` of
  the written row) AND the post-state computed through the keyed
  applicator `applyRowDelta` — the change flows through the landed
  delta/check machinery, so a proposed view delta validates through
  the violation lane where the lanes compose honestly (pinned in
  SchemaTests).

Deliberate exclusions (the leftover rule): INSERT/DELETE view edits
(the new row's complement columns have no preimage to inherit — the
policy lands with the first consumer that can name one); joins and
aggregations (the projection's preimage is one keyed row — the
multi-table and summed fragments need the policy discipline 02 §7
names, not this lane's per-key writeback); composite keys (the Keys
lane's v1 granularity); the `Query.Q`-typed view expression (the cone:
`query/` imports `SchemaCore` — the read-side fragment stays there,
and this lane's columns are the writeback-typed twin, named above).

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's bidirectional face (02 §7) — the view is
  a query, the edit is a keyed update, the verdict is a delta or a
  named refusal.
- **Carrier grade**: the GADT-indexed rows + the writeback-typed
  column paths (a mistyped write unconstructible — the Update lane's
  spine consumed, not re-carried).
- **Spine reading**: none — the lane rides the Keys determinacy
  theorems and the Update delta machinery the way Commit does.
- **Ladder rung**: the lens laws are the small hand kind over the
  determinacy citation (`filter_matches_le_one` is an induction; the
  laws are its corollaries).
- **Gate row**: SchemaTests' viewSpec (the worked keyed edit + the
  ambiguity teeth + the preservation pin + the mandatory negative
  controls) + the axiom report.

Core-only (imports SchemaCore.Update — the cone rule; Keys, Pred,
Check, RowVals arrive transitively and are consumed read-only).
-/

import SchemaCore.Update

namespace SchemaCore

/-! ## The write spine's reader — `ColPath.get` + its laws -/

/-- The positional read: the path's column value, total by the index
    (the write spine's reader — the read face the writeback's laws
    need). -/
def ColPath.get {n : String} {t : Ty} :
    {fs : List Field} → ColPath n t fs → RowVals fs → Value t
  | _, .here, .cons v _ => v
  | _, .there p, .cons _ vs => p.get vs

/-- READ YOUR OWN WRITE: the path's read after the path's write
    returns the written value. -/
theorem ColPath.set_get {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs) (v : Value t),
      ColPath.get p (p.set row v) = v
  | _, .here, .cons _ _, _ => rfl
  | _, .there p, .cons _ vs, v => p.set_get vs v

/-- WRITE WHAT YOU READ: setting the path's column to its own read
    value changes nothing (the unchanged-view preservation's row-level
    kernel). -/
theorem ColPath.set_self {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs),
      p.set row (ColPath.get p row) = row
  | _, .here, .cons _ _ => rfl
  | _, .there p, .cons a vs => by
      show RowVals.cons a (p.set vs (ColPath.get p vs)) = RowVals.cons a vs
      rw [p.set_self vs]

/-- The path's column is on the field list (the name-collision step). -/
theorem ColPath.mem_names {n : String} {t : Ty} :
    ∀ {fs : List Field} (_p : ColPath n t fs), n ∈ fs.map (·.name)
  | _, .here => List.mem_cons_self
  | _, .there p => List.mem_cons_of_mem _ (ColPath.mem_names p)

/-- THE READER IS THE NAME-KEYED PROJECTION: under distinct field
    names, the path's read IS `RowVals.project?` at the path's name —
    the Keys lane's projections and this lane's reads agree (one
    reading, never a parallel table). -/
theorem ColPath.get_project? {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs),
      (fs.map (·.name)).Nodup →
      RowVals.project? fs row n = some { ty := t, val := ColPath.get p row } := by
  intro fs p
  induction p with
  | here =>
      intro row _
      cases row with
      | cons v vs =>
          simp only [RowVals.project?]
          rw [if_pos (beq_self_eq_true _)]
          rfl
  | @there f fs' p ih =>
      intro row hnd
      cases row with
      | cons a vs =>
          have hne : f.name ≠ n := by
            intro he
            have hmem : n ∈ fs'.map (·.name) := ColPath.mem_names p
            rw [← he] at hmem
            have hnd2 : ((f :: fs').map (·.name)).Nodup := hnd
            rw [List.map_cons] at hnd2
            exact (List.nodup_cons.mp hnd2).1 hmem
          simp only [RowVals.project?]
          rw [if_neg (by rw [beq_false_of_ne hne]; simp)]
          exact ih vs (List.nodup_cons.mp hnd).2

/-- ANOTHER COLUMN'S WRITE IS INVISIBLE: reading the path after a
    write at a DIFFERENTLY-NAMED column returns the original read (the
    frame's row-level kernel — the Update lane's
    `set_project?_neutral` at the reader). -/
theorem ColPath.get_set_neutral {n₁ n₂ : String} {t₁ t₂ : Ty} :
    ∀ {fs : List Field} (p₁ : ColPath n₁ t₁ fs) (p₂ : ColPath n₂ t₂ fs),
      n₁ ≠ n₂ → ∀ (row : RowVals fs) (v : Value t₂),
        ColPath.get p₁ (p₂.set row v) = ColPath.get p₁ row := by
  intro fs
  induction fs with
  | nil => intro p₁ p₂ _; cases p₁ <;> cases p₂
  | cons f fs' ih =>
      intro p₁ p₂ hne row v
      cases row with
      | cons a vs =>
          cases p₁ with
          | here =>
              cases p₂ with
              | here => exact absurd rfl hne
              | there _ => rfl
          | there p₁' =>
              cases p₂ with
              | here => rfl
              | there p₂' =>
                  show ColPath.get p₁' (p₂'.set vs v) = ColPath.get p₁' vs
                  exact ih p₁' p₂' hne vs v

/-- The projection's head equations (the GADT-index literal form —
    ordinary `rw` cannot rewrite under the map-form index; the literal
    form is what the equations fire on). -/
theorem RowVals.project?_cons_head {f : Field} {fs : List Field}
    (v : Value f.ty) (vs : RowVals fs) (n : String) (h : (f.name == n) = true) :
    RowVals.project? (f :: fs) (RowVals.cons v vs) n
      = some { ty := f.ty, val := v } := by
  simp only [RowVals.project?]
  rw [if_pos h]

theorem RowVals.project?_cons_miss {f : Field} {fs : List Field}
    (v : Value f.ty) (vs : RowVals fs) (n : String) (h : (f.name == n) = false) :
    RowVals.project? (f :: fs) (RowVals.cons v vs) n = RowVals.project? fs vs n := by
  simp only [RowVals.project?]
  rw [if_neg (by rw [h]; simp)]

/-! ## The view: a query over the keyed table's rows -/

/-- The view's write column: the projected field + the structural
    write path into the base row (the update lane's `ColPath` spine —
    the writeback-typed twin of the read-side column data). -/
structure ViewCol (fs : List Field) where
  field : Field
  path : ColPath field.name field.ty fs

/-- THE VIEW (a query over the schema's table): the projected columns
    + the selection predicate (the schema's OWN `Pred` fragment). The
    view row's schema is COMPUTED (`vfields`). -/
structure ViewDef (fs : List Field) where
  name : String
  cols : List (ViewCol fs)
  sel : Pred fs := .lit true

/-- The view row's schema: the projected fields, in column order. -/
def ViewDef.vfields (vd : ViewDef fs) : List Field := vd.cols.map (·.field)

/-- The view's per-row read: the projected row (total by the paths'
    indices — no projection failure path at all). -/
def vpick (fs : List Field) :
    (cols : List (ViewCol fs)) → RowVals fs → RowVals (cols.map (·.field))
  | [], _ => .nil
  | c :: cs, row => .cons (c.path.get row) (vpick fs cs row)

/-- The view's per-row write: each projected column set from the view
    row, left to right (the write spine's fold — distinct names make
    the order unobservable). -/
def vwrite (fs : List Field) :
    (cols : List (ViewCol fs)) →
      RowVals (cols.map (·.field)) → RowVals fs → RowVals fs
  | [], .nil, row => row
  | c :: cs, .cons v vr, row => vwrite fs cs vr (c.path.set row v)

/-- The view's read: the selected base rows, projected (the view IS a
    query — the selection restricts, the projection reads). -/
def ViewDef.get (vd : ViewDef fs) (rows : List (RowVals fs)) :
    List (RowVals vd.vfields) :=
  (rows.filter vd.sel.check).map (vpick fs vd.cols)

/-! ## The writeback's laws (the lens's row-level kernel) -/

/-- The write is INVISIBLE to a name the columns do not project (the
    complement lens, 03 §2: the base retains what the surface can't
    express). -/
theorem vwrite_project?_neutral {fs : List Field} :
    ∀ (cols : List (ViewCol fs)) (v : RowVals (cols.map (·.field)))
        (row : RowVals fs) (n : String),
      n ∉ cols.map (·.field.name) →
      RowVals.project? fs (vwrite fs cols v row) n = RowVals.project? fs row n := by
  intro cols
  induction cols with
  | nil => intro v row n _; cases v; rfl
  | cons c cs ih =>
      intro v row n hn
      cases v with
      | cons val vr =>
          simp only [vwrite]
          rw [ih vr (c.path.set row val) n
            (fun hmem => hn (List.mem_cons.mpr (Or.inr hmem)))]
          exact ColPath.set_project?_neutral c.path row val n
            (fun he => hn (List.mem_cons.mpr (Or.inl he)))

/-- The write AT a projected name lands the view row's value: under
    distinct names, the base projection after the writeback IS the
    view row's projection (the writeback does not lie). -/
theorem vwrite_project?_key {fs : List Field}
    (fieldNodup : (fs.map (·.name)).Nodup) :
    ∀ (cols : List (ViewCol fs)), (cols.map (·.field.name)).Nodup →
      ∀ (v : RowVals (cols.map (·.field))) (row : RowVals fs) (n : String),
        n ∈ cols.map (·.field.name) →
        RowVals.project? fs (vwrite fs cols v row) n
          = RowVals.project? (cols.map (·.field)) v n := by
  intro cols
  induction cols with
  | nil =>
      intro _ v row n h
      cases v
      exact absurd h (by simp)
  | cons c cs ih =>
      intro hnd v row n hn
      cases v with
      | cons val vr =>
          have htail : (cs.map (·.field.name)).Nodup := (List.nodup_cons.mp hnd).2
          rcases List.mem_cons.mp hn with he | hmem'
          · rw [he]
            simp only [vwrite]
            rw [vwrite_project?_neutral cs vr (c.path.set row val) c.field.name
              (fun hmem => (List.nodup_cons.mp hnd).1 hmem)]
            rw [c.path.get_project? (c.path.set row val) fieldNodup,
              c.path.set_get]
            exact (RowVals.project?_cons_head val vr _ (beq_self_eq_true _)).symm
          · have hne : n ≠ c.field.name := by
              intro heq
              rw [heq] at hmem'
              exact (List.nodup_cons.mp hnd).1 hmem'
            have hbeq : (c.field.name == n) = false :=
              beq_false_of_ne (fun h => hne h.symm)
            simp only [vwrite]
            rw [ih htail vr (c.path.set row val) n hmem']
            exact (RowVals.project?_cons_miss val vr n hbeq).symm

/-- The view row's projection IS the base row's projection at the
    projected names (the read face of the same agreement). -/
theorem vpick_project? {fs : List Field}
    (fieldNodup : (fs.map (·.name)).Nodup) :
    ∀ (cols : List (ViewCol fs)), (cols.map (·.field.name)).Nodup →
      ∀ (row : RowVals fs) (n : String), n ∈ cols.map (·.field.name) →
        RowVals.project? (cols.map (·.field)) (vpick fs cols row) n
          = RowVals.project? fs row n := by
  intro cols
  induction cols with
  | nil => intro _ row n h; exact absurd h (by simp)
  | cons c cs ih =>
      intro hnd row n hn
      show RowVals.project? (c.field :: cs.map (·.field))
        (RowVals.cons (c.path.get row) (vpick fs cs row)) n = _
      simp only [RowVals.project?]
      rcases List.mem_cons.mp hn with he | hmem'
      · subst he
        rw [if_pos (beq_self_eq_true _), c.path.get_project? row fieldNodup]
      · have hne : n ≠ c.field.name := by
          intro heq
          rw [heq] at hmem'
          exact (List.nodup_cons.mp hnd).1 hmem'
        have hbeq : (c.field.name == n) = false :=
          beq_false_of_ne (fun h => hne h.symm)
        rw [if_neg (by rw [hbeq]; simp)]
        exact ih (List.nodup_cons.mp hnd).2 row n hmem'

/-- PUT∘GET (the preservation law's row-level kernel): writing back
    what the view read changes nothing. -/
theorem vwrite_vpick (fs : List Field) :
    ∀ (cols : List (ViewCol fs)) (row : RowVals fs),
      vwrite fs cols (vpick fs cols row) row = row := by
  intro cols
  induction cols with
  | nil => intro row; rfl
  | cons c cs ih =>
      intro row
      show vwrite fs cs (vpick fs cs row)
        (c.path.set row (ColPath.get c.path row)) = row
      rw [c.path.set_self]
      exact ih row

/-- A write fold is invisible to a column none of its entries name
    (the neutrality lift the per-row laws ride). -/
theorem vwrite_get_neutral {fs : List Field} :
    ∀ (cols : List (ViewCol fs)) (c : ViewCol fs),
      (∀ c' ∈ cols, c'.field.name ≠ c.field.name) →
      ∀ (v : RowVals (cols.map (·.field))) (row : RowVals fs),
        ColPath.get c.path (vwrite fs cols v row) = ColPath.get c.path row := by
  intro cols
  induction cols with
  | nil => intro c _ v row; cases v; rfl
  | cons c0 cs ih =>
      intro c hne v row
      cases v with
      | cons val vr =>
          simp only [vwrite]
          rw [ih c (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) vr
            (c0.path.set row val)]
          exact ColPath.get_set_neutral c.path c0.path
            (Ne.symm (hne c0 List.mem_cons_self)) row val

/-- GET∘PUT (the read-after-write law's row-level kernel): the
    projected read after the writeback IS the edited view row — the
    distinct-names premise is load-bearing (a duplicated column's
    later write would clobber the earlier's read). -/
theorem vpick_vwrite (fs : List Field) :
    ∀ (cols : List (ViewCol fs)), (cols.map (·.field.name)).Nodup →
      ∀ (v : RowVals (cols.map (·.field))) (row : RowVals fs),
        vpick fs cols (vwrite fs cols v row) = v := by
  intro cols
  induction cols with
  | nil => intro _ v row; cases v; rfl
  | cons c cs ih =>
      intro hnd v row
      cases v with
      | cons val vr =>
          show RowVals.cons
            (ColPath.get c.path (vwrite fs cs vr (c.path.set row val)))
            (vpick fs cs (vwrite fs cs vr (c.path.set row val)))
            = RowVals.cons val vr
          rw [vwrite_get_neutral cs c
                (fun c' hc' => by
                  have hmem : c'.field.name ∈ cs.map (·.field.name) :=
                    List.mem_map_of_mem hc'
                  have hnot : c.field.name ∉ cs.map (·.field.name) :=
                    (List.nodup_cons.mp hnd).1
                  intro heq
                  rw [← heq] at hnot
                  exact hnot hmem) vr
                (c.path.set row val),
              c.path.set_get,
              ih (List.nodup_cons.mp hnd).2 vr (c.path.set row val)]

/-! ## The determinacy's writable face -/

/-- THE WRITABLE FRAGMENT'S DETERMINACY (the Keys lane's payoff at the
    fiber): under a CHECKED `uniqueOn`, the rows matching a key image
    (with any extra Bool condition) are at most ONE — the edit maps
    back uniquely. The determinacy theorem is consumed
    (`uniqueOn_determines` via `keyImages?_mem`), never re-proved. -/
theorem KeyDecl.filter_matches_le_one (kd : KeyDecl) (k : FieldVal)
    (c : RowVals kd.fields → Bool) :
    ∀ (rows : List (RowVals kd.fields)), kd.uniqueOn rows = true →
      (rows.filter (fun r => c r && kd.matchesKey r k)).length ≤ 1 := by
  intro rows
  induction rows with
  | nil => intro _; simp
  | cons r0 rest ih =>
      intro huniq
      obtain ⟨v, vs, hir, hrest, hnup⟩ :
          ∃ v vs, kd.image? r0 = some v ∧ kd.keyImages? rest = some vs
            ∧ FieldVal.nodup (v :: vs) = true := by
        cases hv : kd.image? r0 with
        | none => simp [uniqueOn, keyImages?, hv] at huniq
        | some v =>
            cases hrest : kd.keyImages? rest with
            | none => simp [uniqueOn, keyImages?, hv, hrest] at huniq
            | some vs =>
                rw [uniqueOn, keyImages?, hv, hrest] at huniq
                exact ⟨v, vs, rfl, rfl, huniq⟩
      have hrestU : kd.uniqueOn rest = true := by
        rw [uniqueOn, hrest]
        exact (FieldVal.nodup_cons hnup).1
      rw [List.filter_cons]
      by_cases hc : (c r0 && kd.matchesKey r0 k) = true
      · have hmk0 : kd.matchesKey r0 k = true := by
          rw [Bool.and_eq_true] at hc
          exact hc.2
        have hvk : v = k :=
          Option.some.inj (hir.symm.trans (kd.matchesKey_image r0 k hmk0))
        have h0 : rest.filter (fun r => c r && kd.matchesKey r k) = [] := by
          rw [List.filter_eq_nil_iff]
          intro r' hr' hcon
          cases hbad : (c r' && kd.matchesKey r' k) with
          | false => exact absurd hcon (by rw [hbad]; simp)
          | true =>
              rw [Bool.and_eq_true] at hbad
              obtain ⟨_, hmk⟩ := hbad
              have hkmem : k ∈ vs := kd.keyImages?_mem rest r' k vs hr'
                (kd.matchesKey_image r' k hmk) hrest
              obtain ⟨_, hne⟩ := FieldVal.nodup_cons hnup
              rw [hvk] at hne
              exact absurd (FieldVal.beq_refl k)
                (by rw [hne k hkmem]; simp)
        rw [if_pos hc, h0]
        simp
      · rw [if_neg hc]
        exact ih hrestU

/-! ## The classifier: the edit's verdict — the delta or the NAMED refusal -/

/-- The named refusals (the ambiguity discipline — each refusal
    CARRIES the ambiguity as data, never a bare `false`). -/
inductive ViewRefusal where
  /-- The edited key image names no selected base row (an INSERT is
      trying to speak — outside the update fragment). -/
  | noPreimage (k : FieldVal)
  /-- n base preimages: a violated uniqueness makes the key no longer
      determine the row — the aggregate-edit-many-preimages case; for
      a projection that does not carry the key, n is the full-row
      fiber's count (n = 0 reads as no preimage; even the
      singleton-fiber policy is refused — the declared extension). -/
  | ambiguous (n : Nat)

/-- The edit's verdict: the base DELTA (the update lane's shared
    carrier) + the post-state computed through the keyed applicator —
    or the named refusal. -/
inductive ViewEditVerdict (fs : List Field) where
  | apply : List (RowDelta fs) → List (RowVals fs) → ViewEditVerdict fs
  | refuse : ViewRefusal → ViewEditVerdict fs

/-- The verdict's post-state face (the commit lane's reading). -/
def ViewEditVerdict.post? {fs : List Field} :
    ViewEditVerdict fs → Option (List (RowVals fs))
  | .apply _ r' => some r'
  | .refuse _ => none

/-- The verdict's refusal face (the diagnostic's reading). -/
def ViewEditVerdict.refusal? {fs : List Field} :
    ViewEditVerdict fs → Option ViewRefusal
  | .apply _ _ => none
  | .refuse r => some r

/-- The refusal's rendering (diagnostics + test pins; NOT byte-tied). -/
def ViewRefusal.render : ViewRefusal → String
  | .noPreimage _ => "no-preimage"
  | .ambiguous n => s!"ambiguous({n})"

/-- The non-key-respecting fiber: the base rows the edited view row's
    FULL projection reads from (the ambiguity's data when the
    projection does not carry the key). -/
def viewFiber (fs : List Field) (vd : ViewDef fs)
    (rows : List (RowVals fs)) (v : RowVals vd.vfields) : List (RowVals fs) :=
  rows.filter (fun r => rowBeq vd.vfields (vpick fs vd.cols r) v)

/-- THE CLASSIFIER (the bidirectional problem, as data): the edited
    view row's key image decides — the key-respecting fiber (the
    SELECTED rows carrying the image) is the preimage; a singleton
    applies the keyed writeback as the shared `RowDelta.update` (the
    delta/check machinery's carrier), anything else REFUSES with the
    ambiguity named. Total and decidable. -/
def viewPut (kd : KeyDecl) (vd : ViewDef kd.fields)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields) :
    ViewEditVerdict kd.fields :=
  match RowVals.project? vd.vfields v kd.key with
  | none =>
      .refuse (.ambiguous (viewFiber kd.fields vd rows v).length)
  | some k =>
      match rows.filter (fun r => vd.sel.check r && kd.matchesKey r k) with
      | [] => .refuse (.noPreimage k)
      | [r] =>
          .apply [RowDelta.update (vwrite kd.fields vd.cols v r)]
            (applyRowDelta kd.key
              (RowDelta.update (vwrite kd.fields vd.cols v r)) rows)
      | fiber => .refuse (.ambiguous fiber.length)

/-- A projected row's `some` projection names its column (the
    key-respecting evidence's derivation). -/
theorem viewColOfProject? {fs : List Field} :
    ∀ (cols : List (ViewCol fs)) (v : RowVals (cols.map (·.field)))
        (n : String) (x : FieldVal),
      RowVals.project? (cols.map (·.field)) v n = some x →
        ∃ c ∈ cols, c.field.name = n := by
  intro cols
  induction cols with
  | nil =>
      intro v n x h
      cases v
      have h' : RowVals.project? [] RowVals.nil n = some x := h
      simp only [RowVals.project?] at h'
      exact absurd h' (by simp)
  | cons c cs ih =>
      intro v n x h
      cases v with
      | cons val vr =>
          have h' : RowVals.project? (c.field :: cs.map (·.field))
              (RowVals.cons val vr) n = some x := h
          simp only [RowVals.project?] at h'
          by_cases hc : c.field.name == n
          · rw [if_pos hc] at h'
            exact ⟨c, List.mem_cons_self, beq_iff_eq.mp hc⟩
          · rw [if_neg hc] at h'
            obtain ⟨c', hmem, hname⟩ := ih vr n x h'
            exact ⟨c', List.mem_cons_of_mem _ hmem, hname⟩

/-! ## The coherence pack (the writable fragment's premises) -/

/-- THE COHERENCE PACK (the KeyCoherent precedent): the premises the
    lens laws need, decidable over concrete data — the base field
    names distinct (the first-match tie-break retires), the columns'
    names distinct (read-after-write's premise), the declared key
    column rides the projection (KEY-RESPECTING — the fragment's
    shape), and the selection reads only the key (the
    verdict-stability premise). -/
structure ViewCoherent (kd : KeyDecl) (vd : ViewDef kd.fields) : Prop where
  fieldNodup : (kd.fields.map (·.name)).Nodup
  colNodup : (vd.cols.map (·.field.name)).Nodup
  keyMem : ∃ c ∈ vd.cols, c.field.name = kd.key
  selKeyOnly : ∀ n ∈ vd.sel.reads, n = kd.key

/-- The selection's verdict depends only on its read columns (the
    verdict-stability step: the writeback preserves the key image, so
    a key-only selection's verdict survives the write). -/
theorem Pred.check_project?_ext {fs : List Field} :
    ∀ (p : Pred fs) (key : String), (∀ n ∈ p.reads, n = key) →
      ∀ (x y : RowVals fs),
        RowVals.project? fs x key = RowVals.project? fs y key →
        p.check x = p.check y := by
  intro p
  induction p with
  | lit _ => intro _ _ _ _ _; rfl
  | u64EqLit n v =>
      intro key hreads x y h
      have hnk : n = key := hreads n List.mem_cons_self
      simp only [Pred.check, hnk, h]
  | u64GtLit n v =>
      intro key hreads x y h
      have hnk : n = key := hreads n List.mem_cons_self
      simp only [Pred.check, hnk, h]
  | u64Eq a b =>
      intro key hreads x y h
      have hak : a = key := hreads a List.mem_cons_self
      have hbk : b = key := hreads b (List.mem_cons_of_mem a List.mem_cons_self)
      simp only [Pred.check, hak, hbk, h]
  | strEqLit n s =>
      intro key hreads x y h
      have hnk : n = key := hreads n List.mem_cons_self
      simp only [Pred.check, hnk, h]
  | and p q ihp ihq =>
      intro key hreads x y h
      simp only [Pred.check]
      rw [ihp key (fun n hn => hreads n (List.mem_append.mpr (Or.inl hn))) x y h,
        ihq key (fun n hn => hreads n (List.mem_append.mpr (Or.inr hn))) x y h]
  | or p q ihp ihq =>
      intro key hreads x y h
      simp only [Pred.check]
      rw [ihp key (fun n hn => hreads n (List.mem_append.mpr (Or.inl hn))) x y h,
        ihq key (fun n hn => hreads n (List.mem_append.mpr (Or.inr hn))) x y h]
  | not p ih =>
      intro key hreads x y h
      simp only [Pred.check]
      rw [ih key hreads x y h]

/-! ## The classifier's computed forms (the arm equations) -/

/-- The miss arm: an empty preimage fiber refuses, naming the key. -/
theorem viewPut_miss (kd : KeyDecl) (vd : ViewDef kd.fields)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields) (k : FieldVal)
    (hk : RowVals.project? vd.vfields v kd.key = some k)
    (hfiber : rows.filter (fun r => vd.sel.check r && kd.matchesKey r k) = []) :
    viewPut kd vd rows v = ViewEditVerdict.refuse (.noPreimage k) := by
  simp only [viewPut, hk, hfiber]

/-- The hit arm: a singleton fiber applies the keyed writeback — the
    delta is the update lane's `RowDelta.update` of the written row,
    the post-state the keyed applicator's output. -/
theorem viewPut_hit (kd : KeyDecl) (vd : ViewDef kd.fields)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields) (k : FieldVal)
    (hk : RowVals.project? vd.vfields v kd.key = some k) (r : RowVals kd.fields)
    (hfiber : rows.filter (fun r => vd.sel.check r && kd.matchesKey r k) = [r]) :
    viewPut kd vd rows v
      = ViewEditVerdict.apply [RowDelta.update (vwrite kd.fields vd.cols v r)]
          (applyRowDelta kd.key
            (RowDelta.update (vwrite kd.fields vd.cols v r)) rows) := by
  simp only [viewPut, hk, hfiber]

/-- The ambiguity arm: two or more preimages refuse, naming the count
    (the aggregate-edit-many-preimages case). -/
theorem viewPut_many (kd : KeyDecl) (vd : ViewDef kd.fields)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields) (k : FieldVal)
    (hk : RowVals.project? vd.vfields v kd.key = some k)
    (r0 r1 : RowVals kd.fields) (rest : List (RowVals kd.fields))
    (hfiber : rows.filter (fun r => vd.sel.check r && kd.matchesKey r k)
      = r0 :: r1 :: rest) :
    viewPut kd vd rows v
      = ViewEditVerdict.refuse (.ambiguous (r0 :: r1 :: rest).length) := by
  simp only [viewPut, hk, hfiber]

/-- The no-key arm: a projection that does not carry the declared key
    refuses over the full-row fiber (the non-key-respecting view's
    named ambiguity). -/
theorem viewPut_noKey (kd : KeyDecl) (vd : ViewDef kd.fields)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields)
    (hk : RowVals.project? vd.vfields v kd.key = none) :
    viewPut kd vd rows v
      = ViewEditVerdict.refuse
          (.ambiguous (viewFiber kd.fields vd rows v).length) := by
  simp only [viewPut, hk]

/-- The keyed applicator's update arm keeps the written row whenever
    the replaced row shares its key image (the delta-integration's
    membership step). -/
theorem applyRowDelta_update_mem_of_image {fs : List Field} (key : String)
    (w src : RowVals fs) (k : FieldVal) (rows : List (RowVals fs))
    (hsrc : src ∈ rows)
    (hsimg : RowVals.project? fs src key = some k)
    (hwimg : RowVals.project? fs w key = some k) :
    w ∈ applyRowDelta key (RowDelta.update w) rows := by
  show w ∈ rows.map
    (fun old =>
      match RowVals.project? fs old key with
      | some a =>
          match RowVals.project? fs w key with
          | some c => if FieldVal.beq a c then w else old
          | none => old
      | none => old)
  rw [List.mem_map]
  exact ⟨src, hsrc, by simp [hsimg, hwimg, FieldVal.beq_refl]⟩

/-- The keyed applicator's update arm is the IDENTITY when the written
    row is already the table's row at its key image (the preservation
    law's table-level step). -/
theorem applyRowDelta_update_self {fs : List Field} (key : String)
    (rows : List (RowVals fs)) (b : RowVals fs) (k : FieldVal)
    (hbimg : RowVals.project? fs b key = some k)
    (hdet : ∀ r ∈ rows, RowVals.project? fs r key = some k → r = b) :
    applyRowDelta key (RowDelta.update b) rows = rows := by
  show rows.map
      (fun old =>
        match RowVals.project? fs old key with
        | some a =>
            match RowVals.project? fs b key with
            | some c => if FieldVal.beq a c then b else old
            | none => old
        | none => old) = rows
  apply map_eq_self_of_forall
  intro old ho
  cases hp : RowVals.project? fs old key with
  | none => rfl
  | some a =>
      simp only [hbimg]
      by_cases hbe : FieldVal.beq a k = true
      · have hak : a = k := (FieldVal.beq_eq_true_iff_eq a k).mp hbe
        have h' : RowVals.project? fs old key = some k := by rw [hp, hak]
        rw [if_pos hbe, hdet old ho h']
      · rw [if_neg hbe]

/-! ## THE LENS LAWS -/

/-- **LAW 1 — READ-AFTER-WRITE** (get∘put, 02 §7): an APPLIED edit's
    view returns the requested row. The proof consumes the key's
    determinacy only through the classifier's own decision (a hit IS a
    singleton fiber); the distinct-names premise discharges the
    writeback's read-back (`vpick_vwrite`). -/
theorem viewPut_get (kd : KeyDecl) (vd : ViewDef kd.fields)
    (coh : ViewCoherent kd vd)
    (rows : List (RowVals kd.fields)) (v : RowVals vd.vfields)
    (δ : List (RowDelta kd.fields)) (r' : List (RowVals kd.fields))
    (h : viewPut kd vd rows v = ViewEditVerdict.apply δ r') :
    v ∈ vd.get r' := by
  cases hk : RowVals.project? vd.vfields v kd.key with
  | none =>
      rw [viewPut_noKey kd vd rows v hk] at h
      simp at h
  | some k =>
      obtain ⟨kc, hkcmem, hkcname⟩ := viewColOfProject? vd.cols v kd.key k hk
      cases hfiber : rows.filter (fun r => vd.sel.check r && kd.matchesKey r k) with
      | nil =>
          rw [viewPut_miss kd vd rows v k hk hfiber] at h
          simp at h
      | cons r rest =>
          cases rest with
          | cons r1 rest1 =>
              rw [viewPut_many kd vd rows v k hk r r1 rest1 hfiber] at h
              simp at h
          | nil =>
              rw [viewPut_hit kd vd rows v k hk r hfiber] at h
              obtain ⟨hδ, hr'⟩ := ViewEditVerdict.apply.inj h
              subst hr'
              -- the preimage row: selected, carrying the edited key image
              have hrfil : r ∈ rows.filter
                  (fun r => vd.sel.check r && kd.matchesKey r k) := by
                rw [hfiber]; exact List.mem_cons_self
              obtain ⟨hr, hfsel⟩ := List.mem_filter.mp hrfil
              rw [Bool.and_eq_true] at hfsel
              obtain ⟨hselr, hmkr⟩ := hfsel
              have himg : kd.image? r = some k := kd.matchesKey_image r k hmkr
              have himgp : RowVals.project? kd.fields r kd.key = some k := himg
              -- the written row: the key image lands, the read-back holds
              have hkeyin : kd.key ∈ vd.cols.map (·.field.name) := by
                rw [← hkcname]; exact List.mem_map_of_mem hkcmem
              have hwimg : RowVals.project? kd.fields
                  (vwrite kd.fields vd.cols v r) kd.key = some k := by
                rw [vwrite_project?_key coh.fieldNodup vd.cols coh.colNodup v r
                  kd.key hkeyin]
                exact hk
              -- the delta keeps the written row (the keyed applicator)
              have hwmem := applyRowDelta_update_mem_of_image kd.key
                (vwrite kd.fields vd.cols v r) r k rows hr himgp hwimg
              -- the written row stays selected (the key-only selection)
              have hselw : vd.sel.check (vwrite kd.fields vd.cols v r) = true := by
                rw [Pred.check_project?_ext vd.sel kd.key coh.selKeyOnly
                  (vwrite kd.fields vd.cols v r) r (by rw [hwimg]; exact himgp.symm)]
                exact hselr
              -- the read-back: the requested view row comes back
              rw [ViewDef.get]
              exact List.mem_map.mpr ⟨vwrite kd.fields vd.cols v r,
                List.mem_filter.mpr ⟨hwmem, hselw⟩,
                vpick_vwrite kd.fields vd.cols coh.colNodup v r⟩

/-- **LAW 2 — UNCHANGED-VIEW PRESERVATION** (put∘get's honest form, 02
    §7): the edit that writes back what the view read restores the
    table EXACTLY — the delta is the row's own `RowDelta.update`, and
    the keyed applicator's map fixes every row. The singleton-fiber
    premise is discharged by the KEY'S DETERMINACY (the checked
    `uniqueOn` through `filter_matches_le_one`), never assumed. -/
theorem viewPut_preserves (kd : KeyDecl) (vd : ViewDef kd.fields)
    (coh : ViewCoherent kd vd)
    (rows : List (RowVals kd.fields)) (b : RowVals kd.fields)
    (huniq : kd.uniqueOn rows = true) (hb : b ∈ rows)
    (hsel : vd.sel.check b = true) :
    viewPut kd vd rows (vpick kd.fields vd.cols b)
      = ViewEditVerdict.apply [RowDelta.update b] rows := by
  obtain ⟨kc, hkcmem, hkcname⟩ := coh.keyMem
  have hkeyin : kd.key ∈ vd.cols.map (·.field.name) :=
    hkcname ▸ List.mem_map_of_mem (f := fun x => x.field.name) hkcmem
  have hbkey : RowVals.project? kd.fields b kd.key
      = some { ty := kc.field.ty, val := kc.path.get b } := by
    rw [← hkcname]
    exact kc.path.get_project? b coh.fieldNodup
  have hk : RowVals.project? (vd.cols.map (·.field))
      (vpick kd.fields vd.cols b) kd.key
      = some { ty := kc.field.ty, val := kc.path.get b } := by
    rw [vpick_project? coh.fieldNodup vd.cols coh.colNodup b
      kd.key hkeyin, hbkey]
  have hmb : kd.matchesKey b ⟨kc.field.ty, kc.path.get b⟩ = true := by
    show (match RowVals.project? kd.fields b kd.key with
      | some v => v.beq ⟨kc.field.ty, kc.path.get b⟩
      | none => false) = true
    simp [hbkey, FieldVal.beq_refl]
  have hfiber : rows.filter
      (fun r => vd.sel.check r && kd.matchesKey r
        ⟨kc.field.ty, kc.path.get b⟩) = [b] := by
    have hlen := kd.filter_matches_le_one ⟨kc.field.ty, kc.path.get b⟩
      vd.sel.check rows huniq
    have hmem : b ∈ rows.filter
        (fun r => vd.sel.check r && kd.matchesKey r
          ⟨kc.field.ty, kc.path.get b⟩) := by
      rw [List.mem_filter]; exact ⟨hb, by simp [hsel, hmb]⟩
    cases hfx : rows.filter
        (fun r => vd.sel.check r && kd.matchesKey r
          ⟨kc.field.ty, kc.path.get b⟩) with
    | nil => rw [hfx] at hmem; exact absurd hmem List.not_mem_nil
    | cons r rest =>
        cases rest with
        | nil =>
            have hbr : b = r := List.mem_singleton.mp (hfx ▸ hmem)
            rw [hbr]
        | cons r1 rest1 =>
            rw [hfx] at hlen
            simp only [List.length_cons] at hlen
            omega
  rw [viewPut_hit kd vd rows (vpick kd.fields vd.cols b)
    ⟨kc.field.ty, kc.path.get b⟩ hk b hfiber, vwrite_vpick,
    applyRowDelta_update_self kd.key rows b ⟨kc.field.ty, kc.path.get b⟩ hbkey
      (fun r' hr' hm => kd.uniqueOn_determines _ rows r' b huniq hr' hb
        (by simp only [KeyDecl.matchesKey, KeyDecl.image?, hm,
          FieldVal.beq_refl])
        hmb)]

/-! ## THE LENS — the view/update pair as the honest carrier -/

/-- THE RELATIONAL LENS (02 §7's view + update policy + laws): the
    view/update pair with the round-trip laws as FIELDS riding their
    honest premises. The put is PARTIAL by design — the ambiguity
    refusals are the honest gap, never a fabricated base row. NOT a
    `Kit.Iso` and not a `Kit.Retraction`: the view cannot express the
    base's complement columns (03 §2), so no round trip is total —
    the grade's honesty IS the partiality. -/
structure ViewLens (kd : KeyDecl) (vd : ViewDef kd.fields) where
  /-- The read: the view rows (the query's face). -/
  get : List (RowVals kd.fields) → List (RowVals vd.vfields)
  /-- The write: the edited view row's verdict — the base delta + the
      post-state, or the named refusal (the policy's face). -/
  put : List (RowVals kd.fields) → RowVals vd.vfields →
    ViewEditVerdict kd.fields
  /-- Read-after-write: an applied edit's view returns the requested
      row (the coherence pack is the fragment's premise — the law's
      honest hypothesis form). -/
  get_put : ∀ (_coh : ViewCoherent kd vd) rows v δ r',
    put rows v = ViewEditVerdict.apply δ r' → v ∈ get r'
  /-- Unchanged-view preservation: the edit that writes back what the
      view read restores the table exactly (the CHECKED uniqueness —
      the determinacy — discharges the singleton-fiber premise). -/
  put_get : ∀ (_coh : ViewCoherent kd vd) rows b,
    kd.uniqueOn rows = true → b ∈ rows → vd.sel.check b = true →
    put rows (vpick kd.fields vd.cols b)
      = ViewEditVerdict.apply [RowDelta.update b] rows

/-- THE KEYED VIEW LENS (the assembled pair over the keyed writeback):
    the read is the view's query, the write is the classifier, and the
    law fields are the theorems above cited — never re-proved. -/
def keyedViewLens (kd : KeyDecl) (vd : ViewDef kd.fields) :
    ViewLens kd vd where
  get := vd.get
  put := viewPut kd vd
  get_put := fun coh rows v δ r' h => viewPut_get kd vd coh rows v δ r' h
  put_get := fun coh rows b huniq hb hsel =>
    viewPut_preserves kd vd coh rows b huniq hb hsel

end SchemaCore
