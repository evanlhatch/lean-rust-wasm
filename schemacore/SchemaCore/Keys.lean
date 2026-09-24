/-
# SchemaCore.Keys — the keys lane: declared keys + foreign keys

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/02-data-plane.md §3 (KEYS ARE DETERMINACY
THEOREMS — they drive API shape: a key-backed query is `Option`-shaped,
an ordinary query stays `List`-shaped, and the inference is
CONSERVATIVE: unproven uniqueness yields collection results, never
invented uniqueness); notes/v3/12-construction.md §2 (the lane recipe:
item + mount + the WF legality + the obligation view + tests);
notes/v3/15-patterns.md #1 (relation + executable checker + the proved
bridge, one bridge lemma per rung).

Provenance: mined from
`legacy/lean/schema-lang/SchemaLang/Keys.lean` (W8.2), ported at the
slice's model size (`Item` is records-only, `KeyTy` is the scalar
sub-universe):

- `ForeignKey` / `KeyDecl` — the declaration DATA. THE DRIFT-FREE
  RULE: the foreign key stores only `field` + `target` — the target's
  own key field is never restated; the checker and the obligation lane
  RESOLVE the target's `KeyDecl`, so the pair cannot drift.
- The one-per-rung WF checker cascade — `keyFieldDiags ← foreignTyDiags
  ← foreignDeclDiags ← foreignDiags ← keyRecordDiags ← KeyDecl.check ←
  keyDeclsCheck` — with a BRIDGE LEMMA PER RUNG (`*_eq_nil_iff`), the
  pattern-#1 discipline. The legacy `foreignItemDiags` rung (the
  target-must-be-a-record gate) is UNREPRESENTABLE here: the slice's
  `Item` has no variants — the cascade is one rung shorter by
  construction, not by omission.
- `FieldVal.beq` + ITS LAWFULNESS — the projected-value equality. THE
  HONEST JUDGMENT the mining asked for: the legacy lawfulness
  (`FieldVal.beq_eq_true_iff_eq`) rode the CODEC IMAGE — beq compared
  byte images, so lawfulness needed the round-trip collapse and a
  `CodecClosed` hypothesis on each side (floats sat outside the closed
  fragment). The new tree's `Value.beq` is STRUCTURAL over the value
  family (`SchemaCore.Value`), so the law is UNCONDITIONAL: beq-true ↔
  equal, both directions, no codec, no closure hypothesis — a
  `LawfulBEq FieldVal` instance. Simpler, and the simplification is
  real, not deferred work.
- `uniqueOn` / `referencesOn` — the canonical meanings (the row-set is
  a FUNCTION from key to row; every foreign-key image resolves in the
  target's key images).
- THE DETERMINACY PAYOFF (02 §3): `uniqueOn_determines` — under a
  CHECKED primary key, the rows matching a key image are pairwise
  equal; `lookup?` is the `Option`-shaped key-backed query and
  `lookup?_atMostOne` is its type-shape theorem; `lookupAll` is the
  `List`-shaped conservative surface with NO uniqueness theorem
  attached — the discipline, not an oversight.
- The obligation view — the Prop-INDEXED obligation (Kit.Obligation):
  the claim IS the uniqueness/reference property (the type index), the
  tier computes `decidableNow`, and the pinned claim table is the
  ALL-DEFAULT SINGLETON (`defaultRow?` — the one table materializable
  from the declaration alone; a `bounded 0` field is default-less and
  the discharge is the loud `none`).
- The WF bridge as a `Kit.CheckedProp` (`keysChecked`) — relation +
  checker + proved BOTH directions (the loud completeness choice).

Deliberate exclusions (the leftover rule): composite keys (v1:
single-field keys, the legacy granularity); the ∀-tables universal
closure of uniqueness (undecidable — the table-invariant lane's
universal form); emitter consumption (no emitter reads the key
registry — the byte-tie holds by construction).

The mount rides `Kit.Lane.register_lane` (the lane recipe's steps 1–2
in one kit call): `keysExt` (the append-only compile-time event log),
`@[key]` (the attribute — the legacy `schema_keys` command's mount;
the SINGULAR spelling — the substrate's `get<base>s` convention
appends the plural itself, so the base is `key` and the accessor is
`getKeys`), `keysRegistry` / `keyNameOf` / `keyAttrReg`. The
entries live in `SchemaCore.KeysSlice` (a module's own initializers do
not run during ITS OWN elaboration).

The five questions (notes/v3/01-core.md): root = the keys lane (the
determinacy theorems become first-class data + obligations); carrier =
the GADT-free item model + the registry's nodup-in-type; spine reading
= registration = append → replay = the accessor → the obligation rows
= the lane's output; ladder rung = `decidableNow` (every claim is a
decidable row-data predicate; the WF bridge is the small hand kind);
gate row = SchemaTests' keysSpec + the axiom report + KeysSlice's
build-time teeth.

Core-only (imports Kit.Lane + SchemaCore.Check + SchemaCore.RowVals +
SchemaCore.Snapshot — the cone rule; Check supplies the ONE derived
`DecidableEq Field` instance; Snapshot supplies `keyOfTy`, the ONE
`Ty` → `KeyTy` gate — the parser-side twin is reused, never a parallel
table).
-/

import Kit.Lane
import SchemaCore.Check
import SchemaCore.RowVals
import SchemaCore.Snapshot

open Kit

namespace SchemaCore

/-! ## The declaration data -/

/-- A declared FOREIGN KEY (data): this record's field `field`
    references the record named `target` via the target's DECLARED
    primary key. THE DRIFT-FREE RULE: the target's key field name is
    NOT stored — stored data stays drift-free; the checker and the
    obligation lane resolve the target's own `KeyDecl`. -/
structure ForeignKey where
  field : String
  target : String
deriving Inhabited

/-- A record's declared keys (data): the record's registry name, the
    field-list snapshot (the registry read — a stale snapshot is a
    finding, never a silent re-read), the PRIMARY key field name, and
    the foreign keys. -/
structure KeyDecl where
  record : String
  fields : List Field
  key : String
  foreign : List ForeignKey := []
deriving Inhabited

-- `Field` equality — the cascade's `if fields = kd.fields` gate needs
-- it; the ONE derived instance lives in SchemaCore.Check (the check
-- lane's consumer) and is REUSED here by import — a second deriving
-- would collide on the auto-generated instance name at import time.

/-! ## The projected-value equality — lawfulness, unconditionally

The legacy lane compared projected values through the CODEC IMAGE
(`encodeValue` bytes), so its lawfulness was conditional on
`CodecClosed`. The new tree's `Value.beq` is structural
(`SchemaCore.Value`), so the same theorem is UNCONDITIONAL — and the
comparison surface becomes honest equality data (`LawfulBEq`). -/

/-- Executable equality on projected values: same type index, then
    structural value equality (the GADT's `Value.beq` — the type guard
    matters: values of different `Ty` indices are different values). -/
def FieldVal.beq (a b : FieldVal) : Bool :=
  match a, b with
  | ⟨ta, va⟩, ⟨tb, vb⟩ =>
      if h : ta = tb then Value.beq ta va (h ▸ vb) else false

/-- The refl pin (kernel-checked — the equality is not vacuous). -/
theorem FieldVal.beq_refl (a : FieldVal) : a.beq a = true := by
  obtain ⟨ta, va⟩ := a
  simp only [FieldVal.beq]
  rw [dif_pos trivial]
  exact Value.beq_refl ta va

mutual
/-- THE BEQ-EQUALITY DIRECTION: structural equality is sound — beq-true
    collapses to genuine equality (the legacy codec-image proof's
    replacement: one induction over the sibling family, no round trip,
    no closure hypothesis). -/
theorem Value.beq_eq : ∀ (t : Ty) (a b : Value t), Value.beq t a b = true → a = b
  | .bool, .bool x, .bool y, h => by
      simp only [Value.beq] at h
      exact congrArg _ (beq_iff_eq.mp h)
  | .u64, .u64 x, .u64 y, h => by
      simp only [Value.beq] at h
      exact congrArg _ (beq_iff_eq.mp h)
  | .i64, .i64 x, .i64 y, h => by
      simp only [Value.beq] at h
      exact congrArg _ (beq_iff_eq.mp h)
  | .string, .string x, .string y, h => by
      simp only [Value.beq] at h
      exact congrArg _ (beq_iff_eq.mp h)
  | .option _, .none, .none, _ => rfl
  | .option _, .none, .some _, h => by simp [Value.beq] at h
  | .option _, .some _, .none, h => by simp [Value.beq] at h
  | .option t, .some a, .some b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (Value.beq_eq t a b h)
  | .result _ _, .ok a, .ok b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (Value.beq_eq _ a b h)
  | .result _ _, .ok _, .err _, h => by simp [Value.beq] at h
  | .result _ _, .err _, .ok _, h => by simp [Value.beq] at h
  | .result _ _, .err a, .err b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (Value.beq_eq _ a b h)
  | .list _, .list a, .list b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (VList.beq_eq a b h)
  | .map _ _, .map a, .map b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (VMap.beq_eq a b h)
  | .set _, .set a, .set b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (VList.beq_eq a b h)
  | .bounded _, .bounded a, .bounded b, h => by
      simp only [Value.beq] at h
      exact congrArg _ (Fin.val_inj.mp (beq_iff_eq.mp h))

theorem VList.beq_eq : ∀ {t : Ty} (a b : VList t), VList.beq a b = true → a = b
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _, h => by simp [VList.beq] at h
  | _, .cons _ _, .nil, h => by simp [VList.beq] at h
  | _, .cons a as, .cons b bs, h => by
      simp only [VList.beq, Bool.and_eq_true] at h
      rw [Value.beq_eq _ a b h.1, VList.beq_eq as bs h.2]

theorem VMap.beq_eq : ∀ {k : KeyTy} {v : Ty} (a b : VMap k v),
    VMap.beq a b = true → a = b
  | _, _, .nil, .nil, _ => rfl
  | _, _, .nil, .cons _ _ _, h => by simp [VMap.beq] at h
  | _, _, .cons _ _ _, .nil, h => by simp [VMap.beq] at h
  | _, _, .cons a b as, .cons c d bs, h => by
      simp only [VMap.beq, Bool.and_eq_true] at h
      rw [Value.beq_eq _ a c h.1.1, Value.beq_eq _ b d h.1.2,
        VMap.beq_eq as bs h.2]
end

/-- THE LAWFULNESS: `FieldVal.beq` IS equality — true iff equal, BOTH
    directions, UNCONDITIONALLY (the legacy version needed
    `CodecClosed` on both sides; the structural beq retires the
    hypothesis). This is what makes the key-image distinctness plain
    `≠` data below. -/
theorem FieldVal.beq_eq_true_iff_eq (a b : FieldVal) : a.beq b = true ↔ a = b := by
  obtain ⟨ta, va⟩ := a
  obtain ⟨tb, vb⟩ := b
  by_cases hty : ta = tb
  · subst hty
    simp only [FieldVal.beq]
    rw [dif_pos trivial]
    constructor
    · intro h
      rw [Value.beq_eq ta va vb h]
    · intro h
      cases h  -- ctor injection: the components unify (ty already agrees)
      exact Value.beq_refl ta _
  · simp only [FieldVal.beq]
    rw [dif_neg hty]
    simp [FieldVal.mk.injEq, hty]

/-- The BEq instance (the lanes' comparison surface; the ReflBEq/
    LawfulBEq instances below carry the law in the type). -/
instance : BEq FieldVal := ⟨FieldVal.beq⟩

/-- The refl law (the `ReflBEq` face of the lawful instance). -/
instance : ReflBEq FieldVal := ⟨fun {a} => FieldVal.beq_refl a⟩

/-- The lawful instance: the lanes' comparison surface carries its law
    in the type (beq-true IS equality — no conditional theorems). -/
instance : LawfulBEq FieldVal := ⟨fun {_ _} h => (FieldVal.beq_eq_true_iff_eq _ _).mp h⟩

/-! ## The canonical meanings (what keys MEAN over tables) -/

/-- The key image of one row: `some v` iff the declared-key projection
    resolves (a declaration whose stored fields don't carry its key —
    the refusal reading, never a fabricated image). -/
def KeyDecl.image? (kd : KeyDecl) (row : RowVals kd.fields) : Option FieldVal :=
  RowVals.project? kd.fields row kd.key

/-- The keyed membership test: the row's key image equals `k` (the
    lookup's row predicate — beq, lawfully equality). -/
def KeyDecl.matchesKey (kd : KeyDecl) (row : RowVals kd.fields) (k : FieldVal) : Bool :=
  match kd.image? row with
  | some v => v.beq k
  | none => false

/-- The key images of a table under the declared key; `none` = the
    projection failed on some row. -/
def KeyDecl.keyImages? (kd : KeyDecl) (rows : List (RowVals kd.fields)) :
    Option (List FieldVal) :=
  match rows with
  | [] => some []
  | r :: rest =>
      (kd.image? r).bind (fun v => (kd.keyImages? rest).map (fun vs => v :: vs))

/-- All-distinct under `FieldVal.beq` (the key-image fold). -/
def FieldVal.nodup : List FieldVal → Bool
  | [] => true
  | k :: ks => !ks.any (fun k' => k.beq k') && FieldVal.nodup ks

/-- THE KEY-UNIQUENESS CHECK — what a primary key MEANS (the canonical
    law: the row-set is a FUNCTION from key to row): every row projects
    its declared key and the images are all-distinct. -/
def KeyDecl.uniqueOn (kd : KeyDecl) (rows : List (RowVals kd.fields)) : Bool :=
  match kd.keyImages? rows with
  | some ks => FieldVal.nodup ks
  | none => false

/-- THE REFERENTIAL-INTEGRITY CHECK — what a foreign key MEANS: every
    source row's foreign-key image resolves among the target table's
    key images. (The target's own `KeyDecl` rides the argument — the
    drift-free rule: nothing about the target is restated here.) -/
def KeyDecl.referencesOn (kd : KeyDecl) (fk : ForeignKey) (target : KeyDecl)
    (srcRows : List (RowVals kd.fields))
    (tgtRows : List (RowVals target.fields)) : Bool :=
  match target.keyImages? tgtRows with
  | none => false
  | some tkeys =>
      srcRows.all fun r =>
        match RowVals.project? kd.fields r fk.field with
        | some v => tkeys.any fun tk => v.beq tk
        | none => false

/-! ## THE DETERMINACY PAYOFF (02 §3) — the API-shape derivation

Keys drive API SHAPE: a key-backed query is `Option`-shaped (at most
one row), an ordinary query is `List`-shaped. The theorem is the
determinacy content; the hypothesis is the CHECKED uniqueness — the
inference is conservative, never invented. -/

/-- A matching row's key image IS the queried image (the lawfulness
    doing the work: beq-true is genuine equality). -/
theorem KeyDecl.matchesKey_image (kd : KeyDecl) (row : RowVals kd.fields)
    (k : FieldVal) (h : kd.matchesKey row k = true) :
    kd.image? row = some k := by
  unfold matchesKey at h
  split at h
  · next v hv =>
      rw [hv]
      exact congrArg _ ((FieldVal.beq_eq_true_iff_eq v k).mp h)
  · exact absurd h (by simp)

/-- The image list is aligned with the table: a member's UNWRAPPED key
    image is a member of the image list. -/
theorem KeyDecl.keyImages?_mem (kd : KeyDecl) :
    ∀ (rows : List (RowVals kd.fields)) (r : RowVals kd.fields)
        (w : FieldVal) (ks : List FieldVal),
      r ∈ rows → kd.image? r = some w → kd.keyImages? rows = some ks →
        w ∈ ks := by
  intro rows
  induction rows with
  | nil => intro r w ks hmem _ _; exact absurd hmem (by simp)
  | cons r0 rest ih =>
      intro r w ks hmem hw hks
      rw [keyImages?] at hks
      obtain ⟨v, hv, hks⟩ := Option.bind_eq_some_iff.mp hks
      obtain ⟨vs, hrest, hks⟩ := Option.map_eq_some_iff.mp hks
      subst hks
      rcases List.mem_cons.mp hmem with e | hmem'
      · -- r = r0: the two image readings agree
        rw [e] at hw
        have hvw : w = v := Option.some.inj (hw.symm.trans hv)
        rw [hvw]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih r w vs hmem' hw hrest)

/-- The nodup fold's cons law: the head is beq-distinct from every tail
    element, and the tail is itself nodup. -/
theorem FieldVal.nodup_cons {v : FieldVal} {vs : List FieldVal}
    (h : FieldVal.nodup (v :: vs) = true) :
    FieldVal.nodup vs = true ∧ ∀ v' ∈ vs, v.beq v' = false := by
  rw [nodup, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h2, fun v' hv' => ?_⟩
  cases hbb : v.beq v' with
  | false => rfl
  | true =>
      rw [List.any_eq_true.mpr ⟨v', hv', hbb⟩] at h1
      simp at h1

/-- THE DETERMINACY THEOREM: under a CHECKED primary key, the rows of
    the table matching a key image are PAIRWISE EQUAL — at most one
    row. This is 02 §3's content: `OrderId → the whole row`; the
    Option-shaped lookup below is its API face. The hypothesis is the
    checked `uniqueOn` — the conservative-inference discipline: the
    theorem exists ONLY where uniqueness was proved. -/
theorem KeyDecl.uniqueOn_determines (kd : KeyDecl) (k : FieldVal)
    (rows : List (RowVals kd.fields)) (r1 r2 : RowVals kd.fields)
    (huniq : kd.uniqueOn rows = true) (h1 : r1 ∈ rows) (h2 : r2 ∈ rows)
    (hm1 : kd.matchesKey r1 k = true) (hm2 : kd.matchesKey r2 k = true) :
    r1 = r2 := by
  induction rows with
  | nil => exact absurd h1 (by simp)
  | cons r rest ih =>
      -- the table's images all resolve and are nodup
      obtain ⟨v, vs, hir, hrest, hnup⟩ :
          ∃ v vs, kd.image? r = some v ∧ kd.keyImages? rest = some vs
            ∧ FieldVal.nodup (v :: vs) = true := by
        cases hv : kd.image? r with
        | none => simp [uniqueOn, keyImages?, hv] at huniq
        | some v =>
            cases hrest : kd.keyImages? rest with
            | none => simp [uniqueOn, keyImages?, hv, hrest] at huniq
            | some vs =>
                rw [uniqueOn, keyImages?, hv, hrest] at huniq
                exact ⟨v, vs, rfl, rfl, huniq⟩
      have him1 : kd.image? r1 = some k := kd.matchesKey_image r1 k hm1
      have him2 : kd.image? r2 = some k := kd.matchesKey_image r2 k hm2
      rcases List.mem_cons.mp h1 with e1 | m1
      · subst e1
        rcases List.mem_cons.mp h2 with e2 | m2
        · subst e2
          rfl
        · exfalso
          have hvk : v = k := by rw [hir] at him1; exact Option.some.inj him1
          have hmem : k ∈ vs :=
            kd.keyImages?_mem rest r2 k vs m2 him2 hrest
          obtain ⟨_, hfalse⟩ := FieldVal.nodup_cons hnup
          rw [hvk] at hfalse
          exact absurd (FieldVal.beq_refl k)
            (by rw [hfalse k hmem]; simp)
      · rcases List.mem_cons.mp h2 with e2 | m2
        · exfalso
          subst e2
          have hvk : v = k := by rw [hir] at him2; exact Option.some.inj him2
          have hmem : k ∈ vs :=
            kd.keyImages?_mem rest r1 k vs m1 him1 hrest
          obtain ⟨_, hfalse⟩ := FieldVal.nodup_cons hnup
          rw [hvk] at hfalse
          exact absurd (FieldVal.beq_refl k)
            (by rw [hfalse k hmem]; simp)
        · have huniq' : kd.uniqueOn rest = true := by
            rw [uniqueOn, hrest]
            exact (FieldVal.nodup_cons hnup).1
          exact ih huniq' m1 m2

/-- THE KEY-BACKED QUERY — the Option shape (02 §3): at most one row,
    by the determinacy theorem. -/
def KeyDecl.lookup? (kd : KeyDecl) (rows : List (RowVals kd.fields))
    (k : FieldVal) : Option (RowVals kd.fields) :=
  rows.find? (fun r => kd.matchesKey r k)

/-- THE API-SHAPE THEOREM: the key-backed lookup's result is
    subsingleton — any two rows it can return are equal (the Option
    shape is a THEOREM, not a convention). -/
theorem KeyDecl.lookup?_atMostOne (kd : KeyDecl) (rows : List (RowVals kd.fields))
    (huniq : kd.uniqueOn rows = true) (k : FieldVal)
    {r1 r2 : RowVals kd.fields}
    (h1 : kd.lookup? rows k = some r1) (h2 : kd.lookup? rows k = some r2) :
    r1 = r2 := by
  have hfind1 : List.find? (fun r => kd.matchesKey r k) rows = some r1 := h1
  have hfind2 : List.find? (fun r => kd.matchesKey r k) rows = some r2 := h2
  have m1 := List.find?_some hfind1
  have m2 := List.find?_some hfind2
  have mem1 := List.mem_of_find?_eq_some hfind1
  have mem2 := List.mem_of_find?_eq_some hfind2
  exact kd.uniqueOn_determines k rows r1 r2 huniq mem1 mem2 m1 m2

/-- THE CONSERVATIVE SURFACE: without a CHECKED key the collection
    shape is all the API gets — `lookupAll` is List-shaped, and NO
    theorem converts it to the Option shape without `uniqueOn`. The
    determinacy theorem above takes its hypothesis; nothing here
    invents uniqueness (02 §3's inference discipline). -/
def KeyDecl.lookupAll (kd : KeyDecl) (rows : List (RowVals kd.fields))
    (k : FieldVal) : List (RowVals kd.fields) :=
  rows.filter (fun r => kd.matchesKey r k)

/-- The lookup's contract: a hit is a real member satisfying the keyed
    test (the Option face's spec; the at-most-one law is
    `lookup?_atMostOne`). -/
theorem KeyDecl.lookup?_spec (kd : KeyDecl) (rows : List (RowVals kd.fields))
    (k : FieldVal) (r : RowVals kd.fields)
    (h : kd.lookup? rows k = some r) : r ∈ rows ∧ kd.matchesKey r k = true := by
  have hfind : List.find? (fun r' => kd.matchesKey r' k) rows = some r := h
  have hm := List.find?_some hfind
  have hmem := List.mem_of_find?_eq_some hfind
  exact ⟨hmem, hm⟩

/-! ## The executable WF checker (the diagnostic authority)

One def per rung, one bridge lemma per rung (pattern #1): each
`*_eq_nil_iff` discharges exactly ONE match level. Empty list = well
formed. The cascade: `keyFieldDiags ← foreignTyDiags ← foreignDeclDiags
← foreignDiags ← keyRecordDiags ← KeyDecl.check ← keyDeclsCheck`. The
legacy `foreignItemDiags` rung (target must be a record) is
unrepresentable: `Item` is records-only in this tree. The messages name
their rung (`key:` / `foreign:`) — a broken declaration refuses with
the named rung's diagnostic. -/

/-- The key-field rung: present (first match) + injects from `KeyTy`
    (the scalar discipline — `keyOfTy`, the ONE `Ty` → `KeyTy` gate). -/
def keyFieldDiags (rec : String) (fields : List Field) (key : String) :
    List String :=
  match fields.find? (fun f => f.name == key) with
  | none =>
      [s!"key: record `{rec}` has no field `{key}` to key on\
        {Kit.suggestSuffix key (fields.map (·.name))}"]
  | some f =>
      if (keyOfTy f.ty).isSome then []
      else [s!"key: field `{f.name}` does not inject from the scalar key \
          universe — valid: bool, u64, i64, string"]

/-- The type-agreement rung: the target's key field resolves on the
    target's fields and its Ty IS the foreign-key field's Ty. -/
def foreignTyDiags (rec : String) (fk : ForeignKey) (ff : Field)
    (tfields : List Field) (tkd : KeyDecl) : List String :=
  match tfields.find? (fun f => f.name == tkd.key) with
  | none =>
      [s!"foreign: the target's key field `{tkd.key}` is not on record \
        `{fk.target}` — `{rec}.{fk.field}` references `{fk.target}`"]
  | some tf =>
      if tf.ty = ff.ty then []
      else [s!"foreign: type mismatch — `{rec}.{fk.field}` carries \
          {toString (repr ff.ty)}, the target key `{fk.target}.{tkd.key}` \
          carries {toString (repr tf.ty)}"]

/-- The target-declaration rung: the target has a DECLARED key (the
    forward-reference rule — declare the target's keys first). -/
def foreignDeclDiags (decls : List KeyDecl) (rec : String) (fk : ForeignKey)
    (ff : Field) (tfields : List Field) : List String :=
  match decls.find? (fun d => d.record == fk.target) with
  | none =>
      [s!"foreign: the target record `{fk.target}` has no declared key — \
        declare the target's key first (the forward-reference rule)"]
  | some tkd => foreignTyDiags rec fk ff tfields tkd

/-- One foreign key against the universe + the declaration set: the
    field is on the record, the target resolves in the universe (the
    target-is-a-record gate needs no rung — `Item` is records-only),
    then the declaration cascade. -/
def foreignDiags (items : List Item) (decls : List KeyDecl) (rec : String)
    (fields : List Field) (fk : ForeignKey) : List String :=
  match fields.find? (fun f => f.name == fk.field) with
  | none =>
      [s!"foreign: record `{rec}` has no field `{fk.field}` for the \
        foreign key{Kit.suggestSuffix fk.field (fields.map (·.name))}"]
  | some ff =>
      match items.find? (fun it => it.name == fk.target) with
      | none =>
          [s!"foreign: the target record `{fk.target}` is not in the \
            universe{Kit.suggestSuffix fk.target (items.map (·.name))}"]
      | some it => foreignDeclDiags decls rec fk ff it.fields

/-- The foreign-key list walk (the cascade's table arm — a plain
    recursion, the bridge reads it directly). -/
def foreignDiagsAll (items : List Item) (decls : List KeyDecl) (rec : String)
    (fields : List Field) : List ForeignKey → List String
  | [] => []
  | fk :: fks =>
      foreignDiags items decls rec fields fk
        ++ foreignDiagsAll items decls rec fields fks

/-- The resolved-record rung: the stored field list must BE the
    record's (a stale snapshot is a finding, not a silent re-read);
    only then do the key-field and foreign-key gates run. -/
def keyRecordDiags (items : List Item) (decls : List KeyDecl) (kd : KeyDecl)
    (fields : List Field) : List String :=
  if fields = kd.fields then
    keyFieldDiags kd.record fields kd.key
      ++ foreignDiagsAll items decls kd.record fields kd.foreign
  else
    [s!"key: the stored field snapshot is stale — `{kd.record}`'s fields \
      drifted from the universe's"]

/-- One declaration against the universe + the declaration set: the
    record name must RESOLVE, then the resolved-record rung. -/
def KeyDecl.check (items : List Item) (decls : List KeyDecl) (kd : KeyDecl) :
    List String :=
  match items.find? (fun it => it.name == kd.record) with
  | none =>
      [s!"key: record `{kd.record}` is not in the universe\
        {Kit.suggestSuffix kd.record (items.map (·.name))}"]
  | some it => keyRecordDiags items decls kd it.fields

/-- The duplicated-record scan (one declaration per record): every
    element with a LATER duplicate, plus the downstream duplicates —
    structural recursion (a `filter`-based spell would need wf on the
    filtered tail; this fold is plain structural).
    `dupNames ns = [] ↔ ns.Nodup` is the bridge below. -/
def dupNames : List String → List String
  | [] => []
  | n :: ns =>
      if ns.contains n then n :: dupNames ns else dupNames ns

/-- The declaration-set check: ALL per-declaration diagnostics + the
    dup scan. Empty list = well formed. The `@[key]` mount's teeth and
    the tests run this SAME checker — one authority, two mount points. -/
def keyDeclsCheck (items : List Item) (decls : List KeyDecl) : List String :=
  decls.flatMap (KeyDecl.check items decls)
    ++ (dupNames (decls.map (fun kd => kd.record))).map
      (fun n => s!"key: duplicate key declaration for record `{n}`")

/-- The Bool projection (derived from the diagnostic authority — one
    authority, two readings). -/
def keyDeclsWellFormed (items : List Item) (decls : List KeyDecl) : Bool :=
  (keyDeclsCheck items decls).isEmpty

/-! ## The reasoning authority (the Prop side, rung by rung) -/

/-- The key-field gate as a Prop (the `keyFieldDiags` mirror). -/
def KeyFieldOk (fields : List Field) (key : String) : Prop :=
  ∃ f, fields.find? (fun f => f.name == key) = some f
    ∧ (keyOfTy f.ty).isSome = true

/-- One foreign key as a Prop (the `foreignDiags` mirror, cascade arm
    by arm — the target-is-a-record conjunct is gone: unrepresentable). -/
def ForeignOk (items : List Item) (decls : List KeyDecl) (fields : List Field)
    (fk : ForeignKey) : Prop :=
  ∃ (ff : Field) (it : Item) (tkd : KeyDecl) (tf : Field),
    fields.find? (fun f => f.name == fk.field) = some ff
    ∧ items.find? (fun x => x.name == fk.target) = some it
    ∧ it.name = fk.target
    ∧ decls.find? (fun d => d.record == fk.target) = some tkd
    ∧ it.fields.find? (fun f => f.name == tkd.key) = some tf
    ∧ tf.ty = ff.ty

/-- One declaration as a Prop (the `KeyDecl.check` mirror). -/
def KeyDeclOk (items : List Item) (decls : List KeyDecl) (kd : KeyDecl) : Prop :=
  ∃ fields : List Field,
    items.find? (fun it => it.name == kd.record) = some ⟨kd.record, fields⟩
    ∧ fields = kd.fields
    ∧ KeyFieldOk fields kd.key
    ∧ ∀ fk, fk ∈ kd.foreign → ForeignOk items decls fields fk

/-- THE REASONING AUTHORITY for declared keys: every declaration checks
    against the universe + the declaration set, and declared records
    are unique. -/
def KeysWellFormed (items : List Item) (decls : List KeyDecl) : Prop :=
  (∀ kd, kd ∈ decls → KeyDeclOk items decls kd)
    ∧ (decls.map (fun kd => kd.record)).Nodup

/-! ## The bridge, rung by rung -/

theorem keyFieldDiags_eq_nil_iff {rec : String} {fields : List Field}
    {key : String} :
    keyFieldDiags rec fields key = [] ↔ KeyFieldOk fields key := by
  unfold keyFieldDiags KeyFieldOk
  cases hx : fields.find? (fun f => f.name == key) with
  | none => simp
  | some f =>
      by_cases hs : (keyOfTy f.ty).isSome = true
      · exact ⟨fun _ => ⟨f, rfl, hs⟩, fun _ => by simp [hs]⟩
      · simp [hs]

theorem foreignTyDiags_eq_nil_iff {rec : String} {fk : ForeignKey}
    {ff : Field} {tfields : List Field} {tkd : KeyDecl} :
    foreignTyDiags rec fk ff tfields tkd = [] ↔
      ∃ tf : Field, tfields.find? (fun f => f.name == tkd.key) = some tf
        ∧ tf.ty = ff.ty := by
  unfold foreignTyDiags
  cases hx : tfields.find? (fun f => f.name == tkd.key) with
  | none => simp
  | some tf =>
      by_cases hty : tf.ty = ff.ty
      · exact ⟨fun _ => ⟨tf, rfl, hty⟩, fun _ => by simp [hty]⟩
      · simp [hty]

theorem foreignDeclDiags_eq_nil_iff {decls : List KeyDecl} {rec : String}
    {fk : ForeignKey} {ff : Field} {tfields : List Field} :
    foreignDeclDiags decls rec fk ff tfields = [] ↔
      ∃ (tkd : KeyDecl) (tf : Field),
        decls.find? (fun d => d.record == fk.target) = some tkd
        ∧ tfields.find? (fun f => f.name == tkd.key) = some tf
        ∧ tf.ty = ff.ty := by
  unfold foreignDeclDiags
  cases hd : decls.find? (fun d => d.record == fk.target) with
  | none => simp
  | some tkd =>
      rw [foreignTyDiags_eq_nil_iff]
      constructor
      · rintro ⟨tf, h2, h3⟩; exact ⟨tkd, tf, rfl, h2, h3⟩
      · rintro ⟨tkd', tf, h1, h2, h3⟩
        rw [← Option.some.inj h1] at h2
        exact ⟨tf, h2, h3⟩

theorem foreignDiags_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {rec : String} {fields : List Field} {fk : ForeignKey} :
    foreignDiags items decls rec fields fk = [] ↔
      ForeignOk items decls fields fk := by
  unfold foreignDiags ForeignOk
  cases hff : fields.find? (fun f => f.name == fk.field) with
  | none => simp
  | some ff =>
      cases ht : items.find? (fun x => x.name == fk.target) with
      | none => simp
      | some it =>
          have hs := List.find?_some ht
          have hname : it.name = fk.target := beq_iff_eq.mp hs
          rw [foreignDeclDiags_eq_nil_iff]
          constructor
          · rintro ⟨tkd, tf, hC, hD, hE⟩
            exact ⟨ff, it, tkd, tf, rfl, rfl, hname, hC, hD, hE⟩
          · rintro ⟨ff', it', tkd, tf, hA, hB, hN, hC, hD, hE⟩
            cases hA
            cases hB
            exact ⟨tkd, tf, hC, hD, hE⟩

theorem foreignDiagsAll_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {rec : String} {fields : List Field} :
    ∀ (fks : List ForeignKey),
      foreignDiagsAll items decls rec fields fks = [] ↔
        ∀ fk, fk ∈ fks → ForeignOk items decls fields fk := by
  intro fks
  induction fks with
  | nil => simp [foreignDiagsAll]
  | cons fk fks ih =>
      rw [foreignDiagsAll, List.append_eq_nil_iff, ih,
        foreignDiags_eq_nil_iff]
      constructor
      · rintro ⟨h1, h2⟩ fk' hmem'
        rcases List.mem_cons.mp hmem' with e | hmem2
        · subst e; exact h1
        · exact h2 fk' hmem2
      · intro h
        exact ⟨h fk List.mem_cons_self,
          fun fk' hmem' => h fk' (List.mem_cons_of_mem _ hmem')⟩

theorem keyRecordDiags_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {kd : KeyDecl} {fields : List Field} :
    keyRecordDiags items decls kd fields = [] ↔
      fields = kd.fields ∧ KeyFieldOk fields kd.key
        ∧ ∀ fk, fk ∈ kd.foreign → ForeignOk items decls fields fk := by
  unfold keyRecordDiags
  by_cases hfs : fields = kd.fields
  · subst hfs
    rw [if_pos rfl, List.append_eq_nil_iff, keyFieldDiags_eq_nil_iff,
      foreignDiagsAll_eq_nil_iff]
    exact ⟨fun h => ⟨rfl, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  · rw [if_neg hfs]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hfs⟩

theorem keyDeclCheck_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {kd : KeyDecl} :
    KeyDecl.check items decls kd = [] ↔ KeyDeclOk items decls kd := by
  unfold KeyDecl.check KeyDeclOk
  cases h : items.find? (fun it => it.name == kd.record) with
  | none => simp
  | some it =>
      cases it with
      | mk n fs =>
          have hs := List.find?_some h
          have hrn : n = kd.record := beq_iff_eq.mp hs
          simp only [hrn]
          rw [keyRecordDiags_eq_nil_iff]
          constructor
          · rintro ⟨h1, hkey, hfk⟩
            exact ⟨fs, rfl, h1, hkey, hfk⟩
          · rintro ⟨fields, hA, hB, hC, hD⟩
            cases hA
            exact ⟨hB, hC, hD⟩

theorem dupNames_eq_nil_iff {ns : List String} :
    dupNames ns = [] ↔ ns.Nodup := by
  induction ns with
  | nil => simp [dupNames]
  | cons n ns ih =>
      by_cases hc : ns.contains n = true
      · rw [dupNames, if_pos hc]
        have hmem : n ∈ ns := List.contains_iff_mem.mp hc
        simp [List.nodup_cons, hmem]
      · rw [dupNames, if_neg hc, ih]
        exact ⟨fun h => List.nodup_cons.mpr
            ⟨fun hmem => hc (List.contains_iff_mem.mpr hmem), h⟩,
          fun h => (List.nodup_cons.mp h).2⟩

theorem flatMap_nil_iff {α β : Type} (f : α → List β) :
    ∀ (l : List α), l.flatMap f = [] ↔ ∀ a, a ∈ l → f a = [] := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.append_eq_nil_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ a' hmem'
        rcases List.mem_cons.mp hmem' with e | hmem2
        · subst e; exact h1
        · exact h2 a' hmem2
      · intro h
        exact ⟨h a List.mem_cons_self,
          fun a' hmem' => h a' (List.mem_cons_of_mem _ hmem')⟩

/-- MASTER BRIDGE: the executable authority and the relation agree
    (pattern #1 — the checker never lies in either direction). -/
theorem keyDeclsCheck_eq_nil_iff {items : List Item} {decls : List KeyDecl} :
    keyDeclsCheck items decls = [] ↔ KeysWellFormed items decls := by
  unfold keyDeclsCheck KeysWellFormed
  rw [List.append_eq_nil_iff, flatMap_nil_iff, List.map_eq_nil_iff,
    dupNames_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun kd hkd => keyDeclCheck_eq_nil_iff.mp (h1 kd hkd), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun kd hkd => keyDeclCheck_eq_nil_iff.mpr (h1 kd hkd), h2⟩

/-- The bridge, sound direction: a clean checker run transports INTO
    the relation. -/
theorem keyDeclsCheck_sound {items : List Item} {decls : List KeyDecl} :
    keyDeclsCheck items decls = [] → KeysWellFormed items decls :=
  keyDeclsCheck_eq_nil_iff.mp

/-- The bridge, complete direction: the relation certifies a clean
    checker run. -/
theorem keyDeclsCheck_complete {items : List Item} {decls : List KeyDecl} :
    KeysWellFormed items decls → keyDeclsCheck items decls = [] :=
  keyDeclsCheck_eq_nil_iff.mpr

/-- The gate reading (`isEmpty` projection) composed with the bridge. -/
theorem keyDeclsWellFormed_iff {items : List Item} {decls : List KeyDecl} :
    keyDeclsWellFormed items decls = true ↔ KeysWellFormed items decls := by
  rw [keyDeclsWellFormed, List.isEmpty_iff, keyDeclsCheck_eq_nil_iff]

/-- The keys lane as the canon's `Kit.CheckedProp` (pattern #1's
    assembly): relation + checker + PROVED both directions — a
    one-directional gate would declare `.missing`, loudly. -/
def keysChecked : Kit.CheckedProp (List Item × List KeyDecl) :=
  Kit.CheckedProp.ofComplete
    (fun p => KeysWellFormed p.1 p.2)
    (fun p => keyDeclsWellFormed p.1 p.2)
    (fun _ h => keyDeclsCheck_sound (List.isEmpty_iff.mp h))
    (fun _ h => List.isEmpty_iff.mpr (keyDeclsCheck_complete h))

/-! ## The obligation view (what a key declaration MEANS, as data)

The substrate is the Prop-INDEXED `Kit.Obligation`: the claim IS the
type index — a discharge proves the ACTUAL uniqueness/reference
property, never a claim-shaped name (15-patterns #4 at the indexed
strength). The tier computes `decidableNow`: over a PROVIDED
materialized table the claim is a closed decide; the discipline's
pinned table is the ALL-DEFAULT SINGLETON (`defaultRow?` — the one
table materializable from the declaration alone). Enforcement is NOT
hand-wired here — the update language is the first consumer. -/

/-- The default value of the boundary universe — total EXCEPT the empty
    bounded (`Fin 0` is empty): the Option is the honest shape (the
    legacy `defaultRow?` discipline). -/
def defaultVal? : (t : Ty) → Option (Value t)
  | .bool => some (.bool false)
  | .u64 => some (.u64 0)
  | .i64 => some (.i64 0)
  | .string => some (.string "")
  | .option _ => some .none
  | .list _ => some (.list .nil)
  | .result ok _ => (Value.ok ·) <$> defaultVal? ok
  | .map _ _ => some (.map .nil)
  | .set _ => some (.set .nil)
  | .bounded cap => if h : 0 < cap then some (.bounded ⟨0, h⟩) else none

/-- The all-default row for a field list (the default-singleton table's
    row; `none` = some field is default-less — the loud gap). -/
def defaultRow? : (fs : List Field) → Option (RowVals fs)
  | [] => some .nil
  | f :: fs =>
      match defaultVal? f.ty with
      | none => none
      | some v => (defaultRow? fs).map (fun r => RowVals.cons v r)

/-- The ALL-DEFAULT SINGLETON table (the one table the obligation's
    decide discharge sees from the declaration alone — the invariant
    lane's default-row discipline lifted from row to table). -/
def KeyDecl.defaultTable? (kd : KeyDecl) : Option (List (RowVals kd.fields)) :=
  (defaultRow? kd.fields).map (fun row => [row])

/-- The fact a key declaration records: the record's row-set is a
    FUNCTION from key to row (`unique` — key-uniqueness), or every
    foreign-key image resolves in the target's row-set (`references` —
    referential integrity; the target declaration rides the payload so
    the claim needs no re-resolution). -/
inductive KeyClaim where
  | unique (kd : KeyDecl)
  | references (kd : KeyDecl) (fk : ForeignKey) (target : KeyDecl)

/-- The primary-key obligation row: THE CLAIM IS THE TYPE INDEX
    (`kd.uniqueOn rows = true`) — a discharge of this row can never
    prove a different proposition than the table it was built for. -/
def KeyDecl.uniqueObligation (kd : KeyDecl) (rows : List (RowVals kd.fields)) :
    Obligation KeyClaim (kd.uniqueOn rows = true) :=
  { label := s!"keys/{kd.record}/unique({kd.key})"
    tier := .decidableNow
    payload := .unique kd
    provenance := `SchemaCore }

/-- The foreign-key obligation row: the claim index is the
    referential-integrity property over the two provided tables. -/
def KeyDecl.referencesObligation (kd : KeyDecl) (fk : ForeignKey)
    (target : KeyDecl) (srcRows : List (RowVals kd.fields))
    (tgtRows : List (RowVals target.fields)) :
    Obligation KeyClaim (kd.referencesOn fk target srcRows tgtRows = true) :=
  { label := s!"keys/{kd.record}/{fk.field}-references-{fk.target}({target.key})"
    tier := .decidableNow
    payload := .references kd fk target
    provenance := `SchemaCore }

/-- THE DISCHARGE — the kit's decidableNow backend, never a hand-rolled
    trio: the claim discharged is the obligation's OWN index. `none` is
    the loud gap (a false claim or a mis-set tier; the backend refuses,
    it does not fabricate evidence). -/
def KeyDecl.dischargeUniqueOn (kd : KeyDecl) (rows : List (RowVals kd.fields)) :
    Option Evidence :=
  (kd.uniqueObligation rows).decideDischarge

/-- The discharge's SOUNDNESS — a citation of the kit backend's
    theorem (never a re-proof), at the indexed strength. -/
theorem KeyDecl.dischargeUniqueOn_sound (kd : KeyDecl)
    (rows : List (RowVals kd.fields))
    (h : kd.dischargeUniqueOn rows = some (.decided true)) :
    kd.uniqueOn rows = true :=
  Obligation.decideDischarge_sound (kd.uniqueObligation rows) rfl h

/-- The discharge's COMPLETENESS — a true claim fires the backend. -/
theorem KeyDecl.dischargeUniqueOn_complete (kd : KeyDecl)
    (rows : List (RowVals kd.fields)) (hc : kd.uniqueOn rows = true) :
    kd.dischargeUniqueOn rows = some (.decided true) :=
  Obligation.decideDischarge_of_claim (kd.uniqueObligation rows) rfl hc

/-- The foreign-key discharge (the kit backend, at the references
    claim's index). -/
def KeyDecl.dischargeReferencesOn (kd : KeyDecl) (fk : ForeignKey)
    (target : KeyDecl) (srcRows : List (RowVals kd.fields))
    (tgtRows : List (RowVals target.fields)) : Option Evidence :=
  (kd.referencesObligation fk target srcRows tgtRows).decideDischarge

theorem KeyDecl.dischargeReferencesOn_sound (kd : KeyDecl) (fk : ForeignKey)
    (target : KeyDecl) (srcRows : List (RowVals kd.fields))
    (tgtRows : List (RowVals target.fields))
    (h : kd.dischargeReferencesOn fk target srcRows tgtRows
      = some (.decided true)) :
    kd.referencesOn fk target srcRows tgtRows = true :=
  Obligation.decideDischarge_sound
    (kd.referencesObligation fk target srcRows tgtRows) rfl h

theorem KeyDecl.dischargeReferencesOn_complete (kd : KeyDecl) (fk : ForeignKey)
    (target : KeyDecl) (srcRows : List (RowVals kd.fields))
    (tgtRows : List (RowVals target.fields))
    (hc : kd.referencesOn fk target srcRows tgtRows = true) :
    kd.dischargeReferencesOn fk target srcRows tgtRows = some (.decided true) :=
  Obligation.decideDischarge_of_claim
    (kd.referencesObligation fk target srcRows tgtRows) rfl hc

/-- The obligation view of one declaration over its default-singleton
    table: the primary obligation (always present) + one referential
    obligation per foreign key whose TARGET declaration resolves (a
    well-formed declaration set always resolves — the checker's
    forward-reference arm). The Σ-wrapper is the heterogeneous-claims
    face (the collection over rows with different claim indices); the
    INDIVIDUAL rows are the Prop-indexed obligations above. -/
def KeyDecl.defaultObligations (decls : List KeyDecl) (kd : KeyDecl) :
    List (Σ _ : KeyClaim, Prop) :=
  match kd.defaultTable? with
  | none => []
  | some table =>
      ⟨.unique kd, kd.uniqueOn table = true⟩ ::
        kd.foreign.filterMap fun fk =>
          (decls.find? (fun d => d.record == fk.target)).bind fun t =>
            t.defaultTable?.map fun tgtTable =>
              ⟨.references kd fk t,
                kd.referencesOn fk t table tgtTable = true⟩

/-! ## The mount — `@[key]`, by `Kit.Lane.register_lane` -/

/- The keys lane's registration (the lane recipe's steps 1-2 in one
    kit call; the legacy `schema_keys` command's content at the
    substrate's attribute spelling). Generates: `keysExt` (the
    append-only compile-time event log), `@[key]` (the attribute
    mount — the entry is a `def` of the item type, evaluated at
    elaboration), `getKeys` (the replay accessor), `keysRegistry` (the
    fold hook), `keyNameOf` (the registry's lookup key — the RECORD
    name: one declaration per record, the dup scan's type-level face).
    The entries live in `SchemaCore.KeysSlice` (initializers run at
    import). -/
register_lane KeyDecl where
  attr := key
  naming := fun kd => kd.record

end SchemaCore
