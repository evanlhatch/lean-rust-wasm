/-
# SchemaLang.Keys — declared keys + foreign keys (W8.2)

The canon row: **a table of entities = a `@[schema]` record + declared
keys** (canon Part 3). This module is the TARGET-NEUTRAL core: the
declaration DATA, the well-formedness lane (relation + checker +
bridge, the `Wf.lean`/CheckedProp doctrine), the obligation view (what
a key declaration MEANS, as data), and the one "which key?" answer
(`Item.keyOfWith`).

The metadata rides its OWN registry (`SchemaLang.Meta.Keys` — the
`invariantItemExt` precedent): `Item` is the closed boundary universe
and carries no key metadata, so the emitters' `List Item` fold is
untouched and the byte-tie holds BY CONSTRUCTION (no emitter, no
`GenCtx` field, no Demo change reads this module's data).

- `ForeignKey` / `KeyDecl` — the declaration data. The primary key's
  Ty must inject from `KeyTy` (the W8.1 scalar discipline) — enforced
  at elaboration by `schema_keys`, checked for hand-built data by
  `KeyDecl.check` (the `Item.check` two-level pattern).
- `keyDeclsCheck` / `KeysWellFormed` / `keyDeclsCheck_eq_nil_iff` —
  the Wf lane's keys sibling: the diagnostic authority, the reasoning
  authority, and the proved bridge, packed as `keysChecked` (the
  canon's CheckedProp row, `.proved` completeness — a one-directional
  gate would declare `.missing`, loudly).
- `KeyDecl.obligations` / `KeyObligation.discharge` — the OBLIGATION
  view (SchemaLang.Obligation's substrate): a key declaration produces
  a key-uniqueness obligation (the row-set is a FUNCTION from key to
  row) and one referential-integrity obligation per foreign key, tier
  computed (`decidableNow` — the claims are decidable row-data
  predicates over the pinned all-default singleton table, the
  invariant lane's default-row discipline). Enforcement is NOT
  hand-wired here — W8.3's update language is the first consumer.
- `Item.keyOfWith` — the declared key WINS; `Item.keyOf`'s first-field
  convention is the default for undeclared records.
  `keyOfWith_eq_keyOf_of_decl_head` is the migration equivalence: a
  declaration naming the FIRST field reproduces the convention
  bit-for-bit (the ledger/Demo shape).

Ownership: the keys lane (this module + Meta.Keys). Deliberate
exclusions: emitter consumption (byte-tie — no emitter reads keys
yet); composite keys (v1: single-field keys, the `Item.keyOf`
convention's granularity); the ∀-tables universal closure of
uniqueness (undecidable — W8.7's table-level-invariant lane owns the
universal form; the pinned claim here is the lane's decidable
projection, exactly the invariant lane's default-row reading).
-/

module

public import SchemaLang.Wf
public import SchemaLang.Validate
public import SchemaLang.CodecValue
public import CodegenCore

@[expose] public section

namespace SchemaLang

/-! ## The declaration data -/

/-- A declared FOREIGN KEY (data): this record's field `field`
    references the record named `target` via the target's DECLARED
    primary key. The target's key field name is NOT stored — stored
    data stays drift-free; the checker and the obligation lane resolve
    the target's own `KeyDecl`. -/
structure ForeignKey where
  field : String
  target : String
deriving Repr, BEq, DecidableEq, Inhabited

/-- A record's declared keys (data): the PRIMARY key field name, the
    record's field-list snapshot (the registry read — the
    `SchemaInvariant.fields` precedent: the obligation lane's row
    claims are typed by it), and the foreign keys. -/
structure KeyDecl where
  record : String
  fields : List Field
  key : String
  foreign : List ForeignKey := []
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The one "which key?" answer -/

/-- The DECLARED key wins: a record with a `KeyDecl` keys by its
    declared key field; the first-field convention (`Item.keyOf`,
    Item.lean) is the DEFAULT for undeclared records. The
    event-sourcing lane (Meta.EventSourced) reads through this — a
    declared key, when present, WINS; the convention stays the
    default. -/
def Item.keyOfWith (decls : List KeyDecl) : Item → Option Field
  | .record n fields =>
      match decls.find? (·.record == n) with
      | some kd => fields.find? (·.name == kd.key)
      | none => fields.head?
  | _ => none

/-- No declarations: the declared-key reading IS the convention. -/
theorem Item.keyOfWith_eq_keyOf (it : Item) :
    Item.keyOfWith [] it = Item.keyOf it := by
  cases it with
  | record n fields => rfl
  | variant n cases => rfl
  | func s => rfl
  | resource n => rfl

/-- Declared = conventional when the declaration names the FIRST field
    (the ledger/Demo shape): migrating such a record to a declared key
    changes NO key-dependent behavior. -/
theorem Item.keyOfWith_eq_keyOf_of_decl_head {decls : List KeyDecl} {kd : KeyDecl}
    {n : String} {f : Field} {rest : List Field}
    (hfind : decls.find? (·.record == n) = some kd) (hkey : kd.key = f.name) :
    Item.keyOfWith decls (.record n (f :: rest)) =
      Item.keyOf (.record n (f :: rest)) := by
  have hb : (f.name == kd.key) = true := by rw [hkey]; exact beq_self_eq_true _
  show (match decls.find? (fun x => x.record == n) with
      | some d => (f :: rest).find? (fun x => x.name == d.key)
      | none => (f :: rest).head?) = (f :: rest).head?
  rw [hfind]
  show (f :: rest).find? (fun x => x.name == kd.key) = (f :: rest).head?
  have hfind2 : (f :: rest).find? (fun x => x.name == kd.key) = some f := by
    rw [List.find?_cons]
    simp [hb]
  rw [hfind2, List.head?_cons]

/-! ## The row projection + the table checks (what keys MEAN) -/

/-- A projected field value: the type index + the payload — the
    DATA-level twin of the typed `ColPath.get` (registry rows are
    data; the existential is what a name-keyed walk returns). -/
abbrev FieldVal := Σ t, Value t

/-- The name-keyed field projection over a schema-aligned row (FIRST
    match wins — the same first-match reading the WF lane pins). -/
def RowVals.project? : (fs : List Field) → RowVals fs → (n : String) →
    Option FieldVal
  | [], .nil, _ => none
  | f :: _, .cons v vs, n =>
      if f.name == n then some ⟨f.ty, v⟩ else RowVals.project? _ vs n

/-- Executable equality on projected values: same type index, then
    byte equality of the codec image (the `Gen.valueEq` route — the
    GADT has no `DecidableEq`; the codec's byte equality is total and
    reflexive). The TYPE guard matters: byte images collide across
    types (a `bool` and a `u8` share the one-byte shape). -/
def FieldVal.beq (a b : FieldVal) : Bool :=
  if h : a.1 = b.1 then encodeValue a.1 a.2 == encodeValue a.1 (h ▸ b.2)
  else false

/-- The refl pin, kernel-checked (the equality is not vacuous). -/
theorem FieldVal.beq_refl (a : FieldVal) : a.beq a = true := by
  simp [FieldVal.beq]

/-- All-distinct under `FieldVal.beq`. -/
def FieldVal.nodup : List FieldVal → Bool
  | [] => true
  | k :: ks => !ks.any (fun k' => k.beq k') && FieldVal.nodup ks

/-- The key images of a table under the declared key; `none` = the
    projection failed on some row (a declaration whose stored fields
    don't carry its key — the refusal reading, the `guardCastApply`
    discipline: a mismatch refuses rather than misreads). -/
def KeyDecl.keyImages? (kd : KeyDecl) (rows : List (RowVals kd.fields)) :
    Option (List FieldVal) :=
  rows.mapM fun r => RowVals.project? kd.fields r kd.key

/-- THE KEY-UNIQUENESS CHECK — what a primary key MEANS (the canonical
    law: the row-set is a FUNCTION from key to row): every row
    projects its declared key and the images are all-distinct. -/
def KeyDecl.uniqueOn (kd : KeyDecl) (rows : List (RowVals kd.fields)) : Bool :=
  match kd.keyImages? rows with
  | some ks => FieldVal.nodup ks
  | none => false

/-- THE REFERENTIAL-INTEGRITY CHECK — what a foreign key MEANS: every
    source row's foreign-key image resolves among the target table's
    key images. -/
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

/-! ## The executable checker (the diagnostic authority)

`KeyDecl.check` / `keyDeclsCheck` are the `Item.check`/`universeCheck`
of the keys lane: STRUCTURED diagnostics (`SchemaDiag`'s W8.2 ctors),
empty list = well formed. The `schema_keys` command runs this SAME
checker as its elaboration gate — one authority, two mount points.

The cascade is one def per rung (`foreignTyDiags` ← `foreignDeclDiags`
← `foreignItemDiags` ← `foreignDiags`; `keyRecordDiags` ←
`KeyDecl.check`) — the Wf.lean piecewise style: each bridge lemma
below discharges exactly ONE match level. -/

/-- The key-field gate: present (first match) + injects from `KeyTy`. -/
def keyFieldDiags (rec : String) (fields : List Field) (key : String) :
    List SchemaDiag :=
  match fields.find? (·.name == key) with
  | none => [.keyFieldMissing rec key
      (CodegenCore.didYouMean key (fields.map (·.name)))]
  | some f =>
      if (Ty.toKeyTy? f.ty).isSome then []
      else [.keyNotScalar rec f.name (reprStr f.ty)]

/-- The type-agreement rung: the target's key field resolves on the
    target and its Ty IS the foreign-key field's Ty. -/
def foreignTyDiags (rec : String) (fk : ForeignKey) (ff : Field)
    (tfields : List Field) (tkd : KeyDecl) : List SchemaDiag :=
  match tfields.find? (·.name == tkd.key) with
  | none => [.foreignTargetKeyless rec fk.field fk.target]
  | some tf =>
      if tf.ty = ff.ty then []
      else [.foreignTypeMismatch rec fk.field fk.target
          (reprStr ff.ty) (reprStr tf.ty)]

/-- The target-declaration rung: the target has a DECLARED key (the
    forward-reference rule — declare the target's keys first). -/
def foreignDeclDiags (decls : List KeyDecl) (rec : String) (fk : ForeignKey)
    (ff : Field) (tfields : List Field) : List SchemaDiag :=
  match decls.find? (·.record == fk.target) with
  | none => [.foreignTargetKeyless rec fk.field fk.target]
  | some tkd => foreignTyDiags rec fk ff tfields tkd

/-- The target-record rung: the target IS a record in the universe
    (variants/funcs/resources cannot be foreign-key targets). The
    caller's `find?` already ties the record's name to `fk.target`
    (the `hname` hypothesis the bridge carries). -/
def foreignItemDiags (decls : List KeyDecl) (rec : String) (fk : ForeignKey)
    (ff : Field) (it : Item) : List SchemaDiag :=
  match it with
  | .record _ tfields => foreignDeclDiags decls rec fk ff tfields
  | _ => [.foreignTargetNotRecord rec fk.field fk.target]

/-- One foreign key against the universe + the declaration set: the
    field is on the record, then the target cascade. -/
def foreignDiags (items : List Item) (decls : List KeyDecl) (rec : String)
    (fields : List Field) (fk : ForeignKey) : List SchemaDiag :=
  match fields.find? (·.name == fk.field) with
  | none => [.foreignFieldMissing rec fk.field
      (CodegenCore.didYouMean fk.field (fields.map (·.name)))]
  | some ff =>
      match items.find? (fun it => it.name == fk.target) with
      | none => [.foreignTargetMissing rec fk.field fk.target
          (CodegenCore.didYouMean fk.target (Item.typeNames items))]
      | some it => foreignItemDiags decls rec fk ff it

/-- The resolved-record rung: the stored field list must BE the
    record's (a stale snapshot is a finding, not a silent re-read);
    only then do the key-field and foreign-key gates run (against the
    RECORD's fields — the authority). -/
def keyRecordDiags (items : List Item) (decls : List KeyDecl) (kd : KeyDecl)
    (fields : List Field) : List SchemaDiag :=
  if fields = kd.fields then
    keyFieldDiags kd.record fields kd.key
      ++ kd.foreign.flatMap (foreignDiags items decls kd.record fields)
  else [.keyFieldsMismatch kd.record]

/-- One declaration against the universe + the declaration set: the
    record name must RESOLVE to an `Item.record`, then the
    resolved-record rung. -/
def KeyDecl.check (items : List Item) (decls : List KeyDecl) (kd : KeyDecl) :
    List SchemaDiag :=
  match items.find? (fun it => it.name == kd.record) with
  | some it =>
      match it with
      | .record _ fields => keyRecordDiags items decls kd fields
      | _ => [.keyRecordNotRecord kd.record]
  | none => [.keyRecordMissing kd.record
      (CodegenCore.didYouMean kd.record (Item.typeNames items))]

/-- The declaration-set check: ALL per-declaration diagnostics + the
    dup scan (one declaration per record). Empty list = well formed. -/
def keyDeclsCheck (items : List Item) (decls : List KeyDecl) : List SchemaDiag :=
  let ns := decls.map (·.record)
  let dupDiags :=
    (ns.filter (fun n => ns.countP (· == n) > 1)).eraseDups.map SchemaDiag.dupKeyDecl
  decls.flatMap (KeyDecl.check items decls) ++ dupDiags

/-- The Bool projection (derived from the diagnostic authority — one
    authority, two readings). -/
def keyDeclsWellFormed (items : List Item) (decls : List KeyDecl) : Bool :=
  (keyDeclsCheck items decls).isEmpty

/-! ## The reasoning authority (the Wf lane's keys sibling) -/

/-- The key-field gate as a Prop (the `keyFieldDiags` mirror): the
    FIRST field named `key` exists and its Ty injects from `KeyTy`. -/
def KeyFieldOk (fields : List Field) (key : String) : Prop :=
  ∃ f, fields.find? (·.name == key) = some f
    ∧ (Ty.toKeyTy? f.ty).isSome = true

/-- One foreign key as a Prop (the `foreignDiags` mirror, cascade
    arm by arm). -/
def ForeignOk (items : List Item) (decls : List KeyDecl) (fields : List Field)
    (fk : ForeignKey) : Prop :=
  ∃ (ff : Field) (tfields : List Field) (tkd : KeyDecl) (tf : Field),
    fields.find? (·.name == fk.field) = some ff
    ∧ items.find? (fun it => it.name == fk.target)
        = some (.record fk.target tfields)
    ∧ decls.find? (·.record == fk.target) = some tkd
    ∧ tfields.find? (·.name == tkd.key) = some tf
    ∧ tf.ty = ff.ty

/-- One declaration as a Prop (the `KeyDecl.check` mirror). -/
def KeyDeclOk (items : List Item) (decls : List KeyDecl) (kd : KeyDecl) : Prop :=
  ∃ fields : List Field,
    items.find? (fun it => it.name == kd.record)
      = some (.record kd.record fields)
    ∧ fields = kd.fields
    ∧ KeyFieldOk fields kd.key
    ∧ ∀ fk, fk ∈ kd.foreign → ForeignOk items decls fields fk

/-- THE REASONING AUTHORITY for declared keys (the `WellFormed`
    sibling): every declaration checks against the universe + the
    declaration set, and declared records are unique. -/
def KeysWellFormed (items : List Item) (decls : List KeyDecl) : Prop :=
  (∀ kd, kd ∈ decls → KeyDeclOk items decls kd)
    ∧ (decls.map (·.record)).Nodup

/-! ## The bridge, rung by rung -/

theorem keyFieldDiags_eq_nil_iff {rec : String} {fields : List Field}
    {key : String} :
    keyFieldDiags rec fields key = [] ↔ KeyFieldOk fields key := by
  unfold keyFieldDiags KeyFieldOk
  generalize hf : fields.find? (·.name == key) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨f, h1, _⟩ := hok; cases h1⟩
  | some f =>
      show (if (Ty.toKeyTy? f.ty).isSome = true then []
          else [SchemaDiag.keyNotScalar rec f.name (reprStr f.ty)]) = [] ↔ _
      by_cases hs : (Ty.toKeyTy? f.ty).isSome = true
      · rw [if_pos hs]
        exact ⟨fun _ => ⟨f, rfl, hs⟩, fun _ => rfl⟩
      · rw [if_neg hs]
        refine ⟨fun hc => absurd hc (List.cons_ne_nil _ _), fun hok => ?_⟩
        obtain ⟨f', h1, hs'⟩ := hok
        cases h1
        exact absurd hs' hs

theorem foreignTyDiags_eq_nil_iff {rec : String} {fk : ForeignKey}
    {ff : Field} {tfields : List Field} {tkd : KeyDecl} :
    foreignTyDiags rec fk ff tfields tkd = [] ↔
      ∃ tf : Field, tfields.find? (·.name == tkd.key) = some tf
        ∧ tf.ty = ff.ty := by
  unfold foreignTyDiags
  generalize hk : tfields.find? (·.name == tkd.key) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨tf, h1, _⟩ := hok; cases h1⟩
  | some tf =>
      show (if tf.ty = ff.ty then []
          else [SchemaDiag.foreignTypeMismatch rec fk.field fk.target
            (reprStr ff.ty) (reprStr tf.ty)]) = [] ↔ _
      by_cases hty : tf.ty = ff.ty
      · rw [if_pos hty]
        exact ⟨fun _ => ⟨tf, rfl, hty⟩, fun _ => rfl⟩
      · rw [if_neg hty]
        refine ⟨fun hc => absurd hc (List.cons_ne_nil _ _), fun hok => ?_⟩
        obtain ⟨tf', h1, hty'⟩ := hok
        cases h1
        exact absurd hty' hty

theorem foreignDeclDiags_eq_nil_iff {decls : List KeyDecl} {rec : String}
    {fk : ForeignKey} {ff : Field} {tfields : List Field} :
    foreignDeclDiags decls rec fk ff tfields = [] ↔
      ∃ (tkd : KeyDecl) (tf : Field),
        decls.find? (·.record == fk.target) = some tkd
        ∧ tfields.find? (·.name == tkd.key) = some tf
        ∧ tf.ty = ff.ty := by
  unfold foreignDeclDiags
  generalize hd : decls.find? (·.record == fk.target) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨tkd, tf, h1, _⟩ := hok; cases h1⟩
  | some tkd =>
      rw [foreignTyDiags_eq_nil_iff]
      constructor
      · intro h
        obtain ⟨tf, h2, h3⟩ := h
        exact ⟨tkd, tf, rfl, h2, h3⟩
      · intro hok
        obtain ⟨tkd', tf, h1, h2, h3⟩ := hok
        cases h1
        exact ⟨tf, h2, h3⟩

theorem foreignItemDiags_eq_nil_iff {decls : List KeyDecl} {rec : String}
    {fk : ForeignKey} {ff : Field} {it : Item} (hname : it.name = fk.target) :
    foreignItemDiags decls rec fk ff it = [] ↔
      ∃ (tfields : List Field) (tkd : KeyDecl) (tf : Field),
        it = .record fk.target tfields
        ∧ decls.find? (·.record == fk.target) = some tkd
        ∧ tfields.find? (·.name == tkd.key) = some tf
        ∧ tf.ty = ff.ty := by
  cases it with
  | record tn tfields =>
      have htn : tn = fk.target := hname
      subst htn
      show foreignDeclDiags decls rec fk ff tfields = [] ↔ _
      rw [foreignDeclDiags_eq_nil_iff]
      constructor
      · intro h
        obtain ⟨tkd, tf, hC, hD, hE⟩ := h
        exact ⟨tfields, tkd, tf, rfl, hC, hD, hE⟩
      · intro hok
        obtain ⟨tfields', tkd, tf, hit, hC, hD, hE⟩ := hok
        cases hit
        exact ⟨tkd, tf, hC, hD, hE⟩
  | variant cn cs =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨tfields, tkd, tf, hit, _⟩ := hok; cases hit⟩
  | func s =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨tfields, tkd, tf, hit, _⟩ := hok; cases hit⟩
  | resource rn =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨tfields, tkd, tf, hit, _⟩ := hok; cases hit⟩

theorem foreignDiags_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {rec : String} {fields : List Field} {fk : ForeignKey} :
    foreignDiags items decls rec fields fk = [] ↔
      ForeignOk items decls fields fk := by
  unfold foreignDiags ForeignOk
  generalize hff : fields.find? (·.name == fk.field) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by
          obtain ⟨ff, tfields, tkd, tf, h1, _⟩ := hok
          cases h1⟩
  | some ff =>
      generalize ht : items.find? (fun it => it.name == fk.target) = y
      cases y with
      | none =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by
              obtain ⟨ff', tfields, tkd, tf, h1, h2, _⟩ := hok
              cases h2⟩
      | some it =>
          have h2 := List.find?_some ht
          have hname : it.name = fk.target := beq_iff_eq.mp h2
          rw [foreignItemDiags_eq_nil_iff hname]
          constructor
          · intro h
            obtain ⟨tfields, tkd, tf, hit, hC, hD, hE⟩ := h
            exact ⟨ff, tfields, tkd, tf, rfl, by rw [hit], hC, hD, hE⟩
          · intro hok
            obtain ⟨ff', tfields, tkd, tf, hA, hB, hC, hD, hE⟩ := hok
            cases hA
            cases hB
            exact ⟨tfields, tkd, tf, rfl, hC, hD, hE⟩

/-- The resolved-record rung's mirror. -/
theorem keyRecordDiags_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {kd : KeyDecl} {fields : List Field} :
    keyRecordDiags items decls kd fields = [] ↔
      fields = kd.fields ∧ KeyFieldOk fields kd.key
        ∧ ∀ fk, fk ∈ kd.foreign → ForeignOk items decls fields fk := by
  unfold keyRecordDiags
  by_cases hfs : fields = kd.fields
  · subst hfs
    rw [if_pos rfl, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
      keyFieldDiags_eq_nil_iff]
    exact ⟨fun h => ⟨rfl, h.1, fun fk hfk =>
        foreignDiags_eq_nil_iff.mp (h.2 fk hfk)⟩,
      fun h => ⟨h.2.1, fun fk hfk =>
        foreignDiags_eq_nil_iff.mpr (h.2.2 fk hfk)⟩⟩
  · rw [if_neg hfs]
    exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
      fun hok => absurd hok.1 hfs⟩

/-- The per-declaration mirror. -/
theorem keyDeclCheck_eq_nil_iff {items : List Item} {decls : List KeyDecl}
    {kd : KeyDecl} :
    KeyDecl.check items decls kd = [] ↔ KeyDeclOk items decls kd := by
  unfold KeyDecl.check KeyDeclOk
  generalize h : items.find? (fun it => it.name == kd.record) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
  | some it =>
      cases it with
      | record rn fields =>
          have h2 := List.find?_some h
          have hrn : rn = kd.record := beq_iff_eq.mp h2
          subst hrn
          show keyRecordDiags items decls kd fields = [] ↔ _
          rw [keyRecordDiags_eq_nil_iff]
          constructor
          · intro hdk
            exact ⟨fields, rfl, hdk.1, hdk.2.1, hdk.2.2⟩
          · intro hok
            obtain ⟨w, h1, h2', hkey, hfk⟩ := hok
            cases h1
            exact ⟨h2', hkey, hfk⟩
      | variant cn cs =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
      | func s =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
      | resource rn =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩

/-- The dup-diagnostic arm in Prop form (the `Wf.dupDiags_eq_nil_iff`
    shape at the `dupKeyDecl` ctor). -/
theorem keyDupDiags_eq_nil_iff {ns : List String} :
    ((ns.filter fun n => ns.countP (· == n) > 1).eraseDups.map
        SchemaDiag.dupKeyDecl = []) ↔ ns.Nodup := by
  rw [List.map_eq_nil_iff, eraseDups_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    refine nodup_iff_countP_le_one.mpr fun n hn => Nat.not_lt.mp fun hgt => h n hn ?_
    exact decide_eq_true hgt
  · intro hnd n hn hp
    have hgt : ns.countP (· == n) > 1 := of_decide_eq_true hp
    have hle := nodup_iff_countP_le_one.mp hnd n hn
    omega

/-- Master bridge: the executable authority and the relation agree. -/
theorem keyDeclsCheck_eq_nil_iff {items : List Item} {decls : List KeyDecl} :
    keyDeclsCheck items decls = [] ↔ KeysWellFormed items decls := by
  have hUC : keyDeclsCheck items decls =
      decls.flatMap (KeyDecl.check items decls)
        ++ ((decls.map (·.record)).filter
              fun n => (decls.map (·.record)).countP (· == n) > 1).eraseDups.map
            SchemaDiag.dupKeyDecl := rfl
  rw [hUC, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    keyDupDiags_eq_nil_iff]
  constructor
  · intro h
    exact ⟨fun kd hkd => keyDeclCheck_eq_nil_iff.mp (h.1 kd hkd), h.2⟩
  · intro h
    exact ⟨fun kd hkd => keyDeclCheck_eq_nil_iff.mpr (h.1 kd hkd), h.2⟩

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

/-- The gate reading (`isEmpty` projection) composed with the bridge —
    the `universeWellFormed_iff` shape. -/
theorem keyDeclsWellFormed_iff {items : List Item} {decls : List KeyDecl} :
    keyDeclsWellFormed items decls = true ↔ KeysWellFormed items decls := by
  have hbr := keyDeclsCheck_eq_nil_iff (items := items) (decls := decls)
  cases hc : keyDeclsCheck items decls with
  | nil =>
      exact ⟨fun _ => hbr.mp hc, fun _ => by simp [keyDeclsWellFormed, hc]⟩
  | cons d ds =>
      exact ⟨fun h => by simp [keyDeclsWellFormed, hc] at h, fun hwf => by
        have hnil := hbr.mpr hwf
        rw [hc] at hnil
        exact absurd hnil (List.cons_ne_nil d ds)⟩

/-- The keys lane as the canon's `CheckedProp` (the W6.11/Error.lean
    pattern): relation + checker + PROVED both directions — a
    one-directional gate would declare `.missing`, loudly. -/
def keysChecked : CodegenCore.CheckedProp (List Item × List KeyDecl) :=
  CodegenCore.CheckedProp.ofComplete
    (fun (items, decls) => KeysWellFormed items decls)
    (fun (items, decls) => keyDeclsWellFormed items decls)
    (fun _ h => keyDeclsCheck_sound (List.isEmpty_iff.mp h))
    (fun _ h => List.isEmpty_iff.mpr (keyDeclsCheck_complete h))

/-! ## The obligation view (what a key declaration MEANS, as data)

The substrate is `SchemaLang.Obligation`'s (the kit's `Obligation`
instantiated at the lane's payload): a key declaration PRODUCES
obligations; backends discharge them. Enforcement is not hand-wired
here — the view + the computed tier + the decidableNow backend are
the deliverable; W8.3's update language is the first consumer. -/

/-- The fact a key declaration records: the record's row-set is a
    FUNCTION from key to row (`unique` — key-uniqueness, the
    table-level invariant), or every foreign-key image resolves in the
    target's row-set (`references` — referential integrity; the target
    declaration rides the payload so the claim needs no re-resolution). -/
inductive KeyClaim where
  | unique (decl : KeyDecl)
  | references (decl : KeyDecl) (fk : ForeignKey) (target : KeyDecl)
deriving Repr, Inhabited

/-- The schema-level key obligation: the kit's shape at the key
    declaration row (`abbrev` — reducible, the kit discipline). -/
abbrev KeyObligation := CodegenCore.Obligation KeyClaim

/-- The computed tier: key claims are decidable row-data predicates —
    the `decidableNow` rung (the doctrine ladder's decide backend).
    No citation lane (uniqueness is the DECLARATION's content — no
    user theorem to cite) and no generated-check lane yet (the
    byte-tie: no emitter reads the key registry). -/
def KeyClaim.tierOf : KeyClaim → CodegenCore.Obligation.Tier :=
  fun _ => .decidableNow

/-- The obligation VIEW of one declaration (additive — the declaration
    and the emitters are untouched; the byte-tie holds). One primary
    obligation per declaration + one referential obligation per
    foreign key whose TARGET declaration resolves (a well-formed
    declaration set always resolves — the checker's
    `foreignTargetKeyless` arm). -/
def KeyDecl.obligations (decls : List KeyDecl) (kd : KeyDecl) :
    List KeyObligation :=
  { label := s!"{kd.record}.key-unique({kd.key})"
  , tier := KeyClaim.tierOf (.unique kd)
  , payload := .unique kd
  , provenance := kd.record.toName }
    :: kd.foreign.filterMap fun fk =>
        (decls.find? (·.record == fk.target)).map fun t =>
          { label := s!"{kd.record}.{fk.field}-references-{fk.target}({t.key})"
          , tier := KeyClaim.tierOf (.references kd fk t)
          , payload := .references kd fk t
          , provenance := kd.record.toName }

/-- All key obligations of a declaration set (the enumeration the
    tests pin). -/
def keyObligations (decls : List KeyDecl) : List KeyObligation :=
  decls.flatMap (KeyDecl.obligations decls)

/-- The decidableNow CLAIM at the key lane: the pinned table is the
    ALL-DEFAULT SINGLETON (the invariant lane's default-row
    discipline, lifted from row to table — the one table the lane can
    materialize from the declaration alone, so the decide discharge
    and any future emitted replay decide the SAME fact). The claim
    exercises the WIRING end-to-end (key projection + all-distinct /
    membership over the pinned tables); a declaration whose projection
    fails (a missing key field — hand-built, non-WF data) or whose
    record has no literal-default row decides FALSE / has no claim and
    the backend REFUSES. A ∀-tables closure is NOT the claim
    (undecidable; W8.7 owns the universal form). -/
def KeyObligation.decidableClaim (o : KeyObligation) : Prop :=
  match o.payload with
  | .unique kd =>
      match SchemaLang.defaultRow? kd.fields with
      | some row => kd.uniqueOn [row] = true
      | none => False
  | .references kd fk t =>
      match SchemaLang.defaultRow? kd.fields,
          SchemaLang.defaultRow? t.fields with
      | some srow, some trow => kd.referencesOn fk t [srow] [trow] = true
      | _, _ => False

/-- The claim IS decidable: valued default rows reduce it to a `Bool`
    equation (`uniqueOn`/`referencesOn` compute); a default-less
    record is `False`. (Named explicitly — the anonymous instance
    auto-name `instDecidableDecidableClaim` collides with
    Obligation.lean's invariant-lane instance.) -/
instance keyClaimDecidable (o : KeyObligation) : Decidable o.decidableClaim := by
  unfold KeyObligation.decidableClaim
  split
  · split <;> infer_instance
  · split <;> infer_instance

/-- THE DISCHARGE. Only the `decidableNow` rung is a key-lane
    assignment (`KeyClaim.tierOf`); the kernel's `decide` over
    `decidableClaim` is the evidence. `none` = the loud gap: a
    hand-set tier the lane cannot serve, a FALSE decide verdict (a
    broken declaration, a type-mismatched foreign key), a default-less
    record — discharge refuses, it does not fabricate evidence. -/
def KeyObligation.discharge (o : KeyObligation) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .decidableNow =>
      match decide o.decidableClaim with
      | true => some (.decided true)
      | false => none
  | .provedAtElab | .generatedCheck | .oracleSwept | .guestVerified => none

/-- SOUNDNESS of the key lane's decidableNow backend: a
    `.decided true` verdict means the claim HOLDS (the kernel's
    `decide` validated the key predicate on the pinned table —
    `of_decide_eq_true`; no new trust base). -/
theorem KeyObligation.discharge_decidableNow_sound (o : KeyObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim := by
  unfold KeyObligation.discharge at h
  rw [ht] at h
  cases hd : decide o.decidableClaim with
  | true => exact of_decide_eq_true hd
  | false =>
      rw [hd] at h
      simp at h

/-- COMPLETENESS: a true claim discharges to the `.decided true`
    evidence — the backend FIRES on the claims it can decide. -/
theorem KeyObligation.discharge_decidableNow_of_claim (o : KeyObligation)
    (ht : o.tier = .decidableNow) (h : o.decidableClaim) :
    o.discharge = some (.decided true) := by
  unfold KeyObligation.discharge
  rw [ht, decide_eq_true h]

end SchemaLang
