/-
# SchemaLang.Subschema — the typed-query subschema family (FP-lean §7.3)

Lifted from the book's §7.3 "Typed Queries" (`Subschema` / `Row.project`
/ `addColumn` / `reflexive`), adapted to OUR schema shape: the book's
`Schema = List Column` with `Column = (name, DBType)` becomes OUR
`List Field` with `Field = {name, ty : Ty}` — the same (name, type)
shape, with the closed `Ty` universe in place of `DBType` (nullability
is `.option`, not a flag).

Contents:
- `Subschema : List Field → List Field → Type` — `nil`/`cons`, the
  cons head carrying `HasCol bigger f.name f.ty` (the book's HasCol
  evidence: the field survives with the SAME name AND type — a retype
  is NOT an embedding).
- `RowVals.project` — the projection: a big-schema row → the
  subschema's row. Total (can't-fail) BY TYPE: the extraction rides
  `ColPath` constructor data, there is no failure value to return.
- `addColumn` + `addColumn_sub` (the cons-preserving embedding),
  `reflexive`, `weaken`, `trans` (via `widen`).
- The constructive backward-compat tie: `ofMem?` / `subschemaOfItem?` /
  `subschemaViaDiff?` — the old fields all surviving (name AND type)
  yields `Subschema old new` evidence; `none` = breaking. The proved
  core is `ofMem?_some_of_forall_mem` (membership ⟹ evidence) and
  `ofMem?_none_of_breaking` (a lost field ⟹ `none`); the link to
  `Diff.fieldDiffsOf`'s all-added shape is pinned by EXECUTED tests
  (the `find?`/`contains` reasoning of `fieldDiffsOf` is out of the
  theorem scope v1 — stated honestly, not hand-waved).
- The Vortex dtype tie: `vortexSelect` — the field-mask-shaped
  selection on lowered struct fields.

Ergonomics finding (the book's `by repeat constructor`): over CONCRETE
field lists, `repeat constructor` builds the evidence in one line —
the cons unpacks `HasCol` to a `ColPath` goal and the path constructors
close it against the literal list. `by decide` does NOT apply: the
family is Type-valued DATA (a `ColPath` rides inside — there is
nothing to decide, and no `Decidable` instance is wanted). Pinned by
examples + `#guard_msgs` negative controls in `Tests/Main.lean`.

Ownership: the SUBSCHEMA lane. Additive: no existing declaration
changed. `SchemaLang.Validate` is consumed read-only (`RowVals`,
`ColPath`, `HasCol` — the projection is the consumer the Validate
header predicted). Deliberate exclusions: no `Decidable` instance for
`Subschema` (data, not a decidable-closed Prop); the BATCH-level
Vortex projection is the Rust executor's job (see `vortexSelect`).
-/

import SchemaLang.Diff
import SchemaLang.Validate
import SchemaLang.Vortex.DType

namespace SchemaLang

/-! ## The family -/

/--
`Subschema small big` — evidence that every field of `small` appears
in `big` with the SAME name AND type: `nil` embeds the empty schema
anywhere; `cons` embeds the head field `f` via `HasCol` (whose
`ColPath` is the runtime extraction data) and recurses on the tail.
A retyped field fails the `HasCol` gate — the embedding does not
exist (the type-level reading of `Diff`'s `fieldTypeChanged` being
breaking).
-/
inductive Subschema : List Field → List Field → Type where
  | nil : Subschema [] bigger
  | cons : {f : Field} → {smaller bigger : List Field} →
      HasCol bigger f.name f.ty → Subschema smaller bigger →
      Subschema (f :: smaller) bigger

/-! ## The projection (the typed query) -/

/--
The projection: a row of the BIG schema → the subschema's row.
Total by construction — the `HasCol` evidence's `ColPath` reads the
right slot out of the schema-aligned row, `nil` yields the empty row,
and there is no failure value to return (the book's can't-fail
`Row.project`, over OUR boxed `RowVals`).

Recursion consumes the EVIDENCE with the row held fixed — the big
schema does not shrink, so the recursive call re-projects the same
row against the tail embedding.
-/
def RowVals.project :
    {s' s : List Field} → RowVals s → Subschema s' s → RowVals s'
  | _, _, _, .nil => .nil
  | _, _, row, .cons h rest => .cons (h.path.get row) (row.project rest)

/-! ## The algebra: weaken, addColumn, reflexive, trans -/

/-- Weakening: an embedding survives prepending a field to the BIG
    side (every existing path gains one `there`). This is the general
    shape `addColumn_sub`'s cons arm needs. -/
def Subschema.weaken :
    {smaller bigger : List Field} → Subschema smaller bigger →
    {f : Field} → Subschema smaller (f :: bigger)
  | _, _, .nil, _f => .nil
  | _, _, .cons h rest, _f => .cons ⟨.there h.path⟩ (weaken rest)

/-- The book's `addColumn`: prepend a fresh field (the safe schema
    change). -/
def addColumn (s : List Field) (n : String) (t : Ty) : List Field :=
  { name := n, ty := t } :: s

/-- Reflexivity: every schema embeds in itself. -/
def Subschema.reflexive : (s : List Field) → Subschema s s
  | [] => .nil
  | _f :: fs => .cons ⟨.here⟩ (Subschema.weaken (Subschema.reflexive fs))

/-- Prefixing ANY field list to a schema preserves the embedding:
    `s` embeds into `pre ++ s` (reflexive on the empty prefix, one
    `weaken` per prefix field). -/
def Subschema.prefixEmbed : (pre s : List Field) → Subschema s (pre ++ s)
  | [], s => Subschema.reflexive s
  | g :: pre, s => Subschema.weaken (f := g) (Subschema.prefixEmbed pre s)

/-- `addColumn` is safe BY CONSTRUCTION: the augmented schema is the
    old one with a field-list prefix, and `prefixEmbed` embeds it. -/
def addColumn_sub (s : List Field) (n : String) (t : Ty) :
    Subschema s (addColumn s n t) :=
  Subschema.prefixEmbed [{ name := n, ty := t }] s

/-- Lift a `ColPath` through an embedding: a path into the SMALL
    schema becomes a path into the BIG one (`here` is replaced by the
    head evidence's path; a `there` descends into the tail's
    embedding — the BIG index never grows, so no constructor wraps
    the recursive result). -/
def Subschema.widen :
    {smaller bigger : List Field} → Subschema smaller bigger →
    {n : String} → {t : Ty} → ColPath n t smaller → ColPath n t bigger
  | _, _, .cons h _, _, _, .here => h.path
  | _, _, .cons _ rest, _, _, .there p => widen rest p
  | _, _, .nil, _, _, p => nomatch p

/-- Transitivity: embeddings compose. -/
def Subschema.trans :
    {a b c : List Field} → Subschema a b → Subschema b c → Subschema a c
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h rest, sub => .cons ⟨widen sub h.path⟩ (trans rest sub)

/-! ## The constructive backward-compat tie (the migration direction)

`Diff` reports breaking changes as DATA; this section constructs the
PROOF-shaped counterpart: for one record's field lists, the old fields
either embed in the new list (the `Subschema old new` evidence — the
old schema's every read is still answerable, and `RowVals.project` is
the runner that executes old consumers on new rows) or they do not
(`none` — the change is breaking, with no projection to offer).
-/

/-- The path evidence for a PROVEN field equality: `f = g` lets
    `ColPath.here` see the head field as `f` (eta for structures).
    Type-valued, so a `def` (a `theorem` cannot state it). -/
def Field.colPath_here_of_eq {f g : Field} {fs : List Field}
    (h : f = g) : ColPath f.name f.ty (g :: fs) := by
  subst h
  exact .here

/-- Look up field `f` in `fs`: the `ColPath` iff SOME field of `fs`
    IS `f` (name AND type — `Field`'s `DecidableEq` compares both). -/
def Subschema.findCol? (fs : List Field) (f : Field) :
    Option (ColPath f.name f.ty fs) :=
  match fs with
  | [] => none
  | g :: rest =>
      if h : f = g then some (Field.colPath_here_of_eq h)
      else ColPath.there <$> findCol? rest f

/-- Constructive embedding search: every old field present (name AND
    type) in `newFs` yields the `Subschema oldFs newFs` evidence. -/
def Subschema.ofMem? (newFs : List Field) :
    (oldFs : List Field) → Option (Subschema oldFs newFs)
  | [] => some .nil
  | f :: oldFs =>
      match findCol? newFs f with
      | some p => .cons ⟨p⟩ <$> ofMem? newFs oldFs
      | none => none

/-! ### The proved core -/

theorem Subschema.findCol?_some_of_mem :
    ∀ (fs : List Field) (f : Field), f ∈ fs →
      ∃ p, findCol? fs f = some p := by
  intro fs
  induction fs with
  | nil => intro f h; cases h
  | cons g rest ih =>
      intro f h
      by_cases hfg : f = g
      · exact ⟨Field.colPath_here_of_eq hfg, by
          simp [findCol?, hfg]⟩
      · have hrest : f ∈ rest := (List.mem_cons.mp h).resolve_left hfg
        obtain ⟨p, hp⟩ := ih f hrest
        exact ⟨ColPath.there p, by
          simp [findCol?, hfg, hp]⟩

theorem Subschema.findCol?_none_of_not_mem {fs : List Field} {f : Field}
    (h : f ∉ fs) : findCol? fs f = none := by
  cases fs with
  | nil => rfl
  | cons g rest =>
      have hng : f ≠ g := by
        intro hfg; apply h; rw [hfg]; exact List.Mem.head _
      have hrest : f ∉ rest := fun hm => h (List.Mem.tail g hm)
      simp [findCol?, hng, findCol?_none_of_not_mem hrest]

/-- THE MIGRATION THEOREM (the positive direction): if every old field
    survives into `newFs` (name AND type), the embedding evidence is
    CONSTRUCTED — `none` is impossible. This is what the breaking
    gate's "additions are safe" verdict means proof-shaped. -/
theorem Subschema.ofMem?_some_of_forall_mem :
    ∀ (newFs oldFs : List Field), (∀ f, f ∈ oldFs → f ∈ newFs) →
      ∃ sub, ofMem? newFs oldFs = some sub := by
  intro newFs oldFs
  induction oldFs with
  | nil => intro _; exact ⟨.nil, rfl⟩
  | cons g rest ih =>
      intro h
      obtain ⟨p, hp⟩ := findCol?_some_of_mem newFs g (h g (List.Mem.head _))
      obtain ⟨sub, hsub⟩ := ih fun f hf => h f (List.Mem.tail g hf)
      exact ⟨Subschema.cons ⟨p⟩ sub, by simp [ofMem?, hp, hsub]⟩

/-- THE MIGRATION THEOREM (the negative direction): one old field
    lost (renamed OR retyped) and the search returns `none` — the
    breaking verdict, as a proof. -/
theorem Subschema.ofMem?_none_of_breaking :
    ∀ (newFs : List Field) (f : Field) (oldFs : List Field),
      f ∈ oldFs → f ∉ newFs → ofMem? newFs oldFs = none := by
  intro newFs f oldFs
  induction oldFs with
  | nil => intro hmem _; cases hmem
  | cons g rest ih =>
      intro hmem hnew
      by_cases h_eq : f = g
      · subst h_eq
        simp [ofMem?, findCol?_none_of_not_mem hnew]
      · have hrest : f ∈ rest := (List.mem_cons.mp hmem).resolve_left h_eq
        have hn : ofMem? newFs rest = none := ih hrest hnew
        cases hfind : findCol? newFs g with
        | none => simp [ofMem?, hfind]
        | some p => simp [ofMem?, hfind, hn]

/-! ### The item-level tie (Diff ⟷ Subschema) -/

/-- The item-level embedding search: the old item's fields either
    embed in the new item's fields (the backward-compat certificate —
    `RowVals.project` is the runner that replays old consumers onto
    new rows) or they do not (`none` = breaking). Field-projection
    based, so it applies to records, variants' payload cases, and
    func signatures alike (whatever `Item.fieldsOf` sees). -/
def subschemaOfItem? (prev it : Item) :
    Option (Subschema prev.fieldsOf it.fieldsOf) :=
  Subschema.ofMem? it.fieldsOf prev.fieldsOf

/-- The DIFF-GATED reading: when `Diff.fieldDiffsOf` reports only
    additions, hand back the embedding evidence; anything else
    (a removal, a retype, semantic drift) is `none` — the breaking
    shape. The gate ⟹ evidence direction rests on `fieldDiffsOf`'s
    `find?`/`contains` reasoning and is pinned by EXECUTED tests (the
    `ofMem?` theorems above are the proved core); a `some` result is
    real evidence BY TYPE regardless of the gate. -/
def subschemaViaDiff? (prev it : Item) :
    Option (Subschema prev.fieldsOf it.fieldsOf) :=
  if (fieldDiffsOf prev it).all fun
      | .fieldAdded _ => true
      | _ => false
  then subschemaOfItem? prev it
  else none

/-! ## The Vortex tie (the dtype-level projection) -/

/-- The dtype-side reading of a subschema: the lowered struct fields
    of the BIG schema, picked in the OLD schema's order, one pair per
    subschema field (name-matched). `none` = the lowered list drifted
    from the schema (a subschema name the dtype list lacks).

    This is the field-mask SHAPE of a Vortex projection at the SPEC
    level. The BATCH-level read is the Rust executor's job: the
    emitter's `IntoVortex` builds struct arrays column-wise, so the
    projection is a `StructArray::from_fields` over the selected
    columns — Rust-side, driven by this spec shape. -/
def Subschema.vortexSelect :
    {oldFs newFs : List Field} → Subschema oldFs newFs →
    List (Vortex.FieldName × Vortex.DType) →
    Option (List (Vortex.FieldName × Vortex.DType))
  | _, _, .nil, _ => some []
  | _, _, @Subschema.cons f _ _ _ rest, dfs =>
      match dfs.find? (fun p => p.1 == f.name) with
      | some pair => (pair :: ·) <$> vortexSelect rest dfs
      | none => none

end SchemaLang
