/-
# SchemaLang.Diff — schema compatibility (the `breaking` engine)

The buf-breaking analog, proof-aware: common names are compared with
`EqAns`-backed equality; removals and payload changes are the breaking
surface. v1 reports the change LIST (removed / added / changed); the
proof-carrying migration evidence (`.yes h` reuse for upcast functions)
lands with schema-indexed.
-/

import SchemaLang.Item

namespace SchemaLang

/-! ## Field-level compat evidence (EqAns-based: WHICH fields moved) -/

/-- One field-level finding between two same-name items. The evidence
    a migration tool needs: not just "user changed" but which field was
    added, removed, or retyped (old type and new type, both carried). -/
inductive FieldDiff where
  | fieldAdded (name : String)
  | fieldRemoved (name : String)
  | fieldTypeChanged (name : String) (oldTy newTy : Ty)
deriving Repr, BEq, Inhabited

instance : ToString FieldDiff where
  toString
    | .fieldAdded n => s!"added field {n}"
    | .fieldRemoved n => s!"removed field {n}"
    | .fieldTypeChanged n oldTy newTy =>
        s!"field {n}: {toString (repr oldTy)} → {toString (repr newTy)}"

/-- The fields of an item, name+type pairs (the EqAns comparison surface).
    Records: fields as-is. Variants: payload-carrying cases (payloadless
    cases contribute no field — arity drift still trips `changed`).
    Funcs: params, plus the return type under the reserved name `"(ret)"`.
    Resources: none. -/
def Item.fieldsOf : Item → List Field
  | .record _ fields => fields
  | .variant _ cases => cases.filterMap fun (c, payload) =>
      match payload with | some t => some ⟨c, t⟩ | none => none
  | .func s => s.params.map (fun (n, t) => ⟨n, t⟩) ++ [⟨"(ret)", s.ret⟩]
  | .resource _ => []

/-- Field-level evidence between two same-name items, old-field order
    first (removals, then type changes), then additions in new order. -/
def fieldDiffsOf (prev it : Item) : List FieldDiff :=
  let oldFs := prev.fieldsOf
  let newFs := it.fieldsOf
  let oldNames := oldFs.map (·.name)
  let newNames := newFs.map (·.name)
  let removed := oldFs.filterMap fun f =>
    if newNames.contains f.name then none else some (.fieldRemoved f.name)
  let changed := oldFs.filterMap fun f =>
    match newFs.find? (fun g => g.name == f.name) with
    | some g => if g.ty == f.ty then none else some (.fieldTypeChanged f.name f.ty g.ty)
    | none => none
  let added := newFs.filterMap fun f =>
    if oldNames.contains f.name then none else some (.fieldAdded f.name)
  removed ++ changed ++ added

/-- One compatibility finding between two universe versions. -/
inductive Change where
  | removed (name : String)            -- was referenceable, is gone: BREAKING
  | added (name : String)              -- new item: safe
  | changed (name : String) (fieldDiffs : List FieldDiff)  -- same name, different shape: BREAKING, with field evidence
deriving Repr, BEq, Inhabited

instance : ToString Change where
  toString
    | .removed n => s!"removed {n}"
    | .added n => s!"added {n}"
    | .changed n fds => s!"changed {n} ({String.intercalate "; " (fds.map toString)})"

/-- Compare two universes by item name and shape. Order of findings:
    removals, changes, additions (registry order within each). -/
def diff (old new : List Item) : List Change :=
  let oldNames := old.map Item.name
  let newNames := new.map Item.name
  let removed := old.filter (fun it => !newNames.contains it.name)
                   |>.map (fun it => Change.removed it.name)
  let added := new.filter (fun it => !oldNames.contains it.name)
                  |>.map (fun it => Change.added it.name)
  let changed := new.filterMap fun it =>
    match old.find? (fun o => o.name == it.name) with
    | some prev =>
        -- BEq (EqAns-backed shape inequality) triggers; FieldDiffs are the evidence
        if prev == it then none else some (.changed it.name (fieldDiffsOf prev it))
    | none => none
  removed ++ changed ++ added

/-- True iff `new` is backward-compatible with `old` (nothing removed,
    nothing reshaped). Additions are safe. -/
def backwardCompatible (old new : List Item) : Bool :=
  let d := diff old new
  d.all fun c => match c with | .added _ => true | _ => false

end SchemaLang
