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

/-- One compatibility finding between two universe versions. -/
inductive Change where
  | removed (name : String)            -- was referenceable, is gone: BREAKING
  | added (name : String)              -- new item: safe
  | changed (name : String)            -- same name, different shape: BREAKING
deriving Repr, BEq, Inhabited

instance : ToString Change where
  toString
    | .removed n => s!"removed {n}"
    | .added n => s!"added {n}"
    | .changed n => s!"changed {n}"

/-- Compare two universes by item name and shape. Order of findings:
    removals, changes, additions (registry order within each). -/
def diff (old new : List Item) : List Change :=
  let oldNames := old.map Item.name
  let newNames := new.map Item.name
  let removed := old.filter (fun it => !newNames.contains it.name)
                   |>.map (fun it => Change.removed it.name)
  let added := new.filter (fun it => !oldNames.contains it.name)
                  |>.map (fun it => Change.added it.name)
  let changed := new.filter (fun it =>
    oldNames.contains it.name &&
    match old.find? (fun o => o.name == it.name) with
    | some prev => !(prev == it)   -- BEq: shape-level inequality
    | none => false)
    |>.map (fun it => Change.changed it.name)
  removed ++ changed ++ added

/-- True iff `new` is backward-compatible with `old` (nothing removed,
    nothing reshaped). Additions are safe. -/
def backwardCompatible (old new : List Item) : Bool :=
  let d := diff old new
  d.all fun c => match c with | .added _ => true | _ => false

end SchemaLang
