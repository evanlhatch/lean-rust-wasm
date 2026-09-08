/-
# SchemaLang.Emit.Rust — the Rust target

Fold `Item`s to the rich Rust domain crate. Records → structs, variants
→ enums; func signatures are NOT emitted here (they are the WIT world's
exports — the component-host glue consumes the WIT in Phase 5).

Lowering (target-neutral universe → Rust):
- scalars 1:1 (`bool`, `u8`…`u64`, `i8`…`i64`, `f32`, `f64`)
- `string` → `String`, `bytes` → `Vec<u8>`
- `option`/`result`/`list` → `Option`/`Result`/`Vec` (1:1)
- `future`/`stream` unreachable in field position (wellFormed bans —
  the flatland audit doctrine: the emitter may assume checked input)
- `.ty n` → `Pascal n`

Derives are a parameter (v1: Clone/Debug/PartialEq/Eq; fast-observe,
bon, serde land with the faults/tabular packages). Names pre-mangled via
`Emit.pascal`/`rustIdent` — the AST never case-converts.
-/

import CodegenCore
import SchemaLang.Item

namespace SchemaLang.Emit.Rust

open CodegenCore.Emit (pascal rustIdent)

/-- The base derives stamped on every generated type. Eq is added
    conditionally — f32/f64 don't implement Eq. -/
def baseDerives : List String := ["Clone", "Debug", "PartialEq"]

/-- Check whether a Ty's Rust lowering contains a float type. -/
def hasFloat : Ty → Bool
  | .f32 | .f64 => true
  | .option a => hasFloat a
  | .result ok err => hasFloat ok || hasFloat err
  | .list a => hasFloat a
  | .future a => hasFloat a
  | .stream a => hasFloat a
  | _ => false

/-- Lower a `Ty` to Rust type text. `future`/`stream` cannot reach this
    in field position (wellFormed bans them); if a func-signature
    emitter reuses this, the future unwraps at `async`. -/
def tyRust : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "String"
  | .bytes => "Vec<u8>"
  | .option a => s!"Option<{tyRust a}>"
  | .result ok err => s!"Result<{tyRust ok}, {tyRust err}>"
  | .list a => s!"Vec<{tyRust a}>"
  | .future a | .stream a => tyRust a
  | .ty n => pascal n

/-- A record → `struct` item. -/
def recordItem (derives : List String) : Item → CodegenCore.Emit.Rust.Item
  | .record n fields =>
      .struct (pascal n) derives
        (fields.map fun f => { name := rustIdent f.name, ty := tyRust f.ty })
  | _ => .comment "recordItem: not a record"

/-- A variant → `enum` item (payload cases carry their type). -/
def variantItem (derives : List String) : Item → CodegenCore.Emit.Rust.Item
  | .variant n cases =>
      .enum (pascal n) derives
        (cases.map fun (c, payload) =>
          match payload with
          | some t => s!"{pascal c}({tyRust t})"
          | none => pascal c)
  | _ => .comment "variantItem: not a variant"

/-- A full universe → the Rust module items (types only; funcs are the
    WIT world's exports, not Rust-side types). Eq is added per-record
    only when no field contains a float. -/
def schemaItems (derives : List String) (items : List Item) :
    List CodegenCore.Emit.Rust.Item :=
  items.filterMap fun it =>
    match it with
    | .record _ fields =>
        let eqOk := !(fields.any (fun f => hasFloat f.ty))
        let ds := if eqOk then derives ++ ["Eq"] else derives
        some (recordItem ds it)
    | .variant _ cases =>
        let eqOk := !(cases.any fun (_, payload) =>
          match payload with
          | some t => hasFloat t
          | none => false)
        let ds := if eqOk then derives ++ ["Eq"] else derives
        some (variantItem ds it)
    | _ => none

end SchemaLang.Emit.Rust

/-- The Rust emitter plugin: rich domain types. -/
def rustEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "rust"
  style := .doubleSlash
  specSource := "SchemaLang/Spec/Demo.lean"
  outputs := ["../../src/schema_generated.rs"]
  run items := [
    { path := "../../src/schema_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule (SchemaLang.Emit.Rust.schemaItems SchemaLang.Emit.Rust.baseDerives items) }
  ]
