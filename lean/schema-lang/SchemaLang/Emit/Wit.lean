/-
# SchemaLang.Emit.Wit — the WIT target

Fold `Item`s to a WIT world. Discipline per codegen-core: names arrive
pre-mangled (kebab via `Emit.kebab` — WIT identifiers are kebab-case),
output is `Std.Format` → text, byte-tie CI is the drift guard (validated
by wit-parser roundtrip in CI — the canonical parser, not this printer,
is the correctness authority).

Lowering decisions (target-neutral universe → WIT):
- `option t` → `option<t>`, `result ok err` → `result<ok, err>` (1:1)
- `future t` / `stream t` → `future<t>` / `stream<t>` (WASI 0.3-native)
- records → `record`, variants → `variant` (payload cases → `case(ty)`)
- funcs → `func` in the world's export interface
- resources → `resource` declaration

Deliberately omitted: worlds/packages layout policy (the caller names the
world; one world per universe today), interface splitting (small
interfaces are the wasmtron rule — split when a real consumer needs it).
-/

import CodegenCore
import SchemaLang.Item

namespace SchemaLang.Emit.Wit

open CodegenCore.Emit (kebab)

/-- Lower a `Ty` to WIT type text. -/
def tyWit : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "s8" | .i16 => "s16" | .i32 => "s32" | .i64 => "s64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "string"
  | .bytes => "list<u8>"
  | .option a => s!"option<{tyWit a}>"
  | .result ok err => s!"result<{tyWit ok}, {tyWit err}>"
  | .list a => s!"list<{tyWit a}>"
  | .future a => s!"future<{tyWit a}>"
  | .stream a => s!"stream<{tyWit a}>"
  | .ty n => kebab n

/-- One type item as WIT text lines (record/variant/resource). -/
def typeDecl : Item → List String
  | .record n fields =>
    let open_ := "record " ++ kebab n ++ " {"
    let ls := fields.map fun f => "  " ++ kebab f.name ++ ": " ++ tyWit f.ty ++ ","
    open_ :: ls ++ ["}"]
  | .variant n cases =>
    let open_ := "variant " ++ kebab n ++ " {"
    let ls := cases.map fun (c, payload) =>
      match payload with
      | some t => "  " ++ kebab c ++ "(" ++ tyWit t ++ "),"
      | none => "  " ++ kebab c ++ ","
    open_ :: ls ++ ["}"]
  | .resource n => ["resource " ++ kebab n ++ ";"]
  | _ => []

/-- One function as a WIT func declaration line. -/
def funcDecl : FuncSig → String :=
  fun s =>
    let params := s.params.map fun (p, t) => kebab p ++ ": " ++ tyWit t
    "  " ++ kebab s.name ++ ": func(" ++ String.intercalate ", " params
      ++ ") -> " ++ tyWit s.ret ++ ";"

/-- The world, in the wasmtron small-interfaces shape:

    interface <world>-types { records, variants, resources }
    interface <world>-exports { use <world>-types.{...}; funcs }
    world <world> { export <world>-exports; }

Types live in their own interface; the exports interface `use`s exactly
the type names its signatures reference (deduped, kebab-mangled).
-/
def worldOf (packageName worldName : String) (items : List Item) : String :=
  let typeItems := items.filter fun it =>
    match it with | .record _ _ | .variant _ _ | .resource _ => true | _ => false
  let funcs := items.filterMap fun it =>
    match it with | .func s => some s | _ => none
  let typeLines := typeItems.flatMap typeDecl
  -- types referenced by func signatures (deduped, registration order)
  let refs :=
    (funcs.flatMap fun s => s.params.map (·.2) ++ [s.ret])
      |>.flatMap Ty.tyRefs
      |>.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []
  let useLine :=
    if refs.isEmpty then ""
    else "  use " ++ kebab worldName ++ "-types.{"
      ++ String.intercalate ", " (refs.map kebab) ++ "};\n"
  let exportsIface :=
    "interface " ++ kebab worldName ++ "-exports {\n"
      ++ useLine
      ++ String.join (funcs.map (fun s => "  " ++ funcDecl s ++ "\n"))
      ++ "}\n"
  "package " ++ packageName ++ ";\n\n"
    ++ "interface " ++ kebab worldName ++ "-types {\n"
    ++ String.join (typeLines.map (· ++ "\n"))
    ++ "}\n\n"
    ++ exportsIface ++ "\n"
    ++ "world " ++ kebab worldName ++ " {\n  export " ++ kebab worldName
    ++ "-exports;\n}\n"

end SchemaLang.Emit.Wit

/-- The WIT emitter plugin. -/
def witEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "wit"
  style := .doubleSlash
  specSource := "SchemaLang/Spec/Demo.lean"
  outputs := ["wit/gateway.wit"]
  run items := [
    { path := "wit/gateway.wit"
      contents := SchemaLang.Emit.Wit.worldOf "demo:gateway" "gateway" items }
  ]
