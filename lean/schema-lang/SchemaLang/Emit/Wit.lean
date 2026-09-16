/-
# SchemaLang.Emit.Wit — the WIT target

Fold `Item`s to a WIT world. Discipline per codegen-core: names arrive
pre-mangled (kebab via `Emit.kebab` — WIT identifiers are kebab-case),
output is `Std.Format` → text, byte-tie CI is the drift guard (validated
by wit-parser roundtrip in CI — the canonical parser, not this printer,
is the correctness authority).

Text assembly: structural `Std.Format` (hard `line`s — NO `group`s, so
every line breaks and `.pretty` cannot reflow; `nest` for the block
bodies, `joinSep` for the comma lists, `.pretty` once at the `String`
boundary). The bytes are pinned identical to the pre-Format emitter by
the goldens (`goldens/wit/`, `goldens/wit-fixtures/`): the only
deliberate quirk preserved is the 4-space column of the func decls —
`worldOf` folds each under `nest 4 (line ++ …)` while every other
interface member sits at 2 (as emitted since the first emitter). Leaf payloads (`tyFmt`'s type atoms, the `package`
line) interpolate — never join.

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

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx

@[expose] public section

namespace SchemaLang.Emit.Wit

open CodegenCore.Emit (kebab)
open Std.Format

/-- Lower a `Ty` to WIT type text as a format ATOM (no `line`s —
    `.pretty` is the identity on it, so `tyWit`'s bytes are the old
    `s!` interpolation's, exactly). -/
def tyFmt : Ty → Std.Format
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "s8" | .i16 => "s16" | .i32 => "s32" | .i64 => "s64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "string"
  | .bytes => "list<u8>"
  -- the flat form: WIT has no tensors — a tensor field lowers to
  -- `list<elem>` (row-major; the dims are schema metadata the WIT
  -- boundary cannot carry — the canonical-ABI pair-form keeps the
  -- count, not the shape)
  | .tensor _ a => f!"list<{tyFmt a}>"
  | .option a => f!"option<{tyFmt a}>"
  | .result ok err => f!"result<{tyFmt ok}, {tyFmt err}>"
  | .list a => f!"list<{tyFmt a}>"
  | .future a => f!"future<{tyFmt a}>"
  | .stream a => f!"stream<{tyFmt a}>"
  | .ty n => kebab n

/-- Lower a `Ty` to WIT type text. -/
def tyWit (t : Ty) : String := (tyFmt t).pretty

/-- The body of a brace block at column 0: first `line` nested 2 (the
    members' indent), hard lines BETWEEN the members — none after the
    last, so no trailing whitespace — and an empty member list degrades
    to a bare `line` (header and close brace on consecutive lines, the
    pre-Format fold's shape). -/
def blockBody (members : List Std.Format) : Std.Format :=
  match members with
  | [] => line
  | _ => nest 2 (line ++ joinSep members line)

/-- One type item as WIT text (record/variant/resource; non-type items
    are the empty format — `worldOf` filters them out first). -/
def typeDecl : Item → Std.Format
  | .record n fields =>
      f!"record {kebab n} \{" ++ blockBody
        (fields.map fun f => f!"{kebab f.name}: {tyFmt f.ty},") ++ line ++ f!"}"
  | .variant n cases =>
      f!"variant {kebab n} \{" ++ blockBody
        (cases.map fun (c, payload) =>
          match payload with
          | some t => f!"{kebab c}({tyFmt t}),"
          | none => f!"{kebab c},") ++ line ++ f!"}"
  | .resource n => f!"resource {kebab n};"
  | _ => ""

/-- One function as a WIT func declaration (UNINDENTED — `worldOf`
    nests it, giving the 4-space column the goldens pin). A `future a`
    return becomes an
    `async func` returning `a` — the wasi 0.3 async ABI: the async-ness
    lives in the FUNCTION TYPE, not in a sync-func-returning-`future`
    (the component validator rejects the latter: the `async` canonical
    lift option requires an async function type). `delivery = stream`
    renders the result as `stream<a>` — the delta-shaped contract: the
    host consumes the results incrementally (the elements of the impl's
    list, delivered by the async-lift's stream builtins). -/
def funcDecl : FuncSig → Std.Format :=
  fun s =>
    let params := joinSep (s.params.map fun (p, t) => f!"{kebab p}: {tyFmt t}") (text ", ")
    -- the RESULT: delivery=stream surfaces the list's ELEMENT as the
    -- stream's item type (the impl's `List a` = the buffered stream)
    let witRet (t : Ty) : Std.Format :=
      match t with
      | .list a => f!"stream<{tyFmt a}>"
      | a => tyFmt a
    match s.ret with
    | .future a =>
        let r := if s.sem.delivery == (.stream : Delivery) then witRet a else tyFmt a
        f!"{kebab s.name}: async func({params}) -> {r};"
    | ret =>
        f!"{kebab s.name}: func({params}) -> {tyFmt ret};"

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
  -- types referenced by func signatures (deduped, registration order)
  let refs :=
    (funcs.flatMap fun s => s.params.map (·.2) ++ [s.ret])
      |>.flatMap Ty.tyRefs
      |>.eraseDups
  let usePart : Std.Format :=
    if refs.isEmpty then ""
    else line ++ f!"  use {kebab worldName}-types.\{{joinSep (refs.map kebab) (text ", ")}};"
  let typesIface : Std.Format :=
    f!"interface {kebab worldName}-types \{"
      ++ typeItems.foldl (fun acc it => acc ++ line ++ typeDecl it) ""
      ++ line ++ "}"
  let exportsIface : Std.Format :=
    f!"interface {kebab worldName}-exports \{" ++ usePart
      ++ funcs.foldl (fun acc s => acc ++ nest 4 (line ++ funcDecl s)) ""
      ++ line ++ "}"
  (f!"package {packageName};" ++ line ++ line ++ typesIface ++ line ++ line
    ++ exportsIface ++ line ++ line
    ++ f!"world {kebab worldName} \{" ++ line
    ++ f!"  export {kebab worldName}-exports;" ++ line ++ "}" ++ line
  ).pretty

end SchemaLang.Emit.Wit

/-- The WIT emitter plugin. Repo-root-relative path (the `../../` prefix)
    matches the Rust/vortex emitters — the forge byte-tie checks the SAME
    file the emitter writes. The world folds the ctx's DEMO partition
    (`GenCtx.rootItems` — the driver-derived root-namespace split): with a
    second project's registry replayed, the gateway world stays exactly
    the Demo universe (byte-identical output, same fold, same order). -/
def witEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "wit"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../wit/gateway.wit"]
  run ctx := [
    { path := "../../wit/gateway.wit"
      contents := SchemaLang.Emit.Wit.worldOf "demo:gateway" "gateway"
        (ctx.rootItems `Demo) }
  ]

/-- The flags world's WIT emitter (the second project's wire lane): the
    FEATUREFLAGS partition of the same ctx, rendered by the SAME `worldOf`
    fold — one lowering, two worlds. The partition is DERIVED (the
driver's `GenCtx.rootPartitionOf` over the replayed registry — no
    hand-listed item names): a new `@[schema]` in FeatureFlags.lean joins
    `wit/flags.wit` without touching this emitter. Demo-only replays
    (the test goldens) see the empty partition = the bare world. -/
def flagsWitEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "flags-wit"
  style := .doubleSlash
  specSource := "FeatureFlags.lean (via GenCtx.rootPartitionOf)"
  outputs := ["../../wit/flags.wit"]
  run ctx := [
    { path := "../../wit/flags.wit"
      contents := SchemaLang.Emit.Wit.worldOf "guestlang:flags" "flags"
        (ctx.rootItems `FeatureFlags) }
  ]
