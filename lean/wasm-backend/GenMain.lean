import Lean
import Lean.Compiler.LCNF
import CodegenCore
import WasmBackend
import WasmBackend.Check

/-!
# WasmBackend.GenMain — the LCNF → WAT artifact writer

The `leanir` pattern: import the target module's oleans, re-run the LCNF
pipeline (the impure-phase LCNF — Perceus RC included — is NOT persisted
in oleans), read the final `Decl`s from `impureExt`, emit WAT.

Pipeline: this exe writes `target/demo.wat` (+ the differential oracle
program); the justfile drives `wasm-tools parse -g` → binary, the
component wrap, and the differential smoke.
-/

open Lean

/-- The SCHEMA-FN wire names: the impl fn → the WIRE name the world
    exports (the schema fn's name — `GuestImpl.getUserImpl` implements
    the schema's `get-user`). Everything else wires as its own simple
    name kebabbed. -/
def wireNames : List (Name × String) :=
  [ (`GuestImpl.getUserImpl, "get-user")
  , (`GuestImpl.watchOrdersImpl, "watch-orders")
  , (`GuestImpl.greet, "greet")
  , (`GuestImpl.strLenDemo, "str-len-demo") ]

def targetDecls : Array Name := #[`double, `isBig, `adder, `area, `doubleArea, `pick, `applyAll, `runPaps, `curried, `apply2All, `useCurried, `sumList, `total, `GuestImpl.getUserImpl, `GuestImpl.greet, `GuestImpl.strLenDemo, `GuestImpl.watchOrdersImpl]

/-- Run the LCNF pipeline + emit the module, in CoreM. -/
def emitModuleWasm : CoreM String := do
  Lean.Compiler.LCNF.main targetDecls {}
  let mut decls : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in targetDecls do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls := d :: decls
  decls := decls.reverse
  -- Closure constants + lambdas: `_closed`/`_lam` decls (holding the
  -- paps) are generated IN-PROCESS by the re-run — never in the imported
  -- env. Include every impure decl UNDER a target's namespace.
  let mut names := targetDecls
  let all ← Lean.Compiler.LCNF.getLocalImpureDecls
  let internal := all.filter fun n =>
    let s := n.toString
    s.contains "." && targetDecls.any fun t => s.startsWith (t.toString ++ ".")
  names := names ++ internal
  let mut decls2 : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in names do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls2 := d :: decls2
  decls2 := decls2.reverse
  -- Debug dump: the final LCNF per decl (the compiler line's x-ray).
  for d in decls2 do
    let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
    IO.eprintln s!"--- {d.name}\n{fmt}"
  let wireNameOf (n : Name) : String :=
    match wireNames.find? (fun (m, _) => m == n) with
    | some (_, w) => w
    | none => CodegenCore.Emit.kebab n.getString!
  let exportTargets := targetDecls.toList.map fun n => (wireNameOf n, n)
  -- which targets return a STRING (the canonical ABI's post-return
  -- (ptr,len) convention): from the ORIGINAL def type — the LCNF type is
  -- erased to `obj` for every object result, Shape and String alike
  let env ← getEnv
  let stringResult? (n : Name) : Bool :=
    match env.find? n with
    | some (.defnInfo di) =>
        let rec peel (e : Expr) : Expr :=
          match e with | .forallE _ _ b _ => peel b | _ => e
        match peel di.type with
        | .const c _ => c == `String
        | _ => false
    | _ => false
  let res : Except String (String × WasmBackend.S) :=
    StateT.run (WasmBackend.emitModule decls2 exportTargets stringResult?) {}
  match res with
  | .ok (wat, _) =>
    -- splice the hand-written runtime (pooled allocator + Perceus RC)
    -- into the module body: single module, no imports.
    let rt ← IO.FS.readFile "runtime.wat"
    -- WAT line comments are `;;` — CommentStyle.wat (2.10).
    let hdr := CodegenCore.Emit.header .wat "wasm-backend" "DemoFn.lean"
    pure (hdr ++ (wat.replace "(module\n" ("(module\n" ++ rt ++ "\n")))
  | .error e => throwError e

/-! ## The component world (the SSOT for demo-world.wit)

The world file the component embed consumes is EMITTED, not
hand-maintained — the hand-written copy was the last contract surface
with no writer (the one-writer doctrine). The table is CURATED (not
folded from `targetDecls`): object-parameterized functions (`area` over
`Shape`, `applyAll` over closures) have no flat component
representation yet — they join the world when the canonical ABI
flattens them (strings/objects), and the KEPT list is the honest
surface of what the component actually exports.
-/

/-- The SCHEMA fns (the demo-exports INTERFACE's members; the core
    exports = the interface-qualified paths). -/
def interfaceFns : List String := ["get-user", "watch-orders"]

/-- One world export: (wit name, NAMED wit params — WIT requires
    parameter names, `wit-parser` rejects bare types — wit result —
    the async marking: GATED OFF (the async-lift's fused-adapter
    generation mismatches inside wit-component 0.244's own code-gen;
    the protocol's shapes = verified against the wit-bindgen 0.61
    reference + the minimal-module probes — the plan doc's Track 1b)). -/

def worldExports : List (String × List String × String × Bool) :=
  [ ("double", ["x: u64"], "u64", false)
  , ("adder", ["a: u64", "b: u64"], "u64", false)
  , ("is-big", ["x: u64"], "bool", false)
  , ("double-area", ["r: u64"], "u64", false)
  , ("run-paps", ["x: u64"], "u64", false)
  , ("total", ["a: u64", "b: u64", "c: u64"], "u64", false)
  , ("pick", ["b: bool", "a: u64", "x: u64"], "u64", false)
  , ("str-len-demo", ["n: u64"], "u64", false)
  , ("greet", ["n: u64"], "string", false)
  , ("get-user", ["id: u64"], "option<user>", false)
  , ("watch-orders", ["into: order-error"], "list<user>", false) ]

/-- The oracle's fn names — mirrors `oracleSrc`'s `rows`/`resultOf`
    (kebab, as the JSON spells them). The drift surface 3.4 pins: an
    oracle row for a fn the world does not export is a differential row
    with no component export to run it against. -/
def oracleFns : List String :=
  ["double", "is-big", "adder", "double-area", "run-paps", "total", "pick", "str-len-demo", "greet", "get-user"]

-- 3.4: every oracle fn IS a world export (the component contract covers
-- everything the differential manifest exercises).
#guard oracleFns.all fun f => worldExports.any fun (w, _, _, _) => w == f

/-- The world document (doubleSlash comments; the driver prepends the
    header). -/
def worldWit : String :=
  "package guestlang:demo;\n\n"
    ++ "interface demo-types {\n"
    ++ "  record user {\n    id: u64,\n    name: string,\n    email: string,\n    tags: list<string>,\n  }\n"
    ++ "  variant order-error {\n    empty-cart,\n    invalid-item(u64),\n    insufficient-funds(f64),\n  }\n"
    ++ "}\n\nworld demo {\n"
    ++ "  use demo-types.{user, order-error};\n"
    ++ String.intercalate "\n"
      ((worldExports.filter fun (name, _params, _ret, _isAsync) =>
          !(interfaceFns.contains name)).map fun (name, params, ret, _) =>
        s!"    export {name}: func({String.intercalate ", " params}) -> {ret};")
    ++ "\n}\n"

/-! ## The COMPILED world — the gateway's compilable subset

`get-user` is the first SCHEMA function the backend compiles: option +
record + strings + list<string> through the canonical ABI. The world
`use`s the gateway's types (one type authority — the record is the
SSOT's user, not a structural copy). `watch-orders` (async) + `db`
(resource) join when the async ABI + resources land — the compiled
world is the HONEST surface of what's compiled, and the compiled
component embeds IT.
-/

/-- The compiled world's WIT (types `use`d from the gateway package). -/
def compiledWorldWit : String :=
  "package guestlang:compiled;\n\n"
    ++ "use demo:gateway/gateway-types.{user};\n\n"
    ++ "world compiled {\n"
    ++ "    export get-user: func(id: u64) -> option<user>;\n"
    ++ "}\n"

/-- The DIFFERENTIAL ORACLE program: calls the real Lean functions over
generated inputs and prints the manifest as JSON. The Lean semantics is
the authority; the Rust diff test replays this against the emitted wasm.
(String VALUES go through `Lean.Json.str`/`compress` — proper escaping;
the row skeleton stays hand-spelled: `Json.mkObj` sorts keys and
`compress` strips spaces, so neither may touch the manifest's bytes.) -/
def oracleSrc : String := "
import Lean
import DemoFn
import GuestlangStd

def u64s : List UInt64 :=
  ((List.range 20).map (fun i => (i * 7 + 3) % 100)).map (fun n => n.toUInt64)

def rows : List (String × List String) :=
  (u64s.map fun a => (\"double\", [toString a]))
  ++ (u64s.map fun a => (\"is-big\", [toString a]))
  ++ (u64s.map fun a => (\"adder\", [toString a, toString (a + 3)]))
  ++ (u64s.map fun a => (\"double-area\", [toString a]))
  ++ (u64s.map fun a => (\"run-paps\", [toString a]))
  ++ ((List.range 20).map fun i =>
    (\"total\", [toString (i * 3), toString (i + 1), toString (i * 2)]))
  ++ (u64s.map fun a => (\"pick\", [if a % 2 == 0 then \"1\" else \"0\", toString a, toString (a + 1)]))
  ++ (u64s.map fun a => (\"str-len-demo\", [toString a]))
  ++ (u64s.map fun a => (\"greet\", [toString a]))
  ++ (u64s.map fun a => (\"get-user\", [toString a]))

def resultOf (fn : String) (args : List String) : String :=
  match fn, args with
  | \"double\", [a] => toString (double a.toNat!.toUInt64)
  | \"is-big\", [a] => if isBig a.toNat!.toUInt64 then \"1\" else \"0\"
  | \"adder\", [a, b] => toString (adder a.toNat!.toUInt64 b.toNat!.toUInt64)
  | \"double-area\", [a] => toString (doubleArea a.toNat!.toUInt64)
  | \"run-paps\", [a] => toString (runPaps a.toNat!.toUInt64)
  | \"total\", [a, b, c] => toString (total a.toNat!.toUInt64 b.toNat!.toUInt64 c.toNat!.toUInt64)
  | \"pick\", [b, a, x] => toString (pick (b == \"1\") a.toNat!.toUInt64 x.toNat!.toUInt64)
  | \"str-len-demo\", [a] => toString (GuestImpl.strLenDemo a.toNat!.toUInt64)
  | \"greet\", [a] => GuestImpl.greet a.toNat!.toUInt64
  | \"get-user\", [a] => match GuestImpl.getUserImpl a.toNat!.toUInt64 with
    | none => \"none\"
    | some u =>
      let tagS := String.intercalate \",\" (u.tags.map (fun t => t))
      s!\"some(\\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) })\"
  | _, _ => \"?\"

def jsonRow (fn : String) (args : List String) (expected : String) : String :=
  -- values via Lean.Json (compress = core's escaping); the skeleton
  -- keeps the manifest's byte format (`mkObj` sorts keys — forbidden
  -- here).
  \"{\" ++ \"\\\"fn\\\": \" ++ (Lean.Json.str fn).compress ++ \", \\\"args\\\": [\" ++
    String.intercalate \",\" (args.map fun a => (Lean.Json.str a).compress) ++
    \"], \\\"expected\\\": \" ++ (Lean.Json.str expected).compress ++ \"}\"

def main : IO Unit := do
  let mut out := \"[\"
  let mut first := true
  for (fn, args) in rows do
    let expected := resultOf fn args
    if !first then out := out ++ \",\"
    first := false
    out := out ++ jsonRow fn args expected
  out := out ++ \"]\"
  IO.println out
"

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  -- 2.1 was 'DemoFn only' (mathlib cost) — OBSOLETE: the guest IMPLS
  -- (lean/std, schema-typed functions) are now the point of this exe;
  -- they need the schema types (Demo — via GuestlangStd's import) and
  -- the std ops. The mathlib-in-closure cost is the product now.
  let env ← Lean.importModules #[`DemoFn, `GuestlangStd] (opts := {}) (loadExts := true)
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default }
  let state : Core.State := { env := env }
  let (wat, _) ← emitModuleWasm.toIO ctx state
  IO.FS.createDirAll "target"
  IO.FS.writeFile "target/demo.wat" wat
  IO.FS.writeFile "target/oracle.lean" oracleSrc
  let witHdr := "// GENERATED by wasm-backend — DO NOT EDIT\n"
    ++ "// spec source: DemoFn.lean (worldExports)\n"
    ++ "// regenerate via `just wasm-compile`; the world is the component\n"
    ++ "// contract — hand-edits are overwritten\n"
  IO.FS.writeFile "demo-world.wit" (witHdr ++ worldWit)
  let compiledHdr := CodegenCore.Emit.header .doubleSlash "wasm-backend" "Demo.lean (the compilable subset)"
  IO.FS.writeFile "compiled-world.wit" (compiledHdr ++ compiledWorldWit)
  IO.println "wrote target/demo.wat + target/oracle.lean + demo-world.wit"
