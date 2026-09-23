/-
# Faults.Emit.Rust — the fast-observe emitter

Folds allocated failure modes into ONE `fast_observe::error!` block:
codes, categories, advice, and payload fields all flow from the
registry — the E-code means the same thing in the Lean elaboration
layer and the production trace (TOOLKIT §11.1, completed).

Also emitted:
- `init_guest()` — the wasm contract: linkme's link-time registry
  doesn't exist on wasm, so `register_statics` must be called once at
  startup. Generated, not hand-written: forgetting it is impossible
  because the function only exists here.
- Payload fields via `SchemaLang.Emit.Rust.tyRust` — one type authority.
- Variant names pre-mangled (Pascal via `Emit.pascal`), fields via
  `rustIdent` — codegen-core discipline.

The macro body is a single `Body` leaf inside `Item.macroCall` (the
audited-leaf concession: `error!` is a macro, not Rust item grammar).
-/

import CodegenCore
import SchemaLang
import Faults.Registry

namespace Faults.Emit.Rust

open CodegenCore.Emit (pascal rustIdent)
open SchemaLang.Emit.Rust (tyRust)

/-- One failure mode → the error! variant text (attributes + fields).
    Field shape per fast-observe's README: `Name { field: Type }`,
    single line; empty payload → unit variant. -/
def faultVariant (code : String) (m : FailureModeItem) : String :=
  let l := fun s => "\n    " ++ s
  let attrs :=
    "    #[error(\"" ++ m.display ++ "\")]" ++ l
      ("#[code = \"" ++ code ++ "\", category = " ++ m.category.rustName
        ++ ", advice = \"" ++ m.advice ++ "\"]")
  let fields := m.payload.map fun (n, t) =>
    rustIdent n ++ ": " ++ tyRust t
  let variant :=
    match fields with
    | [] => pascal m.name
    | fs => pascal m.name ++ " { " ++ String.intercalate ", " fs ++ " }"
  attrs ++ "\n    " ++ variant ++ ","

/-- The whole error! block for one registry. -/
def errorBlock (enumName : String) (modes : List (FailureModeItem × String)) : String :=
  let variants := modes.map (fun (m, code) => faultVariant code m)
  let open_ := "    pub enum " ++ pascal enumName ++ " {"
  String.intercalate "\n" ([open_] ++ variants) ++ "\n    }"

/-- The module: error! block + the init hook. `guest? = true` emits the
guest flavor (wasm comments + `init_guest` — linkme's link-time registry
doesn't exist on wasm); `false` emits the host flavor (`init_host`, no
wasm comments). -/
def faultModule (enumName : String) (modes : List (FailureModeItem × String))
    (guest? : Bool := true) :
    List CodegenCore.Emit.Rust.Item :=
  let initFn := if guest? then "init_guest" else "init_host"
  (if guest?
    then [.comment "wasm: linkme's link-time registry is unavailable — call once",
           .comment "at guest startup; native builds resolve codes at link time."]
    else [])
  ++ [ .macroCall "fast_observe::error" [errorBlock enumName modes]
     , .fn s!"fn {initFn}()"
          s!"fast_observe::register_statics({pascal enumName}::ENTRIES);" ]

end Faults.Emit.Rust
