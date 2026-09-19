/-
# SchemaLang.Debug — the author's REPL commands

`#schema`, `#world`, `#spans` — the Metaprogramming-in-Lean `#assertType`
pattern (a command elab that LOGS, never mutates) applied to the schema
registry. These are DEBUG tools: no side effects on any registry
extension — the elabs read the elab-time environment (the authoring
file's registry, with the imports' rows replayed) and log.

- `#schema` — every registered item: Lean name → kind + compact sig
  (params/ret/delivery for funcs; field/case counts for records and
  variants) + the item's provenance summary (the declaring constant's
  first doc line, when it carried one — W7.5). Types are WIT-spelled
  via `Emit.Wit.tyWit` — never the `repr` (the author reads what the
  emitter writes).
- `#world <ident>` — the EXACT bytes `worldOf` folds for that world name
  over the registered items (the WIT preview — what `witEmitter` would
  write, pre-driver-header). Any name is accepted; a misspelled name
  degrades gracefully to a world spelled with that name (worlds are not
  registry rows, so there is nothing to fail against).
- `#spans` — the observability preview: one `SpanSpec` row per func
  item, mirroring the wasm-backend driver's fold (`SchemaGenMain.lean`'s
  observability manifest: name, delivery — `stream` iff the async
  future-return carries `delivery = stream` — and the (param, wit-ty)
  field list). The rows are the emitted Rust's `SPANS` table.

Ownership: this module owns the debug-command lane ONLY. Read-only
dependencies: `SchemaLang.Meta.Reflect` (the registry),
`SchemaLang.Emit.Wit` (`tyWit`/`worldOf`), `CodegenCore.Emit` (`kebab`).
The span-row rendering deliberately DUPLICATES the SchemaGenMain fold's shape
instead of importing it — SchemaGenMain is a driver exe, not a library.
-/

module

public import Lean
public meta import SchemaLang.Item
public meta import SchemaLang.Emit.Wit
public import SchemaLang.Meta.Reflect

public meta section

namespace SchemaLang.Debug

open Lean
open CodegenCore.Emit (kebab)
open SchemaLang.Emit.Wit (tyWit)

/-! ## Renderers (pure String folds — no monad, no side effects) -/

/-- One registered item → its compact debug line. The Lean name is the
    registry's key; the schema-side text is what the WIT emitter spells
    (`kebab` + `tyWit`), NOT the repr. -/
def itemLine (leanName : Name) : Item → String
  | .record n fs => s!"{leanName} : record {kebab n} ({fs.length} fields)"
  | .variant n cs => s!"{leanName} : variant {kebab n} ({cs.length} cases)"
  | .resource n => s!"{leanName} : resource {kebab n}"
  | .func s =>
      let params := String.intercalate ", "
        (s.params.map fun (p, t) => s!"{kebab p}: {tyWit t}")
      s!"{leanName} : func {kebab s.name}({params}) -> {tyWit s.ret}"
        ++ s!" delivery={s.sem.delivery.toToken}"

/-- One func sig → its `SpanSpec` row text — the SchemaGenMain observability
    fold, verbatim shape: delivery `stream` iff the return is an async
    `future` carrying `delivery = stream` (the WASI 0.3 stream lift),
    else `once`; fields = the params' (kebab name, wit type) pairs. -/
def spanRow : FuncSig → String :=
  fun s =>
    let fields := s.params.map fun (p, t) => s!"(\"{kebab p}\", \"{tyWit t}\")"
    let del := match s.ret with
      | .future _ => if s.sem.delivery == (.stream : Delivery) then "stream" else "once"
      | _ => "once"
    s!"SpanSpec \{ name: \"{kebab s.name}\", delivery: \"{del}\", fields: "
      ++ s!"&[{String.intercalate ", " fields}] }"

/-- The provenance suffix for one registered item: the declaring
    constant's first doc line when it carried one (`provenanceOf`'s
    payload half — the decl name already leads the item line). -/
def docSuffix (env : Environment) (leanName : Name) (it : Item) : String :=
  let prov := SchemaLang.Meta.provenanceOf env leanName it
  let pfx := toString leanName ++ ": "
  if prov.startsWith pfx then " — " ++ prov.drop pfx.length else ""

/-- Debug lines as a bulleted `MessageData` block (one line each). -/
def bulletLines : List String → MessageData :=
  fun ls => ls.foldl (fun acc l => acc ++ (m!"\n  {l}" : MessageData)) (m!"" : MessageData)

/-! ## The commands -/

/-- `#schema` — dump the registered items (the elab env's registry:
    this file's registrations plus every import's replayed rows). -/
syntax (name := schemaDumpCmd) "#schema" : command

elab_rules : command
  | `(command| #schema) => do
    let env ← getEnv
    let items := SchemaLang.Meta.registeredItems env
    logInfo (m!"registered schema items ({items.length}):"
      ++ bulletLines (items.map fun (ln, it) =>
        itemLine ln it ++ docSuffix env ln it))

/-- `#world <ident>` — the WIT preview: the EXACT bytes `worldOf`
    folds for that world name over the registered items. -/
syntax (name := schemaWorldCmd) "#world " ident : command

elab_rules : command
  | `(command| #world $w:ident) => do
    let items := (SchemaLang.Meta.registeredItems (← getEnv)).map (·.2)
    logInfo (SchemaLang.Emit.Wit.worldOf "guestlang" w.getId.toString items)

/-- `#spans` — the observability preview: one `SpanSpec` row per
    registered func item (the emitted Rust's `SPANS` table). -/
syntax (name := schemaSpansCmd) "#spans" : command

elab_rules : command
  | `(command| #spans) => do
    let rows := (SchemaLang.Meta.registeredItems (← getEnv)).filterMap fun (_, it) =>
      match it with | .func s => some (spanRow s) | _ => none
    logInfo (m!"span rows ({rows.length}):" ++ bulletLines rows)

end SchemaLang.Debug
