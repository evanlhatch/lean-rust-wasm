/-
# SchemaLang.Docs — the markdown API-page emitter (the DOCS-SITE lane)

The ecosystem's "API docs from WIT" item: fold the universe (`List Item`)
into ONE GitHub-flavored-markdown API page (`docs/api.md`,
repo-root-relative like every other emitter output — the docs-site
scaffold consumes the path, the renderer stays agnostic).

Provenance: source = the SAME reflected registry every other emitter
folds (`Demo.lean` via `SchemaLang.Emit.Registry`); skipped = nothing —
records, variants, funcs (with their semantic contract fields), and
resources all render.

Driving decisions:
- Type text is `SchemaLang.Emit.tyWit` — the ONE type spelling, the
  same bytes the wire's `wit/gateway.wit` uses. The docs page cannot
  disagree with the wire contract about what `order-item` contains.
- Func signature blocks REUSE `SchemaLang.Emit.Wit.funcDecl` (the
  async/stream delivery lowering included) rather than re-stating it —
  a second signature renderer would be a second place to drift.
- Strings, not `Std.Format`: the page is flat, independent rows (tables,
  one heading per line) — there is nothing for `group`/`nest` to reflow,
  so Format would be ceremony, not structure. The WIT emitter keeps
  Format because its block bodies nest; this emitter has no nesting.
- Header style is `.hash` (an EXISTING `CommentStyle` — no codegen-core
  edit): the driver-prepended `# GENERATED …` lines render as markdown
  headings, which keeps the "DO NOT EDIT" banner visible in the rendered
  page. A dedicated `<!-- … -->` markdown style would be a closed-enum
  addition outside this lane's brief; reported, not done.
- Item order = registration order (`filter`/`filterMap` preserve it) —
  the same determinism discipline as the WIT world.
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx
public import SchemaLang.Emit.Wit

@[expose] public section

namespace SchemaLang.Docs

open CodegenCore.Emit (kebab)
open SchemaLang.Emit.Wit (tyWit funcDecl)

/-! ## The renderers (one per item kind) -/

/-- One record-field table row. -/
def fieldRow : Field → String :=
  fun f => s!"| `{kebab f.name}` | `{tyWit f.ty}` |"

/-- One record as a section block: kebab heading + field table. -/
def recordSection : Item → String
  | .record n fields =>
      s!"### `{kebab n}`\n\n| Field | Type |\n| --- | --- |\n"
        ++ String.intercalate "\n" (fields.map fieldRow)
  | _ => ""

/-- One variant as a section block: kebab heading + case table.
    Payload-less cases render an em dash (GFM table cell). -/
def variantSection : Item → String
  | .variant n cases =>
      s!"### `{kebab n}`\n\n| Case | Payload |\n| --- | --- |\n"
        ++ String.intercalate "\n" (cases.map fun (c, payload) =>
          match payload with
          | some t => s!"| `{kebab c}` | `{tyWit t}` |"
          | none => s!"| `{kebab c}` | — |")
  | _ => ""

/-- One func as a section block: the WIT signature (fenced — `funcDecl`
    is the ONE lowering, async/stream included) + the semantic contract
    fields (nullSem / determinism / delivery), as DATA (6.5.1). -/
def funcSection : FuncSig → String :=
  fun s =>
    s!"### `{kebab s.name}`\n\n```wit\n{(funcDecl s).pretty}\n```\n\n"
      ++ s!"null: `{s.sem.nullSem.toToken}` · determinism: "
      ++ s!"`{s.sem.determinism.toToken}` · delivery: `{s.sem.delivery.toToken}`"

/-- One resource as a section block. -/
def resourceSection (n : String) : String :=
  s!"### `{kebab n}`\n\nOpaque handle — its methods are `func` items whose first parameter references it."

/-! ## The page -/

/-- A page section: the heading + one block per item, DROPPED when the
    universe has no items of that kind (no dead headings). -/
def sectionOf (title : String) (blocks : List String) : List String :=
  if blocks.isEmpty then [] else title :: blocks

/-- The markdown API page over the universe. Sections: records, variants,
    functions, resources — each in registration order. -/
def docsOf (items : List Item) : String :=
  let records := items.filterMap fun it =>
    match it with | .record _ _ => some it | _ => none
  let variants := items.filterMap fun it =>
    match it with | .variant _ _ => some it | _ => none
  let funcs := items.filterMap fun it =>
    match it with | .func s => some s | _ => none
  let resources := items.filterMap fun it =>
    match it with | .resource n => some n | _ => none
  let secs :=
    sectionOf "## Records" (records.map recordSection)
      ++ sectionOf "## Variants" (variants.map variantSection)
      ++ sectionOf "## Functions" (funcs.map funcSection)
      ++ sectionOf "## Resources" (resources.map resourceSection)
  let intro := String.intercalate "\n"
    ["# demo:gateway — API reference"
    , "Generated from the schema-lang universe (`Demo.lean`); types are"
    , "WIT-rendered — the same spelling the emitted `wit/gateway.wit`"
    , "uses. DO NOT EDIT: regenerate with `just gen`."]
  (String.intercalate "\n\n" (intro :: secs)) ++ "\n"

/-- The docs emitter plugin: ONE page at the repo root's `docs/`.
    Header style `.hash` — see the module header for the choice (the
    driver-prepended banner renders as markdown headings). -/
def docsEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "docs"
  style := .hash
  specSource := "Demo.lean"
  outputs := ["../../docs/api.md"]
  run ctx :=
    [{ path := "../../docs/api.md"
       contents := docsOf ctx.items }]

end SchemaLang.Docs
