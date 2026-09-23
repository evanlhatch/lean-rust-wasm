/-
# SchemaLang.ModuleDocs — the module-docstring extraction (the DOCSTRING-EXTRACTION lane)

The docs-site's "lean internals" page: the MODULE-HEADER prose (the
doctrine-mandated ownership/provenance/exclusions/decisions text) folded
into ONE GitHub-flavored-markdown page (`docs/lean-internals.md`,
repo-root-relative like every other emitter output).

The extraction is the CORE API, zero deps: `Lean.getModuleDoc?`
(Lean/DocString/Extension.lean) over the elaboration-time environment.
Verified by the build-time probe below: module docstrings ARE replayed
across imports at the level lake elaborates with — no export-level
config needed (the extension exports its entries at the `.server` level
and that data loads; if a toolchain change ever hides them, the probe
FAILS THE BUILD rather than shipping a page of gap markers).

Provenance and deliberate scope:
- The manifest (`internalsModules`) is DATA — one def, extensible by
  one line. Today: schema-lang's core (Item / Diff / Validate / Session),
  the W8+ wave modules (Witness / WitnessCheck / WitnessSpec / Update2 /
  Refine / PrePost / TableInvariant / Commands / EntityMachine, the Meta
  elaborator lanes) and Machines' Session / Sim / Fusion.
- WasmBackend's modules are NOT in the manifest: schema-lang cannot
  import wasm-backend (std → schema-lang, wasm-backend → std — a back
  edge would cycle the package graph). Reported to the owning lane.
- The rich block-comment headers of Item/Diff/Validate/Sim (the
  `# Module …` first-block form) are PLAIN block comments — not in the
  environment. The extraction carries the modules' docstrings (the
  `!`-form section prose, verbatim); converting the big headers to the
  docstring form is a one-character edit per file in files this lane
  does not own. Reported, not done.

Driving decisions:
- KEEP SIMPLE: the docstring prose IS the page's content. No decl
  counts, no indexes — the rich prose is the point.
- Doc-less manifest entries render an EXPLICIT gap marker (missing
  documentation is information, not silence — the negative controls
  in Tests pin the marker).
- The capture point is a TERM ELABORATOR (`capturedInternalsPage`),
  not `run_cmd` + `elabCommand`: in this toolchain `elabEvalCore`
  wraps action generation in `withoutModifyingEnv`, so declarations
  made by a `run_cmd` do not persist. A term elaborator reads the
  current environment directly and quotes the page as a string
  literal — the emitter downstream is then PURE data, per the
  emitter discipline (only drivers write).
- Strings, not `Std.Format` — same reasoning as `SchemaLang.Docs`:
  flat independent rows, nothing to reflow.
- Header style `.hash` (an EXISTING `CommentStyle`): the
  driver-prepended `# GENERATED …` banner renders as markdown
  headings, keeping the "DO NOT EDIT" line visible in the rendered
  page — the same choice `SchemaLang.Docs` made.
-/

module

public import Lean
-- `import all` (W5.4): module-mode oleans carry module docstrings at the
-- server/private level only (`Lean.DocString.Extension.moduleDocExt`
-- exports `exported := #[]`); a plain import's exported level leaves
-- `Lean.getModuleDoc?` empty and the capture renders gap markers. The
-- private level includes them, and `import all` selects it.
import all SchemaLang.Item
import all SchemaLang.Diff
import all SchemaLang.Validate
import all SchemaLang.Session
public import SchemaLang.Emit.GenCtx
import all Machines.Session
import all Machines.Sim
-- W15-25 waves (the consolidation batch): `import all` stays NON-public
-- (constraint 14 — Update2/Fusion are mathlib-carrying; the
-- leak rule forbids public imports of them into a module consumed by
-- legacy/downstream packages).
import all SchemaLang.Witness
import all SchemaLang.WitnessCheck
import all SchemaLang.WitnessSpec
import all SchemaLang.Update2
import all SchemaLang.Refine
import all SchemaLang.PrePost
import all SchemaLang.TableInvariant
import all SchemaLang.Commands
import all SchemaLang.EntityMachine
import all SchemaLang.Meta.EventSourced
public meta import SchemaLang.Meta.EventSourced
import all SchemaLang.Meta.Keys
import all SchemaLang.Meta.WireCodec
import all SchemaLang.Meta.TableInvariant
import all SchemaLang.Meta.Mono
import all Machines.Fusion

public meta section

open Lean Elab Term

namespace SchemaLang.ModuleDocs

/-! ## The extraction core (pure: `Environment → String`) -/

/-- One module's docstrings, VERBATIM, joined. `none` = the module has
    no module docstrings visible in the environment. A whitespace-only
    doc block counts as none: a module whose header is a plain `/- -/`
    block comment registers an EMPTY docstring entry (observed:
    WitnessSpec / Meta.Keys / Meta.TableInvariant / Meta.Mono) — the
    gap marker, not silence, is the doctrine's answer to that. -/
def moduleDocBlock (env : Lean.Environment) (mod : Lean.Name) : Option String :=
  match (Lean.getModuleDoc? env mod).map fun docs =>
    String.intercalate "\n\n" (docs.toList.map (·.doc)) with
  | some docs => if docs.trimAscii.isEmpty then none else some docs
  | none => none

/-- The page body over an ALREADY-EXTRACTED manifest: one `## <module>`
    section per entry; doc-less entries render the explicit gap marker.
    Pure over the extraction results — this is the function the negative
    controls exercise (empty manifest, doc-less module) without needing
    an environment. -/
meta def pageOf (mods : List (Lean.Name × Option String)) : String :=
  let intro :=
    "# Lean internals — module documentation\n\n" ++
    "Generated from the elaborated environment (`Lean.getModuleDoc?`) at the\n" ++
    "build of `SchemaLang.ModuleDocs`: the module manifest (`internalsModules`)\n" ++
    "is data, the docstrings are VERBATIM environment replay. DO NOT EDIT:\n" ++
    "regenerate with `just gen`."
  let secs := mods.map fun (m, doc?) =>
    match doc? with
    | some docs => s!"## {m}\n\n{docs}"
    | none => s!"## {m}\n\n> (no module docstrings in the environment — the header"
      ++ " is a plain block comment, or the module has none)"
  (String.intercalate "\n\n" (intro :: secs)) ++ "\n"

/-- The extraction: fold the manifest over the environment. -/
meta def moduleDocsOf (env : Lean.Environment) (mods : List Lean.Name) : String :=
  pageOf (mods.map fun m => (m, moduleDocBlock env m))

/-! ## The manifest (data — extensible by one line) -/

/-- The template's packages' modules this page covers. Adding a module =
    one line here (and its package must be importable — see the module
    header for the WasmBackend exclusion). -/
def internalsModules : List Lean.Name :=
  [ `SchemaLang.Item
  , `SchemaLang.Diff
  , `SchemaLang.Validate
  , `SchemaLang.Session
  , `Machines.Session
  , `Machines.Sim
  , `SchemaLang.Witness
  , `SchemaLang.WitnessCheck
  , `SchemaLang.WitnessSpec
  , `SchemaLang.Update2
  , `SchemaLang.Refine
  , `SchemaLang.PrePost
  , `SchemaLang.TableInvariant
  , `SchemaLang.Commands
  , `SchemaLang.EntityMachine
  , `SchemaLang.Meta.EventSourced
  , `SchemaLang.Meta.Keys
  , `SchemaLang.Meta.WireCodec
  , `SchemaLang.Meta.TableInvariant
  , `SchemaLang.Meta.Mono
  , `Machines.Fusion
  ]

/-! ## The build-time capture (the probe) -/

/-
The capture point: at THIS module's elaboration, fold the manifest
over the current environment (the imports' replayed docstrings).
The probe: `SchemaLang.Item` MUST have visible module docs — it
ships several docstring sections; `none` here means the cross-import
replay broke and the page would be a list of gap markers. Fail the
build with the diagnosis instead. (A doc comment cannot sit between
`open … in` and `elab` — this is a block comment.)
-/
private meta def capturePage : TermElabM Expr := do
  let env ← getEnv
  match Lean.getModuleDoc? env `SchemaLang.Item with
  | none =>
      throwError ("internals extraction: SchemaLang.Item has no module docs in the" ++
        " environment — the cross-import docstring replay failed (server-level" ++
        " export/olean-level change?). Fix the extraction, do not ship gap markers.")
  | some _ => return .lit (.strVal (moduleDocsOf env internalsModules))

elab "capturedInternalsPage" : term => capturePage

end SchemaLang.ModuleDocs
end -- public meta section

@[expose] public section
namespace SchemaLang.ModuleDocs

/-- The captured page — plain data by the time the emitter reads it. -/
def internalsPage : String := capturedInternalsPage

/-! ## The emitter plugin -/

/-- The internals-page emitter: ONE page at the repo root's `docs/`.
    `run` ignores the ctx — the page was captured at build time (see the
    capture point above); the emitter discipline's purity is preserved
    trivially. Registered in `SchemaLang.Emit.Registry.coreEmitters`, so
    the forge-jobs manifest (and its byte-tie) pick it up by derivation.

    W7.9 `Emitter.law` sweep — NO law, and why: the page's content is
    Lean's OWN module docstrings replayed through the environment (the
    capture elaborates-or-THROWS — the failure mode is loud at build
    time, not an emitted-artifact risk), so there is no spec→artifact
    correspondence left to state by emission time. -/
def internalsEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "internals-docs"
  style := .hash
  specSource := "SchemaLang.ModuleDocs (internalsModules via Lean.getModuleDoc?)"
  outputs := ["../../docs/lean-internals.md"]
  run _ctx :=
    [{ path := "../../docs/lean-internals.md"
       contents := internalsPage }]

end SchemaLang.ModuleDocs
