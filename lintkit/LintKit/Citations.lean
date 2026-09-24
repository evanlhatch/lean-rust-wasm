/-
LintKit.Citations — the reference census shared by the proof-hygiene
linters that need to know WHO cites a declaration (zeroCitation: the
proof-level leftover rule; graduation: the toImageIso call-site scan).

Two sources of citation, because they are visible in different media:

1. The ENVIRONMENT: every PROJECT constant's type + value
   `getUsedConstants` — the proof/expr mentions. Built once per process
   (the env is fixed after `importModules`), cached keyed on the module
   count (the same cache-shape discipline as DupDefBodies' per-root
   maps). PROJECT-ONLY, deliberately: a toolchain module (`Lean`/`Init`/
   `Std`/`Lake` root) can never cite a project constant, and forcing its
   imported (lazy) value via `value? (allowOpaque := true)` is the
   census's whole cost — the first cut swept the whole env and the
   census-mode test run paid ~14 min for ~zero information. Scanning the
   tree's own modules is the sound cut: any citation of a project decl
   lives in a project decl (or a test source, source 2 below).
2. The TEST SOURCES: `#print axioms Foo` pins leave NO constant in the
   environment (the command only prints), so a theorem pinned by a test
   file would read as uncited. The honest fix is a substring scan of the
   test modules' SOURCE files (modules with a `Tests` name component —
   the verdictCtors precedent), resolved through the tree's srcDir
   layout + cwd fallback. Limitation (documented): a pin spelled without
   the full dotted name is missed — the census is report-only, so the
   false-positive review catches it.

The five questions (notes/v3/01-core.md):
- root: none — host machinery (the citation census).
- carrier grade: none — findings feed the linters, not a data crossing.
- spine reading: interpretation stage (env → citation graph).
- ladder rung: n/a.
- gate row: none of its own — consumed by zeroCitation (census) and
  graduation (census).
-/
module

public import LintKit.Basic

public meta section

open Lean

namespace LintKit

/-- A module name counts as a test module when it has a name component
ENDING in `Tests` (`LintKitTests`, `KitTests`, `SchemaTests`, … — the
verdictCtors intent; a plain `.contains "Tests"` never matches, since
`Tests` is not itself a component). -/
def isTestModule (m : Name) : Bool :=
  m.components.any fun c => c.toString.endsWith "Tests"

/-- The constants a declaration's type and value cite (deduplicated). -/
def declRefs (env : Environment) (decl : Name) : Array Name :=
  match env.find? decl with
  | none => #[]
  | some info => Id.run do
    let trefs := info.type.getUsedConstants
    let vrefs := match info.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    let mut seen : NameSet := {}
    let mut out : Array Name := #[]
    for r in trefs ++ vrefs do
      unless seen.contains r do
        seen := seen.insert r
        out := out.push r
    out

/-! ## the cached citation graph -/

/-- Toolchain module roots whose constants can never cite project code
(Lean core itself — the tree imports it, it imports nothing of ours).
The census skips them: forcing core's imported values one by one
(`value? (allowOpaque := true)`) is the sweep's cost, for zero rows.
Host-side DEPENDENCY libs (Cli, batteries) land here too if ever
imported — same argument (a dependency cannot cite its dependent). -/
def coreModuleRoots : List Name := [`Init, `Lean, `Std, `Lake]

/-- Is the module at `idx` OUTSIDE the toolchain roots — i.e. a module
whose constants the census scans? -/
def isProjectModule (env : Environment) (idx : Nat) : Bool :=
  not (coreModuleRoots.any (·.isPrefixOf env.header.moduleNames[idx]!))

/-- citee → citing decls (type + value mentions), built over the
PROJECT constants of the linted environment (see `coreModuleRoots` —
core decls are skipped, they cannot cite project code). Cached keyed on
the module count (the env is fixed in a lint run; a different env means
a different count in practice — the cache is per-process). -/
initialize citationCensusRef :
    IO.Ref (Option (Nat × NameMap (Array Name))) ← IO.mkRef none

def computeCitationCensus (env : Environment) : NameMap (Array Name) :=
  Id.run do
  let mut citedBy : NameMap (Array Name) := {}
  for (decl, info) in env.constants.map₁.toList do
    -- project modules only: the core skip is the perf fix's whole point
    -- (the value-forcing below is per-decl and core is most of the env)
    let some idx := env.const2ModIdx[decl]? | continue
    unless isProjectModule env idx do continue
    let mut seen : NameSet := {}
    for r in info.type.getUsedConstants do
      unless seen.contains r do
        seen := seen.insert r
        citedBy := citedBy.insert r ((citedBy.find? r).getD #[] |>.push decl)
    if let some v := info.value? (allowOpaque := true) then
      for r in v.getUsedConstants do
        unless seen.contains r do
          seen := seen.insert r
          citedBy := citedBy.insert r ((citedBy.find? r).getD #[] |>.push decl)
  citedBy

/-- The citation graph of `env`, cached. -/
def citationCensus (env : Environment) : CoreM (NameMap (Array Name)) := do
  let key := env.header.moduleNames.size
  let cached? := (← citationCensusRef.get).bind
    fun (k, m) => if k == key then some m else none
  match cached? with
  | some m => return m
  | none =>
    let m := computeCitationCensus env
    citationCensusRef.set (some (key, m))
    return m

/-- Is `decl` cited by any constant of a module OTHER than its own? -/
def citedOutsideModule? (env : Environment) (census : NameMap (Array Name))
    (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx =>
    let mod := env.header.moduleNames[idx]!
    ((census.find? decl).getD #[]).any fun c =>
      match env.getModuleIdxFor? c with
      | some ci => env.header.moduleNames[ci]! != mod
      | none => false

/-! ## the test-source corpus (the #print-axioms pins) -/

/-- Directories tried (relative to cwd) when resolving a module's source
for the pin scan — the tree's srcDir layout (lakefile.toml), then the
cwd fallback. -/
def citationSrcDirs : Array String :=
  #["kit", "textkit", "testingkit", "lintkit", "gates", "wit",
    "schemacore", "zset", "machines"]

/-- Resolve a module's source file: first `citationSrcDirs` mount that
contains it, then the cwd; `none` when unresolvable (the runner's
missing-source precedent — skipped, never fatal). -/
def moduleSource? (m : Name) : IO (Option String) := do
  let cwd ← IO.currentDir
  let mut dirs : Array System.FilePath := citationSrcDirs.map (fun (s : String) => cwd / s)
  dirs := dirs.push cwd
  for dir in dirs do
    let f := modToFilePath dir m "lean"
    if ← f.pathExists then
      return some (← IO.FS.readFile f)
  return none

/-- The test modules' sources in `env`: (module, content) pairs, cached
keyed on the module count like the citation graph. -/
initialize testSourceCorpusRef :
    IO.Ref (Option (Nat × Array (Name × String))) ← IO.mkRef none

def testSourceCorpus (env : Environment) : CoreM (Array (Name × String)) := do
  let key := env.header.moduleNames.size
  let cached? := (← testSourceCorpusRef.get).bind
    fun (k, c) => if k == key then some c else none
  match cached? with
  | some c => return c
  | none =>
    let mut c : Array (Name × String) := #[]
    for m in env.header.moduleNames do
      if isTestModule m then
        if let some src ← moduleSource? m then
          c := c.push (m, src)
    testSourceCorpusRef.set (some (key, c))
    return c

/-- Does any test module's source PIN `decl` — the `#print axioms <full
name>` shape? (A pin spelled through an `open` — leaf name only — is
missed; the census's false-positive review catches it.) -/
def citedInTestSources? (env : Environment) (decl : Name) : CoreM Bool := do
  let corpus ← testSourceCorpus env
  let needle := "#print axioms " ++ toString decl
  return corpus.any fun (_, src) => src.contains needle

end LintKit
