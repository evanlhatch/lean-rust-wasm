/-
# Gates.KernelCheck — the lean4lean double-check (`gates kernel-check`)

Replays every gated package's modules through lean4lean
(github.com/digama0/lean4lean — a Lean 4 kernel written in pure Lean 4).
Per package, all of its modules in ONE lean4lean invocation (NON-fresh
mode: imported decls are trusted — mathlib is NOT re-inferred — and only
the target modules' own declarations are checked; observed: the imports
are still REPLAYED into lean4lean's environment, which is where the
memory goes). On a failed batch the package is re-run per module so the
report names the failures. Per the project owner: perf is explicitly a
non-goal here; correctness only.

The three caveats this gate ships with (read before trusting a green
run):

(a) reduceBool GAP: lean4lean does NOT support `reduceBool`, the kernel
    extension `native_decide`'s trust base reduces through. Our 3
    disclosed `native_decide` uses (edgepython's Parity module;
    schema-lang's Emit/Circuit ×2 — the allowlisted
    `_native.native_decide.*` trust bases) are OUTSIDE lean4lean's
    checking: modules whose proofs reduce through `reduceBool` are
    expected to fail or be skipped here. The axiom gate
    (`gates axioms`) remains their enforcement — this gate's value is
    everything ELSE. The known-gap module list lives in
    `knownReduceBoolGaps` below — additive only when a NEW disclosed
    native_decide use lands (the axiom allowlist is the discovery
    mechanism).
(b) SHARED LINEAGE: lean4lean shares design lineage with the C++ kernel
    (same author circle, same algorithmic shape). A green run is a
    bug-catching DOUBLE-CHECK (it has historically caught real kernel
    bugs), not independence from the C++ kernel's failure modes.
(c) THE PIN: lean4lean's default branch targets
    leanprover/lean4:v4.33.0-rc2; we pin rev
    8223d223ed98661882e95d9d6a7126df7097cd76 (master @ pin date) after
    verifying it builds under the v4.33.0 RELEASE toolchain with
    batteries v4.33.0 (the root require in gates' lakefile overrides
    lean4lean's rc2 batteries pin; lean4lean itself is NOT patched).
(d) BLIND SPOTS — what a green run does NOT prove (the honest-gaps
    list):
    1. `example`s — they create no constants, so NO env-based sweep sees
       them (this gate replays the env's constants; the axiom census
       walks the same constants): a sorry inside an `example` is caught
       only by the build's warning, never by either gate.
    2. structure-field defaults — a default value body is elaborated at
       declaration time but never replayed as a standalone constant, so
       its firing path is outside the kernel sweep.
    3. anything OUTSIDE `gatedPackages` — the sweep covers only the
       gated set (gates itself is exempt by role — Gates.Packages); a
       new package must join the list or it ships unchecked. The axiom
       census half (`gates axioms`) additionally covers only the gated
       ROOTS' declarations — same gap at module granularity.
    Pair this gate with `just gates`' other lanes; a green kernel sweep
    means exactly the checked surface, never more.

Mechanics (first-sweep lessons — the full sweep's findings were all
harness/resource artifacts, ZERO kernel disagreements; see
notes/divergences.md):

* The lean4lean exe builds on demand
  (`lake build lean4lean:exe` — the package's exe facet: its ONLY exe
  target, never the Theory/Verify libs) into
  `.lake/packages/lean4lean/.lake/build/bin/`.
* Each package is spawned DIRECTLY (not via `lake env`) with
  `LEAN_PATH := <pkg's own .lake/build/lib/lean> : <lake env's LEAN_PATH>`.
  Own-dir-FIRST is the fix for the same-named-module wrinkle: with
  `lake env`'s deps-first order, `feature-flags/Tests.Stress` resolved
  into substrait's tree and `wasm-backend/Tests.Axioms`/`Tests.Audit`
  into Machines' tree (oleans absent there → hard "object file does not
  exist" failures). With own-first order every module resolves to the
  package's own olean (verified on all three former collision sites).
* IMPORT-ONLY ROOT AGGREGATES ARE SKIPPED, with the precondition checked
  in code (`sourceHasDecls` — a root that gains declarations is NOT
  skipped). Rationale: non-fresh lean4lean checks only the target
  module's OWN declarations; the module-migration roots are `module` +
  `public import` only, so checking one checks zero declarations — while the
  import replay still loads the package's FULL closure. Observed: the
  `Dbsp` and `SchemaLang` root replays peaked at 20–22GB RSS and were
  SIGTERM-killed by earlyoom (this host: 29GB, earlyoom's 20% line);
  every other module — including each of those packages' real modules —
  replayed clean. Skipping loses no kernel coverage: every declaration
  lives in a child module that IS replayed.
* Signal-killed runs (exit ≥ 128 — earlyoom) are reported as KILLED,
  distinct from kernel REJECTIONS (lean4lean prints "found a problem"
  and exits 1). Both fail the gate; only rejections are divergence
  candidates for notes/divergences.md.
* Target modules are enumerated from the package's OWN
  `.lake/build/lib/lean` (`*.olean`, exact suffix — the module system
  also writes `.olean.private`/`.olean.server` parts, which are not
  separate modules). A package with no oleans is an ERROR (the gate
  requires `just lean-build` first — a skipped package is NOT a checked
  package).

Pure Lean core + Gates.Packages (+ Gates.Common's shared driver tails).
-/
import Lean
import Gates.Packages
import Gates.Common  -- the shared driver tails; transitively pulls
                     -- schema-lang oleans — import-graph only, the exe
                     -- loads the whole tree anyway

open Lean

namespace Gates.KernelCheck

/-- Modules whose expected lean4lean failure is the reduceBool gap
    (caveat (a)): the packages' disclosed native_decide sites. The axiom
    gate owns their enforcement; a failure HERE for any OTHER module is
    a real finding. -/
def knownReduceBoolGaps : Array (String × Name) := #[
  ("edgepython", `EdgePython.Parity),
  ("schema-lang", `SchemaLang.Emit.Circuit)
]

/-- The lean4lean exe, built on demand (only the exe target — its
    Theory/Verify libs are lean4lean's own proof lane, not the checker's
    runtime). -/
def ensureExe : IO System.FilePath := do
  let exe : System.FilePath := "../../.lake/packages/lean4lean/.lake/build/bin/lean4lean"
  unless ← exe.pathExists do
    IO.println "kernel-check: building the lean4lean exe (one-time; only the exe target)"
    let out ← IO.Process.output { cmd := "lake", args := #["--dir", "../..", "build", "lean4lean:exe"] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"kernel-check: `lake build lean4lean:exe` failed:\n{out.stdout}\n{out.stderr}"
  return exe

/-- Recursive olean walk (filesystem depth — `partial`, termination is
    the dir tree's finiteness, not a structural measure). -/
partial def walkOleans (dir : System.FilePath) (acc : Array System.FilePath) :
    IO (Array System.FilePath) := do
  let mut acc := acc
  for e in ← dir.readDir do
    if ← e.path.isDir then
      acc ← walkOleans e.path acc
    else if e.path.extension == some "olean" then
      acc := acc.push e.path
  return acc

/-- All modules of a package, enumerated from its own olean dir
    (`Foo/Bar.olean` → `Foo.Bar`; `.olean.private`/`.olean.server`/
    `.ir`/`.ilean` siblings excluded by the exact-suffix test). -/
def modulesOf (libDir : System.FilePath) : IO (Array Name) := do
  let files ← walkOleans libDir #[]
  let pre := libDir.toString ++ "/"
  return files.map fun p =>
    let rel := match p.toString.dropPrefix? pre with
      | some r => r.toString | none => p.toString
    let stem := match rel.dropSuffix? ".olean" with
      | some s => s.toString | none => rel
    String.intercalate "." (stem.splitOn "/") |>.toName

/-- Column-0 declaration openers. The module-migration root aggregates
    are `module` + `public import` lines inside a `/- -/` header-comment
    — none of these at column 0. -/
def declOpeners : Array String := #[
  "@[", "def ", "theorem ", "instance", "abbrev ", "inductive ",
  "structure ", "class ", "opaque ", "axiom ", "example", "initialize",
  "macro ", "syntax ", "elab ", "export ", "noncomputable"]

/-- Does a source file declare anything? Fail-closed: any column-0
    declaration opener (even inside a comment — our headers never put
    one there) counts as declarations, and then the module is CHECKED,
    not skipped. -/
def sourceHasDecls (path : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.any fun l =>
    !l.isEmpty && !l.startsWith " " && !l.startsWith "\t" &&
      declOpeners.any (l.startsWith ·)

/-- A package's own LEAN_PATH entry first, then its `lake env` closure
    (the same-named-module fix — see the header). An ABSORBED package
    (`pkg.leanPath` set — notes/single-lake-migration.md) has no lakefile
    to `lake env` against: its entry IS the root build dir, which already
    carries the whole dep closure. -/
def leanPathOf (pkg : PkgSpec) (pkgDir : System.FilePath) : IO String := do
  match pkg.leanPath with
  | some own =>
    -- ABSOLUTIZE the override and APPEND the root workspace's closure: the
    -- root build dir carries the ABSORBED modules, but while sibling
    -- packages are still standing (pre-phase-5), their oleans live in
    -- THEIR OWN .lake dirs — `lake env printenv LEAN_PATH` from the ROOT
    -- dir enumerates them (absolute paths, so the spawn's cwd := pkgDir
    -- cannot break them; observed pre-fix: `unknown module prefix
    -- 'SchemaLang'`). Root build dir FIRST (own-dir-first — the same-
    -- named-module fix in the header).
    let rootOut ← IO.Process.output
      { cmd := "lake", args := #["--dir", s!"{pkgDir}/../..", "env", "printenv", "LEAN_PATH"]
      , cwd := some "." }
    unless rootOut.exitCode == 0 do
      throw <| IO.userError s!"`lake env printenv LEAN_PATH` failed at the root:\n{rootOut.stderr}"
    let ownAbs : System.FilePath := own
    let ownAbs ←
      if ownAbs.isAbsolute then
        pure ownAbs
      else do
        let cwd ← IO.currentDir
        pure (cwd / ownAbs)
    return s!"{ownAbs.toString}:{rootOut.stdout.trimAscii}"
  | none =>
    let out ← IO.Process.output
      { cmd := "lake", args := #["--dir", s!"{pkgDir}/../..", "env", "printenv", "LEAN_PATH"]
      , cwd := some pkgDir }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"`lake env printenv LEAN_PATH` failed in {pkgDir}:\n{out.stderr}"
    return s!"{pkgDir}/.lake/build/lib/lean:{out.stdout.trimAscii}"

/-- Spawn lean4lean over `mods` in `pkgDir` (direct spawn — `lake env`
    would re-prepend the closure deps-first; the env entry merges over
    the inherited one, so PATH keeps the toolchain `lean` lean4lean
    shells out to). -/
def runLean4lean (exe : System.FilePath) (pkgDir : System.FilePath)
    (leanPath : String) (mods : Array Name) : IO IO.Process.Output := do
  let absExe := (← IO.currentDir) / exe
  IO.Process.output
    { cmd := absExe.toString
    , args := mods.map toString
    , cwd := some pkgDir
    , env := #[("LEAN_PATH", some leanPath)] }

/-- One package's outcome. `rejected` = the kernel reported a problem
    (divergence candidates); `killed` = the process died by signal
    (resource limit — investigated class, see the header); `skipRoots` =
    import-only root aggregates, skipped with the precondition verified
    (zero own declarations — nothing to check). -/
structure PkgOutcome where
  checked : Nat := 0
  skipRoots : Array Name := #[]
  killed : Array Name := #[]
  rejected : Array Name := #[]

/-- Kernel-check one package: all its modules in ONE lean4lean
    invocation; on a failed batch, per-module isolation so the report
    names the failures (perf is a non-goal per the project owner). -/
def checkPkg (exe : System.FilePath) (pkg : PkgSpec) : IO (Except String PkgOutcome) := do
  let pkgDir := pkg.srcDirOf
  let libDir := pkg.oleanDirOf
  unless ← libDir.pathExists do
    return .error s!"{pkg.dir}: no oleans at {libDir} — run `just lean-build` first"
  let leanPath ← leanPathOf pkg pkgDir
  -- partition: import-only single-segment roots are skipped (verified
  -- per module — a root that gained decls is checked, not skipped)
  let mut skipRoots : Array Name := #[]
  let mut checkMods : Array Name := #[]
  for m in ← modulesOf libDir do
    -- OWNERSHIP (the single-lake fix): an ABSORBED package's oleanDir is
    -- the ROOT build dir — it also holds its sibling packages' modules.
    -- A module is this package's iff its source sits under its srcDir;
    -- everything else belongs to an absorbed sibling (checked in THAT
    -- sibling's shard).
    let src := modToFilePath pkgDir m "lean"
    unless ← src.pathExists do continue
    -- nested `if`s, NOT `&&` over monadic operands: do-notation hoists
    -- every `←` out of `&&` eagerly (the short-circuit never engages —
    -- observed: sourceHasDecls read a nonexistent Tests.Main.lean)
    let mut skip := false
    if m.getRoot == m && !m.isAnonymous then
      if ← src.pathExists then
        unless ← sourceHasDecls src do
          skip := true
    if skip then
      skipRoots := skipRoots.push m
    else
      checkMods := checkMods.push m
  let out ← runLean4lean exe pkgDir leanPath checkMods
  if out.exitCode == 0 then
    IO.println s!"{pkg.dir}: {checkMods.size} module(s) replayed by the pure-Lean kernel — clean"
    return .ok { checked := checkMods.size, skipRoots }
  -- isolate: re-run per module so the report names the failures
  IO.println s!"{pkg.dir}: batch run exited {out.exitCode} — isolating per module"
  let mut killed : Array Name := #[]
  let mut rejected : Array Name := #[]
  for m in checkMods do
    let one ← runLean4lean exe pkgDir leanPath #[m]
    if one.exitCode != 0 then
      let tail := String.intercalate "\n"
        (((one.stderr ++ one.stdout).splitOn "\n").reverse.take 6).reverse
      if one.exitCode ≥ 128 && !((one.stderr ++ one.stdout).contains "found a problem") then
        killed := killed.push m
        IO.println s!"  {pkg.dir}/{m}: KILLED (exit {one.exitCode} — signal, no kernel verdict)"
      else
        rejected := rejected.push m
        IO.println s!"  {pkg.dir}/{m}: REJECTED\n{tail}"
  return .ok { checked := checkMods.size - killed.size - rejected.size
             , skipRoots, killed, rejected }

unsafe def run (pkgName : Option String) : IO UInt32 := do
  -- --package filter (the NativePolicy pattern): one package's env per
  -- process — the sharded mode the kernel-check recipe loops (the whole
  -- sweep in one process exceeds 30 min on this box).
  let some pkgs ← Driver.selectPackages "kernel-check" pkgName | return 1
  let exe ← ensureExe
  let mut failures : Array (String × Name) := #[]
  let mut killed : Array (String × Name) := #[]
  let mut gaps : Array (String × Name) := #[]
  let mut skipped : Array String := #[]
  let mut roots : Array (String × Name) := #[]
  for pkg in pkgs do
    match ← checkPkg exe pkg with
    | .error e => skipped := skipped.push e; IO.println s!"kernel-check: {e}"
    | .ok o =>
      for m in o.skipRoots do roots := roots.push (pkg.dir, m)
      for m in o.killed do killed := killed.push (pkg.dir, m)
      for m in o.rejected do
        if knownReduceBoolGaps.contains (pkg.dir, m) then
          gaps := gaps.push (pkg.dir, m)
        else
          failures := failures.push (pkg.dir, m)
  IO.println ""
  unless roots.isEmpty do
    IO.println "kernel-check: import-only root aggregates skipped (zero own declarations — \
      their decls are replayed via the child modules; a root that gains decls is checked):"
    for (d, m) in roots do IO.println s!"  {d}/{m}"
  unless gaps.isEmpty do
    IO.println "kernel-check: known reduceBool gaps (caveat (a) — the axiom gate owns these):"
    for (d, m) in gaps do IO.println s!"  {d}/{m}"
  if failures.isEmpty && killed.isEmpty && skipped.isEmpty then
    IO.println "kernel-check: clean — every gated module replayed by the pure-Lean kernel"
    return 0
  unless skipped.isEmpty do
    IO.println "kernel-check: SKIPPED packages (not built — not the same as checked):"
    for s in skipped do IO.println s!"  {s}"
  unless killed.isEmpty do
    IO.println "kernel-check: KILLED by signal (resource limit — NOT a kernel rejection; \
      investigate before accepting):"
    for (d, m) in killed do IO.println s!"  {d}/{m}"
  unless failures.isEmpty do
    IO.println "kernel-check: REJECTIONS outside the known reduceBool gaps \
      (divergence candidates — ledger in notes/divergences.md):"
    for (d, m) in failures do IO.println s!"  {d}/{m}"
  return 1

end Gates.KernelCheck
