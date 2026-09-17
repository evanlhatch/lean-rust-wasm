/-
# Gates.KernelCheck — the lean4lean double-check (`gates kernel-check`)

Replays every gated package's modules through lean4lean
(github.com/digama0/lean4lean — a Lean 4 kernel written in pure Lean 4):
`lake env <lean4lean> <Module>...` per package (NON-fresh mode —
lean4lean's whole-path multithreaded mode: each target module's own
declarations are re-checked by the pure-Lean kernel against the imported
environment; imported decls are trusted, so mathlib is NOT replayed).
Per the project owner: perf is explicitly a non-goal here; correctness
only.

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

Mechanics: the lean4lean exe builds on demand
(`lake build lean4lean:exe` — the package's exe facet: its ONLY exe
target, never the Theory/Verify libs) into
`.lake/packages/lean4lean/.lake/build/bin/`.
Each package runs under its own `lake env` (cwd `../<pkg>`), so LEAN_PATH
is that package's closure. Target modules are enumerated from the
package's OWN `.lake/build/lib/lean` (`*.olean`, exact suffix — the
module system also writes `.olean.private`/`.olean.server` parts, which
are not separate modules). Known wrinkle: for same-named modules across
the closure (`Tests.Main`), lean4lean's olean resolution follows
`lake env`'s path order (deps first), so a package's `Tests.Main` check
may replay a dependency's copy instead; lib roots never collide, so the
library surface — the gate's point — is always the package's own.

Pure Lean core + Gates.Packages — no LintKit/schema-lang imports.
-/
import Lean
import Gates.Packages

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
  let exe : System.FilePath := ".lake/packages/lean4lean/.lake/build/bin/lean4lean"
  unless ← exe.pathExists do
    IO.println "kernel-check: building the lean4lean exe (one-time; only the exe target)"
    let out ← IO.Process.output { cmd := "lake", args := #["build", "lean4lean:exe"] }
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

/-- Kernel-check one package: all its modules in ONE lean4lean
    invocation (whole-path multithreaded mode). `.error` = the package's
    oleans are absent (the gate requires `just lean-build` first — a
    skipped package is NOT a checked package). On a failed batch run we
    re-run per module so the report names the failures (perf is a
    non-goal per the project owner). -/
def checkPkg (exe : System.FilePath) (pkg : PkgSpec) : IO (Except String (Array Name)) := do
  let pkgDir : System.FilePath := s!"../{pkg.dir}"
  let libDir := pkgDir / ".lake" / "build" / "lib" / "lean"
  unless ← libDir.pathExists do
    return .error s!"{pkg.dir}: no oleans at {libDir} — run `just lean-build` first"
  let mods ← modulesOf libDir
  let absExe := (← IO.currentDir) / exe
  let out ← IO.Process.output
    { cmd := "lake"
    , args := #["env", absExe.toString] ++ mods.map toString
    , cwd := some pkgDir }
  if out.exitCode == 0 then
    IO.println s!"{pkg.dir}: {mods.size} module(s) replayed by the pure-Lean kernel — clean"
    return .ok #[]
  -- isolate: re-run per module so the report names the failures
  IO.println s!"{pkg.dir}: batch run exited {out.exitCode} — isolating per module"
  let mut failed : Array Name := #[]
  for m in mods do
    let one ← IO.Process.output
      { cmd := "lake"
      , args := #["env", absExe.toString, toString m]
      , cwd := some pkgDir }
    if one.exitCode != 0 then
      failed := failed.push m
      let tail := String.intercalate "\n" (((one.stderr ++ one.stdout).splitOn "\n").reverse.take 6).reverse
      IO.println s!"  {pkg.dir}/{m}: FAILED\n{tail}"
  return .ok failed

unsafe def run : IO UInt32 := do
  let exe ← ensureExe
  let mut failures : Array (String × Name) := #[]
  let mut gaps : Array (String × Name) := #[]
  let mut skipped : Array String := #[]
  for pkg in gatedPackages do
    match ← checkPkg exe pkg with
    | .error e => skipped := skipped.push e; IO.println s!"kernel-check: {e}"
    | .ok mods =>
      for m in mods do
        if knownReduceBoolGaps.contains (pkg.dir, m) then
          gaps := gaps.push (pkg.dir, m)
        else
          failures := failures.push (pkg.dir, m)
  IO.println ""
  unless gaps.isEmpty do
    IO.println "kernel-check: known reduceBool gaps (caveat (a) — the axiom gate owns these):"
    for (d, m) in gaps do IO.println s!"  {d}/{m}"
  if failures.isEmpty && skipped.isEmpty then
    IO.println "kernel-check: clean — every gated module replayed by the pure-Lean kernel"
    return 0
  unless skipped.isEmpty do
    IO.println "kernel-check: SKIPPED packages (not built — not the same as checked):"
    for s in skipped do IO.println s!"  {s}"
  unless failures.isEmpty do
    IO.println "kernel-check: FAILURES outside the known reduceBool gaps:"
    for (d, m) in failures do IO.println s!"  {d}/{m}"
  return 1

end Gates.KernelCheck
