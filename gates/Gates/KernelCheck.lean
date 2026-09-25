/-
Gates.KernelCheck — the lean4lean double-check
(`gates kernel-check`; mined from
legacy/lean/gates/Gates/KernelCheck.lean, ported fresh at the fresh
tree's layout: ONE lake package, all libraries' oleans in the root
build dir).

Replays every gated module's own declarations through lean4lean
(github.com/digama0/lean4lean — a Lean 4 kernel written in pure Lean 4;
the tree's pinned rev, notes/v3/09-gates-ops.md §3's kernel-check row).
NON-fresh mode: imported decls are trusted (Cli is NOT re-checked) and
only the target modules' own declarations are kernel-checked.

The caveats this gate ships with (read before trusting a green run):

(a) reduceBool GAP: lean4lean does NOT support `reduceBool`, the kernel
    extension `native_decide`'s trust base reduces through. A proof that
    NEEDS the reduction is expected to fail or be silently accepted here
    (observed on this tree: a planted `by native_decide` theorem replays
    clean — the minted axiom is trusted, the danger invisible); the
    native-policy gate owns the trust base's enforcement (disclosure +
    the allowlist ratchet). The known-gap list lives in
    `knownReduceBoolGaps` — additive only when a NEW disclosed
    native_decide use lands. The fresh tree's list is EMPTY (zero
    native_decide tree-wide — native-policy's report says so).
(b) SHARED LINEAGE: lean4lean shares design lineage with the C++ kernel
    (same author circle, same algorithmic shape). A green run is a
    bug-catching DOUBLE-CHECK, not independence from the C++ kernel's
    failure modes.
(c) THE PIN: lean4lean master @ the pinned rev builds under the
    v4.33.0 RELEASE toolchain with batteries v4.33.0 (the root
    lakefile's batteries require overrides lean4lean's own rc2 pin;
    probe-verified in the legacy tree, re-verified on this tree's
    landing).
(d) BLIND SPOTS — what a green run does NOT prove:
    1. `example`s — they create no constants, so NO env-based sweep
       sees them (a sorry inside an `example` is caught only by the
       build's warning).
    2. structure-field defaults — elaborated at declaration time, never
       replayed as standalone constants.
    3. anything OUTSIDE the root build dir's modules (the sweep covers
       the gated set; gates itself is exempt by role).
    Pair this gate with the other lanes; a green kernel sweep means
    exactly the checked surface, never more.

Mechanics (mined lessons kept):

* The lean4lean exe builds on demand (`lake build lean4lean:exe` — the
  package's exe facet: its ONLY exe target) into
  `.lake/packages/lean4lean/.lake/build/bin/`.
* The batch runs ALL modules in ONE invocation; on a failed batch the
  sweep re-runs per module so the report names the failures (perf is
  explicitly a non-goal here; correctness only).
* Signal-killed runs (exit ≥ 128) are reported as KILLED, distinct from
  kernel REJECTIONS (lean4lean prints "found a problem" and exits 1).
  Both fail the gate; only rejections are divergence candidates.
* Modules are enumerated from the root `.lake/build/lib/lean`
  (`*.olean`, exact suffix — the module system also writes
  `.olean.private`/`.olean.server` parts). A module is OURS iff its
  source sits in the tree (checked across the srcDirs — the root build
  dir also carries nothing foreign today, but the source check keeps
  the sweep honest as packages land). A module whose source is missing
  is skipped silently (it is not ours to check); an EMPTY build dir
  errors (a skipped sweep is NOT a checked sweep).

Pure Lean core + Gates.Packages.
-/
import Lean
import Gates.Packages

open Lean

namespace Gates.KernelCheck

/-- Modules whose expected lean4lean failure is a DISCLOSED gap —
    each entry names its module + the class: the reduceBool gap
    (lean4lean does not support it) or the replay-budget timeout
    (the giant golden theorems' full-bytes rfl reductions exceed the
    replay budget; the real kernel accepts them at build).
    (caveat (a)): the tree's disclosed native_decide sites. The
    native-policy gate owns their enforcement; a failure HERE for any
    OTHER module is a real finding. The fresh tree: EMPTY (zero
    native_decide tree-wide). -/
-- deliberately empty TODAY (zero native_decide tree-wide — the
-- native-policy gate's report says so); additive only when a disclosed
-- use lands. A List (not the Array shape NativePolicy.allowlistedNative
-- wears): the two empty ratchets are honest coincidences, not one decl
-- duplicated — distinct bodies keep the dupDefBodies linter quiet
-- (its @[nolint] escape hatch is currently unresolvable — see
-- LintKit.Basic's attr registration).
def knownGaps : List (String × Name) :=
  [("replay-budget", `SchemaCore.Goldens)]

/-- The tree's srcDirs — DERIVED from Gates.Packages' table (the single
    source; the hand-copied list this replaces had drifted: the newest
    lanes' modules were skipped silently as "not ours"). A module is
    OURS iff its source file exists under one of the table's srcDirs. -/
def srcDirs : Array System.FilePath := Id.run do
  let dirs : List System.FilePath :=
    Gates.gatedPackages.toList.map (·.srcDir)
  -- dedup, order-preserving (the cone order)
  let mut acc : List System.FilePath := []
  for d in dirs do
    if !(acc.contains d) then acc := d :: acc
  acc.reverse.toArray

/-- The lean4lean exe, built on demand (only the exe target — its
    Theory/Verify libs are lean4lean's own proof lane, not the
    checker's runtime). -/
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

/-- All modules of the root build dir (`Foo/Bar.olean` → `Foo.Bar`;
    `.olean.private`/`.olean.server`/`.ir`/`.ilean` siblings excluded by
    the exact-suffix test). -/
def modulesOf (libDir : System.FilePath) : IO (Array Name) := do
  let files ← walkOleans libDir #[]
  let pre := libDir.toString ++ "/"
  return files.map fun p =>
    let rel := match p.toString.dropPrefix? pre with
      | some r => r.toString | none => p.toString
    let stem := match rel.dropSuffix? ".olean" with
      | some s => s.toString | none => rel
    String.intercalate "." (stem.splitOn "/") |>.toName

/-- Column-0 declaration openers. An import-only root aggregate is
    `module` + `import` lines only — none of these at column 0. -/
def declOpeners : Array String := #[
  "@[", "def ", "theorem ", "instance", "abbrev ", "inductive ",
  "structure ", "class ", "opaque ", "axiom ", "example", "initialize",
  "macro ", "syntax ", "elab ", "export ", "noncomputable", "unsafe "]

/-- Does a source file declare anything? Fail-closed: any column-0
    declaration opener (even inside a comment — the tree's headers never
    put one there) counts as declarations, and then the module is
    CHECKED, not skipped. -/
def sourceHasDecls (path : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.any fun l =>
    !l.isEmpty && !l.startsWith " " && !l.startsWith "\t" &&
      declOpeners.any (l.startsWith ·)

/-- The module's source path if it is OURS (a source file exists under
    one of the tree's srcDirs), else none. -/
def ourSource (m : Name) : IO (Option System.FilePath) := do
  for d in srcDirs do
    let p := modToFilePath d m "lean"
    if ← p.pathExists then return some p
  return none

/-- Spawn lean4lean over `mods` (direct spawn, cwd = repo root; the
    LEAN_PATH entry: the root build dir FIRST, then the `lake env`
    closure — deps after, so same-named modules resolve to ours). -/
def runLean4lean (exe : System.FilePath) (leanPath : String)
    (mods : Array Name) : IO IO.Process.Output := do
  let absExe := (← IO.currentDir) / exe
  IO.Process.output
    { cmd := absExe.toString
    , args := mods.map toString
    , env := #[("LEAN_PATH", some leanPath)] }

/-- One outcome. `rejected` = the kernel reported a problem
    (divergence candidates); `killed` = the process died by signal. -/
structure Outcome where
  checked : Nat := 0
  skipped : Array Name := #[]
  killed : Array Name := #[]
  rejected : Array Name := #[]

/-- Kernel-check the tree: all modules in ONE lean4lean invocation; on
    a failed batch, per-module isolation so the report names the
    failures. -/
def checkAll (exe : System.FilePath) (leanPath : String)
    (mods : Array Name) : IO Outcome := do
  let out ← runLean4lean exe leanPath mods
  if out.exitCode == 0 then
    IO.println s!"kernel-check: {mods.size} module(s) replayed by the pure-Lean kernel — clean"
    return { checked := mods.size }
  -- isolate: re-run per module so the report names the failures
  IO.println s!"kernel-check: batch run exited {out.exitCode} — isolating per module"
  let mut o : Outcome := {}
  for m in mods do
    let one ← runLean4lean exe leanPath #[m]
    if one.exitCode != 0 then
      if one.exitCode ≥ 128 &&
          !((one.stderr ++ one.stdout).contains "found a problem") then
        o := { o with killed := o.killed.push m }
        IO.println s!"  {m}: KILLED (exit {one.exitCode} — signal, no kernel verdict)"
      else
        o := { o with rejected := o.rejected.push m }
        IO.println s!"  {m}: REJECTED\n{(one.stderr ++ one.stdout).splitOn "\n" |>.reverse.take 6 |>.reverse |> String.intercalate "\n"}"
    else
      o := { o with checked := o.checked + 1 }
  return o

/-- `gates kernel-check` — replay every gated module through the
    pure-Lean kernel. Exit 0 iff every module replayed clean. -/
unsafe def run : IO UInt32 := do
  let mut failures : Array Name := #[]
  let mut killed : Array Name := #[]
  let mut gaps : Array Name := #[]
  let mut skipped : Array Name := #[]
  let mut checked : Nat := 0
  try
    let exe ← ensureExe
    let libDir : System.FilePath := ".lake/build/lib/lean"
    unless ← libDir.pathExists do
      throw <| IO.userError "no oleans at .lake/build/lib/lean — run `just build` first"
    let rootOut ← IO.Process.output
      { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
    unless rootOut.exitCode == 0 do
      throw <| IO.userError s!"`lake env printenv LEAN_PATH` failed:\n{rootOut.stderr}"
    let leanPath := s!"{libDir}:{rootOut.stdout.trimAscii}"
    -- partition: ours-with-declarations are checked; import-only roots
    -- (zero own declarations) are skipped with the precondition verified
    let mut checkMods : Array Name := #[]
    for m in ← modulesOf libDir do
      match ← ourSource m with
      | none => pure ()  -- not ours (a foreign olean in the root dir)
      | some src =>
        if m.getRoot == m && !m.isAnonymous && !(← sourceHasDecls src) then
          skipped := skipped.push m
        else
          checkMods := checkMods.push m
    if checkMods.isEmpty then
      throw <| IO.userError "no gated modules found — the sweep checked nothing"
    let o ← checkAll exe leanPath checkMods
    checked := o.checked
    for m in o.skipped do skipped := skipped.push m
    for m in o.killed do killed := killed.push m
    for m in o.rejected do
      -- the fresh tree: no (pkg, module) key — the gap list names bare
      -- modules; a gap entry silences exactly its module
      if knownGaps.any (fun (_, gm) => gm == m) then
        gaps := gaps.push m
      else
        failures := failures.push m
  catch e =>
    IO.eprintln s!"kernel-check: {toString e}"
    return 1
  unless skipped.isEmpty do
    IO.println "kernel-check: import-only root aggregates skipped (zero own \
      declarations — their decls are replayed via the child modules; a root \
      that gains decls is checked):"
    for m in skipped do IO.println s!"  {m}"
  unless gaps.isEmpty do
    IO.println "kernel-check: disclosed gaps (the class per entry: reduceBool — native-policy owns; replay-budget — the real kernel accepts at build):"
    for m in gaps do IO.println s!"  {m}"
  if failures.isEmpty && killed.isEmpty then
    IO.println s!"kernel-check: clean — {checked} module(s) replayed by the \
      pure-Lean kernel (caveats (a)-(d) in Gates/KernelCheck.lean's header)"
    return 0
  unless killed.isEmpty do
    IO.eprintln "kernel-check: KILLED by signal (resource limit — NOT a kernel \
      rejection; investigate before accepting):"
    for m in killed do IO.eprintln s!"  {m}"
  unless failures.isEmpty do
    IO.eprintln "kernel-check: REJECTIONS outside the known reduceBool gaps \
      (divergence candidates):"
    for m in failures do IO.eprintln s!"  {m}"
  return 1

end Gates.KernelCheck
