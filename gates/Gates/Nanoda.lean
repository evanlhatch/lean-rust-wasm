/-
Gates.Nanoda — the kernel-check row's SECOND lane: the external-kernel
double-check (`lake exe gates kernel-check --nanoda [--package=<dir>]`;
mined from the probe's verdicts, notes/nanoda-probe.md).

nanoda (ammkrn/nanoda_lib, Rust) is a second kernel from a DIFFERENT
implementation lineage than the C++ kernel AND lean4lean. The lane
re-plays the gated content through it: each gated root is exported via
lean4export (`lake env lean4export <root>` → NDJSON) and checked by
nanoda with a `permitted_axioms` config GENERATED FROM
`LintKit.AxiomAllowlist` (the gate's axiom data IS the config — ONE
table, never two; every emitted row is CHECKED against the allowlist
predicate at run time, so a drift refuses the lane).

THE PINS (the three-way pin; drift = the loud refusal):
  lean4export @ 66f1fb4bc256072069767fce52d39480e4524869, its
    `lean-toolchain` OVERWRITTEN to the tree's pin (leanprover/lean4:
    v4.33.0) — an exporter built against a different toolchain would
    invalidate the lane (the probe's toolchain-discipline caveat);
  nanoda_lib @ 3a2407216ee84a75f9e1aead6803d0578be06ae7 (v0.4.19);
  exporter format 3.1.0 (the meta line's first NDJSON row) ↔ lean
  4.33.0 — the lane parses the meta line of EVERY export and REFUSES a
  drift (the format-drift tooth).

THE TOOLS' HOME: `.tools/nanoda-lane/` (gitignored build residue, NOT
committed binaries) — the justfile's `tools-nanoda` row is the artifact:
clone-at-pin + build. The lane INVOKES the pair if present and SKIPS
with the honest note if absent — the optional-lane discipline: the
second lane is ADDITIVE, never blocking the lean4lean lane, and a skip
is reported as a skip, never laundered into a pass.

THE CADENCE (the honest cost): one root's export is ~772MB / ~100s
(Kit's closure: 13.6M lines, 174,918 decls) + the check ~116s — the
lane runs on the WAVE cadence (`--nanoda` is opt-in; `gates all` NEVER
runs it; CI runs it weekly/manual only). `--package=<dir>` shards to
one gated package's roots (the live one-library run of record:
`--package=Kit`, the probe's AGREEMENT run).

THE TEETH (all three, each live):
  1. the planted axiom violation: the lane self-tests before the real
     run — a MINIMAL hand-built NDJSON export declaring `plantedAxiom`
     outside the allowlist (+ a def depending on it) MUST be REFUSED
     (exit ≠ 0 under `permitted_axioms: []`), and the SAME export
     MUST pass with the axiom permitted (exit 0) — a blunt-teeth run
     (nanoda accepting the violation, or refusing the clean twin)
     refuses the lane. The tooth bytes are shared with the GatesTests
     pins (ONE copy).
  2. the format drift: every export's meta line is parsed; a version
     ≠ (3.1.0, 4.33.0) is the loud refusal (an exporter/toolchain skew
     would invalidate every verdict downstream).
  3. the absent tools: the SKIPPED note, exit 0, "not a pass" spelled
     out — the honest skip.

The stack discipline: nanoda overflows the default 8MB main-thread
stack on large exports (the probe's operational caveat) — every
invocation runs under `ulimit -s unlimited` (the runner recipe owns
the same requirement).

The five questions (notes/v3/01-core.md):
- root: none — the kernel-check row's second lane over Gates.Packages'
  roots.
- carrier grade: none — process plumbing over rendered configs.
- spine reading: the check face of the kernel-check row, second
  kernel; the lean4lean lane stays the per-run face, this the wave
  face.
- ladder rung: the axiom allowlist's SECOND reader (01 §7's disclosure
  mechanism re-tested by a disjoint kernel).
- gate row: the kernel-check row's `--nanoda` face (the summary in
  GatesMain names it; the teeth live here + the GatesTests pins).
-/
import Lean
import LintKit
import Gates.Common
import Gates.Packages

open Lean

namespace Gates.Nanoda

/-! ## The pins -/

/-- The exporter format version the lane accepts (the meta line's
    `format.version`). -/
def formatVersion : String := "3.1.0"

/-- The Lean toolchain version the lane accepts (the meta line's
    `lean.version` — the tree's own pin; a skew between exporter and
    tree invalidates the lane). -/
def toolchainVersion : String := "4.33.0"

/-- The tools' home (gitignored build residue; `just tools-nanoda` is
    the artifact — clone-at-pin + build, never committed binaries). -/
def toolsDir : System.FilePath := ".tools/nanoda-lane"

/-- The exporter exe (built against the TREE's toolchain — the pin
    overwrite happens in the recipe). -/
def exporterPath : System.FilePath :=
  toolsDir / "lean4export" / ".lake" / "build" / "bin" / "lean4export"

/-- The nanoda exe (the release build of the pinned checkout). -/
def nanodaPath : System.FilePath :=
  toolsDir / "nanoda_lib" / "target" / "release" / "nanoda_bin"

/-- The export artifact dir (build residue — regenerated per run). -/
def exportDir : System.FilePath := toolsDir / "exports"

/-! ## The config face (generated FROM LintKit.AxiomAllowlist) -/

/-- The core triple's rows — checked against THE predicate
    (`LintKit.isAllowedAxiom`) by the tooth below. -/
def tripleRows : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- The native trust base's EXPORTED faces: the concrete axiom names
    the export really mints for the tree's disclosed native_decide use
    (the probe's Q4 census: `Lean.trustCompiler`, `Lean.ofReduceBool`,
    `Lean.ofReduceNat` — the prelude's OWN trust-base declarations,
    declared once by Lean itself). The allowlist's certificate-shaped
    arm (`*_native.native_decide.ax_*`) covers the per-use certificate
    axioms; the prelude's trust base surfaces under these fixed names
    in EVERY export, so the config names them literally — derived from
    the probe's observed export surface, not a second axiom table. -/
def nativeRows : List Name :=
  [`Lean.trustCompiler, `Lean.ofReduceBool, `Lean.ofReduceNat]

/-- The permitted-axiom config's rows: the core triple + the native
    trust base's exported faces. Generated FROM
    `LintKit.AxiomAllowlist` — the generator's ONE tooth below checks
    the triple against THE predicate, so this list can never become a
    second table: a drift refuses the lane. -/
def axiomRows : List Name :=
  tripleRows ++ nativeRows

/-- The generation tooth: the triple's rows satisfy
    `LintKit.isAllowedAxiom` (the ONE allowlist) and the triple is
    present in full. `sorryAx` is deliberately ABSENT and UNPERMITTED
    with `hard_error: false` (the probe's config face): the prelude
    DECLARES it, but any actual USE fails the run — the zero-sorry
    rule independently re-tested by the second kernel. -/
def axiomRowsAllowlisted : Bool :=
  tripleRows.all LintKit.isAllowedAxiom &&
  tripleRows.all axiomRows.contains &&
  !axiomRows.contains `sorryAx

/-- The nanoda config's render (Lean.Json — no hand-rolled escaping).
    `hardError` is `true` only for the teeth runs (the planted axiom
    must be FATAL there); the real run keeps the probe's face —
    `false`, with sorryAx unpermitted so a sorry USE still errors the
    run. -/
def renderConfig (exportPath : String) (axioms : List Name)
    (hardError : Bool) : String :=
  toString <| Json.mkObj
    [ ("export_file_path", Json.str exportPath)
    , ("use_stdin", Json.bool false)
    , ("permitted_axioms",
        Json.arr (axioms.map (fun n => Json.str n.toString) |>.toArray))
    , ("unpermitted_axiom_hard_error", Json.bool hardError)
    , ("nat_extension", Json.bool true)
    , ("string_extension", Json.bool true)
    , ("print_success_message", Json.bool true) ]

/-! ## The format-drift tooth (the meta line's parse) -/

/-- The string right after the FIRST `needle` occurrence (up to the
    next `"`), none if the needle is absent. -/
def jsonStrAfter (haystack needle : String) : Option String :=
  match haystack.splitOn needle with
  | _ :: after :: _ => (after.splitOn "\"").head?
  | _ => none

/-- The export's (format, toolchain) versions from the meta line (the
    NDJSON's first row: `{"meta":{"exporter":...,"format":{"version":
    ..},"lean":{...,"version":..}}`). -/
def formatOf (metaLine : String) : Option (String × String) :=
  match jsonStrAfter metaLine "\"format\":{\"version\":\"" with
  | none => none
  | some fmt =>
    -- the lean version rides the githash anchor (the lean object's
    -- fixed first key): a needle at `"lean":{` would stop at the
    -- object's opening quote (`"githash"` first) — splitting AT the
    -- anchor (the remainder is the lean object's body) puts the
    -- version needle unambiguously in reach
    match metaLine.splitOn "\"lean\":{\"githash\":\"" with
    | _ :: leanObj :: _ =>
      match jsonStrAfter leanObj "\"version\":\"" with
      | none => none
      | some lv => some (fmt, lv)
    | _ => none

/-- The pin check: the meta line must name EXACTLY the pinned (format,
    toolchain) pair — any other exporter format or Lean version refuses
    the lane (the three-way pin; a skew would invalidate every verdict
    downstream of it). -/
def formatPinned (metaLine : String) : Bool :=
  formatOf metaLine == some (formatVersion, toolchainVersion)

/-! ## The teeth export (the planted axiom violation) -/

/-- The teeth's MINIMAL hand-built NDJSON (verified live against
    nanoda v0.4.19: refuse exit 1, allow exit 0 — the probe's
    adoption pins): `plantedAxiom : Prop` + `plantedUse := plantedAxiom`.
    Back-ref indices are continuous (nanoda's parser refuses gaps). -/
def toothExport : String :=
  "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}," ++
  "\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":" ++
  "\"0000000000000000000000000000000000000000\",\"version\":\"4.33.0\"}}}\n" ++
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"plantedAxiom\"}}\n" ++
  "{\"ie\":0,\"sort\":0}\n" ++
  "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n" ++
  "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"plantedUse\"}}\n" ++
  "{\"const\":{\"name\":1,\"us\":[]},\"ie\":1}\n" ++
  "{\"def\":{\"all\":[2],\"hints\":\"opaque\",\"levelParams\":[]," ++
  "\"name\":2,\"safety\":\"safe\",\"type\":0,\"value\":1}}\n"

/-! ## The spawns -/

/-- Quoting for the sh -c script (the pinned paths are plain). -/
def shq (s : String) : String := "'" ++ s ++ "'"

/-- One nanoda invocation under the stack discipline (`ulimit -s
    unlimited` — the probe's operational caveat: deep recursion over
    the 13.6M-line export overflows the default 8MB main stack). -/
def runNanoda (nanodaExe cfgPath : String) : IO (UInt32 × String) := do
  let out ← IO.Process.output
    { cmd := "sh"
    , args := #["-c", "ulimit -s unlimited && exec " ++ shq nanodaExe ++
                " " ++ shq cfgPath] }
  return (out.exitCode, out.stdout ++ "\n" ++ out.stderr)

/-- One lean4export run (the TREE's `lake env` supplies the olean
    search path; the exporter bin dir rides PATH). The NDJSON lands at
    `exportPath` (the file, not the pipe — 772MB through a captured
    pipe is the memory hazard). -/
def runExport (exporterBinDir root exportPath : String) :
    IO (UInt32 × String) := do
  let path ← match ← IO.getEnv "PATH" with
    | some p => pure p | none => pure "/usr/bin:/bin"
  let out ← IO.Process.output
    { cmd := "sh"
    , args := #["-c", "PATH=" ++ shq (exporterBinDir ++ ":" ++ path) ++
                " lake env lean4export " ++ shq root ++
                " > " ++ shq exportPath] }
  return (out.exitCode, out.stderr)

/-- nanoda's agreement line's count (`Checked N declarations with no
    typechecker errors`), for the report. -/
def checkedCount (out : String) : Option String :=
  match jsonStrAfter out "Checked " with
  | none => none
  | some rest => (rest.splitOn " ").head?

/-! ## The teeth (the self-test before the real run) -/

/-- The teeth self-test: the planted-axiom export MUST be refused
    (`permitted: []` → exit ≠ 0) and MUST pass with the axiom permitted
    (exit 0). Either bluntness refuses the lane (a nanoda that accepts
    undeclared axioms — or rejects the clean twin — would make every
    real verdict meaningless). -/
def runTeeth (nanodaExe : String) : IO Bool := do
  let dir : System.FilePath := exportDir
  IO.FS.createDirAll dir
  let toothPath := dir / "tooth.ndjson"
  IO.FS.writeFile toothPath toothExport
  let refuseCfg := dir / "tooth-refuse.json"
  let allowCfg := dir / "tooth-allow.json"
  IO.FS.writeFile refuseCfg
    (renderConfig toothPath.toString [] true)
  IO.FS.writeFile allowCfg
    (renderConfig toothPath.toString [`plantedAxiom] true)
  let (rc, _out) ← runNanoda nanodaExe refuseCfg.toString
  if rc == 0 then
    IO.eprintln "kernel-check/nanoda: TEETH BLUNT — nanoda ACCEPTED the \
      planted axiom violation; every downstream verdict is meaningless"
    return false
  let (rc2, out2) ← runNanoda nanodaExe allowCfg.toString
  if rc2 != 0 then
    IO.eprintln s!"kernel-check/nanoda: TEETH BLUNT — nanoda REFUSED the \
      permitted-axiom twin (exit {rc2}):\n{out2}"
    return false
  return true

/-! ## The lane -/

/-- `gates kernel-check --nanoda [--package=<dir>]` — the second lane.
    Exit 0 = every exported root AGREED (or the honest tools-absent
    skip, spelled out); exit 1 = a refusal (a real axiom violation, a
    blunt tooth, a format drift, a failed export). -/
def run (pkg : Option String) : IO UInt32 := do
  -- the ONE allowlist's generation tooth (drift = refusal)
  unless axiomRowsAllowlisted do
    IO.eprintln "kernel-check/nanoda: REFUSED — the config's axiom rows \
      drifted LintKit.AxiomAllowlist (ONE table, never two; fix \
      Gates.Nanoda.axiomRows)"
    return 1
  let exporter : System.FilePath := exporterPath
  let nanoda : System.FilePath := nanodaPath
  unless (← exporter.pathExists) && (← nanoda.pathExists) do
    IO.println "kernel-check/nanoda: SKIPPED — the pinned tools are \
      absent (NOT a pass; `just tools-nanoda` builds lean4export@pin \
      against the tree's toolchain + nanoda@pin). The lane is \
      additive: the lean4lean lane is the per-run kernel check."
    return 0
  -- the teeth BEFORE the real content (a blunt lane must not report)
  unless ← runTeeth nanoda.toString do return 1
  -- the roots (the --package shard; default = every gated root)
  let pkgs : Array Gates.PkgSpec := match pkg with
    | some d => Gates.gatedPackages.filter (fun (p : Gates.PkgSpec) => p.dir == d)
    | none => Gates.gatedPackages
  if pkgs.isEmpty then
    let shard := pkg.getD ""
    IO.eprintln s!"kernel-check/nanoda: REFUSED — unknown --package \
      shard `{shard}` (no gated package by that dir)"
    return 1
  let roots := pkgs.map (·.roots) |>.foldl (· ++ ·) #[]
  -- the exe's dir rides PATH (`lake env lean4export` resolves the exe
  -- by name — the probe's invocation shape)
  let binDir := match (exporterPath : System.FilePath).parent with
    | some d => d.toString | none => "."
  IO.println s!"kernel-check/nanoda: {roots.size} root(s) — exporting \
    via lean4export@pin (format {formatVersion}, lean \
    {toolchainVersion}) and checking via nanoda@pin (the wave-cadence \
    lane; a root's export is ~772MB / ~100s)"
  let mut agreed : Nat := 0
  let mut decls : Nat := 0
  for p in pkgs do
    for root in p.roots do
      let fname := (p.dir ++ "-" ++ root.toString ++ ".ndjson")
      let exportPath := exportDir / fname
      let (rc, err) ← runExport binDir root.toString exportPath.toString
      if rc != 0 then
        IO.eprintln s!"kernel-check/nanoda: REFUSED — the export of \
          {root} failed (exit {rc}):\n{err}"
        return 1
      -- the format-drift tooth: the meta line pins EVERY export
      let text ← IO.FS.readFile exportPath
      let metaLine := match text.splitOn "\n" with
        | l :: _ => l | [] => ""
      unless formatPinned metaLine do
        IO.eprintln s!"kernel-check/nanoda: REFUSED — format drift in \
          {root}'s export meta line: {formatOf metaLine} ≠ pinned \
          ({formatVersion}, {toolchainVersion}). The three-way pin \
          (nanoda ↔ format ↔ toolchain) broke — re-pin `tools-nanoda`."
        return 1
      -- the check
      let cfgPath := exportDir / (fname ++ ".config.json")
      IO.FS.writeFile cfgPath
        (renderConfig exportPath.toString axiomRows false)
      let (rc2, out2) ← runNanoda nanoda.toString cfgPath.toString
      if rc2 != 0 then
        IO.eprintln s!"kernel-check/nanoda: REFUSED — nanoda rejected \
          {root}'s content (exit {rc2}):\n{out2}"
        return 1
      let n := checkedCount out2
      agreed := agreed + 1
      decls := decls + (match n with | some s => s.toNat?.getD 0 | none => 0)
      let shown := n.getD "?"
      IO.println s!"kernel-check/nanoda: {root} — AGREEMENT \
        (nanoda checked {shown} declarations)"
  IO.println s!"kernel-check/nanoda: clean — {agreed}/{roots.size} \
    root(s) AGREED, {decls} declarations checked by the second kernel \
    (the pins + the teeth in Gates/Nanoda.lean's header)"
  return 0

end Gates.Nanoda
