/-
Gates.Census — the proof-hygiene CENSUS rows, promoted to baselined
report-gates (the axiom-report pattern: the fresh render committed,
drift flagged, the loud re-baseline discipline) at 09 §8's trigger —
the first adjudicated NONEMPTY run.

* `decide-first-census` — `linter.guestlang.decideFirst` (04 §1: a
  decidable closed finite space gets `decide`, not a hand script).
* `zero-citation-census` — `linter.guestlang.zeroCitation` (the
  proof-level leftover rule: a theorem cited nowhere outside its own
  module is the proof layer's dead code — or the named public-API/
  load-bearing `@[nolint]` row).
* `evidence-redundancy-census` — `linter.guestlang.evidenceRedundancy`
  (B6; D37; 16-surface §3: re-proofs of carried laws + weaker-than-
  kernel obligation rows — the entourage's first question, at the
  hand-written face).

Promotion, not hard-gating: the census linters stay default-OFF (their
heuristics' limits are named in their own headers — promoting them to
FAIL-on-finding would tax every honest declaration with the census's
uncertainty, the 09 §8 reasoning verbatim); the gate consumes the
FINDINGS as data. A drift — a new finding, or one adjudicated away —
fails the row until the deliberate re-baseline names it.

The dispatch rides `Gates.gateDispatch` (the warm fold without
`--package`, one package's shard face in-process with it); the warm
fold is TWO legs — the library rows in-process against the shared env,
the tests-lib rows as child shards (`Gates.testLibPool`, the root-
`main` collision's honest remainder; the report block on stdout, the
parent assembles the baseline — the Axioms twin's shape) — plus
`Driver.reportGate` (the write-or-diff tail).

The five questions (notes/v3/01-core.md): none of its own — the
censuses' answers live in their linters (DecideFirst/ZeroCitation);
this module is the gate rows.
-/
import Lean
import LintKit
import Gates.Packages
import Gates.Common

namespace Gates.Census

open Gates (PkgSpec gatedPackages pkgIsTestLib testLibPackages)
open Lean

/-- One census row's identity: the linter option + the committed baseline
+ the human name (the two rows are ONE shape). -/
structure Census where
  /-- The default-OFF linter option the census enables. -/
  opt : Name
  /-- The committed baseline (the axiom-report pattern). -/
  path : System.FilePath
  /-- The gate row's name (the dispatch + the report face). -/
  gate : String

/-- The decide-first census: 04 §1's rung discipline, census mode. -/
def decideFirst : Census :=
  { opt := `linter.guestlang.decideFirst
    path := "notes/decide-first-census.md", gate := "decide-first-census" }

/-- The zero-citation census: the proof-level leftover rule, census mode. -/
def zeroCitation : Census :=
  { opt := `linter.guestlang.zeroCitation
    path := "notes/zero-citation-census.md", gate := "zero-citation-census" }

/-- The evidence-redundancy census: D37's teeth (B6), census mode. -/
def evidenceRedundancy : Census :=
  { opt := `linter.guestlang.evidenceRedundancy
    path := "notes/evidence-redundancy-census.md",
    gate := "evidence-redundancy-census" }

/- The three rows' titles + descriptions — the BASELINE HEADER's
inputs (reportHeader renders them into the committed file), so ONE
source serves both the exe's table rows (GatesMain) and the warm
dispatch's fold (`runWarmGate`); a second copy would drift the
baselines. The strings are the promoted rows' verbatim texts. -/

def decideFirstTitle : String :=
  "Decide-first census — hand scripts over decidable closed finite spaces"

def decideFirstDescr : String :=
  "The census linter (linter.guestlang.decideFirst, 04 §1): a theorem whose \
    statement is decidable over a closed finite space yet whose proof term \
    depends on non-computational lemmas. FIRST ADJUDICATED RUN (the \
    enforcement wave): every finding is the heuristic's own false-positive \
    class — theorems PROVED BY rfl whose elaborated term routes through \
    non-computational casts (the proof-side approximation's blindness), and \
    quantified-hypothesis statements the statement-side synthesizable- \
    Decidable filter lets through (not actually closed spaces). The findings \
    are DATA (the promotion, not a hard gate — 09 §8's rule: the census's \
    limits are named in its own header, so it stays census-grade); a drift \
    (a new finding, or one adjudicated away) is the deliberate re-baseline."

def zeroCitationTitle : String :=
  "Zero-citation census — the proof-level leftover rule"

def zeroCitationDescr : String :=
  "The census linter (linter.guestlang.zeroCitation): a theorem referenced \
    nowhere outside its own module. FIRST ADJUDICATED RUN (the enforcement \
    wave): the finding set is the LAW-LIBRARY class — the theorem layer ships \
    as API (Kit.Iso/Rel/Obligation's laws, the lanes' consumed-in-module \
    helpers), and mechanically it is INDISTINGUISHABLE from dead code (the \
    census's named limit; the ~130 reasoned @[nolint] rows cover only the \
    sites the earlier adjudication touched). So the census stays CENSUS-GRADE \
    (09 §8's rule): the findings are DATA, never failures, and the DRIFT LINES \
    are the review queue — every new uncited theorem shows up as a deliberate \
    re-baseline diff naming it (fixed, consumed, or the reasoned opt-out)."

def evidenceRedundancyTitle : String :=
  "Evidence-redundancy census — carried-law re-proofs + weaker-than-kernel rows"

def evidenceRedundancyDescr : String :=
  "The census linter (linter.guestlang.evidenceRedundancy, 16-surface \
    §3 + D37): the entourage's first question — does the type already \
    carry it? — over the hand-written face. TWO detectable shapes: a \
    theorem whose statement is a carried law's own round-trip shape \
    (Codec.decode_encode / Iso.to_inv / Iso.inv_to, same instance both \
    sides) whose proof does not cite the law field; an obligation row \
    (Obligation/Discharged) whose claim is closed and Decidable- \
    synthesizable while the claimed backend is a LITERAL weaker tier \
    (oracleSwept/generatedCheck/guestVerified). FIRST ADJUDICATED RUN \
    (the B6 landing): the one false-positive class was the carried-law \
    fields' OWN declaration sites (the field decl IS the construction \
    — fixed by the name exemption in the test); Class B's fold was \
    empty (no weaker-than-kernel row in the buildable tree — the \
    honest zero; the fixture teeth prove the class fires). BOUNDARY: \
    this first run's tree was red in WasmCore.Decode (another lane's \
    in-flight work) — the packages whose env loads through it \
    (WasmCore, WasmCoreTestsLib, Gates, GatesTestsLib, Guest, \
    ComponentTestsLib, DemoApp, LedgerApp) are ABSENT below; their \
    sections arrive at the green re-baseline, and that drift is the \
    record of the blocked first run. The heuristic's limits are named \
    in its own header (unbounded claims, computed tiers, and the \
    sweep fn's carrier are invisible), so the census stays \
    CENSUS-GRADE (09 §8's rule): the findings are DATA, never \
    failures, and a drift is the deliberate re-baseline."

/-- The census lint config: EVERY env-linter whole-disabled except the
census linter, enabled at the CLI-override level (the runner skips the
disabled passes entirely; the axiomOnlyConfig shape). -/
def censusConfig (c : Census) : LintKit.DriverConfig :=
  { overrides :=
      (({} : NameMap Bool)
        |>.insert `linter.guestlang.axiomAllowlist false
        |>.insert `linter.guestlang.dupDefBodies false
        |>.insert `linter.guestlang.packageNamespace false
        |>.insert `linter.guestlang.bareChecker false
        |>.insert `linter.guestlang.verdictCtors false
        |>.insert `linter.guestlang.recursiveSimpEqns false
        |>.insert `linter.guestlang.guestBan false
        |>.insert `linter.guestlang.graduation false
        |>.insert `linter.guestlang.decideFirst false
        |>.insert `linter.guestlang.zeroCitation false
        |>.insert `linter.guestlang.evidenceRedundancy false)
        |>.insert c.opt true }

/-- One package's census analysis over its env: the census linter's
findings, the decl names sorted (the deterministic report). SCOPED
(the warm-server equivalence gear, LintKit.Citations' scope note): the
citation-consuming linter's citers restrict to this package's modules —
the shard discipline's env-closure visibility made explicit, so the
warm fold over the shared env and the old per-package shards agree
datum for datum. -/
def analyzeEnv (c : Census) (roots : Array Name) :
    Lean.CoreM (Array Name) := do
  let decls ← LintKit.packageDecls (← getEnv) roots
  LintKit.withCensusScope roots do
    let findings ← LintKit.runLintersOnDecls decls (censusConfig c)
    return (findings.map (·.decl) |>.qsort Name.quickLt)

/-- The committed report's fixed header (everything before the first
`## ` section line). -/
def reportHeader (c : Census) (title descr : String) : List String :=
  [ s!"# {title}"
  , ""
  , s!"GENERATED by `lake exe gates {c.gate} --write` — do not hand-edit."
  , s!"CI runs `{c.gate}` without `--write`; a diff against this file fails the gate."
  , ""
  , descr
  , ""
  , "Per package: the census linter's findings over the package's root modules'"
  , "declarations, one `  <decl>` line per finding; a section with no finding"
  , "lines means zero findings. A drift (a new finding, or one adjudicated"
  , "away) fails the gate until the deliberate `--write --accept-drift`"
  , "re-baseline. Findings are DATA here (the promotion, not a hard gate);"
  , "each line is fixed, a reasoned `@[nolint]`, or this baseline's record."
  , "" ]

/-- ONE package's shard (the per-package process — the memory
discipline): the report BLOCK on stdout, the load failure on stderr. -/
unsafe def runPkg (c : Census) (pkg : PkgSpec) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  match ← Gates.analyzePkg c.gate (·.roots) (analyzeEnv c) base pkg with
  | .inl e =>
      IO.eprintln s!"{c.gate}: {pkg.dir}: LOAD FAILED — {e}"
      return 1
  | .inr decls =>
      IO.println s!"## {pkg.dir}"
      for d in decls do
        IO.println s!"  {d}"
      IO.println ""
      return 0

/-- The WARM face, TWO LEGS (the Axioms twin's shape): the LIBRARY
rows fold against the shared warm env (one Core state, per-package
scopes), their sections assembled directly from the data; the
TESTS-LIB rows ride `Gates.testLibPool` (one child shard per row —
the root-`main` collision bars them from the warm env), their stdout
sections merged in `gatedPackages` order (the shard's trailing
`println` LF dropped — the section text's byte-twin). A failed shard
poisons the run: its section stays out, its stderr line already
streamed live. The baseline text's bytes are the shard path's (the
same header + per-package sections in `gatedPackages` order). -/
unsafe def runWarm (c : Census) (title descr : String)
    (write acceptDrift : Bool) (env : Environment) : IO UInt32 := do
  let ctx : Lean.Core.Context :=
    { fileName := s!"<gates-{c.gate}>", fileMap := default }
  let mut failed := false
  let mut libSections : Array (String × String) := #[]
  for pkg in gatedPackages do
    unless pkgIsTestLib pkg do
      -- no per-package load face on the warm leg: the warm env is
      -- all-or-nothing upstream (the loud WARM LOAD FAILED line)
      let (decls, _) ← (analyzeEnv c pkg.roots).toIO ctx { env }
      libSections := libSections.push (pkg.dir, String.intercalate "\n"
        ([s!"## {pkg.dir}"] ++ decls.toList.map (fun d => s!"  {d}") ++ [""]))
  let mut shardSections : Array (String × String) := #[]
  for (i, code, out) in ← Gates.testLibPool c.gate do
    let pkg := testLibPackages[i]!
    if code != 0 then
      failed := true
    else
      shardSections := shardSections.push (pkg.dir, (out.dropEnd 1).toString)
  let mut sections : List String := []
  for pkg in gatedPackages do
    let pool := if pkgIsTestLib pkg then shardSections else libSections
    match pool.find? fun (d, _) => d == pkg.dir with
    | some (_, s) => sections := sections ++ [s]
    | none => pure ()
  let text := String.intercalate "\n" (reportHeader c title descr ++ sections)
  Driver.reportGate c.gate c.path text write acceptDrift failed
    s!"{c.gate}: clean — the census in sync (the findings baselined, drift flagged)"
    (Driver.diffCheck c.gate "report" "the census's findings changed" c.path text)

/-- `{c.gate} [--package=<dir>] [--write] [--accept-drift]` — the
census gate row: without the flag, the WARM fold (the tree's env
loaded once, every package's scoped census in-process); with it, ONE
package's shard face in-process (the debug face). The write-or-diff
tail. The title/descr come from THIS module's constants (the
baseline's header inputs — see the defs above). -/
unsafe def run (c : Census) (title descr : String)
    (write acceptDrift : Bool) (package : Option String) : IO UInt32 :=
  Gates.gateDispatch c.gate package (runPkg c)
    (Gates.withWarmEnv c.gate (runWarm c title descr write acceptDrift))

end Gates.Census
