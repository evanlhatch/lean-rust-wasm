/-
# Inspector.Cites — the proof-coverage row: who cites this theorem

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: the review's proof-coverage query — "who cites this
theorem" answered FROM THE ENVIRONMENT (the demand-set discipline
applied to theorems: a theorem's demand set is its citation set, and a
ZERO-citation theorem is the proof-level leftover rule's finding);
notes/v3/09-gates-ops.md §4 (the demand-set honesty — the report names
its coverage, exactly the replayed closure).

The DATA is LintKit.Citations' census, CONSUMED (never re-derived): the
citee → citing-decls graph over the PROJECT modules only (the census's
performance lesson — core modules cannot cite project code, and forcing
their values is the ~14-minute trap the first cut paid), plus the
test-source pins (`#print axioms` leaves no constant — source 2 of the
census's two-media discipline).

The census is REPORT-ONLY here (the lintkit zeroCitation linter owns
the promote-to-gate question after the false-positive review): the
inspector renders who cites a theorem and surfaces the uncited theorems
per library; it fails nothing on a zero count.

The five questions (notes/v3/01-core.md):
- root: none — the proof-coverage query's rendering face over the
  citation census (host machinery, consumed).
- carrier grade: none — the census graph is LintKit's; this module's
  `Cites` is the PURE projection the tests pin (census + pins + the
  module resolver as data).
- spine reading: the interpretation stage (env → citation graph →
  the per-theorem answer + the per-library zero report).
- ladder rung: rung 1 — total folds over the graph.
- gate row: none — report-only census (the linter's gate promotion is
  named in LintKit.ZeroCitation's header).
-/

import LintKit
import Lean

namespace Inspector.Cites

open Lean
open LintKit (citationCensus citedInTestSources? isProjectModule isTestModule)

/-! ## the pure projection (the tests' pins; no IO past the host face) -/

/-- The census data, as the tests can build it: the citation graph,
    the test-pin membership, and the decl → module resolver. Pure. -/
structure Cites where
  /-- citee → citing decls (LintKit.Citations' graph). -/
  census : NameMap (Array Name)
  /-- Is the decl pinned by a test source (the `#print axioms` scan)? -/
  pinned : Name → Bool
  /-- A constant's defining module (`none` = not in the env — the
      unknown-constant loud miss's data). -/
  moduleOf : Name → Option Name

/-- One theorem's cites-answer: (rendered, known). An unknown constant
    is the LOUD miss (exit 1 at the exe's face); a known one renders
    its citers — all of them — plus the zero-citation verdict lines
    when the graph and the pins are both silent. -/
def citesAnswer (c : Cites) (thm : Name) : String × Bool :=
  match c.moduleOf thm with
  | none =>
      (s!"cites `{thm}`: NO SUCH CONSTANT — the loud miss (nothing by \
        this name is in the replayed environment)", false)
  | some mod =>
      let citers := (c.census.find? thm).getD #[]
      -- the leftover rule counts the TREE: only citations from OUTSIDE
      -- the defining module discharge the census's question (the same
      -- discipline as `zeroCites` below; an unresolved citer is not
      -- counted — the census's honest limit).
      let outside := citers.filter fun d =>
        match c.moduleOf d with
        | some cm => cm != mod
        | none => false
      let head := s!"cites `{thm}` — defined in `{mod}`, \
        {citers.size} citing declaration(s)"
      let lines := citers.toList.map fun d =>
        let dm := match c.moduleOf d with
          | some m => s!" ({m})"
          | none => " (module unresolved)"
        s!"  ← {d}{dm}"
      let tail :=
        if !outside.isEmpty then ""
        else if c.pinned thm then
          "\n  ZERO in-environment citations, PINNED by a test source — the \
            census's second medium (the `#print axioms` pin leaves no \
            constant; the pin is the citation)."
        else
          "\n  ZERO citations outside its own module — the proof-level \
            leftover rule surfaces it (`inspector uncited`): consume it in \
            the tree, pin it in a test, or it is the proof layer's dead code."
      (String.intercalate "\n" ([head] ++ lines) ++ tail, true)

/-- The zero-citation filter: of the candidate theorems (module, name),
    the ones cited NOWHERE outside their own module and unpinned — the
    proof-level leftover rule's findings, as data. Mirrors
    LintKit.ZeroCitation's detection face (a citer whose module does
    not resolve is NOT counted — the census's honest limit). -/
def zeroCites (c : Cites) (cands : List (Name × Name)) : List (Name × Name) :=
  cands.filter fun (mod, t) =>
    let citers := (c.census.find? t).getD #[]
    !(citers.any fun d =>
        match c.moduleOf d with
        | some cm => cm != mod
        | none => false)
    && !(c.pinned t)

/-- Per-library dedup, order-preserving (the report's section list). -/
def dedupLibs : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedupLibs xs else x :: dedupLibs xs

/-- One library's section: its uncited theorems. -/
def renderLib (unc : List (Name × Name)) (lib : String) : String :=
  let rows := unc.filter (fun (m, _) => m.getRoot.toString == lib)
  s!"  {lib}:" ++ String.intercalate "\n    "
    (rows.map (fun (_, t) => t.toString))

/-- The zero-citation REPORT, grouped per library (the module name's
    first component): the proof-level leftover rule's surface, library
    by library. Report-only — the linter's gate promotion is named in
    LintKit.ZeroCitation's header. -/
def uncitedReport (unc : List (Name × Name)) (_scanned : Nat) : String :=
  if unc.isEmpty then "  (none — every scanned theorem is cited outside \
      its own module or pinned by a test)"
  else String.intercalate "\n"
    ((dedupLibs (unc.map (fun (m, _) => m.getRoot.toString))).map (renderLib unc))

/-- THE ZERO-CITATION REPORT: the coverage statement rides the top (the
    demand-set honesty — the scan is exactly the replayed closure's
    project, non-test modules; a theorem outside them is invisible here
    and silence would lie). -/
def uncitedReportFull (unc : List (Name × Name)) (scanned : Nat) : String :=
  s!"zero-citation report — {scanned} theorem(s) scanned over the \
    replayed closure's project, non-test modules (census discipline: \
    project roots only)\n" ++
  "the uncited, per library (the proof-level leftover rule — census, \
    NOT a gate; the linter's promotion question is lintkit's):\n" ++
  uncitedReport unc scanned

/-! ## the host face (the census assembly over a replayed env) -/

/-- The census's NOISE FLOOR: the auto-deriving/equation machinery's
    name components — the leftover rule targets HAND-written theorems;
    the machinery's names are their consumers' residue and drown the
    report otherwise (observed on the first run: the eq_1/match_1/
    injEq/sizeOf families were ~90% of the rows). Component-level shape
    match — the report's filter, NOT a census rule (LintKit.skipDecl is
    the declaration-level face and is consumed alongside it below). -/
def isMachineryComponent (c : String) : Bool :=
  c.startsWith "eq_" || c == "eq" || c == "eq_def" || c.startsWith "_simp_"
  || c.startsWith "match_" || c.startsWith "_proof_"
  || c.startsWith "_sparseCasesOn" || c.startsWith "congr_"
  || c == "brecOn" || c == "injEq" || c == "inj" || c.startsWith "sizeOf"
  || c == "noConfusion" || c == "noConfusionType" || c == "decEq"
  || c.startsWith "induct_" || c == "_mutual" || c == "ofNat_ctorIdx"
  || c.startsWith "instDecidableEq"

/-- A name whose ANY component is machinery-shaped. -/
def isMachineryName (n : Name) : Bool :=
  (toString n).startsWith "_private"
  || n.components.any (fun c => isMachineryComponent c.toString)

/-- The candidate theorems: every `thmInfo` of a project, non-test
    module in the env, as (module, name) — machinery names excluded
    (the noise floor, above). The census's project-roots discipline IS
    the perf fix — core/test modules never enter. -/
def theoremCands (env : Lean.Environment) : Array (Name × Name) :=
  ((env.constants.map₁.toList.filterMap fun (n, info) =>
    match info with
    | .thmInfo _ =>
        match env.getModuleIdxFor? n with
        | some idx =>
            let m := env.header.moduleNames[idx]!
            if isProjectModule env idx && !isTestModule m
                && !isMachineryName n then some (m, n) else none
        | none => none
    | _ => none)).toArray

/-- Assemble the `Cites` data over a replayed env: the cached census +
    the pin set (the test-source corpus scan, LintKit's, consumed) +
    the env's module resolver. -/
unsafe def assemble (env : Lean.Environment) : CoreM Cites := do
  let census ← citationCensus env
  let mut pins : NameSet := {}
  for (_, t) in theoremCands env do
    if ← citedInTestSources? env t then pins := pins.insert t
  pure { census := census
       , pinned := pins.contains
       , moduleOf := fun d =>
          (env.getModuleIdxFor? d).map (fun idx => env.header.moduleNames[idx]!) }

/-- The uncited report's candidate set: `theoremCands` minus the shared
    skip shapes (LintKit.skipDecl, consumed — the declaration-level
    complement of the name-shape noise floor above). -/
def theoremCandsFiltered (env : Lean.Environment) :
    CoreM (Array (Name × Name)) := do
  let base := theoremCands env
  let mut out : Array (Name × Name) := #[]
  for (m, t) in base do
    unless ← LintKit.skipDecl t do
      out := out.push (m, t)
  pure out

end Inspector.Cites
