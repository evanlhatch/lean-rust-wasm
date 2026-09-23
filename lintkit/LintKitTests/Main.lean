/-
LintKitTests.Main — the cone linter's teeth (notes/v3/15-patterns.md #5:
positive control + the MANDATORY negative control).

Two layers:
1. PURE teeth (data level) — `coneOffences` and the cone order directly:
   the Mathlib/Batteries ban for C0/C1 (unplantable in a core-only
   closure — no such import can exist here, so the positive control for
   the ban can only live at the data level), cone-high project roots,
   and the negative controls (cone-low and same-cone imports pass; the
   `Lean` root passes the ban).
2. ENV teeth — `LintKit.lintModules` over this exe's loaded environment.
   POSITIVE: `LintKitTests.Violator` (imported below) plants the C0→C1
   violation and MUST produce exactly one finding. NEGATIVE: this module
   and the LintKit modules are compliant and MUST produce none — the
   assertion `findings.all (·.decl == Violator)` fails loudly on any
   spurious finding.

Note Main itself imports `LintKitTests.Violator` (root `LintKitTests`,
C0 — same cone, no offence): direct-imports-only means Main is NOT
flagged for Violator's transitive SchemaCore import. That is the first
cut's documented transitivity boundary, demonstrated live.
Evidence, not architecture — the five-question block lives in the modules under test.
-/
import LintKit.Runner
import LintKitTests.Violator

open Lean LintKit

/-- The pure verdict teeth. -/
def checkPureTeeth : Bool :=
  -- the cone order: C0 ≤ everything; nothing is ≤ C0 but C0
  ((Cone.c0machinery : Cone) ≤ .c3app)
    && ((Cone.c0machinery : Cone) ≤ .c0machinery)
    && !((Cone.c1domain : Cone) ≤ .c0machinery)
    && !((Cone.c3app : Cone) ≤ .c2theory)
  -- POSITIVE: the Mathlib/Batteries ban (06 §8) — both roots, and at
  -- any depth below them (importer roots: LintKitTests C0, SchemaTests C1)
  && (!(coneOffences `LintKitTests #[`Mathlib.Algebra.Group]).isEmpty)
  && (!(coneOffences `SchemaTests #[`Batteries.Data.List.Basic]).isEmpty)
  -- POSITIVE: cone-high project root (SchemaCore is C1) — ROOTED names
  -- (the linter roots module names before the verdict; so do the teeth)
  && (!(coneOffences `LintKitTests #[`SchemaCore]).isEmpty)
  -- NEGATIVE: cone-low imports pass (C1 on Kit)
  && (coneOffences `SchemaTests #[`Kit, `LintKit]).isEmpty
  -- NEGATIVE: same-cone imports pass
  && (coneOffences `LintKitTests #[`TextKit, `Kit]).isEmpty
  -- NEGATIVE: the Lean core root passes the C0 ban
  && (coneOffences `LintKitTests #[`Lean.Elab.Tactic]).isEmpty
  -- NEGATIVE: the host-side READER exemption — Gates reads what it
  -- gates (SchemaCore.regen) without firing; the reader keeps its
  -- Mathlib/Batteries ban
  && (coneOffences `Gates #[`SchemaCore]).isEmpty

unsafe def main : IO UInt32 := do
  unless checkPureTeeth do
    IO.println "lintkit-tests: PURE TEETH FAILED (coneOffences / cone order)"
    return 1
  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := `LintKitTests.Main }] {}
      (trustLevel := 1024) (loadExts := true)
  let (findings, _) ← (LintKit.lintModules #[`LintKitTests.Main] {}).toIO
    { fileName := "<lintkit-tests>", fileMap := default } { env }
  let ok := findings.size == 1
    && findings.all fun f => f.decl == `LintKitTests.Violator
  for f in findings do
    IO.println f.message
  if ok then
    IO.println "lintkit-tests: teeth green — exactly 1 finding, at the \
      planted violator LintKitTests.Violator; compliant modules clean"
    return 0
  else
    IO.println s!"lintkit-tests: TEETH FAILED — expected exactly 1 \
      finding at LintKitTests.Violator, got {findings.size}"
    return 1
