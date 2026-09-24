/-
# Scaffold.Specs — the adopted skeletons' spec registry

The spec VALUES the adopted skeletons were emitted from — the
scaffolder's writer side (`ScaffoldGenMain`, the `scaffoldgen` exe)
reads THEM, never a copy: one writer per artifact path means one home
per spec value. A new adoption adds its AppSpec HERE + regenerates
(`lake exe scaffoldgen <Name>`); the byte-tie in ScaffoldTests holds
the tie against the committed bytes.

Five questions (notes/v3/01-core.md): per-spec — each AppSpec value
carries the five-questions answers its generated headers fill.

Core-only (imports Scaffold.Generate — the cone rule).
-/

import Scaffold.Generate

namespace Scaffold

/-- The adopted `DemoApp` skeleton's spec (the seed's byte-tie holds
    the tie; ScaffoldTests reads this value, never a copy). -/
def demoSpec : AppSpec :=
  { name := "DemoApp"
    consumes := ["Order"]
    capabilities := ["registry-lane", "emitter", "diagnostics", "tests"]
    gateRows := ["axioms", "docs-check"]
    root := "crossing"
    rung := "generated"
    carrier := "the lane item over the registry's nodup-in-type substrate"
    spine := "registration = append; the emitters fold the replay" }

/-- The dogfood spec: `LedgerApp` — a tiny inventory/ledger app (the
    scaffolder's first REAL consumer; notes/v3/07's leftover rule: the
    template's output must have a consumer, the dogfood is the
    fitness proof). Exercises the `checks` capability DemoApp's spec
    never requested (the curated refusal rides the ALLOCATED
    `eSCF0013` — the coverage tooth's discipline). -/
def ledgerSpec : AppSpec :=
  { name := "LedgerApp"
    consumes := ["Order"]
    capabilities := ["registry-lane", "emitter", "checks", "diagnostics", "tests"]
    gateRows := ["axioms", "docs-check"]
    root := "crossing"
    rung := "generated"
    carrier := "the posting over the registry's nodup-in-type substrate"
    spine := "registration = append; the ledger folds the replay" }

/-- The adopted skeletons (the writer driver's input; each name's
    paths have exactly one writer: `ScaffoldGenMain` for the GENERATED
    files, the consumer for its hand-owned `<Name>/Flow.lean`). -/
def adoptedSpecs : List AppSpec := [demoSpec, ledgerSpec]

end Scaffold
