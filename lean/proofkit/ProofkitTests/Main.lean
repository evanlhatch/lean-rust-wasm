/-
# Proofkit Tests

The ladder discharges (positive + the Update PO-slot demonstration), the
binop contract's runtime face, and the @[implemented_by] swap actually
running the fast model. Negative control: the DetSpec sabotage proving
the implemented_by checks bite.

Run: `lake build ProofkitTests && .lake/build/bin/ProofkitTests`
-/
import Proofkit
import SchemaLang.Update
import SchemaLang.Update2
import TestKit

open Proofkit SchemaLang TestKit

/-! ## The ladder (TOOLKIT 4.2) -/

/-- The Update PO slots, demonstrated at v2 (the v1→v2 migration):
    the v2 pure lock `Update2Pure` — the autoParam default (`by
    decide`, the ladder's first rung) discharges over the stored
    `volatileRefs`. The update surface is `Update2Item` (the v2 row:
    the singleton SET clause replacing v1's single-column item); the
    composition runs through `Update2Item.apply` (the cascade's
    row-fold), no legality binders needed at execution. -/
abbrev poFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "count", ty := .u64 }]

def updReset : Update2Item poFields :=
  { name := "po-reset", record := ""
  , guard := .eq (.lit 0) (.lit 0)
  , sets := [{ field := ⟨"id", .u64⟩, path := .here, value := .lit 0 }] }

def updBump : Update2Item poFields :=
  { name := "po-bump", record := ""
  , guard := .eq (.lit 0) (.lit 0)
  , sets := [{ field := ⟨"count", .u64⟩
             , path := .there .here, value := .lit 1 }] }

-- THE PAYLOAD: the v2 pure lock assembles by instance search, zero
-- hand proofs (the `volatileRefs := []` default discharges `rfl`).
instance : Update2Pure poFields updReset := {}
instance : Update2Pure poFields updBump := {}

def ladderChecks : CheckResult := do
  -- the autoParam'd slot was discharged at construction
  _ ← assertEq "boundedSeven.n" boundedSeven.n 7
  -- the locked composite RUNS: the reset+bump cascade over id=1,count=2
  -- yields id=0 (the reset), count=1 (the bump) — read back via the
  -- ColPath getters (RowVals is a GADT: no BEq to lean on). The v1
  -- `cascade2`'s order (bump then reset, `cascade2 υ₁ υ₂` applies
  -- υ₂ first) is the v2 fold's application order: reset after bump.
  let row : RowVals poFields :=
    .cons (.u64 1) (.cons (.u64 2) .nil)
  let out := updReset.apply (updBump.apply [row])
  let u64Of : Value .u64 → UInt64 | .u64 n => n
  _ ← assertEq "cascade resets id"
    (out.map (fun r => u64Of (ColPath.get .here r))) [0]
  _ ← assertEq "cascade bumps count"
    (out.map (fun r => u64Of (ColPath.get (.there .here) r))) [1]
  .ok ()

/-! ## The @[implemented_by] swap -/

def implByChecks : CheckResult := do
  -- the runtime took the FAST model (same answers, accumulator shape)
  _ ← assertEq "sumToSpec 10" (sumToSpec 10) 55
  _ ← assertEq "sumToSpec 0" (sumToSpec 0) 0
  .ok ()

/-- The deterministic suite: the swap's positive + the sabotaged control
    (must FAIL — proves the checks bite). -/
def implBySpec : TestKit.DetSpec :=
  { name := "implemented_by fast = proved reference"
  , check := implByChecks
  , control := assertEq "sabotage" (sumToSpec 3) 7
  , controlName := "sumToSpec 3 == 7 (wrong)" }

def main : IO UInt32 := do
  let code ← mainOfChecks "Proofkit"
    [ ("ladder", ladderChecks)
    ]
  if code != 0 then return code
  TestKit.runDets [implBySpec]
