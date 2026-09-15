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
import TestKit

open Proofkit SchemaLang TestKit

/-! ## The ladder (TOOLKIT 4.2) -/

/-- The Update PO slots, demonstrated: BOTH class fields omitted — the
    autoParam defaults (`by decide`, the ladder's first rung) discharge
    over the derived reads. No hand proofs at the instance sites. -/
def poFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "count", ty := .u64 }]

def updReset : UpdateItem poFields ⟨"id", .u64⟩ :=
  { name := "po-reset", guard := .eq (.lit 0) (.lit 0), value := .lit 0
  , writePath := .here }

def updBump : UpdateItem poFields ⟨"count", .u64⟩ :=
  { name := "po-bump", guard := .eq (.lit 0) (.lit 0), value := .lit 1
  , writePath := .there .here }

-- THE PAYLOAD: legality assembles by instance search, zero hand proofs.
instance : UpdatePure poFields ⟨"id", .u64⟩ updReset := {}
instance : UpdatePure poFields ⟨"count", .u64⟩ updBump := {}
instance : NonInterfering poFields ⟨"id", .u64⟩ ⟨"count", .u64⟩
    updReset updBump := {}

def ladderChecks : CheckResult := do
  -- the autoParam'd slot was discharged at construction
  _ ← assertEq "boundedSeven.n" boundedSeven.n 7
  -- the locked composite RUNS: the reset+bump cascade over id=1,count=2
  -- yields id=0 (the reset), count=1 (the bump) — read back via the
  -- ColPath getters (RowVals is a GADT: no BEq to lean on)
  let row : RowVals poFields :=
    .cons (.u64 1) (.cons (.u64 2) .nil)
  let out := UpdateItem.cascade2 updReset updBump [row]
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
