/-
# Ledger tests — the minimal gate files' driver

The scaffold's gate floor: positive + negative controls over the
scaffolded impl, elaboration-checked (`#guard` fails the BUILD on
drift, not just the run). Grow this into TestKit's discipline as the
project does: PropSpec sweeps with the MANDATORY negative control,
DiffSpec for differential gates (TestKit/README, notes/reuse-map.md).
-/
import Lean
import TestKit
import Ledger
import LedgerFn

-- Negative control first: the sentinel id → none.
#guard (LedgerImpl.ledger_get 0).isNone

-- Positive control: a real id → some (the record round-trips).
#guard (LedgerImpl.ledger_get 3).map (·.id) == some 3

-- The spec type survived the rename: the record exists with its fields.
#guard (LedgerImpl.ledger_get 1).map (·.label) == some "ledger"

def main : IO UInt32 := do
  IO.println "LedgerTests: guards green (elab-time)"
  return 0
