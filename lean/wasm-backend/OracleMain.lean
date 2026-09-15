/-
# OracleMain — the differential oracle's driver (`lake exe oracle`)

The row universe + expected-value fold live in `Oracle` (the library —
testable, DiffSpec-covered); this exe is ONLY the emission loop. The
manifest prints to stdout as a JSON array; `just wasm-compile` pipes it
to `target/diff.json`, and steel-host's `wasm_diff` test replays it
against the emitted wasm (wasmtime AND wasmi, with the sabotage
control). Regenerated with the WAT so the manifest can never go stale
against the module it audits.

Ownership: this file owns the emission loop ONLY. Rows, resolution,
and the JSON row format: `Oracle.lean`. Never add rows here.
-/

import Oracle

def main : IO Unit := do
  let mut out := "["
  let mut first := true
  -- the row universe: the pinned grid + the LCG sweeps + the boundary
  -- sweep + the Gen supplement — appended, never spliced (the existing
  -- rows' bytes are the byte-tie invariant).
  for (fn, args) in rowUniverse do
    let expected := resultOf fn args
    if !first then out := out ++ ","
    first := false
    out := out ++ jsonRow fn args expected
  out := out ++ "]"
  IO.println out
