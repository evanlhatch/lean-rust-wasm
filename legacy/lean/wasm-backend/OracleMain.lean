/-
# OracleMain — the differential oracle's driver (`lake exe oracle`)

The row universe + expected-value fold live in `Oracle` (the library —
testable, DiffSpec-covered); this exe is ONLY the emission loop. The
manifest prints to stdout as a JSON array; `just wasm-compile` pipes it
to `artifact/diff.json`, and steel-host's `wasm_diff` test replays it
against the emitted wasm (wasmtime AND wasmi, with the sabotage
control). Regenerated with the WAT so the manifest can never go stale
against the module it audits.

CLI (W6.3 phase 2 — ADDITIVE; the no-arg manifest bytes are the
byte-tie invariant, NEVER changed by the subcommands):
- `lake exe oracle` — the manifest (byte-frozen).
- `lake exe oracle schema-surface` — the canonical schema surface
  string (the schema hash = sha256 of it, computed consumer-side).
- `lake exe oracle coverage` — COVERAGE.md's content (the feature →
  test map; the emitter is pure `Oracle.coverageMd`).
- `lake exe oracle verdict FN ARG... --observed VALUE` — the VERDICT:
  Lean resolves the expected outcome (the authority), judges the
  observed value through `CompareMode.verdict`, prints the verdict JSON
  (pass, or the first-divergence triple + class + schema echo).
  `--observed @trap` = the replay trapped. This is the debug loop's
  Lean half (oracle-runner's `--explain` calls it).

Ownership: this file owns the emission loop ONLY. Rows, resolution,
verdicts, and the JSON formats: `Oracle.lean`. Never add rows here.
-/

import Oracle

/-- The manifest emission (the byte-frozen path — unchanged from
    phase 1). -/
def emitManifest : IO Unit := do
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

/-- `verdict FN ARG... --observed VALUE`: the observed side of the
    comparison arrives as the CLI tail (one argv element — the ser
    forms contain spaces; `@trap` = the replay trapped). -/
def emitVerdict (rest : List String) : IO Unit := do
  -- split FN ARG... from --observed VALUE... (manual walk — the
  -- observed payload is everything after the flag, space-joined)
  let (head, tail) := rest.span (· != "--observed")
  match head, tail with
  | fn :: args, _ :: observed =>
    let observedStr := String.intercalate " " observed
    let obs : Outcome :=
      if observedStr == "@trap" then { error := some .trap, payload := "" }
      else { error := none, payload := observedStr }
    let expected := resolveOutcome fn args
    IO.println (jsonVerdict ((modeOf fn).verdict expected obs))
  | _, _ =>
    IO.eprintln "usage: oracle verdict FN ARG... --observed VALUE|@trap"
    IO.Process.exit 2

def main (args : List String) : IO Unit := do
  match args with
  | [] => emitManifest
  | ["schema-surface"] => IO.println schemaSurface
  | ["coverage"] => IO.print coverageMd
  | "verdict" :: rest => emitVerdict rest
  | _ => do
    IO.eprintln "usage: oracle [schema-surface|coverage|verdict FN ARG... --observed VALUE|@trap]"
    IO.Process.exit 2
