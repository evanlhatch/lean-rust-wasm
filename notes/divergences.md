# Divergences ledger — lean4lean (`gates kernel-check`) vs the C++ kernel

One row per observed disagreement between the pure-Lean kernel
(lean4lean, pinned in lean/gates/lakefile.toml) and the C++ kernel on a
gated module. Policy: **a divergence is investigated before the gate is
bypassed; an empty ledger = we looked.**

Known-gap class (NOT divergences, not recorded here): modules whose
proofs reduce through `reduceBool` — lean4lean does not support the
kernel extension `native_decide`'s trust base reduces through, so those
modules are expected failures, owned by the axiom gate's disclosed
`_native.native_decide.` trust bases. The list lives in
`Gates.KernelCheck.knownReduceBoolGaps`; the axiom allowlist is the
discovery mechanism for new entries.

| date | module | decl | kernel disagreement | resolution |
|---|---|---|---|---|

## First full sweep — 2026-09-17: zero kernel disagreements

15 gated packages swept (lean4lean rev 8223d223, whole-path non-fresh
mode). No module was REJECTED by the pure-Lean kernel. Four findings,
all investigated to harness/resource causes (not divergences, so not
ledgered above):

- `dbsp/Dbsp` and `schema-lang/SchemaLang` (the import-only root
  aggregates): SIGTERM-killed by earlyoom at 20–22GB RSS during the
  import replay. Non-fresh lean4lean checks only the target module's own
  declarations — the W5.4 roots declare none, so the check was vacuous
  while paying the full-closure environment load. Resolution: roots are
  now skipped with the import-only precondition verified in code
  (`Gates.KernelCheck.sourceHasDecls`); every declaration is replayed
  via the child modules.
- `feature-flags/Tests.Stress`, `wasm-backend/Tests.Axioms`,
  `wasm-backend/Tests.Audit`: same-named-module resolution artifacts —
  under `lake env`'s deps-first LEAN_PATH, lean4lean resolved the names
  into substrait's/Machines' trees where the oleans don't exist.
  Resolution: kernel-check spawns lean4lean with the package's OWN build
  dir first on LEAN_PATH; all three then replayed clean (verified
  individually before the fix landed).
