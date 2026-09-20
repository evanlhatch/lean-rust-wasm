/-
# Gates — the Lean-side gates driver (the pipeline-as-machine row)

The root aggregate. Canon row: "the build pipeline itself = a machine"
(notes/canon.md) — this package is the Lean half of that machine, with
TYPED access to what the justfile recipes used to grep/subprocess:

- `Gates.GenCheck`    — the stripped byte-tie (in-process regen + compare)
- `Gates.Axioms`      — the global axiom report (kernel CollectAxioms,
                        LintKit's allowlist consumed, notes/axiom-report.md)
- `Gates.Manifest`    — lakefile ↔ manifest drift (structural, offline)
- `Gates.Coverage`   — the Ty × emitter × oracle coverage matrix
                        (probe-differential; notes/coverage-matrix.md)
- `Gates.ObligationCheck` — the oracle-ref resolution gate (W9.x: every
                        claimed `Evidence.oracleRow` ref resolves to an
                        actual oracle row — the ladder's last rung,
                        armed AND fired)
- `Gates.KernelCheck` — the lean4lean double-check (pure-Lean kernel replay)
- `Gates.NativePolicy`— the native_decide grandfathering gate (W9.7 /
                        design-guest-verified.md §6.3)
- `Gates.ArtifactManifest` — the committed artifacts' inventory
                        (every emitter's outputs → path × content hash;
                        additive to the byte-tie)
- `Gates.Audit`       — the static census (zero-consumer candidates,
                        comment ratio, the hand-roll citation) — report-only

Legacy (non-module) files by design — the drivers touch meta
env-extension state (constraint 12, notes/w5-4-module-migration.md).
-/
import Gates.Packages
import Gates.Common
import Gates.GenCheck
import Gates.Axioms
import Gates.Manifest
import Gates.Coverage
import Gates.ObligationCheck
import Gates.KernelCheck
import Gates.NativePolicy
import Gates.ArtifactManifest
import Gates.Audit
