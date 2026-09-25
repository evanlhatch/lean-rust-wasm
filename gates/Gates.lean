/-
Gates — the Lean-side gates driver (the pipeline-as-machine row,
notes/v3/09-gates-ops.md §3). The root aggregate of the thin skeleton.

- `Gates.Packages`   — the gated package set + the shared env loader
- `Gates.PackagesCheck` — the gated-table drift guard (the table ×
                       lakefile agreement both directions + every row
                       root's source file — a new library without its
                       gates row fails CI)
- `Gates.Common`     — the report-gate combinator (the write-or-diff
                       baseline tail with the loud re-baseline discipline)
- `Gates.Axioms`     — the per-library axiom sweep (kernel CollectAxioms,
                       LintKit's allowlist consumed, notes/axiom-report.md)
- `Gates.DocsCheck`  — the notes excerpt-drift gate (non-sketch lean
                       fences' decl names resolve in the gated envs)
- `Gates.GenCheck`   — the byte-tie gate (committed artifact bytes vs a
                       fresh `SchemaCore.regen`; volatile header exempt)
- `Gates.CodeRegistryCheck` — the persisted E-code registry gate
                       (notes/code-registry.txt: parse + well-formedness
                       + the allocation replay + self-stability + the
                       canonical bytes; notes/v3/05-codegen.md §4)
- `Gates.SnapshotCheck` — the universe-snapshot gate
                       (notes/universe.snapshot: the committed baseline
                       vs the fresh canonical render of the replayed
                       registry; notes/v3/03-bidirectional.md §7)
- `Gates.Audit`         — the artifact self-audit (09 §5: the AuditRule
                       list over every committed generated artifact)
- `Gates.ArtifactHeaders` — the 2-line GENERATED header presence +
                       shape over the artifact surface (the one-writer
                       rule's detection face)
- `Gates.NativePolicy`  — the native_decide grandfathering gate (the
                       committed allowlist set + the staleness ratchet)
- `Gates.Coverage`      — the Ty-ctor × emitter coverage matrix
                       (probe-differential; baseline notes/coverage-matrix.md)
- `Gates.KernelCheck`   — the lean4lean pure-kernel replay of every
                       gated module (the independent double-check)
- `Gates.Ownership`   — the artifact-ownership gate (D15: the
                       declared-vs-actual agreement both directions + the
                       cross-emitter disjointness over the REAL emitter set)
- `Gates.Breaking`    — the breaking gate (the committed universe snapshot
                       vs the replayed registry: the diff + the three-way
                       verdict + the exit-code discipline — unremedied = 2)
- `Gates.Impact`      — the impact-aware gating core (09 §6: the change
                       set → affected modules → artifacts → gates; the
                       conservatism theorems; the `impacted` driver)

The five questions (notes/v3/01-core.md): the registry answers none
directly — it is the gates machine's data row (09 §3): root = Universe
(the closed gate set, below), carrier = none, spine = the gate fold
(`all` runs the registry in order, first failure stops), ladder rung
n/a. Gate row: this IS the gate-row surface (the subcommands are the
rows).

The `all` driver runs each gate as a CHILD `lake exe gates <name>`
process, not in-process: the env-loading gates (axioms, native-policy,
coverage) each import every gated package's environment, and libgc's
conservative stack scan RETAINS a dropped env — in-process accumulation
peaked ~16GB RSS and earlyoom SIGTERM'd the whole run under memory
pressure (the legacy tree's sharded-mode lesson, arrived again at six
gated packages). One child per gate bounds the peak at the heaviest
single gate; `lake` is the in-tree spawn precedent (KernelCheck), the
subcommand interface is the justfile's rows verbatim.
-/
import Gates.Packages
import Gates.PackagesCheck
import Gates.Common
import Gates.Axioms
import Gates.DocsCheck
import Gates.GenCheck
import Gates.CodeRegistryCheck
import Gates.SnapshotCheck
import Gates.Audit
import Gates.ArtifactHeaders
import Gates.NativePolicy
import Gates.Coverage
import Gates.KernelCheck
import Gates.Ownership
import Gates.Breaking
import Gates.Impact

open Gates

/-- The closed gate set, in run order (the `all` driver's data — one
driver over the set, notes/v3/09-gates-ops.md §3). The dispatch lives
in GatesMain (the exe); this list is the single source of WHAT runs.
-/
def Gates.gateNames : List String :=
  ["packages-check", "axioms", "docs-check", "gen-check",
   "code-registry-check", "snapshot-check", "audit", "artifact-headers",
   "native-policy", "coverage", "kernel-check", "ownership", "breaking"]

/-- `gates all` — every registered gate in one run; the first failure
stops the machine. Each gate is a CHILD process (see the module header:
the per-gate RSS bound); the child's stdio is inherited so the report
streams live. -/
unsafe def Gates.runAll : IO UInt32 := do
  for name in Gates.gateNames do
    IO.println s!"══ gates all: {name} ══"
    let child ← IO.Process.spawn
      { cmd := "lake", args := #["exe", "gates", name]
      , stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    if code != 0 then
      IO.eprintln s!"gates all: {name} FAILED (exit {code})"
      return code
  IO.println "gates all: clean"
  return 0
