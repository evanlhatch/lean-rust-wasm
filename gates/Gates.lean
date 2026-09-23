/-
Gates — the Lean-side gates driver (the pipeline-as-machine row,
notes/v3/09-gates-ops.md §3). The root aggregate of the thin skeleton.

- `Gates.Packages`   — the gated package set + the shared env loader
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

The five questions (notes/v3/01-core.md): the registry answers none
directly — it is the gates machine's data row (09 §3): root = Universe
(the closed gate set, below), carrier = none, spine = the gate fold
(`all` runs the registry in order, first failure stops), ladder rung
n/a. Gate row: this IS the gate-row surface (the subcommands are the
rows).
-/
import Gates.Packages
import Gates.Common
import Gates.Axioms
import Gates.DocsCheck
import Gates.GenCheck
import Gates.CodeRegistryCheck
import Gates.SnapshotCheck

open Gates

/-- The gate registry: every gate's name + its run (the `all` driver's
data — one driver over the registry, notes/v3/09-gates-ops.md §3). -/
unsafe def Gates.gateRegistry : List (String × (IO UInt32)) := [
  ("axioms", Gates.Axioms.run false false),
  ("docs-check", Gates.DocsCheck.run),
  ("gen-check", Gates.GenCheck.run),
  ("code-registry-check", Gates.CodeRegistryCheck.run false),
  ("snapshot-check", Gates.SnapshotCheck.run false)
]

/-- `gates all` — every registered gate in one run; the first failure
stops the machine. -/
unsafe def Gates.runAll : IO UInt32 := do
  for (name, run) in Gates.gateRegistry do
    IO.println s!"══ gates all: {name} ══"
    let code ← run
    if code != 0 then
      IO.eprintln s!"gates all: {name} FAILED"
      return code
  IO.println "gates all: clean"
  return 0
