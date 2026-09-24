/-
Gates.Main — the `gates` exe: subcommand dispatch (Cli)

    lake exe gates axioms [--write] [--accept-drift] — the axiom report
                       (the committed baseline notes/axiom-report.md; the
                       loud re-baseline discipline)
    lake exe gates docs-check            — the notes excerpt-drift gate
    lake exe gates gen-check             — the byte-tie gate (the artifacts)
    lake exe gates code-registry-check [--write]
                         — the persisted E-code registry (the allocation
                           history; STABLE allocation, 05 §4)
    lake exe gates all                   — every registered gate in one run

Cli parses argv (hyphenated subcommand names via the string form of
`literalIdent`). Handlers are `unsafe` (the gates import module
environments at runtime — the LintMain/Gates.Main pattern).

The five questions (notes/v3/01-core.md): none — the argv dispatch
shell over Gates' registry. Gate row: none — the exe is how the rows
run, not a row.
-/
import Cli
import Gates

open Cli

unsafe def runAxioms (p : Parsed) : IO UInt32 :=
  Gates.Axioms.run (p.hasFlag "write") (p.hasFlag "accept-drift")

unsafe def runDocsCheck (_p : Parsed) : IO UInt32 := Gates.DocsCheck.run

unsafe def runGenCheck (_p : Parsed) : IO UInt32 := Gates.GenCheck.run

unsafe def runCodeRegistryCheck (p : Parsed) : IO UInt32 :=
  Gates.CodeRegistryCheck.run (p.hasFlag "write")

unsafe def runSnapshotCheck (p : Parsed) : IO UInt32 :=
  Gates.SnapshotCheck.run (p.hasFlag "write")

unsafe def runAudit (_p : Parsed) : IO UInt32 := Gates.Audit.run

unsafe def runArtifactHeaders (_p : Parsed) : IO UInt32 := Gates.ArtifactHeaders.run

unsafe def runNativePolicy (_p : Parsed) : IO UInt32 := Gates.NativePolicy.run

unsafe def runCoverage (p : Parsed) : IO UInt32 :=
  Gates.Coverage.run (p.hasFlag "write") (p.hasFlag "accept-drift") (p.hasFlag "strict")

unsafe def runKernelCheck (_p : Parsed) : IO UInt32 := Gates.KernelCheck.run

unsafe def runOwnership (_p : Parsed) : IO UInt32 := Gates.Ownership.run

unsafe def runBreaking (_p : Parsed) : IO UInt32 := Gates.Breaking.run

unsafe def runAll (_p : Parsed) : IO UInt32 := Gates.runAll

unsafe def axiomsCmd : Cmd := `[Cli|
  "axioms" VIA runAxioms; ["0.1.0"]
  "The per-library axiom report: every gated package declaration's kernel \
   axiom cone (CollectAxioms) checked against LintKit's allowlist \
   (consumed, not re-encoded); diffs against notes/axiom-report.md."

  FLAGS:
    write;            "Update the committed notes/axiom-report.md instead of diffing it."
    "accept-drift";   "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY diff \
      (a drifted report). Without it --write REFUSES any non-empty diff — \
      a re-baseline must not pre-authorize future taint (the baseline discipline)."
]

unsafe def docsCheckCmd : Cmd := `[Cli|
  "docs-check" VIA runDocsCheck; ["0.1.0"]
  "The notes excerpt-drift gate: every ```lean fence in notes/*.md (one \
   level of subdirectories included) must have its declared top-level names \
   resolve in the gated packages' environments; fences of PROPOSED code tag \
   themselves ```lean sketch (the marker convention — the fence is the truth \
   about what is a sketch). Requires build."
]

unsafe def genCheckCmd : Cmd := `[Cli|
  "gen-check" VIA runGenCheck; ["0.1.0"]
  "The byte-tie gate: every emitted artifact's committed bytes vs a fresh \
   regen (the volatile GENERATED-header lines exempt; the content-hash \
   line must tie). Requires build."
]

unsafe def codeRegistryCheckCmd : Cmd := `[Cli|
  "code-registry-check" VIA runCodeRegistryCheck; ["0.1.0"]
  "The persisted E-code registry gate (notes/code-registry.txt): the file \
   parses, is well-formed, REPLAYS as the allocation the discipline \
   produces (a hand-edited code fails), is stable against itself, and is \
   byte-canonical."

  FLAGS:
    write;          "The deliberate allocation step: bootstrap an absent \
      registry (the empty history) and canonicalize formatting — never an \
      ill-formed or non-replayable file (the content checks run first)."
]

unsafe def ownershipCmd : Cmd := `[Cli|
  "ownership" VIA runOwnership; ["0.1.0"]
  "The artifact-ownership gate (D15): every committed-or-not file under \n   the generated-artifact roots (gen/, the generated crate's Rust dirs) \n   must be DECLARED by some registered emitter (an undeclared file is an \n   ORPHAN — the invisible squatter), every declared output must exist \n   (absent = MISSING), and the real emitter set's declared outputs must \n   be pairwise disjoint (Kit.Emit.outputsDisjoint over the real set). \n   Carries a duplicate-output fixture as its negative control — fail \n   closed. Requires build."
]

unsafe def breakingCmd : Cmd := `[Cli|
  "breaking" VIA runBreaking; ["0.1.0"]
  "The breaking gate (notes/universe.snapshot vs the replayed registry): \n   the snapshot-pair diff (the net change over the name key) + the \n   three-way verdict + the exit-code discipline (clean=0, remedied=0 \n   with the evidence named, unremedied=2 — the loud warning). Requires build."
]

unsafe def allCmd : Cmd := `[Cli|
  "all" VIA runAll; ["0.1.0"]
  "Every registered gate in one run (the gate registry's driver)."
]

unsafe def auditCmd : Cmd := `[Cli|
  "audit" VIA runAudit; ["0.1.0"]
  "The artifact self-audit (09 §5): every committed generated artifact \\n   scanned against the AuditRule list (no TODO/FIXME/unwrap(/dbg!/unsafe \\n   in generated output); the observability-inheritance row is noted, not \\n   built — no host-code generator exists yet. Requires build."
]

unsafe def artifactHeadersCmd : Cmd := `[Cli|
  "artifact-headers" VIA runArtifactHeaders; ["0.1.0"]
  "The GENERATED-header gate: every committed generated artifact carries \\n   the 2-line GENERATED block (line 0 the `// GENERATED by … DO NOT EDIT` \\n   marker, line 1 the spec/items/content-hash fields). A headerless file \\n   at a declared artifact path is a hand-written file squatting on the \\n   one-writer rule. Requires build."
]

unsafe def nativePolicyCmd : Cmd := `[Cli|
  "native-policy" VIA runNativePolicy; ["0.1.0"]
  "The native_decide grandfathering gate: every gated declaration's axiom \\n   cone scanned for the `_native.native_decide.` trust base; uses outside \\n   the committed allowlist set FAIL, and a STALE allowlist entry (a module \\n   that no longer depends on native_decide) FAILS too — the ratchet is \\n   fail-closed both ways. Requires build."
]

unsafe def coverageCmd : Cmd := `[Cli|
  "coverage" VIA runCoverage; ["0.1.0"]
  "The Ty-ctor × emitter coverage matrix: probe-differential cells over \\n   the closed universe (a byte-colliding ctor renders `.`) + the committed \\n   registry's exercise column; diffs against notes/coverage-matrix.md. \\n   Requires build."

  FLAGS:
    write;          "Update the committed notes/coverage-matrix.md instead of diffing it."
    "accept-drift"; "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY diff."
    strict;         "Promote registry-quiet ctors (unexercised members of the closed \
      universe) from findings to failures."
]

unsafe def kernelCheckCmd : Cmd := `[Cli|
  "kernel-check" VIA runKernelCheck; ["0.1.0"]
  "The lean4lean pure-kernel replay: every gated module's own declarations \\n   re-checked by the independent Lean-4 kernel (github.com/digama0/lean4lean, \\n   pinned). Builds the lean4lean exe on demand. Requires build."
]

unsafe def snapshotCheckCmd : Cmd := `[Cli|
  "snapshot-check" VIA runSnapshotCheck; ["0.1.0"]
  "The universe-snapshot gate (notes/universe.snapshot): the committed \n   baseline parses and byte-ties the fresh canonical render of the \n   replayed registry (the breaking gate's substrate)."

  FLAGS:
    write;          "The deliberate re-baseline: write the fresh canonical \n      bytes and commit."
]

unsafe def gatesCmd : Cmd := `[Cli|
  "gates" NOOP; ["0.1.0"]
  "The gates driver (the pipeline-as-machine row, notes/v3/09-gates-ops.md §3)."

  SUBCOMMANDS: axiomsCmd; docsCheckCmd; genCheckCmd; codeRegistryCheckCmd; snapshotCheckCmd; auditCmd; artifactHeadersCmd; nativePolicyCmd; coverageCmd; kernelCheckCmd; ownershipCmd; breakingCmd; allCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  gatesCmd.validate args
