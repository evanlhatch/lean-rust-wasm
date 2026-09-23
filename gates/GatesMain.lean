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

unsafe def allCmd : Cmd := `[Cli|
  "all" VIA runAll; ["0.1.0"]
  "axioms + docs-check + gen-check in one run (the gate registry's driver)."
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

  SUBCOMMANDS: axiomsCmd; docsCheckCmd; genCheckCmd; codeRegistryCheckCmd; snapshotCheckCmd; allCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  gatesCmd.validate args
