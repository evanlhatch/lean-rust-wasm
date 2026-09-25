/-
Gates.Main — the `gates` exe: subcommand dispatch (Cli)

    lake exe gates axioms [--write] [--accept-drift] — the axiom report
                       (the committed baseline notes/axiom-report.md; the
                       loud re-baseline discipline)
    lake exe gates docs-check            — the notes excerpt-drift + gate-row
                       honesty gate (the headers' gate-row claims vs
                       Gates.Packages — the D33 durable fix)
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

unsafe def runPackagesCheck (_p : Parsed) : IO UInt32 := Gates.PackagesCheck.run

unsafe def runAxioms (p : Parsed) : IO UInt32 :=
  Gates.Axioms.run (p.hasFlag "write") (p.hasFlag "accept-drift")
    ((p.flag? "package").map fun f => f.value)

unsafe def runDocsCheck (p : Parsed) : IO UInt32 :=
  Gates.DocsCheck.run ((p.flag? "package").map fun f => f.value)

unsafe def runGenCheck (_p : Parsed) : IO UInt32 := Gates.GenCheck.run

unsafe def runCodeRegistryCheck (p : Parsed) : IO UInt32 :=
  Gates.CodeRegistryCheck.run (p.hasFlag "write")

unsafe def runSnapshotCheck (p : Parsed) : IO UInt32 :=
  Gates.SnapshotCheck.run (p.hasFlag "write")

unsafe def runAudit (_p : Parsed) : IO UInt32 := Gates.Audit.run

unsafe def runArtifactHeaders (_p : Parsed) : IO UInt32 := Gates.ArtifactHeaders.run

unsafe def runNativePolicy (p : Parsed) : IO UInt32 :=
  Gates.NativePolicy.run ((p.flag? "package").map fun f => f.value)

unsafe def runCoverage (p : Parsed) : IO UInt32 :=
  Gates.Coverage.run (p.hasFlag "write") (p.hasFlag "accept-drift") (p.hasFlag "strict")

unsafe def runKernelCheck (_p : Parsed) : IO UInt32 := Gates.KernelCheck.run

unsafe def runOwnership (_p : Parsed) : IO UInt32 := Gates.Ownership.run

unsafe def runBreaking (_p : Parsed) : IO UInt32 := Gates.Breaking.run

unsafe def runImpacted (p : Parsed) : IO UInt32 :=
  Gates.Impact.run (p.hasFlag "print-only")
    ((p.flag? "paths").map fun f =>
      (f.value.splitOn ",").map (·.trimAscii.toString) |>.filter (· != ""))

unsafe def runAll (_p : Parsed) : IO UInt32 := Gates.runAll

unsafe def runElabWatch (p : Parsed) : IO UInt32 :=
  Gates.ElabWatch.run (p.hasFlag "write") (p.hasFlag "accept-drift")

unsafe def runLint (p : Parsed) : IO UInt32 :=
  Gates.Lint.run ((p.flag? "package").map fun f => f.value)

unsafe def runDecideFirstCensus (p : Parsed) : IO UInt32 :=
  Gates.Census.run Gates.Census.decideFirst
    "Decide-first census — hand scripts over decidable closed finite spaces"
    "The census linter (linter.guestlang.decideFirst, 04 §1): a theorem whose \
      statement is decidable over a closed finite space yet whose proof term \
      depends on non-computational lemmas. FIRST ADJUDICATED RUN (the \
      enforcement wave): every finding is the heuristic's own false-positive \
      class — theorems PROVED BY rfl whose elaborated term routes through \
      non-computational casts (the proof-side approximation's blindness), and \
      quantified-hypothesis statements the statement-side synthesizable- \
      Decidable filter lets through (not actually closed spaces). The findings \
      are DATA (the promotion, not a hard gate — 09 §8's rule: the census's \
      limits are named in its own header, so it stays census-grade); a drift \
      (a new finding, or one adjudicated away) is the deliberate re-baseline."
    (p.hasFlag "write") (p.hasFlag "accept-drift")
    ((p.flag? "package").map fun f => f.value)

unsafe def runZeroCitationCensus (p : Parsed) : IO UInt32 :=
  Gates.Census.run Gates.Census.zeroCitation
    "Zero-citation census — the proof-level leftover rule"
    "The census linter (linter.guestlang.zeroCitation): a theorem referenced \
      nowhere outside its own module. FIRST ADJUDICATED RUN (the enforcement \
      wave): the finding set is the LAW-LIBRARY class — the theorem layer ships \
      as API (Kit.Iso/Rel/Obligation's laws, the lanes' consumed-in-module \
      helpers), and mechanically it is INDISTINGUISHABLE from dead code (the \
      census's named limit; the ~130 reasoned @[nolint] rows cover only the \
      sites the earlier adjudication touched). So the census stays CENSUS-GRADE \
      (09 §8's rule): the findings are DATA, never failures, and the DRIFT LINES \
      are the review queue — every new uncited theorem shows up as a deliberate \
      re-baseline diff naming it (fixed, consumed, or the reasoned opt-out)."
    (p.hasFlag "write") (p.hasFlag "accept-drift")
    ((p.flag? "package").map fun f => f.value)

unsafe def runNolintCensus (p : Parsed) : IO UInt32 :=
  Gates.NolintCensus.run (p.hasFlag "write") (p.hasFlag "accept-drift")

unsafe def runLegacyHash (p : Parsed) : IO UInt32 :=
  Gates.LegacyHash.run (p.hasFlag "write") (p.hasFlag "accept-drift")

unsafe def runFeasibility (p : Parsed) : IO UInt32 :=
  Gates.Feasibility.run (p.hasFlag "write") (p.hasFlag "accept-drift")

unsafe def packagesCheckCmd : Cmd := `[Cli|
  "packages-check" VIA runPackagesCheck; ["0.1.0"]
  "The gated-table drift guard: every lakefile [[lean_lib]] must have its \\n   Gates.Packages row (a new library without its gates row fails CI), \\n   every row must name a real library, and every row root's source file \\n   must exist. The single gated set: Gates.Packages' table."
]

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
    package : String; "Shard: scan ONE gated package (--package=<dir>, the \
      child dispatch's own body; its report block is its stdout)."
]

unsafe def docsCheckCmd : Cmd := `[Cli|
  "docs-check" VIA runDocsCheck; ["0.1.0"]
  "The notes excerpt-drift gate: every ```lean fence in notes/*.md (one \
   level of subdirectories included) must have its declared top-level names \
   resolve in the gated packages' environments; fences of PROPOSED code tag \
   themselves ```lean sketch (the marker convention — the fence is the truth \
   about what is a sketch). Plus the gate-row honesty scan (the D33 durable \
   fix): a header claiming a library is outside Gates.Packages' gated set \
   while that library HAS a row is a finding. Requires build."

  FLAGS:
    package : String;  "Shard: resolve against ONE gated package \
      (--package=<dir>, the child dispatch's own body; prints the \
      pending names that resolve in that package's env)."
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

unsafe def impactedCmd : Cmd := `[Cli|
  "impacted" VIA runImpacted; ["0.1.0"]
  "The impact-aware dev loop (09 §6): the VCS change set (jj, fallback \
   git) → affected modules (the import-closure walk) → affected \
   artifacts (the ledger's forward query) → ONLY their gates. Any gap \
   in the graph's knowledge widens to the FULL run — the affected set \
   never under-reports."

  FLAGS:
    "print-only";  "Print the verdict without running the gates."
    paths;         "The manual change set: comma-separated paths (overrides the VCS diff)."
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
  "The native_decide grandfathering gate: every gated declaration's axiom \\n   cone scanned for the `_native.native_decide.` trust base; uses outside \\n   the committed allowlist set FAIL, and a STALE allowlist entry (a module \\n   that no longer depends on native_decide) FAILS too — the ratchet is \\n   fail-closed both ways. Runs one child process per gated package (the \\n   memory discipline). Requires build."

  FLAGS:
    package : String;  "Shard: scan ONE gated package (--package=<dir>, the \
      child dispatch's own body)."
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

unsafe def lintCmd : Cmd := `[Cli|
  "lint" VIA runLint; ["0.1.0"]
  "The lint gate row: the env/text linters over every gated package (the \\\n   lintkit exe's own shard fold), the row failing when any package has \\\n   findings. The tree must be lint-clean; the named @[nolint]/allowance \\\n   rows are the honest opt-outs. Requires build."

  FLAGS:
    package : String;  "Shard: lint ONE gated package (--package=<dir>, the \\\n      child dispatch's own body)."
]

unsafe def decideFirstCensusCmd : Cmd := `[Cli|
  "decide-first-census" VIA runDecideFirstCensus; ["0.1.0"]
  "The decide-first census promoted to a baselined report-gate (the \\\n   axiom-report pattern): the census linter's findings as DATA over every \\\n   gated package, the fresh render diffed against notes/decide-first-census.md. \\\n   Requires build."

  FLAGS:
    write;            "Update the committed baseline instead of diffing it."
    "accept-drift";   "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY diff."
    package : String; "Shard: ONE gated package (--package=<dir>)."
]

unsafe def zeroCitationCensusCmd : Cmd := `[Cli|
  "zero-citation-census" VIA runZeroCitationCensus; ["0.1.0"]
  "The zero-citation census promoted to a baselined report-gate (the \\\n   axiom-report pattern): the census linter's findings as DATA over every \\\n   gated package, the fresh render diffed against notes/zero-citation-census.md. \\\n   Requires build."

  FLAGS:
    write;            "Update the committed baseline instead of diffing it."
    "accept-drift";   "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY diff."
    package : String; "Shard: ONE gated package (--package=<dir>)."
]

unsafe def nolintCensusCmd : Cmd := `[Cli|
  "nolint-census" VIA runNolintCensus; ["0.1.0"]
  "The nolint census gate: every @[nolint] row's (linter, file) count over \\\n   the gated sources, baselined in notes/nolint-census.tsv — a new silenced \\\n   site lands as a deliberate re-baseline diff, never silently."

  FLAGS:
    write;          "Update the committed baseline instead of diffing it."
    "accept-drift"; "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY diff."
]

unsafe def legacyHashCmd : Cmd := `[Cli|
  "legacy-hash" VIA runLegacyHash; ["0.1.0"]
  "The legacy-immutability gate (B4): every file under legacy/ (the \
   read-only pre-v3 mining source) hashed against the committed baseline \
   notes/legacy-surface.txt — a drift (any byte changed, any file added \
   or removed) is a finding. The read-only discipline's mechanical tooth. \
   Carries its sabotage controls in GatesTests (a content tamper, a path \
   rename, an added and a dropped file each MUST change the surface)."

  FLAGS:
    write;          "The row's FIRST-WRITE baseline (a new row's baseline \
      is not a re-baseline); afterwards the loud re-baseline discipline \
      applies (--accept-drift required for a non-empty diff)."
    "accept-drift"; "Deliberate re-baseline: allow --write to overwrite a \
      NON-EMPTY diff."
]

unsafe def feasibilityCmd : Cmd := `[Cli|
  "feasibility" VIA runFeasibility; ["0.1.0"]
  "The spec-sanity gate row (B2; 04 §5 + D21): the registered specs' \
   feasibility census — every contract/spec with a precondition answers \
   the feasibility obligations (a proof-carrying witness, the declared \
   emptiness, or the unchecked WARNING — never a silent pass); the \
   contracts rows ride Contracts.Feasibility's proof-carrying face, the \
   machines rows CITE the battery's non-vacuity verdicts. The census is \
   census-grade: the findings are DATA, baselined in \
   notes/feasibility-census.md, drift flagged. The teeth: a planted \
   vacuous contract has NO admissible input (vacuousC_no_witness), so \
   its honest row is the visible declared-empty cell."

  FLAGS:
    write;          "The row's FIRST-WRITE baseline (a new row's baseline \
      is not a re-baseline); afterwards the loud re-baseline discipline \
      applies (--accept-drift required for a non-empty diff)."
    "accept-drift"; "Deliberate re-baseline: allow --write to overwrite a \
      NON-EMPTY diff."
]

unsafe def elabWatchCmd : Cmd := `[Cli|
  "elab-watch" VIA runElabWatch; ["0.1.0"]
  "The elaboration-time regression watch (notes/v3/09-gates-ops.md §7): \n   every gated root's own elaboration re-timed (imports ride the committed \n   oleans) and compared against the committed baseline notes/elab-baseline.tsv \n   — a module over 2× its baseline REGRESSES (the finding); small drifts \n   pass; new roots enter the baseline deliberately; stale rows fail. \n   Requires build."

  FLAGS:
    write;          "The deliberate re-baseline: write the fresh measured \n      rows and commit."
    "accept-drift"; "Deliberate re-baseline: allow --write to overwrite a NON-EMPTY \n      diff (a drifted baseline). Without it --write REFUSES any non-empty \n      diff — a re-baseline must not pre-authorize future taint."
]

unsafe def gatesCmd : Cmd := `[Cli|
  "gates" NOOP; ["0.1.0"]
  "The gates driver (the pipeline-as-machine row, notes/v3/09-gates-ops.md §3)."

  SUBCOMMANDS: packagesCheckCmd; lintCmd; axiomsCmd; docsCheckCmd; genCheckCmd; codeRegistryCheckCmd; snapshotCheckCmd; auditCmd; artifactHeadersCmd; nativePolicyCmd; coverageCmd; kernelCheckCmd; ownershipCmd; breakingCmd; impactedCmd; decideFirstCensusCmd; zeroCitationCensusCmd; nolintCensusCmd; legacyHashCmd; feasibilityCmd; elabWatchCmd; allCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  gatesCmd.validate args
