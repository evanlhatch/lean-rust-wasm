/-
Gates.Main — the `gates` exe: the subcommand table over Kit.Cli (C7's
one-driver discipline)

    lake exe gates <subcommand> [flags...]   — the table below
    lake exe gates --help                    — the GENERATED help
                       (the table is the one source — it cannot drift)

The gate rows and their flags (the shared three: --package=<dir> shard,
--write baseline, --accept-drift re-baseline; rows with extras name
them in their summary):

    packages-check                          — the gated-table drift guard
    lint          [--package=<dir>]         — the lint gate row
    axioms        [--write --accept-drift --package=<dir>]
                       — the axiom report (notes/axiom-report.md)
    docs-check    [--package=<dir>]         — the notes excerpt-drift +
                       gate-row honesty gate (the D33 durable fix)
    gen-check                               — the byte-tie gate (the artifacts)
    code-registry-check [--write]           — the persisted E-code registry
                       (STABLE allocation, 05 §4)
    snapshot-check [--write]                — the universe-snapshot gate
    audit                                   — the artifact self-audit
    artifact-headers                        — the GENERATED-header gate
    native-policy [--package=<dir>]         — the native_decide grandfathering gate
    coverage      [--write --accept-drift --strict]
                       — the Ty-ctor × emitter coverage matrix
    kernel-check                            — the lean4lean pure-kernel replay
    ownership                               — the artifact-ownership gate (D15)
    breaking                                — the breaking gate (the three-way verdict)
    impacted      [--print-only --paths=a,b] — the impact-aware dev loop (09 §6)
    decide-first-census [--write --accept-drift --package=<dir>]
    zero-citation-census [--write --accept-drift --package=<dir>]
    evidence-redundancy-census [--write --accept-drift --package=<dir>]
    nolint-census [--write --accept-drift]  — the silenced-site census
    legacy-hash   [--write --accept-drift]  — the legacy-immutability gate (B4)
    feasibility   [--write --accept-drift]  — the spec-sanity gate row (B2)
    elab-watch    [--write --accept-drift]  — the elaboration-time regression watch
    all                                     — every registered gate in one run

Dispatch + the shared flags + the help are Kit.Cli's (an unknown
subcommand/flag fails through the closed-world Diag — the did-you-mean
teeth). Handlers are `unsafe` (the gates import module environments at
runtime — the LintMain/Gates.Main pattern).

The five questions (notes/v3/01-core.md): none — the argv dispatch
shell over Gates' registry. Gate row: none — the exe is how the rows
run, not a row.
-/
import Kit.Cli
import Gates

/-! ## the shared-flag prelude (one copy) -/

/-- Parse the shared + row-local flags; a refusal renders the curated
Diag and exits through the verdict mapping — ONE copy. -/
unsafe def withFlags (extra : List String) (args : List String)
    (k : Kit.Cli.Flags → IO UInt32) : IO UInt32 := do
  match Kit.Cli.parseFlags extra args with
  | .error d =>
      IO.eprintln (Kit.Diag.toString d)
      return Kit.Cli.Verdict.finding.exit
  | .ok f => k f

/-! ## the handlers (the rows' bodies) -/

unsafe def runPackagesCheck (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.PackagesCheck.run

unsafe def runAxioms (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f =>
    Gates.Axioms.run f.write f.acceptDrift f.pkg

unsafe def runDocsCheck (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f => Gates.DocsCheck.run f.pkg

unsafe def runGenCheck (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.GenCheck.run

unsafe def runCodeRegistryCheck (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.CodeRegistryCheck.run f.write

unsafe def runSnapshotCheck (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.SnapshotCheck.run f.write

unsafe def runAudit (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.Audit.run

unsafe def runArtifactHeaders (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.ArtifactHeaders.run

unsafe def runNativePolicy (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f => Gates.NativePolicy.run f.pkg

unsafe def runCoverage (args : List String) : IO UInt32 :=
  withFlags ["strict"] args fun f =>
    Gates.Coverage.run f.write f.acceptDrift (f.has "strict")

unsafe def runKernelCheck (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.KernelCheck.run

unsafe def runOwnership (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.Ownership.run

unsafe def runBreaking (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.Breaking.run

unsafe def runImpacted (args : List String) : IO UInt32 :=
  withFlags ["print-only", "paths"] args fun f =>
    Gates.Impact.run (f.has "print-only")
      ((f.val "paths").map fun v =>
        (v.splitOn ",").map (·.trimAscii.toString) |>.filter (· != ""))

unsafe def runAll (args : List String) : IO UInt32 :=
  withFlags [] args fun _ => Gates.runAll

unsafe def runElabWatch (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.ElabWatch.run f.write f.acceptDrift

unsafe def runLint (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f => Gates.Lint.run f.pkg

unsafe def runDecideFirstCensus (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f =>
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
      f.write f.acceptDrift f.pkg

unsafe def runZeroCitationCensus (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f =>
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
      f.write f.acceptDrift f.pkg

unsafe def runEvidenceRedundancyCensus (args : List String) : IO UInt32 :=
  withFlags ["package"] args fun f =>
    Gates.Census.run Gates.Census.evidenceRedundancy
      "Evidence-redundancy census — carried-law re-proofs + weaker-than-kernel rows"
      "The census linter (linter.guestlang.evidenceRedundancy, 16-surface \
        §3 + D37): the entourage's first question — does the type already \
        carry it? — over the hand-written face. TWO detectable shapes: a \
        theorem whose statement is a carried law's own round-trip shape \
        (Codec.decode_encode / Iso.to_inv / Iso.inv_to, same instance both \
        sides) whose proof does not cite the law field; an obligation row \
        (Obligation/Discharged) whose claim is closed and Decidable- \
        synthesizable while the claimed backend is a LITERAL weaker tier \
        (oracleSwept/generatedCheck/guestVerified). FIRST ADJUDICATED RUN \
        (the B6 landing): the one false-positive class was the carried-law \
        fields' OWN declaration sites (the field decl IS the construction \
        — fixed by the name exemption in the test); Class B's fold was \
        empty (no weaker-than-kernel row in the buildable tree — the \
        honest zero; the fixture teeth prove the class fires). BOUNDARY: \
        this first run's tree was red in WasmCore.Decode (another lane's \
        in-flight work) — the packages whose env loads through it \
        (WasmCore, WasmCoreTestsLib, Gates, GatesTestsLib, Guest, \
        ComponentTestsLib, DemoApp, LedgerApp) are ABSENT below; their \
        sections arrive at the green re-baseline, and that drift is the \
        record of the blocked first run. The heuristic's limits are named \
        in its own header (unbounded claims, computed tiers, and the \
        sweep fn's carrier are invisible), so the census stays \
        CENSUS-GRADE (09 §8's rule): the findings are DATA, never \
        failures, and a drift is the deliberate re-baseline."
      f.write f.acceptDrift f.pkg

unsafe def runNolintCensus (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.NolintCensus.run f.write f.acceptDrift

unsafe def runLegacyHash (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.LegacyHash.run f.write f.acceptDrift

unsafe def runFeasibility (args : List String) : IO UInt32 :=
  withFlags [] args fun f => Gates.Feasibility.run f.write f.acceptDrift

/-! ## THE TABLE (the one source — the help is generated from it) -/

/-- The gates driver's about line (the pipeline-as-machine row). -/
def gatesAbout : String :=
  "The gates driver (the pipeline-as-machine row, notes/v3/09-gates-ops.md §3)."

unsafe def gateSubs : List Kit.Cli.Sub :=
  [ { name := "packages-check"
      summary := "The gated-table drift guard: every lakefile [[lean_lib]] must have its \
Gates.Packages row, every row must name a real library, and every row root's \
source file must exist (the single gated set: Gates.Packages' table)."
      run := runPackagesCheck }
  , { name := "lint"
      summary := "The lint gate row: the env/text linters over every gated package \
(--package=<dir> shards to one package); the row fails when any package has findings."
      run := runLint }
  , { name := "axioms"
      summary := "The per-library axiom report: every gated declaration's kernel axiom \
cone (CollectAxioms) checked against LintKit's allowlist; diffs against \
notes/axiom-report.md (--write updates the baseline; --accept-drift is the \
deliberate re-baseline for a non-empty diff; --package=<dir> shards)."
      run := runAxioms }
  , { name := "docs-check"
      summary := "The notes excerpt-drift gate: every ```lean fence in notes/*.md must \
resolve in the gated packages' environments (sketch fences are the PROPOSED-code \
marker) + the gate-row honesty scan (the D33 durable fix). --package=<dir> shards."
      run := runDocsCheck }
  , { name := "gen-check"
      summary := "The byte-tie gate: every emitted artifact's committed bytes vs a \
fresh regen (the volatile GENERATED-header lines exempt; the content-hash line \
must tie)."
      run := runGenCheck }
  , { name := "code-registry-check"
      summary := "The persisted E-code registry gate (notes/code-registry.txt): parses, \
is well-formed, REPLAYS as the allocation the discipline produces, is stable \
against itself, and is byte-canonical (--write bootstraps/canonicalizes — never \
an ill-formed or non-replayable file)."
      run := runCodeRegistryCheck }
  , { name := "snapshot-check"
      summary := "The universe-snapshot gate (notes/universe.snapshot): the committed \
baseline parses and byte-ties the fresh canonical render of the replayed \
registry (--write is the deliberate re-baseline)."
      run := runSnapshotCheck }
  , { name := "audit"
      summary := "The artifact self-audit (09 §5): every committed generated artifact \
scanned against the AuditRule list (no TODO/FIXME/unwrap(/dbg!/unsafe in \
generated output)."
      run := runAudit }
  , { name := "artifact-headers"
      summary := "The GENERATED-header gate: every committed generated artifact carries \
the 2-line GENERATED block (the marker + the spec/items/content-hash fields)."
      run := runArtifactHeaders }
  , { name := "native-policy"
      summary := "The native_decide grandfathering gate: native_decide use outside the \
committed allowlist FAILS and a STALE allowlist entry FAILS too (fail-closed \
both ways); one child process per gated package. --package=<dir> shards."
      run := runNativePolicy }
  , { name := "coverage"
      summary := "The Ty-ctor × emitter coverage matrix over the closed universe; diffs \
against notes/coverage-matrix.md (--write updates it; --accept-drift is the \
deliberate re-baseline; --strict promotes registry-quiet ctors to failures)."
      run := runCoverage }
  , { name := "kernel-check"
      summary := "The lean4lean pure-kernel replay: every gated module's own \
declarations re-checked by the independent Lean-4 kernel (pinned); builds the \
lean4lean exe on demand."
      run := runKernelCheck }
  , { name := "ownership"
      summary := "The artifact-ownership gate (D15): every file under the \
generated-artifact roots is DECLARED by some registered emitter (no orphans, no \
missing outputs, no cross-emitter collisions — Kit.Emit.outputsDisjoint); \
carries the duplicate-output fixture as its negative control."
      run := runOwnership }
  , { name := "breaking"
      summary := "The breaking gate (notes/universe.snapshot vs the replayed registry): \
the snapshot-pair diff + the three-way verdict + the exit-code discipline \
(clean=0, remedied=0 with the evidence named, unremedied=2 — the loud warning)."
      run := runBreaking }
  , { name := "impacted"
      summary := "The impact-aware dev loop (09 §6): the VCS change set (jj, fallback \
git) → affected modules → affected artifacts → ONLY their gates; any gap in the \
graph's knowledge widens to the FULL run. --print-only renders the verdict; \
--paths=a,b gives the manual change set."
      run := runImpacted }
  , { name := "decide-first-census"
      summary := "The decide-first census as a baselined report-gate (the axiom-report \
pattern): the linter's findings as DATA over every gated package, diffed against \
notes/decide-first-census.md (--write/--accept-drift/--package=<dir>)."
      run := runDecideFirstCensus }
  , { name := "zero-citation-census"
      summary := "The zero-citation census as a baselined report-gate (the axiom-report \
pattern): the linter's findings as DATA over every gated package, diffed against \
notes/zero-citation-census.md (--write/--accept-drift/--package=<dir>)."
      run := runZeroCitationCensus }
  , { name := "evidence-redundancy-census"
      summary := "The evidence-redundancy census as a baselined report-gate (B6; D37's \
teeth; the decide-first pattern): carried-law re-proofs + weaker-than-kernel \
obligation rows, as DATA over every gated package, diffed against \
notes/evidence-redundancy-census.md (--write/--accept-drift/--package=<dir>)."
      run := runEvidenceRedundancyCensus }
  , { name := "nolint-census"
      summary := "The nolint census gate: every @[nolint] row's (linter, file) count \
over the gated sources, baselined in notes/nolint-census.tsv \
(--write/--accept-drift — a new silenced site lands as a deliberate diff)."
      run := runNolintCensus }
  , { name := "legacy-hash"
      summary := "The legacy-immutability gate (B4): every file under legacy/ hashed \
against notes/legacy-surface.txt — any drift is a finding \
(--write is the FIRST-WRITE baseline; afterwards --accept-drift is required for \
a non-empty diff)."
      run := runLegacyHash }
  , { name := "feasibility"
      summary := "The spec-sanity gate row (B2; 04 §5 + D21): the registered specs' \
feasibility census (a proof-carrying witness, the declared emptiness, or the \
unchecked WARNING — never a silent pass), baselined in \
notes/feasibility-census.md (--write/--accept-drift)."
      run := runFeasibility }
  , { name := "elab-watch"
      summary := "The elaboration-time regression watch (09-gates-ops §7): every gated \
root's own elaboration re-timed and compared against notes/elab-baseline.tsv — \
over 2× baseline REGRESSES (--write/--accept-drift)."
      run := runElabWatch }
  , { name := "all"
      summary := "Every registered gate in one run (the gate registry's driver)."
      run := runAll } ]

unsafe def main (args : List String) : IO UInt32 :=
  Kit.Cli.run "gates" gatesAbout gateSubs none args
