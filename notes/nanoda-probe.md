# nanoda probe — the external-kernel double-check

Date: 2026 (probe session). Spike root: `/tmp/nanoda-spike/` (lean4export clone,
nanoda_lib clone, the kit export, the config). The tree was not modified
except this note; no jj/git state touched; no gate baseline re-written.

## The question

The kernel-check gate replays gated modules through lean4lean — one
independent kernel. nanoda (ammkrn/nanoda_lib, Rust) is a SECOND kernel
from a different implementation lineage. If nanoda accepts the tree's
kernel-checked content, the gate's independence claim strengthens from
"one external re-check" to "two agreeing kernels with disjoint codebases".

## Q1 — toolchain compat: lean4export on the tree's v4.33.0

**PASS.** lean4export's pin is `v4.35.0-rc3`; the tree pins `v4.33.0`.
Cloned lean4export to the spike, overwrote its `lean-toolchain` with
`leanprover/lean4:v4.33.0`, `lake build` clean in 29s (6 jobs, no
source changes, no 4.35-only features exercised). The export ran with the
tree's own toolchain binaries.

Evidence: `/tmp/nanoda-spike/lean4export/` builds and runs on v4.33.0.

## Q2 — nanoda builds with the devenv cargo

**PASS, one fetch caveat.** `cargo build --release` with the devenv
profile (`legacy/.devenv/profiles/wasm/profile/bin`) built nanoda v0.4.19
in ~26s. Dependencies (serde/serde_json, num-bigint, indexmap,
rustc-hash, semver) required one online `cargo fetch` (~60s) — the local
cargo cache did NOT contain them. After fetch, `--offline` builds clean.

Evidence: `/tmp/nanoda-spike/nanoda_lib/target/release/nanoda_bin`.

## Q3 — exporting Kit

**PASS.** `lake build Kit` (already built, 45 jobs), then
`lake env lean4export Kit` — exit 0 in ~101s. Output:
`/tmp/nanoda-spike/kit.ndjson` — 13,646,419 lines, 772 MB (exporter
reports format version 3.1.0). The size is Kit's full transitive
closure — Kit imports the whole standard-library surface it touches.

## Q4 — the check against the tree's own allowlist

**PASS.** The tree's axiom gate allowlist (`notes/axiom-report.md`,
`LintKit.AxiomAllowlist`): propext, Classical.choice, Quot.sound, plus
the disclosed `_native.native_decide`/`_native.bv_decide` trust bases.
The export's 7 axiom declarations resolve to exactly:

    propext, Quot.sound, Classical.choice   — the core triple
    Lean.trustCompiler, Lean.ofReduceBool, Lean.ofReduceNat — the native_decide trust bases
    sorryAx                                  — declared by the prelude, never used

Config (`/tmp/nanoda-spike/nanoda-kit.json`): `permitted_axioms` = triple
+ the three trust bases (mirroring the tree's disclosed list);
`sorryAx` left UNPERMITTED with `unpermitted_axiom_hard_error: false` —
so any actual sorry *use* would hard-error the run. The gate's zero-sorry
rule is thus independently re-tested, not just the triple.

## Q5 — the verdict

**AGREEMENT.**

    Checked 174918 declarations with no typechecker errors
    exit 0, wall ~116s

nanoda accepted every declaration in Kit's transitive closure — the same
content the tree's own kernel and the lean4lean gate lane accept. The
only diagnostic was a harmless pretty-printer note ("Unable to print
axioms"; no pp_declars were requested). Exit 0 with sorryAx unpermitted
also confirms no declaration in the closure actually invokes sorryAx.

Operational caveat found during the run: nanoda overflowed the default
8 MB main-thread stack on the first attempt (deep recursion over the
13.6M-line export). The rerun under `ulimit -s unlimited` succeeded in
the same wall time. Any adoption must pin the stack limit.

## Adoption path — the kernel-check row's second lane

The kernel-check gate row gains a second face: a gated module passes
only when BOTH lanes agree —

1. the lean4lean lane (existing) — Lean-native kernel replay;
2. the nanoda lane (new) — lean4export NDJSON → nanoda with
   `permitted_axioms` generated FROM `LintKit.AxiomAllowlist` (the
   gate's axiom data IS the config — no parallel table; the
   patterns-catalog rule holds: this is the same allowlist, consumed by
   a second reader).

Mechanics per gated module M:
- `lake env lean4export M > export.ndjson` (toolchain-pinned binary);
- `nanoda_bin config.json` with the allowlist-derived config;
- gate fails on nonzero exit.

## Costs (honest)

- **Export toolchain discipline**: the lean4export checkout must be
  pinned to the TREE's toolchain (v4.33.0 today), not upstream's pin —
  a kernel/version skew between exporter and tree would invalidate the
  lane. One `lean-toolchain` overwrite in the spike clone; an adopted
  lane should vendor the exporter with the tree's pin.
- **Export size/time**: Kit alone → 772 MB / ~100s. Per-module gating on
  the full gated set multiplies this; lane runs belong on the wave
  cadence, not every `just gates` (mirrors how the full kernel-check
  replay is already the battery's wall).
- **Stack**: `ulimit -s unlimited` is required for large exports; the
  runner recipe must set it (nanoda issue, not a compat failure).
- **Version pins**: nanoda v0.4.19 ↔ exporter format 3.1.0 ↔ Lean
  v4.33.0 — three-way pin; the justfile row must name all three and the
  gate must fail loudly on a format-version drift (the exporter emits
  it in the first NDJSON line).
- **Cargo fetch**: first build needs network; after one fetch, offline.

## Blockers (honest)

- None hard. The probe passed end-to-end. The soft blockers are the cost
  items above; the binding one is the per-module export cost on the
  full gated set — measure on a wave-sized module before wiring the row.

## Verdict table

| Q | question | verdict |
|---|----------|---------|
| 1 | lean4export on v4.33.0 | builds clean, 29s |
| 2 | nanoda via devenv cargo | builds clean, 26s (+1 online fetch) |
| 3 | export Kit | 772 MB / 13.6M lines, exit 0, ~101s |
| 4 | check w/ tree allowlist | ran as specified |
| 5 | agreement | 174,918 decls, 0 errors, exit 0 — nanoda ACCEPTS |

## Adoption — the landed second lane (Gates.Nanoda)

The kernel-check row carries the nanoda face:
`lake exe gates kernel-check --nanoda [--package=<dir>]`. The lane is
ADDITIVE — the lean4lean lane stays the per-run face byte-for-byte
unchanged; `gates all` never runs this; the registry's closed gate set
is unchanged (the nanoda face rides the kernel-check row, it is not a
new registry row).

- **The tools' home**: `.tools/nanoda-lane/` — gitignored build residue,
  NOT committed binaries. The justfile's `tools-nanoda` row IS the
  artifact: clone-at-pin (leanprover/lean4export @ `66f1fb4` with its
  `lean-toolchain` OVERWRITTEN to the tree's `v4.33.0`;
  ammkrn/nanoda_lib @ `3a24072`, v0.4.19) + build. First cargo build
  needs one online fetch; afterwards offline.
- **The three-way pin**: nanoda v0.4.19 ↔ exporter format 3.1.0 ↔ Lean
  v4.33.0. The lane parses EVERY export's meta line (the first NDJSON
  row) against (3.1.0, 4.33.0) and REFUSES a drift loudly — an
  exporter/toolchain skew would invalidate every verdict downstream.
- **The config**: `permitted_axioms` generated FROM
  `LintKit.AxiomAllowlist` — the six concrete rows (core triple +
  `Lean.trustCompiler`/`Lean.ofReduceBool`/`Lean.ofReduceNat`) each
  CHECKED against the `isAllowedAxiom` predicate at run time (ONE
  table, never two; a drift refuses the lane). `sorryAx` stays
  UNPERMITTED with `unpermitted_axiom_hard_error: false` — the prelude
  declares it, any actual use errors the run.
- **The cadence**: wave cadence, honestly costed — one root's export is
  ~772MB / ~100s (Kit's closure: 13.6M lines, 174,918 decls) + the
  ~116s check. CI: the weekly schedule job + manual dispatch
  (`run_nanoda: true`), running `just tools-nanoda` then the lane over
  Kit (`gates-kernel-check-nanoda-kit`, the run of record).
- **The stack discipline**: every nanoda invocation runs under
  `ulimit -s unlimited` (the probe's operational caveat).

### The teeth (all three live)

1. **The planted axiom violation**: the lane SELF-TESTS before any real
   content — a minimal hand-built NDJSON export declaring
   `plantedAxiom` (+ a def depending on it) MUST be refused by nanoda
   under `permitted_axioms: []` (exit 1, observed:
   `Error: export file declares unpermitted axiom "plantedAxiom"`), and
   the SAME export MUST pass with the axiom permitted (exit 0, observed:
   `Checked 2 declarations with no typechecker errors`). Either
   bluntness refuses the lane. The teeth bytes are shared with the
   GatesTests pins (ONE copy).
2. **The format drift**: the meta-line pin check — a format/toolchain
   skew (or a field-free meta line) refuses fail-closed.
3. **The absent tools**: the SKIPPED note, "NOT a pass" spelled out,
   exit 0 — the optional-lane discipline; the GatesTests live teeth
   skip with the same honesty when the pinned pair is not built.
