# mandate — the thin build spine. Recipes grow when their first consumer
# lands (notes/v3/14-build-map.md); the Lean gates are the first rows
# (notes/v3/09-gates-ops.md §3).

build:
	lake build

# Every test exe — builds ≠ tests (the review-of-record's finding).
# ONE list of FULL EXE NAMES (the lakefile's `[[lean_exe]]` rows — the
# convention: `<Lib>Tests`, the slice's historical `SchemaTests` kept);
# a gates row (the manifest discipline) checks the lakefile's test exes
# against this list, so a new library that forgets its entry fails CI.
test_libs := "KitTests TextKitTests TestingKitTests SchemaTests WasmCoreTests LintKitTests WitTests MachinesTests ZSetTests InspectorTests DatalogTests ScaffoldTests CostTests AnalysisTests QueryTests SubstraitTests GuestTests VortexTests EffectsTests ComponentTests ContractsTests GatesTests ReprTests FaultsTests"

test:
	lake build
	for lib in {{test_libs}}; do lake exe ${lib} || exit 1; done

# The Rust batteries (the duel/differential/persistence/component
# consumer faces) — the byte-tie's consumer side: rot here is a gates
# failure, so it runs in the tree's test discipline, not by hand.
rust:
	cd crates/schema-generated && cargo test
	cd crates/mandate-delta && cargo test
	cd crates/mandate-faults && cargo test
	cd crates/mandate-host && cargo test

# The linter driver over the gated roots (LintKit + Gates).
lint:
	lake exe lintkit

# The dev loop's fast tier: build + the LIGHT gates + lint. The heavy
# three (axioms, coverage, kernel-check — the env replays) stay in
# `just gates` for integration. Measured: the light tier is seconds;
# the full battery's cost is the kernel-check's module replay.
check:
	lake build
	lake exe gates packages-check
	lake exe gates gen-check
	lake exe gates docs-check
	lake exe gates code-registry-check
	lake exe gates snapshot-check
	lake exe gates audit
	lake exe gates artifact-headers
	lake exe gates ownership
	lake exe gates legacy-hash
	lake exe lintkit

# The gates machine: the gate registry's `all` — one driver, every row.
# PARALLEL COLLECTION (the wave-29 speed wave) + the RSS CEILING (wave
# 30, measured on this 29GB box, ~26GB available fresh):
#
#   per-lane costs (/usr/bin/time, peak RSS):
#     lean4lean leaf      <= 1.2GB, 0.4-1.6s   (heaviest: GuestTests.Main)
#     env-replay shard    <= 1.7GB, 1-42s      (axioms Kit shard: 42s)
#     light gate driver   <= 1.0GB             (the artifact/report rows)
#     INNER kernel node   ~24GB alone          (SchemaCore's subtree —
#                     inherent to lean4lean's prefix expansion; runs
#                     EXCLUSIVELY, one at a time)
#
#   ceiling = budget / per-lane, budget = 90% of MemAvailable at run
#   time (~23.4GB here). The headroom story is in the PER-LANE COSTS:
#   each is rounded UP from its measured peak (2GB vs 1.7, 1.3GB vs
#   1.2) — the round-up IS the margin (plus GATES_RSS_MARGIN_MB's 1GB
#   driver slack; GATES_RSS_BUDGET_MB overrides the base). The pools
#   ADMIIT a spawn only while the projected peak (the live lanes'
#   costs + the candidate's + the margin) stays under budget; over
#   budget the work QUEUES — never dropped, never OOM (the OOM's root
#   cause was ~300 UNBOUNDED concurrent kernel replays, 24GB peak).
#
#   The RETUNE lesson (the first cut's 8-lane pools made each heavy
#   gate's worst-case footprint 16GB-class — the heavy gates could
#   not co-run and the battery SERIALIZED, 4:34 vs the before-run's
#   2:38): MODERATE lanes co-run beats many lanes alone. Defaults:
#   GATES_ALL_JOBS=6 (the count cap; the footprints are the real
#   bound), GATES_KERNEL_JOBS=6 (6×1.3GB — the INNER nodes, not the
#   lanes, bound kernel-check's wall), GATES_POOL_JOBS=3 (3×2GB =
#   6.2GB/gate — both shard pools + the kernel leaves share the
#   budget, the full battery overlapped).
# EVERY gate runs, the failures collect, the report is the registry's
# run order (the sequential first-failure-stop was the OOM era's
# shape). Rows: packages-check, axioms, docs-check, gen-check,
# code-registry-check, snapshot-check, audit, artifact-headers,
# native-policy, coverage, kernel-check, ownership, breaking, and the
# rows other waves land (elab-watch). The
# byte-tie's writer side is `just gen` (the component lane's: `just
# componentgen`). THIS is the integration battery.
gates:
	lake exe gates all

# The impact-aware dev loop (09 §6): the change set (jj, fallback git)
# → affected modules → affected artifacts → ONLY their gates. Any gap
# widens to the full run (the conservatism invariant: never
# under-reports) — until the artifact ledger lands, that is every run,
# honestly.
impacted:
	lake build
	lake exe gates impacted

# The schema regen (the byte-tie's writer side: regen + commit the
# artifact; a drift with no regen fails `just gates`).
gen:
	lake exe schema

# The wasm slice regen (the BINARY lane's writer side: the WAT text
# artifact + the wasm bytes + the .hdr sidecar through the emit spine;
# the validator runs at generation — an invalid module refuses loudly,
# nothing written). A drift fails `just gates`.
wasmgen:
	lake exe wasmgen

# Single gates (the loud re-baseline: `just gates-axioms-write` refuses a
# non-empty diff without `--accept-drift` — append it by hand).
# The gated-table drift guard (the single gated set: Gates.Packages'
# table × the lakefile, both directions + every row root's source).
gates-packages-check:
	lake exe gates packages-check

# The loud re-baseline: `just gates-axioms-write` refuses a
# non-empty diff without `--accept-drift` — append it by hand.
gates-axioms:
	lake exe gates axioms

gates-docs-check:
	lake exe gates docs-check

# The persisted E-code registry gate (the allocation history; --write is
# the deliberate allocation/canonicalization step, never a launder —
# the content checks run first).
gates-code-registry-check:
	lake exe gates code-registry-check

# The universe-snapshot gate (the breaking gate's substrate; --write is
# the deliberate re-baseline).
gates-snapshot-check:
	lake exe gates snapshot-check

# The artifact self-audit (09 §5): the AuditRule list over every
# committed generated artifact (no TODO/FIXME/unwrap(/dbg!/unsafe).
gates-audit:
	lake exe gates audit

# The GENERATED-header gate: presence + shape of the 2-line block over
# every committed generated artifact (the one-writer rule's detection
# face).
gates-artifact-headers:
	lake exe gates artifact-headers

# The native_decide grandfathering gate: the committed allowlist set +
# the staleness ratchet (fail-closed both ways).
gates-native-policy:
	lake exe gates native-policy

# The Ty-ctor × emitter coverage matrix (probe-differential cells + the
# registry column; --write is the deliberate re-baseline).
gates-coverage:
	lake exe gates coverage

# The lean4lean pure-kernel replay (the independent double-check; builds
# the lean4lean exe on demand). One invocation PER MODULE (the batch
# mode's ~300 concurrent replays = the recorded hang); the leaves in a
# worker pool (GATES_KERNEL_JOBS, default 6, RSS-BOUNDED: a leaf costs
# <=1.2GB measured, the MemAvailable-derived budget ~23.4GB admits the
# leaves co-runnable beside BOTH shard pools — over budget the leaves
# queue), the inner nodes exclusive
# (SchemaCore's subtree alone peaks ~24GB — inherent, one at a time); a
# per-module wall budget (GATES_KERNEL_BUDGET_SECS, default 300) — a
# module over budget is an UNKNOWN with a named report, never a hang.
gates-kernel-check:
	lake exe gates kernel-check

# The artifact-ownership gate (D15: ownership is GLOBAL — declared-vs-actual
# agreement both directions + the cross-emitter disjointness over the REAL
# emitter set; the orphan's detection face).
gates-ownership:
	lake exe gates ownership

# The breaking gate (the snapshot's forward consumer: the committed
# universe baseline vs the replayed registry — the diff + the three-way
# verdict + the exit-code discipline; unremedied = 2, the loud warning).
gates-breaking:
	lake exe gates breaking

# The legacy-immutability gate (B4): the read-only pre-v3 surface
# (legacy/) hashed per file against notes/legacy-surface.txt — drift is
# a finding. --write is the row's first-write baseline only.
gates-legacy-hash:
	lake exe gates legacy-hash

# The component slice regen (the component lane's writer side: the
# world text + the component bytes + the .hdr sidecar through the emit
# spine; the SKEW CHECK runs at generation — a world/component drift
# refuses loudly, nothing written). MANIFEST-DRIVEN (Guest.GenMain):
# the compile set + the world derive from `Guest.Gen.mandate`'s
# registered surface (the `@[guest]` marks replayed from the oleans),
# never a hand list.
componentgen:
	lake exe componentgen

# The elaboration-time regression watch (notes/v3/09-gates-ops.md §7):
# every gated root's own elaboration re-timed against the committed
# baseline notes/elab-baseline.tsv — the module/reference RATIO is the
# signal (absolute budgets are noise); a >2× ratio delta flags. --write
# is the deliberate re-baseline (loud: a non-empty diff needs
# --accept-drift appended by hand).
gates-elab-watch:
	lake exe gates elab-watch

# The CI battery: the FULL composition — build + test exes + the gates +
# the Rust batteries. CI runs EXACTLY this recipe (the local/CI parity
# discipline, notes/v3/13-interfaces.md: `just gates` locally; CI runs
# the same; a red gate names the gate + the divergence, never a bare
# failure — the gates' own reports are that naming).
ci:
	just build
	just test
	just gates
	just rust
