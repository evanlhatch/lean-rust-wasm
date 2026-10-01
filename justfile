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
	cd crates/mandate-rt && cargo test
	cd crates/mandate-host && cargo test
	cd crates/mandate-store && cargo test

# The bench face (wave-30 C2 — the flatland discipline: a bench is a
# PAIR — candidate vs baseline, the same seeded inputs — with a
# THRESHOLD verdict: parity/within-noise/within-5%; a lone number is
# telemetry). ON-DEMAND, never CI: CI runs the e2e validator (the
# determinism face — `just rust` runs it); the benches are the perf
# face, run deliberately — shared-machine noise makes CI timing a
# lie. Each bench prints the pair + the verdict line from its main.
bench:
	cd crates/schema-generated && cargo bench --bench codec_round_trip
	cd crates/mandate-delta && cargo bench --bench commit_path

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
# nothing written). A drift fails `just gates`. The writer's row set
# includes the FEATURE SHIM (gen/wasm-feature-shim.mjs — the selection
# shim, WasmCore.Profile's feature table rendered; the byte-tie's
# writer side for the wasm-feature-detect discipline).
wasmgen:
	lake exe wasmgen

# The SIMD DUAL-BUILD (the wasm-feature-detect discipline, the Rust
# faces' side): the crate's wasm face builds TWICE — the simd128 bundle
# (RUSTFLAGS "-C target-feature=+simd128") and the scalar twin — and
# the committed selection shim (gen/wasm-feature-shim.mjs, byte-tied
# through the spine) picks at load. WASM SIMD HAS NO RUNTIME FEATURE
# DETECTION: a validated probe module is the whole discipline — the
# shim carries the probe + the select () contract.
#
# THE HONEST BOUNDARY: the guest components are LEAN-EMITTED wasm and
# the emitted fragment is scalar (no v128 ctor in the closed op set),
# so TODAY the dual build applies to the RUST-CRATE wasm faces and any
# future SIMD-emitting guest work — WASM_DUAL_CRATE pins the crate so
# the first SIMD-bearing consumer adopts the recipe by name, never by
# re-invention. THE ENGINE FACES ARE NOT HERE: mandate-rt's wasmi axis
# is the crate-FEATURE axis (its Cargo.toml's note), off in the
# deterministic profile — an ENGINE feature is a dependency edge, not a
# bundle. The build needs nightly -Z build-std (the nix-pinned
# toolchain's sysroot carries no wasm std; rust-src rides the
# profile) and demands the wasm profile on PATH (the devenv env).
WASM_DUAL_CRATE := "crates/mandate-rt"
WASM_TARGET := "wasm32-unknown-unknown"

wasm-dual:
	cd {{WASM_DUAL_CRATE}} && RUSTFLAGS="-C target-feature=+simd128" \
	  CARGO_NET_OFFLINE=true CARGO_TARGET_DIR=target/wasm-dual/simd128 \
	  cargo rustc -Z build-std=core,std,panic_abort --crate-type cdylib \
	  --target {{WASM_TARGET}} --release
	cd {{WASM_DUAL_CRATE}} && RUSTFLAGS="-C target-feature=-simd128" \
	  CARGO_NET_OFFLINE=true CARGO_TARGET_DIR=target/wasm-dual/scalar \
	  cargo rustc -Z build-std=core,std,panic_abort --crate-type cdylib \
	  --target {{WASM_TARGET}} --release
	@echo "wasm-dual: two bundles written ({{WASM_DUAL_CRATE}}/target/wasm-dual/{simd128,scalar}); the selection shim (gen/wasm-feature-shim.mjs) picks at load"

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

# The nanoda SECOND lane's pinned tools (the kernel-check row's
# --nanoda face; notes/nanoda-probe.md). NOT committed binaries: the
# recipe IS the artifact — clone-at-pin + build into .tools/nanoda-lane/
# (gitignored build residue). THE THREE-WAY PIN: lean4export @
# 66f1fb4bc256072069767fce52d39480e4524869 with its lean-toolchain
# OVERWRITTEN to the tree's pin (an exporter on a foreign toolchain
# invalidates the lane), nanoda_lib @ 3a2407216ee84a75f9e1aead6803d0578be06ae7
# (v0.4.19), exporter format 3.1.0 — the gate re-pins EVERY export's
# meta line against (3.1.0, 4.33.0) and refuses a drift. The first
# cargo build needs ONE online fetch (the probe's caveat); afterwards
# offline. The lane runs on the WAVE cadence (~772MB / ~100s per root
# export + the ~116s check) — never in `just gates`; CI: the
# weekly/manual nanoda job (ci.yml).
tools-nanoda:
	mkdir -p .tools/nanoda-lane/exports
	if [ -d .tools/nanoda-lane/lean4export/.git ]; then git -C .tools/nanoda-lane/lean4export fetch origin; else git clone https://github.com/leanprover/lean4export .tools/nanoda-lane/lean4export; fi
	git -C .tools/nanoda-lane/lean4export checkout 66f1fb4bc256072069767fce52d39480e4524869
	echo "leanprover/lean4:v4.33.0" > .tools/nanoda-lane/lean4export/lean-toolchain
	cd .tools/nanoda-lane/lean4export && lake build
	if [ -d .tools/nanoda-lane/nanoda_lib/.git ]; then git -C .tools/nanoda-lane/nanoda_lib fetch origin; else git clone https://github.com/ammkrn/nanoda_lib .tools/nanoda-lane/nanoda_lib; fi
	git -C .tools/nanoda-lane/nanoda_lib checkout 3a2407216ee84a75f9e1aead6803d0578be06ae7
	cd .tools/nanoda-lane/nanoda_lib && cargo build --release
	@echo "tools-nanoda: the pinned pair is at .tools/nanoda-lane/ (lean4export@66f1fb4 on v4.33.0 + nanoda@3a24072/v0.4.19)"

# The nanoda lane's runner row (the honest shape: the gate SKIPS with
# the note — never a laundered pass — when .tools/nanoda-lane/ is
# absent). Wave cadence: NOT in `just gates`/`just ci`; the CI
# weekly/manual job calls this row after `just build tools-nanoda`.
gates-kernel-check-nanoda:
	lake exe gates kernel-check --nanoda

# The nanoda lane's live run of record over ONE library (the probe's
# AGREEMENT run: Kit's closure, 174,918 decls, ~772MB / ~4min). The
# byte-cost proof the wave cadence buys.
gates-kernel-check-nanoda-kit:
	lake exe gates kernel-check --nanoda --package=Kit

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

# ── The DEBLOAT + NON-ACCUMULATION discipline (notes/design-debloat.md) ──
#
# The discipline is NON-ACCUMULATION + minimal project size, NOT
# artifact location — no clean-as-solution row lives here: artifacts
# are prevented from accumulating (the ignore wall, the shared cargo
# target), never swept after the fact. The `size` row is the READ-ONLY
# audit; when its numbers climb, the answer is a prevention piece
# (an ignore row, a config), not a clean recipe.
#
# The zones: the shared target/ (cargo), .lake/ (lake), .tools/
# (the nanoda lane's pinned builds), legacy/'s ARTIFACT zones
# (untracked, regenerable — the TRACKED legacy surface is frozen by
# the legacy-hash gate, never touched), and /tmp's scratch. The
# 2026-10-06 census (the before numbers): .lake 6.3G, .tools 1.1G,
# six per-crate target/ dirs ~26.4G (mandate-host alone 22G),
# legacy/.lake 30M, legacy/crates/guestlang-rt/target 988M,
# legacy/docs-site/node_modules 252M (12,621 files), /tmp scratch ~6G.

# The per-zone footprint report (the audit row — READ-ONLY, it deletes
# nothing; read it after the heavy waves; the discipline is the tree's
# footprint stays BOUNDED, and a bounded claim needs the numbers).
size:
	@echo "== lean-rust-wasm footprint census (regenerable zones)"
	@du -sh .lake .tools target 2>/dev/null || true
	@du -sh crates/*/target 2>/dev/null || echo "(no per-crate target/ — the shared root target is the shape)"
	@du -sh legacy/.lake legacy/crates/guestlang-rt/target legacy/docs-site/node_modules 2>/dev/null || true
	@echo "-- /tmp scratch (lrw-owned)"
	@du -sh /tmp/lean-beam /tmp/mw-baseline /tmp/llvm-spike /tmp/nanoda-spike /tmp/lrw-grind 2>/dev/null || true

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
