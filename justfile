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
test_libs := "KitTests TextKitTests TestingKitTests SchemaTests WasmCoreTests LintKitTests WitTests MachinesTests ZSetTests InspectorTests DatalogTests ScaffoldTests CostTests AnalysisTests QueryTests GuestTests VortexTests EffectsTests"

test:
	lake build
	for lib in {{test_libs}}; do lake exe ${lib} || exit 1; done

# The linter driver over the gated roots (LintKit + Gates).
lint:
	lake exe lintkit

# The dev loop's fast tier: build + the LIGHT gates + lint. The heavy
# three (axioms, coverage, kernel-check — the env replays) stay in
# `just gates` for integration. Measured: the light tier is seconds;
# the full battery's cost is the kernel-check's module replay.
check:
	lake build
	lake exe gates gen-check
	lake exe gates docs-check
	lake exe gates code-registry-check
	lake exe gates snapshot-check
	lake exe gates audit
	lake exe gates artifact-headers
	lake exe gates ownership
	lake exe lintkit

# The gates machine: the gate registry's `all` — one driver, every row,
# first failure stops (notes/v3/09-gates-ops.md §3). Rows: axioms,
# docs-check, gen-check, code-registry-check, snapshot-check, audit,
# artifact-headers, native-policy, coverage, kernel-check. The byte-tie's
# writer side is `just gen`. THIS is the integration battery.
gates:
	lake exe gates all

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
# the lean4lean exe on demand).
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
