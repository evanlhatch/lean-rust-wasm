# The Rust ↔ Lean seam contract — what enforces what, what's proven, what should be

The seam inventory: every place Rust behavior must agree with the Lean
spec, the enforcement mechanism, and the proof status. The doctrine
(§8's ladder): a seam enforced only by a test is Tier 2; promoted into
a theorem = Tier 0. This doc is the work list for the promotions.

## The seams

| # | Seam | The two sides | Enforcement today | Proven? | The promotion |
|---|------|--------------|-------------------|---------|---------------|
| 1 | **Generated artifacts** | Lean emitters → committed WIT/Rust/Vortex files → the Rust build | `gen-check` byte-tie (sha256-verified OCI store) | byte-identity, not semantics | — (the byte-tie IS the right tool: one writer, CI-fail on drift) |
| 2 | **The component WIT surface** | schema items → `wit/gateway.wit` → wit-bindgen's generated Rust types (`bindings.rs`) | `wit_roundtrip` (wit-parser parses the generated WIT; structural pins) + the typed-call tests | ✗ | wit-bindgen's lift IS the host side's authority; the round-trip pins the emitters' output against wit-parser — adequate |
| 3 | **The scalar ABI** (i64 flow, bool→I32 flat) | the adapters' WAT ↔ wasmtime's canonical flattening | `invoke_core`'s param introspection + the duel | ✗ | the flattening = the canonical ABI spec — see #5 |
| 4 | **The guest object layout** | LCNF CtorInfo (the general codegen's sproj offsets) | the backend derives offsets from CtorInfo — ONE source, by construction | the general path: by construction | done for the general path |
| 5 | **The canonical-ABI FLAT record layout** (the adapters' element encoding: id@0, name@8/12, email@16/20, tags@24/28) | the adapters' offsets ↔ wit-bindgen's generated record layout (the host's Lift) | the differential duel (get-user + watch-users rows decode through the host's types) — WAS Tier 2-only, and the gap BIT: the watch-users/listUser bug (all field stores at +0/+4) was invisible until a record element crossed a STREAM | **✓ PROVEN** | **`WasmBackend/Layout.lean` LANDED**: `offsets`/`size` as Lean functions; `go_pairwise` (the offsets strictly increasing = no field overlap) + `go_ge` + `width_pos` proved; the adapters emit FROM `Layout.offsets` (`user_offsets`/`user_size` = the rfl pins: [0,8,16,24], size 32); the same layout drives watch-orders' listUser AND watch-users' streamUser |
| 6 | **The list-walk cursor discipline** | `listWalkWat`'s (ptr,len) stores vs the bump allocator | the watch-users bug: the areaOff=0 "scratch" write landed on the NEXT allocation (element 1's tags array = the outer walk's fill-end cursor). Fixed STRUCTURALLY: the scratch store is DELETED (the walk's areaOff=0 = NO memory write; the callers read the locals) | the invariant ("the walk owns [arr, arr+n·elem) and NOTHING beyond") is now enforced by the ABSENCE of out-of-region stores; unproven | the walk's region-disjointness check = a LintKit-style audit over the EMITTED WAT (every store's address ∈ the walk's region) — the 6.5.3 recipe applied to the backend's own output |
| 7 | **The oracle manifest** | Lean's `resultOf` evals ↔ the shipped wasm's behavior | the duel: 240 rows under wasmtime + the scalar subset under wasmi; the sabotage control (the gate must fail when sabotaged) | empirically total | the per-row authority chain is exact (Lean eval → JSON → replay); the SEMANTIC gap (wasmi/wasmtime's instruction semantics vs Lean's) = the Talos line |
| 8 | **The registry → the world fold** | `@[schema_fn]` items → `worldExportsOf` → demo-world.wit | the fold (the registry is the authority; `body` = the compiled impl pointer); the 3.4 guard (the oracle ⊆ the world) runs in main | by construction (no hand list remains) | done |
| 9 | **Provenance** | the axiom-gate report + the kernel version ↔ the pushed OCI artifact | `forge push --axiom-report --lean-version` → manifest annotations; the puller verifies before instantiating | the report = a claim about the SOURCE tree — binding it to the BLOB = the sha256 chain | the annotation content is as trustworthy as the report file — the gate's output should flow in AUTOMATICALLY (the CI wiring), not by hand |
| 10 | **Fuel** | wasmi's fuel accounting ↔ the host's budget | the stable-fuel pin (run-identical consumption; a wasmi upgrade that shifts accounting fails `rt-conformance`) | determinism: wasmi 2.0's guarantee, tested | a Lean-side fuel BOUND would need a cost model of the emitted WAT — Tier 3; the pin is the honest tool |
| 11 | **Async boundary** | the WASI 0.3 task intrinsics ↔ the standalone rt | the trap-stub linker + the loud-trap negative control (an async fn under wasmi traps with the documented error — never a silent wrong answer) | ✗ (by design — async needs a p3 host) | — |

## What should be proven (the ordered list)

1. **#5, the flat layout** — **DONE, PROVEN** (`WasmBackend/Layout.lean`):
   the non-overlap theorem (`go_pairwise`) + the concrete pins; the
   adapters consume the function. This was the bug class that actually
   happened twice (listUser's +0/+4 clobber; the listWalkWat scratch
   write clobbering the next bump allocation) — the proof closes it.
2. **#4's general path** — the CtorInfo-derived sproj offsets: the same
   layout discipline applied to the general codegen (the offsets there
   are already single-sourced; the theorem is the same shape as #5).
3. **#6, the walk's region disjointness** — needs an effect-tracking
   pass over the emitted WAT (a Lean checker over the INSTRUCTION LIST:
   every store's address ∈ the walk's region). A LINTER more than a
   theorem — a candidate for LintKit's env-linters (the emitted-WAT
   audit = the 6.5.3 recipe applied to the backend's own output).
4. **#7's deep half = the Talos line** (notes/full-remaining-work.md):
   a Lean model of the emitted-WAT fragment + the translation-correctness
   theorem. The fragment is small (no simd/threads/exceptions); the
   model is the project's next big proof.
5. **#9's automation**: the axiom report flows into the push
   automatically in CI — the provenance chain is only as strong as its
   weakest manual step.

## Consumed from the Wasmi 2.0 release (2026-09-12)

* **The deterministic profile, ENFORCED at the runtime**: guestlang-rt's
  config = the closed instruction universe (floats OFF — the f64 in the
  WIT world is a TYPE, the core module has zero f64 instructions;
  memory64/multi-memory/wide-arithmetic/custom-page-sizes OFF;
  simd/relaxed-simd absent at the crate-feature level; the compilation
  mode PINNED to LazyTranslation — wasmi 2.0's `Lazy` is the mode that
  may diverge across implementations). The negative control: a
  hand-encoded f64 module is REFUSED at load. The engine's feature set
  = the runtime mirror of the spec's closed `Ty` universe.
* **The Lean-authority fuzz**: the oracle program grew an LCG-driven
  random-row supplement (200 rows — the RNG runs IN LEAN, the expected
  = `resultOf`'s evals — the authority never leaves Lean). The manifest
  = 440 rows; both engines replay it; the scalar subset crosses the
  u64-wrap boundary the fixed grid avoided.
* **The provenance gate**: `forge pull` REFUSES an artifact whose
  axiom-gate annotation is `unchecked`/absent (`--allow-unchecked` =
  the explicit local-dev hatch); the PROVENANCE SIDECAR
  (`<artifact>.provenance.json`) travels with the materialized
  artifact. The roundtrip test = the gate's test (refused / allowed /
  clean-pass, all three pinned).

## The next lane (designed, not built): `@[invariant]` validators

The template's differentiator: the user writes an invariant over their
schema's records; the template (1) compiles it (the LCNF line —
already works for record→bool logic), (2) the duel rows prove the
compiled validator agrees with Lean's eval, (3) the HOST calls it
before processing (the runtime enforcement at the trust boundary —
the ladder's Tier 2 fed by Tier 0).

The missing ABI piece: a RECORD-param adapter (the inverse of the
element lowering — the flat 32-byte record → the guest object with
refs-first layout + the string/list construction). The pieces exist in
mirror form (the result-side lowerings are green); the param direction
= the remaining work. The schema-INDEXED version (the substrait
`Expr s t n` GADT over the schema's columns — a misspelled field =
elaboration error) = the second phase; the HasCol instance search
already exists in substrait.
