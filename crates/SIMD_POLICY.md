# The Rust lanes' SIMD policy — fearless_simd by default

The crates' compute discipline (the owner's directive (a)): the
Rust faces that carry vectorizable compute use
[`fearless_simd`](https://github.com/simd-lite/fearless_simd) BY
DEFAULT — the portable-SIMD crate: one source, the SIMD/scalar
dispatch free (the crate lowers per target, including the scalar
fallback; `fearless_simd::Simd` over the width-generic mask/select
shape). Thoughtless on the Rust side: a new compute face does not
DEBATE the dependency, it adopts it — the debate happened here, once.

## The boundary (what this does NOT cover)

- **The guest components are Lean-emitted wasm** and the emitted
  fragment is scalar — no v128 ctor in `WasmCore`'s closed op set.
  The dual build (the justfile's `wasm-dual`) applies to the
  RUST-CRATE wasm faces and any future SIMD-emitting guest work;
  the selection shim (`gen/wasm-feature-shim.mjs`, byte-tied through
  the emit spine) is the load-time face. This file is the Rust-side
  policy; the wasm-feature side lives in `WasmCore.Profile` (the
  feature universe + the shim) and `notes/design-wasm-features.md`
  (the discipline doc).
- **The engine faces are not compute faces**: `mandate-rt`'s wasmi and
  `mandate-host`'s wasmtime simd axes are the ENGINES' crate-feature /
  config axes (see `mandate-rt/Cargo.toml`'s note) — off in the
  deterministic profile (`WasmCore.Profile.theProfile.simd`), never
  touched by this policy.

## The dependency's shape (when the first consumer lands)

```toml
[dependencies]
fearless_simd = "<minor current at adoption>"   # pin the minor; no default-features games —
                        # the crate's default is the portable face
```

One dependency line, one import style
(`use fearless_simd::Simd;`), ONE dispatch shape per crate: the
crate's compute entry takes the width-generic `Simd` bound and the
CALLER never sees `#[cfg(target_feature)]` — the crate's lowering is
the dispatch. A hand-rolled `std::simd` (nightly portable SIMD) or a
`#[cfg]`-ladder over `simd128`/`avx2` in a crate face is a policy
violation, not an optimization.

## The FIRST CONSUMER's checklist (the leftover rule)

The dependency does NOT land until a compute face exists — no dep
without a consumer (the tree's leftover rule). When the first
SIMD-relevant compute face lands (the vortex/compute Rust faces are
the named candidates), the consumer's PR carries ALL of:

1. **The dependency line above** in the consuming crate's
   `Cargo.toml` — and a one-line justification naming the compute
   face (the dep discipline: minimal, justified).
2. **The scalar baseline**: the same operation's scalar fold exists
   (a test twin, not a cfg lane) — the duel face: SIMD vs scalar
   agree on the seeded inputs, byte-exact where the output is bytes.
3. **The dual-build adoption**: the justfile's `WASM_DUAL_CRATE`
   points at the consuming crate (or the face rides a crate that
   does) — the simd128/scalar bundles build green (`just wasm-dual`),
   and the wasm face (if the crate has one) is loadable through the
   selection shim's `select ()` contract.
4. **The bench pair** (if the face is perf-motivated): the flatland
   bench discipline — candidate vs the scalar baseline, the same
   seeded inputs, a THRESHOLD verdict; a lone number is telemetry.
5. **This file's boundary sections** still hold: no engine-face
   changes, no guest-fragment changes in the same PR.

A checklist item skipped is a finding (the review's name for it:
"the policy's consumer landed ahead of its own teeth").
