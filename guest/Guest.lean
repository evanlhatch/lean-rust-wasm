/-
# Guest — the guest compiler's first slice (the Lean→wasm lane)

The umbrella (one import point; root-module imports are NOT
re-exported — WasmCore.lean's discipline):

- `Guest.Lcnf` — the LCNF reading (host-side): a compiled environment
  + a target name → the function's impure-phase LCNF as data (the
  singular reader; `readFamily?` reads a ROOT + a family of internal
  `_closed`/`_lam` decls from ONE pipeline run — the closure
  discipline's reader face).
- `Guest.Lower` — the lowering: the scalar fragment
  (literals/copy/the `binop?` faps/Bool cases), the boxed-Nat lane,
  the object seed, the CLOSURE discipline (`pap` + the known-arity
  application + the `_closed` fixpoint family) and the RC seed (the
  real rc cells, no reuse) → `WasmCore`'s ONE AST; every construct
  outside the fragment refuses loudly (the `LowerError` envelope,
  the GC-family E-codes).
- `Guest.Effects` — the effects lane's integration (08 §8): the
  compiler DERIVES each function's effect row + its memory footprint
  from the LCNF content (the honest first cut — pure scalar = the
  empty row, the allocators/RC ops carry `read`+`write`, the unmodeled
  constructs + the callees outside the local fold carry the top-row
  over-approximation); the boundary check refuses an over-claimed
  purity (the named `EffectError.overClaim` diagnostic, GC2023) and
  reports an under-claim's slack; the Prop-indexed obligation per
  function + the computed obligation-row manifest; the footprint
  keys (the layout regions — `Effects.Footprint`'s first consumer).

The end-to-end (GuestTests.Main, the in-tree proof-of-life): the
fixture fn → LCNF → the lowered module → `WasmCore.Encode`'s binary →
`WasmCore.Validate` (the generated module validates) →
`WasmCore.Exec` (the result pinned).

The cone row: `Guest` = C2/host (host-side lane — imports Lean via
Guest.Lcnf + WasmCore; the emitted code is the guest).

The five questions (notes/v3/01-core.md): answered per submodule;
the umbrella is the import point and answers none.
-/

import Guest.Lcnf
import Guest.Lower
import Guest.Effects
