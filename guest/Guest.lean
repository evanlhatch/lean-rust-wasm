/-
# Guest — the guest compiler's first slice (the Lean→wasm lane)

The umbrella (one import point; root-module imports are NOT
re-exported — WasmCore.lean's discipline):

- `Guest.Lcnf` — the LCNF reading (host-side): a compiled environment
  + a target name → the function's impure-phase LCNF as data.
- `Guest.Lower` — the lowering's seed: the scalar fragment
  (literals/copy/the `binop?` faps/Bool cases) → `WasmCore`'s ONE
  AST + the minimal module; every construct outside the fragment
  refuses loudly (the `LowerError` envelope, the GC-family E-codes).

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
