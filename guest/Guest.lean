/-
# Guest — the guest compiler's first slice (the Lean→wasm lane)

The umbrella (one import point; root-module imports are NOT
re-exported — WasmCore.lean's discipline):

- `Guest.EdgePython.Fe` — the SECOND frontend (the multi-frontend
  doctrine's second consumer): the Python-subset surface (`Ast` — the
  closed Py AST + the `pyEval` reference semantics; `Parse` — the
  TextKit parser, the WIT/WAT precedent's shape) folded into the SAME
  IR (`Fe`), riding the SAME `Guest.Lower` — the seam's neutrality
  proven by construction.
- `Guest.Frontend` — the shared frontend KIT (the per-language front
  halves' common machinery, mined from the two ports): the pipeline
  tail (`Frontend.link` — the IR decls ride the shared lowering; a
  third frontend re-writes nothing below it), the fold disciplines'
  census (the explicit-measure family, the env-carrying continuation,
  the op tables — each with its consumer, the leftover rule's teeth),
  and the THIRD FRONTEND'S CHECKLIST in the module header (the
  marginal-frontend cost estimate).
- `Guest.Lcnf` — the LCNF frontend (host-side): a compiled environment
  + a target name → the function's impure-phase LCNF as data (the
  singular reader; `readFamily?` reads a ROOT + a family of internal
  `_closed`/`_lam` decls from ONE pipeline run — the closure
  discipline's reader face) — and the FRONTEND's product, the LCNF →
  IR reading (`toIR`): the type map, the tag prescan, and the fap
  name dispatch reify the LCNF into the IR's closed rows. The
  composed pipeline (`compile`) rides the IR into the lowering.
- `Guest.IR` — the frontend-agnostic intermediate (the CONTRACT): the
  fragment the lowering covers TODAY reified as the IR's constructors
  (the ANF-flavored discipline); the frontends produce it, the
  lowering consumes it — the lowering core imports nothing
  language-specific. The shared refusal envelope (`LowerError`, the
  GC-family E-codes) lives here too: BOTH ends of the contract throw
  into the ONE `Kit.Diag`.
- `Guest.Lower` — the lowering: consumes ONLY the IR (no LCNF import
  — the split's discipline); the scalar fragment, the boxed-Nat lane,
  the object seed, the CLOSURE discipline (`pap` + the known-arity
  application + the `_closed` fixpoint family) and the RC discipline
  (the real rc cells; the del's reuse publish — the behavior-identical
  memory discipline) → `WasmCore`'s ONE AST; every construct
  outside the fragment refuses loudly (the `LowerError` envelope, the
  GC-family E-codes).
- `Guest.Correct` — the translation correctness for the straight-line
  u64 fragment (the legacy `WasmBackend.Correct`/`Sem` content, mined
  for the new tree): the source chain's big-step semantics (`evalS`),
  the compiled templates (`compileChain`/`fnBody` — the exact shapes
  `Lower.lowerFunc` emits), the GENERIC correspondence (per-primitive
  op-map rows + ONE chain theorem — the §6 engine's pattern, the
  Kripke-style evolving relation's first consumer), the fuel
  discipline (the convergence legs carry `need`; the fuel-insensitive
  `run_chain_inv` is the refinement's law), the exit-frame + module
  faces through `runFunc`, the SABOTAGED-op-map negative control (a
  wrong lowering produces a wrong execution — a theorem), and the
  build-failing extraction pins (the REAL lowering's output = the
  templates, full Func values; the sabotaged template ≠ the real
  emission).
- `Guest.SrcMachine` — the source fragment AS a machine (wave 30's
  A4): the `evalS`/`Src` mini-executor as a `Machines.Machine` (the
  binding env as the state, the let-binding as the step — the graph
  of the fold's own continuation), the run tie (`chainTape` →
  `envUpdS`), the value/map ties to `evalS` and the machine-side
  `envUpd` (the Kripke index's agreement — the seam where the
  refinement composes with the machine reading), and the witness
  discipline applied (every chain's run has a witnessing `Exec`).
- `Guest.Effects` — the effects lane's integration (08 §8): the
  compiler DERIVES each function's effect row + its memory footprint
  from the IR content (the honest first cut — pure scalar = the
  empty row, the allocators/RC ops carry `read`+`write`, the callees
  outside the local fold carry the top-row over-approximation; the IR
  reifies the dispatch lanes — `CaseVia`, the `NatFap`/`Binop` rows —
  so the derivation is a plain structural fold over the contract's
  closed constructors, no Lean, no LCNF); the boundary check refuses
  an over-claimed purity (the named `EffectError.overClaim`
  diagnostic, GC2023) and reports an under-claim's slack; the
  Prop-indexed obligation per function + the computed obligation-row
  manifest; the footprint keys (the layout regions —
  `Effects.Footprint`'s first consumer).
- `Guest.GenMain` — the manifest discipline (the legacy WasmGenMain's
  P1 port): the project manifest as a DECLARED value, the compile set
  = the `@[guest]` marks (the replayed registry), the world = the
  honest ABI surface of the marks; the `componentgen` driver's
  derivation face.

The end-to-end (GuestTests.Main, the in-tree proof-of-life): the
fixture fn → LCNF → the IR (the frontend) → the lowered module →
`WasmCore.Encode`'s binary → `WasmCore.Validate` (the generated
module validates) → `WasmCore.Exec` (the result pinned); the TOY
FRONTEND (a hand-written IR program, no LCNF) rides the same
lowering — the conformance evidence that the IR is the whole
contract.

The cone row: `Guest` = C2/host (host-side lane — imports Lean via
Guest.Lcnf + WasmCore; the emitted code is the guest).

The five questions (notes/v3/01-core.md): answered per submodule;
the umbrella is the import point and answers none.
-/

import Guest.Frontend
import Guest.Lcnf
import Guest.Lower
import Guest.EdgePython.Fe
import Guest.Correct
import Guest.SrcMachine

import Guest.Effects
import Guest.GenMain
