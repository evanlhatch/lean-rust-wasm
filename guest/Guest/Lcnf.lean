/-
# Guest.Lcnf — the LCNF reading (the lane's host-side input)

The guest compiler's FIRST input face: a compiled Lean environment +
a target function name → the function's impure-phase LCNF as data
(the decl's params/body). Host-side discipline: `import Lean` +
`Lean.Compiler.LCNF` — the Lean compiler's internals are HOST
tooling (the C2/host cone; the EMITTED code is the guest). Mined
from `legacy/lean/wasm-backend/WasmGenMain.lean` (the LCNF re-run
pattern):

- the pipeline runs IN THIS PROCESS (the impure phase is not
  persisted in oleans — `LCNF.main` over the imported environment);
- `compiler.reuse` is DISABLED (the emitter cannot lower
  reset/reuse joins — the legacy driver's standing option);
- the decl is fetched from the pipeline's LOCAL cache
  (`getLocalImpureDecl?` — the compiled decl never joins the
  environment's constants).

The honest first cut (this slice): ONE target function at a time,
the target's fap callees are the extern scalar primitives (the op
surface — no closure completion fixpoint yet; the multi-target
closure walk is the named follow-up, Lower.lean's header).

The five questions (notes/v3/01-core.md):

- **Root**: none — a host-side READER (the input face of the lane).
- **Carrier grade**: none — the output is LCNF's own data; the
  crossing discipline (the Diag refusals) lives at the lowering.
- **Spine reading**: the LCNF decl is the registry-content the
  lowering folds (Guest.Lower's spine).
- **Ladder rung**: n/a (host machinery; no proof obligation here).
- **Gate row**: `gates kernel-check` (the module replays through the
  pure kernel) — the lane's modules are gated source.

Consumer trail: `Guest.Lower` (the lowering's only producer of
input), `GuestTests.Main` (the driver that owns the unsafe IO —
importModules + this reader). Host-side (imports Lean); NOT
core-only, and not a cone-low module: the guest lane is C2/host.
-/

import Lean
import Lean.Compiler.LCNF

namespace Guest

open Lean Compiler.LCNF

/-- The driver options: `compiler.reuse` disabled (the emitter cannot
    lower reset/reuse joins — the legacy WasmGenMain discipline). -/
def lcnfOptions : Lean.Options :=
  (default : Lean.Options).setBool `compiler.reuse false

/-- Read ONE function's impure-phase LCNF: run the LCNF pipeline over
    `target` in a CoreM context built on the given environment, then
    fetch the decl from the pipeline's local cache. The refusal is the
    named envelope: a target that is not a compilable `def` (or whose
    pipeline run fails) answers `.error`, never a crash. -/
def readDecl? (env : Lean.Environment) (target : Lean.Name) :
    IO (Except String (Decl .impure)) := do
  let ctx : Lean.Core.Context :=
    { fileName := "<guest-lcnf>", fileMap := default
    , options := lcnfOptions }
  let state : Lean.Core.State := { env := env }
  try
    let act : Lean.CoreM (Except String (Decl .impure)) := do
      Lean.Compiler.LCNF.main #[target] lcnfOptions
      match ← Lean.Compiler.LCNF.getLocalImpureDecl? target with
      | some d =>
          pure (Except.ok d)
      | none =>
          pure (Except.error
            s!"Guest.Lcnf: no impure-phase LCNF decl for `{target}` — \
               the target did not compile (is it a `def`?)")
    let (r, _) ← act.toIO ctx state
    return r
  catch e =>
    return .error
      s!"Guest.Lcnf: the LCNF pipeline failed for `{target}`: {toString e}"

end Guest
