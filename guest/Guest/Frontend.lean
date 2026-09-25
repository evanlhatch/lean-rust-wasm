/-
# Guest.Frontend — the shared frontend kit (the per-language frontends' common machinery)

The frontend kit, mined from the TWO frontends' port evidence
(`Guest.Lcnf` — frontend #1, `Guest.EdgePython.Fe` — frontend #2):
ONLY what BOTH frontends actually use lands here (the leftover rule's
teeth — no speculative generality; a shape with one consumer stays
local in its frontend). The kit imports `Guest.IR` + `Guest.Lower` —
NO Lean, NO language module — and the frontends import the kit; the
dependency arrows point one way.

## The census (measured over both frontends, the extraction's evidence)

- **IN — the pipeline tail** (`link`): the frontends' composed face
  ends the SAME way — the IR decls (or the named refusal) ride the
  SHARED lowering (`Guest.lowerFuncs`) into the wasm module. Both
  frontends call it; a third re-writes nothing below this call.
- **STAYS LOCAL — one consumer each** (the shared shape is the
  PATTERN, documented here, not code):
  - The explicit measure/termination family: `Guest.Lcnf`'s lex-pair
    facts + `codeSize`/`altSizes` ride the sizeOf-hopping discipline
    over the FOREIGN LCNF tree; `Guest.EdgePython.Fe`'s owned
    `msE`/`msS`/`msL` ride the self-owned count over its own AST.
    Different substrates, different lemmas — the shared discipline is
    "a frontend fold that cannot be structural carries an explicit
    total measure, with the equation lemmas the decreasing proofs
    fold, proven once, before the fold".
  - The env-carrying-continuation fold (`Fe`'s `compSs`): the
    branch-local assignment semantics (each arm's post-env feeds the
    SAME tail) — `Fe` only; the LCNF walk carries no env.
  - The fresh-variable supply + the binding env (`Fe`'s `FM`/`Env`):
    the LCNF fvars arrive named; a surface frontend mints names.
  - The op-dispatch tables (`Lcnf`'s name-matching `natFapOf?`/
    `binopOf?` vs `Fe`'s ctor-matching `opBinop`/`opCmp`): the same
    SHAPE (the language's op surface → the IR's closed rows) over
    different key types — a table per frontend, the rows closed.
  - The let-spine emission (`Fe`'s `lets.foldr IR.Code.let_` sites):
    `Lcnf` emits single lets; no shared helper.

## THE THIRD FRONTEND'S CHECKLIST (the marginal-frontend cost estimate)

A new surface language (the IR's next producer) provides, in its own
submodule tree (`Guest.<Lang>.*`):

1. **The closed surface AST + the reference semantics** — the closed
   inductive over the fragment + the evaluator the conformance suite
   ties against (the `Ast.lean` shape: `pyEval`'s parity face).
2. **The surface parser** — TextKit's discipline: parsers reason over
   TOKENS, not chars; the literal `"...".toList` rfl family is
   established ONCE per format, never per lemma (the repeated-agent
   trap); the WIT/WAT parser precedent's shape (`Parse.lean`).
3. **The checker** — the surface types → the IR's `Ty` rows
   (`Check.lean`'s Option gate; the `linter.guestlang.bareChecker`
   opt-out names the discipline — a `CheckedProp` relation +
   `check_ok_iff` bridge is the graduation when the lane gets real
   consumers).
4. **The lowering onto the IR** — the fold to `List IR.Decl`:
   ZERO new IR constructors, ZERO new E-codes (the closed vocabulary
   extends compiler-driven, 15-patterns #15); the explicit total
   measure when the fold cannot be structural (the census's
   discipline); the env-carrying-continuation fold when the surface's
   assignment semantics are branch-local; the named boundary refuses
   what the fragment does not cover (every refusal through the ONE
   `Guest.LowerError` envelope → `Kit.Diag`).
5. **The composed pipeline** — `Frontend.link (lower …)`; the tail is
   NOT rewritten (this module's `link`); the rendered-String face at
   the driver boundary (`e.render`).
6. **The battery** — the parity/conformance suite (compiled wasm ==
   the reference semantics on every fixture), the Axioms pin
   (`GuestTests.Axioms`), the mandatory negative controls, and the
   umbrella import (`Guest.lean`'s bullet).

Marginal cost, observed across the two ports: the parser + checker +
fold dominate (the EdgePython port's ~1200 LOC); the IR seam and the
pipeline tail cost NOTHING (the multi-frontend doctrine's payoff).

The five questions (notes/v3/01-core.md):

- **Root**: none — a kit of shared folds (the input face's machinery).
- **Carrier grade**: none — the output is the IR's own data; the
  refusals ride the shared envelope (`Guest.LowerError`, `Kit.Diag`).
- **Spine reading**: the frontends fold their language trees into the
  IR spine (`Guest.Lower`'s spine); `link` is the pipeline's tail.
- **Ladder rung**: n/a (the IR is closed data).
- **Gate row**: `gates kernel-check` (the Guest row, Gates.Packages).

Consumer trail: `Guest.Lcnf.compile` (frontend #1's composed face),
`Guest.EdgePython.Fe.compileModule` (frontend #2's). NOT consumers:
`Guest.Lower` (the split — the lowering consumes only the IR).
-/

import Guest.IR
import Guest.Lower

namespace Guest

/-- THE PIPELINE TAIL (the kit's one two-consumer shape): the
    frontend's product — the IR decls, or the frontend's named refusal
    in the shared envelope — rides the SHARED lowering into the wasm
    module. The frontends' composed faces are this tail + their own
    front half; nothing below this call is per-language. -/
def Frontend.link (ds : Except LowerError (List IR.Decl)) :
    Except LowerError WasmCore.Module :=
  match ds with
  | .error e => .error e
  | .ok irs => lowerFuncs irs

end Guest
