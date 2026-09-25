/-
# Guest.Lower — the impure-phase LCNF → the ONE wasm AST

Ported from `legacy/lean/wasm-backend/WasmBackend.lean` (the emitter's
INTENT; the new tree's substrate differs honestly — index-keyed
locals, the closed `WasmCore.Instr`, the frame-DEPTH discipline in
place of the legacy's WAT labels, the op meanings in
`WasmCore.OpTable`):

- **The scalar type map** (the legacy `wasmTyOf?`): `UInt64 → i64`;
  `UInt32`/`UInt8`/`Bool`/`Char → i32`; a SCALAR-REPRESENTABLE ENUM
  (the tag discipline, below) `→ i32`; EVERYTHING ELSE refuses loudly
  — a type outside the fragment is a named diagnostic, never a silent
  `i32` pointer guess (the object model is not landed).
- **The tag discipline (the scalar-representable enums)**: a `cases`
  whose ctor alts are ALL payload-free (`CtorInfo.isScalar` —
  size/usize/ssize = 0) with every tag below 256 registers the
  scrutinee's TYPE NAME as scalar-representable (a prescan over the
  decl's OWN code — the observed evidence, no env threading): the
  enum's runtime repr is the unboxed ctor TAG, so the value branches
  like a `UInt8`. A payload ctor anywhere in the case keeps the type
  an OBJECT — refused (the boxed-object model).
- **The op surface** (the legacy `binop?`, grown): the `UInt64`
  add/sub/mul/decLt/decEq family, the shifts (`shiftRight`), the
  `UInt32` lane (add/sub/mul/land/xor/decLt/decEq/shiftRight), the
  `UInt8` lane (the arith rows carry the `and 0xFF` mask — i32
  arithmetic wraps mod 2^32, a `UInt8` wraps mod 2^8), the width
  conversions (`toUInt32`/`toUInt64`), all → `WasmCore.Op`'s ctors
  consumed from `WasmCore.OpTable`'s projections (the ONE table,
  07-extensibility R6). A fap outside the rows falls to the CALL LANE
  (below); a fap on NEITHER refuses loudly.
- **The cross-decl call lane** (the legacy scalar-call shape, grown to
  the index-keyed module): an LCNF `fap` naming a SIBLING decl of the
  same module lowers to wasm `call` at the callee's FUNCTION-TABLE
  INDEX (`lowerFuncs`' decl order — a self-recursive decl calls its
  OWN index; the recursion's bound is the executor's fuel honesty,
  `outOfFuel`, never a fabricated termination). The marshalling is
  the EXECUTOR'S calling convention exactly (the validator's `call`
  row is the shared contract): the args push LEFT TO RIGHT (param 0
  first), so the head-top stack has the LAST param on top; the
  executor pops against `ft.params.reverse` and binds `param i →
  local i` — the legacy `for a in args do emitArg a` discipline
  verbatim. The return: the callee's exit-frame discipline leaves the
  result on the callee's final stack; the call boundary joins it over
  the caller's retained stack, so the caller's next `localset` reads
  it — every value crossing the call rides a LOCAL on BOTH sides.
  The INLINER HONESTY: LCNF inlines small calls before the lowering
  sees them — the lane handles what ARRIVES (a remaining `fap` on a
  known decl = the call; an arity drift or an erased arg = the named
  refusal; an unknown name = the op-surface refusal).
- **The boxed-Nat lane (the object discipline's seed)** (the legacy
  `emitLet`'s lit/fap arms, the bounded-Nat model): a guest `Nat` is a
  BOXED machine int — `{rc reserved @0, tag 0 u8 @4, i64 payload @8}`
  — 16 bytes in the module's linear memory, because the pipeline RCs
  Nats as objects (`tobj` params/results, `tagged` literal bindings —
  the probe-observed impure-phase types). The allocator is a BUMP
  arena over the module's one memory page: the bump pointer lives IN
  the memory at cell 0 (the module model has no globals), every
  allocation site inlines the pointer read + bump + store. NO RC:
  an allocation is never freed within a run — the memory leaks inside
  `runFunc`'s zero-initialized page (the named boundary; the Perceus
  RC ops `inc`/`dec`/`del` still refuse).
  - The literals: below the pinned cap 2^62 the literal allocates its
    box and stores the payload; at/above the cap is a DESIGN ERROR
    (refused with `natLitCap`) — and the REAL pipeline's constant
    folding delivers statically-overflowing arithmetic as exactly
    such a literal (observed: `2305843009213693951 * 4` folds to
    `9223372036854775804` ≥ cap — the compile-time refusal IS the
    model's overflow honesty where static).
  - The fap surface (the legacy's sanctioned rows, inline-lowered):
    `Nat.decEq`/`beq`/`decLt`/`decLe` — the payloads' UNSIGNED machine
    compare (a Nat's payload IS its magnitude; the cap keeps
    signed/unsigned equal) → the raw i32 Bool; `Nat.add`/`sub`/`mul`
    — the payload arith into a FRESH box (Nats are immutable under
    the model). The RUNTIME overflow discipline: the 2^62 cap holds
    at runtime too — `add`'s sum of two sub-cap payloads cannot wrap
    u64, so the cap check is exact; `sub` traps on underflow (a − b
    with a < b would wrap); `mul` carries the 128-bit guard (the four
    quarter products give the high word — high ≠ 0 means the true
    product passed 2^64 and the u64 result is a wrap-masquerade) plus
    the low word's cap check. A breach TRAPS (`unreach`) loudly —
    never a silent wrap.
  - The type map's object rows: `tobj`/`tagged`/`obj`/`Nat` → `i32` —
    the ONE pointer repr (the object model's seed face).
  - The ctor-case-on-Nat THROW: a `cases` whose scrutinee is `Nat`
    throws loudly (`natCtorCase`) — the generic tag dispatch would
    read the box's tag 0 and treat the payload as a POINTER, silently
    wrong (the legacy discipline; the real pipeline never produces
    one — Nat cases compile to decEq fap chains — but the hand-built
    face can, and the model refuses).
- **The object seed** (the hand-built face; the real pipeline's ctor
  path goes through `_closed` top-level closures + `inc` — the
  closure fixpoint is THIS slice, below): a ctor with SCALAR fields
  allocates the object — header `{rc @0, tag @4}` + the fields in
  8-byte slots `@8 + i*8` (the legacy slot discipline; a sub-word
  field wastes its slot's high bytes — the layout's honesty) — and
  `sproj` reads a field back at `8 + n*8 + offset` with the load
  width from the field's mapped type. The FIELD-LAYOUT LAW (this
  slice): the ctor face writes the PIPELINE'S packing coordinates
  (ref fields first, one 8-byte slot each; the scalar region after
  them, packed by size class largest first — the pipeline's
  `adjustScalarsForSize` discipline), and a field whose class is
  unclassifiable from the lowering's data (an enum/Char repr) refuses
  (`ctorFieldClass`). No `proj`/`uproj` reads, no in-place field
  writes (`sset` refuses).
- **The closure discipline** (the legacy `pap` arm + the trampoline's
  LAYOUT, grown to the known-arity application): a closure is an
  ALLOCATED OBJECT riding the landed object discipline — `{rc @0,
  tag 254 @4, fnIdx u32 @8, captured slots @16 + i*8}` (the legacy's
  proved offsets). The `pap` value form allocates it, stores the
  callee's FUNCTION-TABLE INDEX (`lowerFuncs`' decl order — the
  pap's fn must name a SIBLING decl, else the named refusal) + the
  captured values (width by mapped type), and records the
  PROVENANCE (fvar → pap fn + captured locals) in the lowering
  state. The APPLICATION (`fvar f args`, `args` nonempty) is the
  HONEST MINIMAL: the KNOWN-ARITY application — when `f`'s binding
  is a tracked pap, captured + fresh must total the callee's arity
  (drift refuses), and the call lowers DIRECTLY to the callee's
  index with the captured locals pushed first, then the fresh args
  (the executor's param-i-to-local-i convention verbatim; a second
  application reuses the same captured locals — closures are
  read-only under the model). A first-class application (an applied
  fvar with NO pap provenance — e.g. a closure PARAM, the real
  pipeline's `applyTwice`/`useFn` bodies) lowers to THE INDIRECT-CALL
  LANE (landed): the applied fvar must be a CLOSURE-POINTER row
  (`tobj`/`obj` — the probe-observed shapes; a non-closure applied —
  a scalar/boxed-scalar fvar — refuses, `closureApplyUnknown`); the
  fresh args push left to right, the closure's fnIdx loads from @8
  (the i32 on top — the table index), and `callindirect` fires at the
  SIGNATURE's type index — the signature (the fresh args' types → the
  result type) registers in the module's type section (the sig
  registry, deduped, module-scoped) and the module's ONE funcref
  table carries the identity entries (table i = function i). The
  EXECUTOR's table discipline is the runtime honesty: an
  out-of-bounds index traps (`tabOOB`), a type-mismatched entry —
  e.g. a PARTIAL pap applied first-class, the twiceAdd5 family's
  real shape — traps (`indirectSig`), never a wrong call.
  - The `_closed` fixpoint: the real pipeline's function-value
    producers (`._closed_N` decls) lower through the SAME lanes —
    the probe-observed shape is `fap _boxed_const_1 args=0` (the
    0-ary sibling call), `inc[persistent]`, `pap _lam._boxed
    [captured]`, `return` the closure pointer. The `_lam._boxed`
    adapters (obj params → `unbox`/`dec` → the scalar `_lam` body →
    `box` the result) are in-fragment and lower as written.
- **The RC seed** (the honest minimal: the inc/dec discipline WITHOUT
  the reuse — the memory-growth boundary named): every allocation
  site stores `rc = 1` @0 (one reference at birth); the `inc`/`dec`
  Code forms lower to the rc cell's REAL arithmetic (u32 @0):
  `inc` adds n; `dec` subtracts n under the OVER-DEC GUARD (`rc ≥ n`
  or the `unreach` trap — a dec past zero is a use-after-free bug,
  never a silent wrap). A dec to ZERO leaves rc=0 — the DEAD
  object is observable in memory but its slot is never reused: the
  REUSE opportunity (the rc=0 slot's freelist) needs the SIZE-CLASS
  discipline — a size-blind pop overruns the dead slot (a 16-byte
  box's slot reused for a 40-byte closure) — so the honest minimal
  defers it with the leak bounded by the arena's one page (the
  memOOB trap; the named follow-up, not a silent lie). The flags
  ride recorded-and-ignored (`check`/`persistent` — the runtime's
  cross-run cache discipline, not modeled); `dec` with `objs?` (the
  field-cascade dec) refuses (`rcCascade` — the ref-field reads it
  needs are the object seed's boundary); `del` refuses (without the
  freelist it could only drop the slot silently).
  - The scalar-box lane (`box`/`unbox`): a scalar's box IS the landed
    boxed-Nat layout (`{rc, tag 0, payload @8}`, width from the boxed
    type's map) — the real pipeline's `_boxed_const_1` shape (`box
    ty=UInt64` of a u64 literal binding); an OBJECT-row boxed type
    (Nat/tobj/tagged/obj) is the IDENTITY copy (the value IS the box
    already under the model).
- **The object tag dispatch** (this slice — the list discipline's
  engine): a `cases` whose scrutinee is an OBJECT-typed fvar (the i32
  pointer repr; anything outside the scalar lanes — Bool/UInt8/the
  prescan's enums — and the discr maps i32) reads the TAG u8 @4 (the
  landed layout's proved offset — the runtime's `lean_obj_tag` face)
  into a fresh scratch local and the alt chain branches on IT (the
  same `chainWalk` fold the scalar lane rides). The per-alt payload
  projections ride the object layout: the pipeline's field-binding
  lets (`let head := oproj[0] l`) land through the OPROJ lane — the
  ref field's 8-byte slot @8 + i*8, the SAME coordinates the ctor
  face writes. The ctor VALUE's two faces are keyed on the RESULT
  TYPE's row (the pipeline's impure-type law): a scalar-row ctor (an
  enum's) is the unboxed tag; an object-row ctor is a POINTER even
  when payload-free — the runtime's `lean_box`, an 8-byte {rc, tag}
  object (a bare tag would make the dispatch read the tag from the
  SCALAR — silently wrong).
  - **The list discipline** (the payoff): a list is the cons/nil
    objects — the literal's cons chain rides the object ctor face,
    the fold's `match l with` rides the tag dispatch, the cons arm's
    fields ride the oproj lane, the recursion rides the call lane's
    self-recursive fap, the sum rides the boxed-Nat add row, the
    result's `dec` rides the RC seed — the REAL pipeline's
    `listSum`/`listMain` family lowers, validates, runs, and answers
    (the pinned 15 + the objects' tag bytes read from the run's final
    memory).
- **The control flow** (the legacy `emitStep`'s jp/jmp + `buildAlts`,
  re-shaped for the frame-depth AST — the ONE AST's `br`/`brif` carry
  the frame DEPTH, not a label, so the lowering TRACKS the runtime
  frame depth `d` as its single walk parameter):
  - **The exit-frame discipline**: every `.return` stores the
    function's result local and branches `br (d-1)` — the outermost
    frame (emitted once per function around the whole body) absorbs
    the branch, and `localget res` after it hands the value to the
    run convention (the final stack). Values NEVER ride the stack
    across a branch (wasmcore's frames are no-result; a branch
    restores the frame-ENTRY stack) — every value crossing control
    rides a LOCAL.
  - **`cases`**: the alt chain folds to nested `if_`s keyed on the
    ctor index over the SCALAR-REPR scrutinee (branch on the VALUE,
    not a boxed tag); arm i of the chain lowers at depth `d+i` (each
    chain link is one `if_` frame). The case is TERMINAL in LCNF's
    impure spine (every arm ends return/jmp/unreach or a nested
    case) — no join local, no fallthrough value. A scrutinee/ctor
    outside the scalar discipline refuses loudly.
  - **`jp`/`jmp` (the join-point discipline)**: WAT has no goto; the
    legacy's block-and-fallthrough shape, in depths:
    ```
    block                    ;; $skip (outer)
      block                  ;; $jpL  (inner) — the gotos' target
        <k; a goto = arg stores + br into the jp>
        br 1                 ;; the fallthrough never reaches the body
      end
      <the jp body>          ;; a br to $jpL lands HERE
    end
    unreach                  ;; the seal (every k-path branched)
    ```
    The jmp's depth: the jp registers the offset `X = d_jp + 2` (the
    inner block sits two frames below the jp's own walk depth); a jmp
    at depth `d` emits `br (d - X)` — through any `if_` nesting, out
    of the inner block, into the body. The body is reached ONLY by a
    branch; control never falls past the seal.
  - **The loop shape (the growth beyond the legacy's conservative
    reject)**: a jp whose body jumps back to ITSELF (`jumpsTo` — the
    audit's loop-shaped-jp detection) cannot use the block shape (the
    body sits outside its own label's scope), but IT FITS the `loop`
    frame: the body inside `block [ loop [body; br 1] ]`, the
    self-goto = arg stores + `br (d - X)` restarting the loop (the
    loop frame absorbs `.branch 0` as the restart, carrying the
    branch-point locals — the stored args ride in). The ENTRY
    discipline: LCNF runs `k` FIRST, and a `br` cannot ENTER a frame,
    so `k` must be a straight-line let spine ending in the entry
    `jmp` (its arg stores fall through into the loop's first
    iteration); anything else refuses with the named `loopEntry`
    diagnostic (the entry-duplication transform is the named
    follow-up).
  - **The jmp scoping**: a jp's registration lives exactly as long as
    its structure's emission (deregistered after) — a jmp with no
    live registration (into a finished structure, or with no jp at
    all) refuses (`jpUnregistered`); an arity drift between the jmp's
    args and the jp's params refuses (`jpArityDrift`).
- **The multi-decl module**: `lowerFuncs` lowers SEVERAL decls into
  ONE module (one type + one function + one export each; the entry
  index = the decl order). The module's decls see each other through
  the call lane (the sibling registry `name → (index, arity)` — the
  function-index discipline); a fap naming a NON-sibling refuses
  (never a fabricated index-0 call).
- **The refusal discipline** (05 §4's envelope): every refusal is a
  closed `LowerError` ctor rendered into the ONE `Kit.Diag` (the
  GC-family E-codes); never a bare string, never a silent wrong
  lowering.
- **The recursion is WELL-FOUNDED over explicit total measures** (the
  `codeSize`/`altSize`/`altSizes` block): the LCNF `Code.size` is
  `partial` — unusable for a termination proof, and a `partial`
  lowering is a stub lie. The size measures ride the derived
  `sizeOf` (the pair measure's lex-order facts `lt_left`/`lt_right`
  are proven once); the READER folds (the prescan, `jumpsTo`) and
  the LOWERING itself (`lowerCode`/`chainWalk`) are then well-founded
  over those measures — the decrease proofs are simp+omega over the
  measure equations, kernel-checked, core-triple axioms only.

THE FRAGMENT'S EXACT COVERAGE (the honest boundary, this slice):

- covered: straight-line `let` chains of scalar literals, scalar
  copies, the payload-free-ctor tag lets, and the `binop?` faps (both
  widths + the u8 mask + the shifts + the conversions); `return` of a
  scalar fvar; `cases` on a Bool/U8-repr OR scalar-repr-enum
  scrutinee, with NESTED cases in the arms; `jp`/`jmp` — the block
  shape (shared joins), the loop shape (tail-recursive joins, the
  entry discipline), multiple jps, jps under cases; the multi-decl
  module (the cross-decl call lane: sibling calls at the function-
  table index, the executor's arg-marshalling + return convention,
  SELF-RECURSION at the own index — the fuel-bounded discipline);
  `unreach`.
- covered: straight-line `let` chains of scalar literals, scalar
  copies, the payload-free-ctor tag lets, and the `binop?` faps (both
  widths + the u8 mask + the shifts + the conversions); the BOXED-NAT
  lane (literal boxes in the bump arena, the
  `Nat.decEq`/`beq`/`decLt`/`decLe`/`add`/`sub`/`mul` fap rows with
  the runtime cap discipline, the ctor-case-on-Nat throw); the OBJECT
  SEED (scalar-field ctors + `sproj` reads, hand-built face);
  `return` of a scalar or object-pointer fvar; `cases` on a
  Bool/U8-repr OR scalar-repr-enum scrutinee, with NESTED cases in
  the arms; `jp`/`jmp` — the block shape (shared joins), the loop
  shape (tail-recursive joins, the entry discipline), multiple jps,
  jps under cases; the multi-decl module (the cross-decl call lane:
  sibling calls at the function-table index, the executor's
  arg-marshalling + return convention, SELF-RECURSION at the own
  index — the fuel-bounded discipline; Nat boxes cross calls as the
  i32 pointers they are); the CLOSURE discipline (`pap` allocation +
  the known-arity application + the `_closed` fixpoint family
  through the REAL pipeline — the closure object's layout read back
  from memory); the RC SEED (`inc`/`dec` with real rc cells + the
  over-dec trap, the scalar-box `box`/`unbox` round trip); the OBJECT
  TAG DISPATCH (the tag @4 read + the per-alt dispatch over an
  object-typed scrutinee, the oproj payload lane, the ctor's
  type-row faces — the LIST discipline: the real pipeline's cons/nil
  objects + the fold end-to-end); `unreach`.
- NOT covered (each lands with its named follow-up): the REUSE
  opportunity (the rc=0 slot's freelist — the size-class discipline;
  the leak stays bounded by the arena's page), object tag dispatch
  (`cases` on object-typed scrutinees — so map-over-list, whose list
  walk is object cases, is BEYOND this slice), ref-field reads
  (`oproj`/`proj`/`uproj`), in-place field writes
  (`sset`/`uset`/`oset`/`setTag`), the Perceus field-cascade dec
  (`dec` with `objs?`) and `del`, `return_call` (the
  tail-call lane — the legacy's fusion), loop-jp entries that are
  not a straight-line let spine (the entry-duplication transform),
  `extern` decl values. LANDED since: the cross-decl call lane, the
  FIRST-CLASS closure application (the indirect-call lane — the
  funcref table + `callindirect` + the sig registry; the pap-family
  partial applied first-class is the runtime `indirectSig` trap, the
  pinned tooth).

The five questions (notes/v3/01-core.md):

- **Root**: none — a lowering is a CROSSING (the LCNF decl read
  into the wasm module); its law face lands with the first
  correctness wave (the template pins are the tests' runtime face).
- **Carrier grade**: none new — the refusals ride `Kit.Diag` (the
  ONE envelope); the module output rides WasmCore's grades.
- **Spine reading**: the LCNF `Code` is the spine this module folds
  (one traversal, ONE parameter — the runtime frame depth `d`; the
  legacy `foldImpure` consolidation's discipline).
- **Ladder rung**: rung 1 (total folds over closed data; every
  non-fragment input refuses).
- **Gate row**: `gates kernel-check` + lintkit's gated roots.

Consumer trail: rides `Guest.Lcnf` (the input face), `WasmCore`
(the ONE AST + the op table + the module model), `Kit.Diag` (the
ONE envelope). Host-side (imports Lean via Guest.Lcnf).
-/

import Guest.Lcnf
import Kit.Diag
import WasmCore
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Guest

open Lean Compiler.LCNF

/-! ## The refusal vocabulary (the envelope discipline, 05 §4) -/

/-- THE closed-world refusal vocabulary: the lowering's failure KINDS
    as ctors with their payload data. Closed on purpose: a new
    fragment region is a new ctor, and the compiler drives the
    extension (15-patterns #15). -/
inductive LowerError where
  /-- A Lean type outside the scalar fragment (`what` names the
      position, `ty` the Lean type's rendering). -/
  | typeOutsideFragment (what : String) (ty : String)
  /-- THE bounded-Nat cap: a `Nat` literal at/above 2^62 is a DESIGN
      ERROR (the boxed-Nat model's pinned refusal — the legacy
      discipline, ported verbatim). -/
  | natLitCap (v : Nat)
  /-- A below-cap `Nat` literal: the boxed-Nat lane is the named
      follow-up — refused, never silently scalarized. RETIRED: the
      boxed-Nat lane LANDED (the bump-arena allocation + the
      `{rc, tag, i64 payload}` layout). The ctor stays in the closed
      vocabulary — its E-code GC2003 is an allocated row of the
      registry's history, and a retired code is never reused — but
      the lowering never fires it again. -/
  | natLane (v : Nat)
  /-- THE BOXED-NAT MODEL's pinned throw: a ctor-case on a `Nat`
      scrutinee. The generic tag dispatch would read the box's tag 0
      and treat the payload as a POINTER — silently wrong — so such a
      case throws loudly (the legacy discipline). The real pipeline
      never produces one (Nat cases compile to decEq fap chains); the
      hand-built face can. -/
  | natCtorCase
  /-- A construct outside the fragment (`what` = the LCNF form,
      `detail` = the named boundary it sits behind). -/
  | unsupportedConstruct (what : String) (detail : String)
  /-- An fvar read with no binding (a lowering-internal
      inconsistency — LCNF is ANF; this names the bug, never
      fabricates an index). -/
  | unboundFVar (name : String)
  /-- A non-fvar argument where ANF demands an fvar. -/
  | argShape (what : String)
  /-- A returned fvar's bound type does not match the result local's
      type. -/
  | armTypeMismatch (expected got : String)
  /-- A `jmp` whose target jp has no live registration (the jp's
      structure already ended, or there is no jp). -/
  | jpUnregistered (name : String)
  /-- A `jmp` whose arg count differs from the jp's param count. -/
  | jpArityDrift (jp : String) (got want : Nat)
  /-- The loop-entry discipline: a self-jumping jp whose continuation
      is not a straight-line let spine ending in the entry `jmp`. -/
  | loopEntry (detail : String)
  /-- RETIRED: the cross-decl call lane LANDED (the sibling `fap`
      lowers to `call` at the function-table index). The ctor stays in
      the closed vocabulary — its E-code GC2011 is an allocated row of
      the registry's history, and a retired code is never reused —
      but the lowering never fires it again. -/
  | declCall (fn : String)
  /-- A `pap` whose callee is not a SIBLING decl of the module — never
      a fabricated function index. -/
  | papUnknownFn (fn : String)
  /-- A `pap` whose captured-arg count is not below the callee's arity
      (a full application arrives as `fap`, an over-application is a
      drift). -/
  | papArityDrift (fn : String) (got want : Nat)
  /-- A NON-CLOSURE value applied first-class (the applied fvar's row
      is not a closure-pointer row — a scalar/boxed-scalar fvar has no
      fnIdx slot to dispatch through). The first-class lane LANDED
      (closure values lower to `callindirect`); this refusal is the
      lane's HONESTY face. -/
  | closureApplyUnknown (name : String)
  /-- A closure application whose captured + fresh count differs from
      the callee's arity. -/
  | closureApplyArityDrift (fn : String) (got want : Nat)
  /-- An `inc`/`dec` on a scalar-repr fvar (Perceus only RCs objects;
      this is a lowering-internal inconsistency). -/
  | rcOnScalar (op : String)
  /-- A `dec` with the field-cascade count (`objs?`) — the recursive
      dec needs the ref-field reads, the object seed's named boundary. -/
  | rcCascade
  /-- A ctor field whose pipeline layout class is outside the
      fragment's classification (an enum/Char-typed field — the
      pipeline's u8/u16/u32 enum repr depends on the ctor count, which
      is unknowable from the lowering's data; a non-const type). The
      field-packing law needs the field's size class. -/
  | ctorFieldClass (ty : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! The E-code CONSTANTS (the GC family): one place, ready for the
persisted registry (the WV-family precedent — the registry's stable
allocation is a later integration step; the in-file numbering is
monotone — a retired ctor's code is never reused). -/
namespace LowerError

def ecTypeOutsideFragment : Kit.ECode := ⟨"GC2001"⟩
def ecNatLitCap : Kit.ECode := ⟨"GC2002"⟩
def ecNatLane : Kit.ECode := ⟨"GC2003"⟩
def ecUnsupported : Kit.ECode := ⟨"GC2004"⟩
def ecUnboundFVar : Kit.ECode := ⟨"GC2005"⟩
def ecArgShape : Kit.ECode := ⟨"GC2006"⟩
def ecArmTypeMismatch : Kit.ECode := ⟨"GC2007"⟩
def ecJpUnregistered : Kit.ECode := ⟨"GC2008"⟩
def ecJpArityDrift : Kit.ECode := ⟨"GC2009"⟩
def ecLoopEntry : Kit.ECode := ⟨"GC2010"⟩
def ecDeclCall : Kit.ECode := ⟨"GC2011"⟩
def ecNatCtorCase : Kit.ECode := ⟨"GC2012"⟩
def ecPapUnknownFn : Kit.ECode := ⟨"GC2016"⟩
def ecPapArityDrift : Kit.ECode := ⟨"GC2017"⟩
def ecClosureApplyUnknown : Kit.ECode := ⟨"GC2018"⟩
def ecClosureApplyArityDrift : Kit.ECode := ⟨"GC2019"⟩
def ecRcOnScalar : Kit.ECode := ⟨"GC2020"⟩
def ecRcCascade : Kit.ECode := ⟨"GC2021"⟩
def ecCtorFieldClass : Kit.ECode := ⟨"GC2022"⟩

end LowerError

/-- THE diagnostic envelope: every refusal renders into the ONE Diag —
    the GC-family E-code, the payload data in `got`, the named
    boundary in the valid-space slot (the did-you-mean engine fills
    the suggestion face). -/
def LowerError.toDiag : LowerError → Kit.Diag
  | .typeOutsideFragment what ty =>
      Kit.Diag.closedWorld ecTypeOutsideFragment
        s!"{what} is outside the scalar fragment"
        .error ty
        ["UInt64 (i64)", "UInt32/UInt8/Bool/Char (i32)",
         "a scalar-representable enum (the tag discipline)"]
  | .natLitCap v =>
      Kit.Diag.closedWorld ecNatLitCap
        s!"bounded-Nat: literal {v} at/above the pinned cap 2^62 — a design \
           error (the boxed-Nat model refuses overflow by construction)"
        .error (toString v)
        ["a Nat literal below 2^62"]
  | .natLane _v =>
      Kit.Diag.closedWorld ecNatLane
        "bounded-Nat: the boxed-Nat lane is not landed (RETIRED — the \
         lane landed; this ctor is never fired again)"
        .error (toString _v)
        ["the boxed-Nat lane"]
  | .natCtorCase =>
      Kit.Diag.closedWorld ecNatCtorCase
        "ctor-case on a Nat scrutinee — the boxed-Nat model refuses: the \
         generic tag dispatch would read the box's tag 0 and treat the \
         payload as a pointer (silently wrong)"
        .error "Nat"
        ["Nat cases compile to decEq fap chains (the pipeline's shape)"]
  | .unsupportedConstruct what detail =>
      Kit.Diag.closedWorld ecUnsupported
        s!"unsupported LCNF construct: {what}"
        .error what
        [detail]
  | .unboundFVar name =>
      { code := ecUnboundFVar
      , message := s!"unbound fvar {name} — a lowering-internal \
                      inconsistency (LCNF is ANF; this is a bug)"
      , got := some name }
  | .argShape what =>
      { code := ecArgShape
      , message := s!"non-fvar argument where ANF demands an fvar: {what}"
      , got := some what }
  | .armTypeMismatch expected got =>
      Kit.Diag.closedWorld ecArmTypeMismatch
        "returned value's type differs from the function result's type"
        .error got [expected]
  | .jpUnregistered name =>
      Kit.Diag.closedWorld ecJpUnregistered
        "jmp to a join point with no live registration — the jp's \
         structure already ended (a br cannot enter a frame)"
        .error name
        ["a jmp inside its jp's structure"]
  | .jpArityDrift _jp got want =>
      Kit.Diag.closedWorld ecJpArityDrift
        s!"jmp arity drift: {got} args vs the jp's {want} params"
        .error (toString got)
        [s!"{want} args"]
  | .loopEntry detail =>
      Kit.Diag.closedWorld ecLoopEntry
        s!"the loop-entry discipline: {detail}"
        .error detail
        ["a straight-line let spine ending in the entry jmp"]
  | .declCall fn =>
      Kit.Diag.closedWorld ecDeclCall
        "cross-decl call: the call lane is wasmcore's in-flight work — \
         the module's decls stay call-disjoint in this slice"
        .error fn
        ["the op-surface faps (binop?) only"]
  | .papUnknownFn fn =>
      Kit.Diag.closedWorld ecPapUnknownFn
        "pap: the callee is not a sibling decl of the module — never a \
         fabricated function index"
        .error fn
        ["a pap naming a decl in the lowered set"]
  | .papArityDrift fn got want =>
      Kit.Diag.closedWorld ecPapArityDrift
        s!"pap arity drift on {fn}: {got} captured args vs the callee's \
           arity {want} (a full application arrives as fap, an \
           over-application is a drift)"
        .error (toString got)
        [s!"fewer than {want} captured args"]
  | .closureApplyUnknown name =>
      Kit.Diag.closedWorld ecClosureApplyUnknown
        s!"first-class closure application: {name} is not a closure value \
           (its row is not a closure-pointer row — no fnIdx to dispatch \
           through)"
        .error name
        ["a closure value (the pipeline's tobj/obj rows — the fnIdx @8 \
          is the table index)"]
  | .closureApplyArityDrift fn got want =>
      Kit.Diag.closedWorld ecClosureApplyArityDrift
        s!"closure application arity drift on {fn}: {got} (captured + \
           fresh) vs the callee's arity {want}"
        .error (toString got)
        [s!"{want} total args"]
  | .rcOnScalar op =>
      Kit.Diag.closedWorld ecRcOnScalar
        s!"Perceus RC ({op}) on a scalar-repr fvar — Perceus only RCs \
           objects (a lowering-internal inconsistency)"
        .error op
        ["an object-repr (i32) fvar"]
  | .rcCascade =>
      Kit.Diag.closedWorld ecRcCascade
        "Perceus RC: the field-cascade dec (objs?) needs the ref-field \
         reads — the object seed's named boundary"
        .error "dec (cascade)"
        ["a dec of an object with no ref fields"]
  | .ctorFieldClass ty =>
      Kit.Diag.closedWorld ecCtorFieldClass
        "ctor field outside the layout's size classes — the pipeline's \
         packing law (refs first, then scalars by size) needs the \
         field's size class, and an enum/Char repr's class depends on \
         the ctor count (unknowable from the lowering's data)"
        .error ty
        ["a field of UInt64/UInt32/UInt8 or an object-row type"]

/-- THE CLOSURE-POINTER rows (the first-class application's acceptance
    face): the pipeline's closure values ride `tobj`/`obj` (the object
    param/result rows — the probe-observed shapes). A scalar row (a
    UInt64 fvar applied) is the NON-CLOSURE refusal (`closureApply
    Unknown`); `tagged`/`Nat` (boxed scalars) refuse too — a boxed
    scalar applied is garbage the source type system prevents, and the
    model refuses what it cannot witness. -/
def closureRowName (c : Lean.Name) : Bool :=
  c == `tobj || c == `obj

/-- The sig registry's register-or-lookup: the signature's index in
    the accumulated list (registered at the tail when new). -/
def sigRegister : List WasmCore.FuncType → WasmCore.FuncType →
    Nat × List WasmCore.FuncType
  | [], ft => (0, [ft])
  | t :: ts, ft =>
      if t = ft then (0, t :: ts)
      else
        let (k, l) := sigRegister ts ft
        (k + 1, t :: l)

/-- The one-line rendering (the envelope's `.toString`). -/
def LowerError.render (e : LowerError) : String := Kit.Diag.toString e.toDiag

/-! ## The scalar type map (the legacy `wasmTyOf?`) -/

/-- THE OBJECT ROWS (the boxed-Nat lane's type face): the impure
    pipeline's object types — `tobj` (an object param/result), `tagged`
    (a boxed scalar or a payload-free ctor of an object type), `obj`
    (a compound object), and the source-level `Nat` — all ride the ONE
    pointer repr, `i32`. -/
def objectRowName (c : Lean.Name) : Bool :=
  c == `tobj || c == `tagged || c == `obj || c == `Nat

/-- The type expression's CONST NAME (the field-class lookup's key; a
    non-const type has none). -/
def tyName? : Lean.Expr → Option Lean.Name
  | .const c _ => some c
  | _ => none

/-- The BASE scalar names (the legacy `wasmTyOf?`'s rows). -/
def scalarTyOf? (c : Lean.Name) : Option WasmCore.ValType :=
  if c == `UInt64 then some .i64
  else if c == `UInt32 || c == `UInt8 || c == `Bool || c == `Char then some .i32
  else none

/-- The Lean type expression → the wasm scalar or object-pointer
    type. `enums` = the decl's scalar-representable enum registry (the
    prescan's observed evidence — `collectScalarEnums`); `none` =
    outside the fragment (the caller refuses with the named
    diagnostic). THE OBJECT ROWS: the impure pipeline's object types
    (`objectRowName`) and the prescan's registered enums ride `i32` —
    the ONE pointer repr. -/
def wasmTyOf? (enums : Std.HashMap Lean.Name Unit) : Lean.Expr → Option WasmCore.ValType
  | .const c _ =>
    match scalarTyOf? c with
    | some t => some t
    | none =>
        if objectRowName c then some .i32
        else if enums.contains c then some .i32 else none
  | _ => none

/-! ## The size measures (the well-founded substrate) -/

/-- The pair measure's LEFT fact (the lex order's first component). -/
theorem lt_left {p q : Nat × Nat} (h : p.1 < q.1) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) p q := by
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      exact Prod.Lex.left (ra := fun a₁ a₂ => a₁ < a₂) (rb := fun a₁ a₂ => a₁ < a₂) p₂ q₂ h

/-- The pair measure's RIGHT fact (equal heads, decreasing tails). -/
theorem lt_right {p q : Nat × Nat} (heq : p.1 = q.1) (h : p.2 < q.2) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) p q := by
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      subst heq
      exact Prod.Lex.right (ra := fun a₁ a₂ => a₁ < a₂) (rb := fun a₁ a₂ => a₁ < a₂)
        (b₁ := p₂) (b₂ := q₂) p₁ h

-- THE size measure over the LCNF `Code` (total, unlike the
-- toolchain's `partial` `Code.size`). The `FunDecl`/`Cases` hops
-- (the nested structures the derived sizeOf cannot see through on a
-- variable) are the two lemmas below, proven BEFORE the group.
theorem fd_sizeOf (fd : FunDecl .impure) : sizeOf fd.value < sizeOf fd := by
  cases fd with
  | mk _ _ _ _ v => simp [FunDecl.value]; omega
theorem cases_sizeOf (c : Cases .impure) : sizeOf c.alts < sizeOf c := by
  cases c with
  | mk _ _ _ alts => simp [Cases.alts]; omega

mutual
def codeSize : Code .impure → Nat
  | .let _ k => 1 + codeSize k
  | .jp fd k => 1 + codeSize fd.value + codeSize k
  | .cases c => 1 + altSizes c.alts 0
  | .return _ | .jmp .. | .unreach _ | .fun .. => 1
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => 1 + codeSize k
  termination_by c => (sizeOf c, 0)
  decreasing_by
    all_goals (try have hfd := fd_sizeOf fd)
    all_goals (try have hcs := cases_sizeOf c)
    all_goals (first
      | exact lt_left (by simp <;> omega)
      | exact lt_right (rfl) (by omega))
def altSize : Alt .impure → Nat
  | .ctorAlt _ code => 1 + codeSize code
  | .default code => 1 + codeSize code
  | .alt _ _ _ _ => 0
  termination_by a => (sizeOf a, 0)
  decreasing_by
    all_goals exact lt_left (by simp <;> omega)
/-- The suffix sum of the arm sizes from index `i` (the chain walk's
    measure: the index step AND the chain→walk cross-call both
    decrease it). -/
def altSizes (alts : Array (Alt .impure)) (i : Nat) : Nat :=
  if h : i < alts.size then altSize alts[i] + altSizes alts (i + 1) else 0
  termination_by (sizeOf alts, alts.size - i)
  decreasing_by
    all_goals (first
      | exact lt_left (p := (sizeOf alts[i], 0))
          (q := (sizeOf alts, alts.size - i)) (by simp)
      | exact lt_right (p := (sizeOf alts, alts.size - (i + 1)))
          (q := (sizeOf alts, alts.size - i)) (rfl) (by omega))
end

theorem altSize_pos (a : Alt .impure) : 1 ≤ altSize a := by
  cases a with
  | ctorAlt info code => simp [altSize]
  | default code => simp [altSize]
  | alt _ _ _ h => exact absurd h (by simp)

/-- The chain walk's index step decreases the suffix measure. -/
theorem altSizes_suffix (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size) :
    altSizes alts (i + 1) < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  have h2 := altSize_pos alts[i]
  omega

/-- The chain walk's ARM call decreases the suffix measure (the ctor
    arm's code is a summand). -/
theorem altSizes_gt_ctor (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size)
    (info : CtorInfo) (code : Code .impure) (hget : alts[i] = Alt.ctorAlt info code) :
    codeSize code < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  rw [h1, hget]
  have h2 : altSize (Alt.ctorAlt info code) = 1 + codeSize code := by rw [altSize]
  rw [h2]; omega

/-- The chain walk's DEFAULT-arm call (the same shape). -/
theorem altSizes_gt_default (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size)
    (code : Code .impure) (hget : alts[i] = Alt.default code) :
    codeSize code < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  rw [h1, hget]
  have h2 : altSize (Alt.default code) = 1 + codeSize code := by rw [altSize]
  rw [h2]; omega

/-! ## The tag prescan (the scalar-representable enums) -/

/-- The scalar-enum registration criterion: at least one ctor alt, and
    EVERY ctor alt is payload-free (`CtorInfo.isScalar`) with its tag
    below 256 (the unboxed-tag repr boundary). -/
def altsScalarRepr? (alts : List (Alt .impure)) : Bool :=
  let ctorAlts := alts.filterMap
    (fun a => match a with | .ctorAlt info _ => some info | _ => none)
  ctorAlts.length > 0
    && ctorAlts.all (fun i => i.isScalar && i.cidx < 256)

/-- The registry union (insertMany over the toList). -/
def enumUnion (m1 m2 : Std.HashMap Lean.Name Unit) : Std.HashMap Lean.Name Unit :=
  m1.insertMany m2.toList

/-- The alt-list's size (the list walkers' measure — structural over
    the list, so it needs no well-founded machinery of its own). -/
def listAltSize : List (Alt .impure) → Nat
  | [] => 0
  | a :: rest => altSize a + listAltSize rest

/-! The prescan: the decl's code → the scalar-representable enum
registry (the type names whose OBSERVED cases are all payload-free
ctor alts). Purely structural; the registry feeds `wasmTyOf?` (the
tag discipline — a scalar enum's repr IS the unboxed ctor tag).
NOTE the field orders the patterns spell: a `uset` carries
`y : FVarId` third and a `del` the fvar FIRST — the or-pattern's `k`
binds the CODE field in every arm. -/
mutual
def collectScalarEnums (code : Code .impure) : Std.HashMap Lean.Name Unit :=
  match code with
  | .let _ k => collectScalarEnums k
  | .jp fd k => enumUnion (collectScalarEnums fd.value) (collectScalarEnums k)
  | .cases c =>
    let here :=
      if altsScalarRepr? c.alts.toList
      then ({} : Std.HashMap Lean.Name Unit).insert c.typeName ()
      else ({} : Std.HashMap Lean.Name Unit)
    altScan c.alts 0 here
  | .return _ | .jmp .. | .unreach _ => ({} : Std.HashMap Lean.Name Unit)
  | .fun .. => ({} : Std.HashMap Lean.Name Unit)
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => collectScalarEnums k
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def altScan (alts : Array (Alt .impure)) (i : Nat) (m : Std.HashMap Lean.Name Unit) :
    Std.HashMap Lean.Name Unit :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt _ code => altScan alts (i + 1) (enumUnion m (collectScalarEnums code))
    | .default code => altScan alts (i + 1) (enumUnion m (collectScalarEnums code))
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    m
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The loop-shape detector (the audit's `jumpsTo`) -/

-- Does `code` contain a `jmp` to `target`? (The loop-shape
-- detector — the audit's `jumpsTo`, ported as a plain structural
-- fold; the same field-order spell as `collectScalarEnums`.)
mutual
def jumpsTo (target : Lean.FVarId) (code : Code .impure) : Bool :=
  match code with
  | .jmp f _ => f == target
  | .jp fd k => jumpsTo target fd.value || jumpsTo target k
  | .cases c => altJumps target c.alts 0
  | .let _ k | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _
  | .setTag _ _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ =>
    jumpsTo target k
  | .return _ | .unreach _ => false
  | .fun .. => false
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def altJumps (target : Lean.FVarId) (alts : Array (Alt .impure)) (i : Nat) : Bool :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt _ code => jumpsTo target code || altJumps target alts (i + 1)
    | .default code => jumpsTo target code || altJumps target alts (i + 1)
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    false
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The op surface (the legacy `binop?`, grown) -/

/-- The LCNF callee name → (arity, instructions). The closed row set
    is the legacy's proven surface grown by the probe-mined rows; a
    fap outside it refuses loudly (the named boundary — never a
    silent wrong lowering). The u8 arith rows end in the `and 0xFF`
    mask (i32 arithmetic wraps mod 2^32; a `UInt8` wraps mod 2^8).
    Ops are consumed from `WasmCore.OpTable`'s projections everywhere
    downstream (the ONE table, 07-extensibility R6). -/
def binop? : Lean.Name → Option (Nat × List WasmCore.Instr)
  | ``UInt64.add => some (2, [.op .i64add])
  | ``UInt64.sub => some (2, [.op .i64sub])
  | ``UInt64.mul => some (2, [.op .i64mul])
  | ``UInt64.decLt => some (2, [.op .i64ltu])
  | ``UInt64.decEq => some (2, [.op .i64eq])
  | ``UInt64.shiftRight => some (2, [.op .i64shru])
  | ``UInt64.toUInt32 => some (1, [.op .i32wrapi64])
  | ``UInt32.add => some (2, [.op .i32add])
  | ``UInt32.sub => some (2, [.op .i32sub])
  | ``UInt32.mul => some (2, [.op .i32mul])
  | ``UInt32.land => some (2, [.op .i32and])
  | ``UInt32.xor => some (2, [.op .i32xor])
  | ``UInt32.decLt => some (2, [.op .i32ltu])
  | ``UInt32.decEq => some (2, [.op .i32eq])
  | ``UInt32.shiftRight => some (2, [.op .i32shru])
  | ``UInt32.toUInt64 => some (1, [.op .i64extendi32u])
  | ``UInt8.add => some (2, [.op .i32add, .i32const 255, .op .i32and])
  | ``UInt8.sub => some (2, [.op .i32sub, .i32const 255, .op .i32and])
  | ``UInt8.mul => some (2, [.op .i32mul, .i32const 255, .op .i32and])
  | ``UInt8.decLt => some (2, [.op .i32ltu])
  | ``UInt8.decEq => some (2, [.op .i32eq])
  | ``UInt8.land => some (2, [.op .i32and])
  | ``UInt8.xor => some (2, [.op .i32xor])
  | ``UInt8.shiftRight => some (2, [.op .i32shru])
  | ``UInt8.toUInt64 => some (1, [.op .i64extendi32u])
  | _ => none

/-- THE bounded-Nat cap: 2^62 (the legacy's pinned design constant —
    a literal at/above it is a design error, refused before anything
    else is asked about it). -/
def natCap : Nat := 4611686018427387904

/-! ## The lowering state -/

/-- One lowering's state: the fvar → (local index, type) bindings,
    the DECLARED locals beyond the params (creation order — the
    encoder's local groups), the next fresh index, the emitted
    instructions (accumulated REVERSED; `emitted` reverses at the
    end), the LIVE jp registrations (target → the depth offset `X`
    with `br (d - X)` + the param locals), the decl's scalar-enum
    registry (the prescan), and the module's SIBLING registry (the
    cross-decl call lane's function-index discipline: decl name →
    (function-table index, param arity) — `lowerFuncs`' decl order,
    a self-recursive decl's OWN index included). -/
structure LState where
  /-- The fvar → (local index, wasm type, the LEAN type's const name —
      the field-class law's key at the ctor arm; `none` for a
      non-const type). -/
  fvars : Std.HashMap Lean.FVarId (Nat × WasmCore.ValType × Option Lean.Name) := {}
  locals : List WasmCore.ValType := []
  next : Nat := 0
  out : List WasmCore.Instr := []
  jps : Std.HashMap Lean.FVarId (Nat × List Nat) := {}
  enums : Std.HashMap Lean.Name Unit := {}
  /-- The module's sibling registry (the CALL LANE's function-index
      discipline): decl name → (the function-table index —
      `lowerFuncs`' decl order — and the param arity). -/
  sibs : List (Lean.Name × Nat × Nat) := []
  /-- THE CLOSURE PROVENANCE (the known-arity application's
      discipline): a pap-bound fvar → (the pap's callee name, the
      captured (local, type) slots in order). Function-scoped like
      the locals (a second application reuses the same captured
      locals — closures are read-only under the model). -/
  paps : Std.HashMap Lean.FVarId (Lean.Name × List (Nat × WasmCore.ValType)) := {}
  /-- THE SIG REGISTRY (the indirect-call lane's type-index
      discipline): the closure signatures the first-class applications
      need, in registration order — appended to the module's type
      section AFTER the decl types (the application's type index =
      the decl count + the registry position). Module-scoped: the
      fold threads it across the decls (`lowerFuncs`). -/
  sigs : List WasmCore.FuncType := []
  deriving Inhabited

/-- The lowering monad: state threading over the closed refusal
    envelope (the legacy `StateT S (Except String)` shape, with the
    envelope in place of the bare string). -/
abbrev M := StateT LState (Except LowerError)

/-- The PRIMITIVE: emit one instruction (appended at the tail of the
    reversed accumulator). -/
def emitI (i : WasmCore.Instr) : M Unit :=
  modify fun s => { s with out := i :: s.out }

/-- The emitted instructions IN ORDER (the accumulator reversed). -/
def emitted : M (List WasmCore.Instr) :=
  return (← get).out.reverse

/-- The type map inside the monad (the state carries the prescan's
    enum registry). -/
def tyMap? (e : Lean.Expr) : M (Option WasmCore.ValType) := do
  return wasmTyOf? (← get).enums e

/-- Bind a fresh local of type `t` to the fvar (the legacy
    `bindLocal`). The index is beyond the params (params bind first,
    0..n-1), so it lands in the DECLARED list. `tyName` records the
    LEAN type's const name (the field-class law's key). -/
def bindLocal (fvarId : Lean.FVarId) (t : WasmCore.ValType)
    (tyName : Option Lean.Name) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with
    fvars := s.fvars.insert fvarId (idx, t, tyName)
    locals := s.locals ++ [t]
    next := s.next + 1 }
  return idx

/-- Bind PARAM local i (index in order; NOT in the declared-locals
    list — wasmcore's `Func.locals` means locals BEYOND the params,
    and the validator/types read `params ++ locals`). -/
def bindParam (fvarId : Lean.FVarId) (t : WasmCore.ValType)
    (tyName : Option Lean.Name) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with fvars := s.fvars.insert fvarId (idx, t, tyName), next := s.next + 1 }
  return idx

/-- Bind a fresh local of type `t` with NO fvar (the function's
    result local — the exit-frame discipline's carrier). -/
def bindFresh (t : WasmCore.ValType) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with locals := s.locals ++ [t], next := s.next + 1 }
  return idx

/-- The local's INDEX (the legacy `load`; unbound = the loud bug
    diagnostic, never a fabricated index). -/
def load (fvarId : Lean.FVarId) : M Nat := do
  match (← get).fvars[fvarId]? with
  | some (n, _) => return n
  | none => throw (.unboundFVar fvarId.name.toString)

/-- The fvar's BOUND type (the return-type check's lookup). -/
def tyOf? (fvarId : Lean.FVarId) : M (Option WasmCore.ValType) := do
  return (← get).fvars[fvarId]? |>.map (·.2.1)

/-- The fvar's recorded LEAN type name (the field-class law's key). -/
def tyNameOf? (fvarId : Lean.FVarId) : M (Option Lean.Name) := do
  match (← get).fvars[fvarId]? with
  | some (_, _, nm) => return nm
  | none => return none

/-- Run `act` with a FRESH output buffer, returning the emitted
    instructions in order while KEEPING the bindings, the
    fresh-local counter, and the jp registrations (wasm locals are
    function-scoped; the legacy `scopedOut` discipline). -/
def scopedOut (act : M Unit) : M (List WasmCore.Instr) := do
  let s ← get
  match StateT.run act { s with out := [] } with
  | .error e => throw e
  | .ok ((), s2) =>
      set { s2 with out := s.out }
      return s2.out.reverse

/-! ## The argument + let emission -/

/-- Emit one argument's load (LCNF is ANF: a real arg is always an
    fvar; an erased arg pushes nothing — the legacy `emitArg`). -/
def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emitI (.localget (← load fvarId))
  | .erased => pure ()
  | .type .. => throw (.argShape "a type argument")

/-! ## The boxed-Nat lane (the object discipline's seed) -/

/-- THE BOXED OBJECT's header + payload layout: `{rc @0, tag u8 @4,
    i64 payload @8}` — the 8-byte header slot + the 8-byte payload
    slot (the legacy's proved offsets). THE RC SEED: the rc cell is
    REAL now — every allocation stores rc = 1 (one reference at
    birth), the `inc`/`dec` forms maintain it; a dec to ZERO marks the
    object DEAD (rc=0 observable) with the slot never reused (the
    size-class freelist is the named follow-up). -/
def boxSize : Nat := 8 + 8

/-- THE heap base: the bump arena's first object address. Cell
    `0..4` holds the bump pointer ITSELF (the allocator's state lives
    IN the linear memory — the module model has no globals); a
    zeroed cell (fresh memory) bumps from here. The arena starts one
    full box-slot in — the null region `0..boxSize` (the bump cell
    inside it) is never allocated, so a box's payload (i64, 8-aligned)
    always clears the cell. -/
def heapBase : Nat := boxSize
-- The nolint rows: these are SEMANTICALLY distinct layout rows sharing
-- numeric values with unrelated constants (a tag VALUE is not an rc
-- offset; a payload offset is not a closure's fnIdx slot) — the
-- dup-body linter's opt-out, the named reason.
@[nolint linter.guestlang.dupDefBodies "the Nat box's tag VALUE is its own boxed-Nat-model row — a shared numeric value with the rc cell's offset is coincidence, not duplication"]
def boxTag : Nat := 0
def boxTagOff : Nat := 4
@[nolint linter.guestlang.dupDefBodies "the box payload's offset is its own layout row — a shared numeric value with the closure object's fnIdx slot is coincidence, not duplication"]
def boxPayloadOff : Nat := 8

/-- THE RC CELL's facts: the u32 @0, one reference at birth. -/
-- The nolint rows: these are SEMANTICALLY distinct layout rows sharing
-- numeric values with unrelated constants (a tag is not an rc offset;
-- a flat-param cap is not a closure layout offset) — the dup-body
-- linter's opt-out, the named reason.
@[nolint linter.guestlang.dupDefBodies "the rc cell's offset is its own layout row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def rcCellOff : Nat := 0
@[nolint linter.guestlang.dupDefBodies "the birth reference count is its own RC-discipline row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def rcInit : Nat := 1

/-- THE CLOSURE OBJECT's layout (the legacy trampoline's proved
    offsets): `{rc @0, tag 254 @4, fnIdx u32 @8, captured slots
    @16 + i*8}`. The fnIdx is the pap callee's FUNCTION-TABLE INDEX —
    the known-arity application calls DIRECTLY (the indirect-call
    lane is WasmCore's named exclusion), so the stored index is the
    layout's honest face awaiting that lane; the captured slots ride
    the object discipline's 8-byte slots, width by mapped type. -/
def closureTag : Nat := 254
@[nolint linter.guestlang.dupDefBodies "the closure object's fnIdx slot is its own layout row (the legacy trampoline's proved offsets) — a shared numeric value is coincidence, not duplication"]
def closureFnIdxOff : Nat := 8
@[nolint linter.guestlang.dupDefBodies "the closure object's first captured slot is its own layout row (the legacy trampoline's proved offsets) — a shared numeric value is coincidence, not duplication"]
def closureCapOff : Nat := 16
def closureSize (nCap : Nat) : Nat := closureCapOff + nCap * 8

/-! ## The field-layout law (the pipeline's `CtorLayout` packing) -/

/-- THE FIELD's size class: a ref field (an object-row type) rides one
    full 8-byte slot; a scalar rides the scalar region, packed by size
    class, largest first. An enum/Char-typed field has NO class here —
    the pipeline's enum repr (u8/u16/u32) depends on the ctor count,
    unknowable from the lowering's data — the named `ctorFieldClass`
    refusal. -/
inductive FieldClass where
  | obj | u64 | u32 | u8
deriving BEq, DecidableEq, Inhabited, Repr

def fieldClass? : Option Lean.Name → Option FieldClass
  | some `UInt64 => some .u64
  | some `UInt32 => some .u32
  | some `UInt8 => some .u8
  | some c => if objectRowName c then some .obj else none
  | none => none

/-- The class's byte size (the packing law's weight; a ref field's
    slot is charged 8 by the slot arithmetic, not here). -/
def fieldSize : FieldClass → Nat
  | .u64 => 8 | .u32 => 4 | .u8 => 1 | .obj => 0

/-- A scalar field's offset WITHIN the scalar region: the sum of the
    strictly-larger classes' sizes (each larger class packs first) plus
    the same-class fields packed before it (arg order) — the pipeline's
    `adjustScalarsForSize` discipline (the 8/4/2/1 rounds). -/
def scalarOff (pre : List FieldClass) (cl : FieldClass) : Nat :=
  (pre.filter (fun c => fieldSize c > fieldSize cl)).foldl
    (fun n c => n + fieldSize c) 0 +
  (pre.filter (fun c => c == cl)).length * fieldSize cl

/-- THE BUMP ALLOCATOR (inlined per allocation site): read the bump
    pointer from cell 0, bump by the static size, store back, leave
    the object's address on the stack. A zeroed cell (fresh memory)
    bumps from `heapBase` — the `select` picks `base + sz` over
    `p + sz` exactly when `p < base`, so the first allocation lands
    above the pointer cell + header without any init code. NO RC: the
    allocation is never freed within a run (the named boundary — the
    memory leaks inside the run's one page; an exhausted arena is the
    bounded-memory `memOOB` trap, never corruption). Returns the
    scratch local holding the address (also left on the stack). -/
def allocSeq (sz : Nat) : M Nat := do
  let s ← bindFresh .i32
  emitI (.i32const 0); emitI (.mem .i32load 0 none)              -- p
  emitI (.i32const sz); emitI (.op .i32add)                      -- p + sz
  emitI (.i32const heapBase); emitI (.i32const sz); emitI (.op .i32add)
                                                                 -- base + sz
  emitI (.i32const 0); emitI (.mem .i32load 0 none)              -- p
  emitI (.i32const heapBase); emitI (.op .i32ltu)                -- p < base
  emitI .select                                                  -- new
  emitI (.localset s)
  emitI (.i32const 0)                                            -- the address
  emitI (.localget s)                                            -- the value (top)
  emitI (.mem .i32store 0 none)                                  -- bump = new
  -- THE RC SEED: one reference at birth (the reused-slot question is
  -- the freelist's size-class discipline — the named follow-up)
  emitI (.localget s)
  emitI (.i32const rcInit)
  emitI (.mem .i32store rcCellOff none)
  emitI (.localget s)
  return s

/-- Store the Nat box's tag (u8 @4). -/
def storeBoxTag (ptr : Nat) : M Unit := do
  emitI (.localget ptr); emitI (.i32const boxTag)
  emitI (.mem .i32store8 boxTagOff none)

/-- Store the Nat box's payload from a local (i64 @8). -/
def storeBoxPayload (ptr r : Nat) : M Unit := do
  emitI (.localget ptr); emitI (.localget r)
  emitI (.mem .i64store boxPayloadOff none)

/-- Store the Nat box's payload from a literal (the literal-box
    lane). -/
def storeBoxPayloadLit (ptr : Nat) (v : Nat) : M Unit := do
  emitI (.localget ptr); emitI (.i64const v)
  emitI (.mem .i64store boxPayloadOff none)

/-- THE RUNTIME OVERFLOW DISCIPLINE's shape: emit
    `block [cond, brif 0, unreach]` — the condition TRUE exits the
    block (the ok path); falling through hits `unreach` (the trap).
    The 2^62 cap holds at runtime: a breach TRAPS loudly, never wraps
    silently (the boxed-Nat model's honesty, the runtime face). The
    `br 0` is frame-relative — the discipline composes under any
    surrounding nesting. -/
def trapUnless (cond : List WasmCore.Instr) : M Unit :=
  emitI (.block (cond ++ [.brif 0, .unreach]))

/-- THE RC OP (the Perceus discipline's seed face): the rc cell's REAL
    arithmetic — `inc` adds n, `dec` subtracts n under the OVER-DEC
    GUARD (rc ≥ n or the unreach trap: a dec past zero is a
    use-after-free bug, never a silent wrap). The target must be an
    OBJECT-repr fvar (the rc cell lives @0 of the object); a scalar
    target is the named `rcOnScalar` inconsistency. NO REUSE: a dec
    to zero leaves rc=0 — the DEAD object is observable, its slot is
    never reclaimed (the size-class freelist is the named follow-up;
    the leak is bounded by the arena's page). -/
def rcOp (op : String) (fvarId : Lean.FVarId) (n : Nat) (isInc : Bool) : M Unit := do
  match ← tyOf? fvarId with
  | some .i32 =>
      let ptr ← load fvarId
      emitI (.localget ptr); emitI (.mem .i32load rcCellOff none)
      let rc ← bindFresh .i32
      emitI (.localset rc)
      unless isInc do
        -- the over-dec guard: NOT (rc <u n) — a breach traps loudly
        trapUnless [.localget rc, .i32const n, .op .i32ltu, .op .i32eqz]
      emitI (.localget rc); emitI (.i32const n)
      emitI (.op (if isInc then .i32add else .i32sub))
      let rc' ← bindFresh .i32
      emitI (.localset rc')
      emitI (.localget ptr); emitI (.localget rc')
      emitI (.mem .i32store rcCellOff none)
  | _ => throw (.rcOnScalar op)

/-- The boxed-Nat fap kinds (the legacy's sanctioned surface; the
    probe-observed pipeline rows: `Nat.add`/`mul`/`sub`/`decLt`/
    `decEq`/`decLe` — `Nat.beq` joins the family for the hand-built
    face). -/
inductive NatFap where
  | decEq | beq | decLt | decLe | add | sub | mul

def natFap? : Lean.Name → Option NatFap
  | ``Nat.decEq => some .decEq | ``Nat.beq => some .beq
  | ``Nat.decLt => some .decLt | ``Nat.decLe => some .decLe
  | ``Nat.add => some .add | ``Nat.sub => some .sub
  | ``Nat.mul => some .mul
  | _ => none

/-- Both args' payloads loaded into fresh i64 scratch locals (the
    boxed-Nat faps' read discipline: ANF fvar args, the payload
    i64 @8). -/
def loadPayloads (fn : Lean.Name) (args : Array (Arg .impure)) : M (Nat × Nat) := do
  if args.size != 2 then
    throw (.unsupportedConstruct s!"fap {fn}"
      s!"arity {args.size} on a boxed-Nat row of arity 2")
  let mut ps : List Nat := []
  for a in args do
    match a with
    | .fvar _ =>
        emitArg a
        emitI (.mem .i64load boxPayloadOff none)
        let s ← bindFresh .i64
        emitI (.localset s)
        ps := ps ++ [s]
    | _ => throw (.argShape "a boxed-Nat fap argument (ANF demands an fvar)")
  match ps with
  | [x, y] => pure (x, y)
  | _ => throw (.argShape "a boxed-Nat fap argument")

/-- The compare rows' emission: the payloads' UNSIGNED machine
    compare (a Nat's payload IS its magnitude; the cap keeps
    signed/unsigned equal) → the raw i32 Bool. -/
def natCompare (o : WasmCore.Op) (x y : Nat) : M Unit := do
  emitI (.localget x); emitI (.localget y); emitI (.op o)

/-- The arith rows' box face: bind the result (an object pointer),
    allocate the fresh box, store tag + payload (Nats are immutable
    under the model — every arith result is a NEW box). -/
def boxFromPayload (decl : LetDecl .impure) (r : Nat) : M Unit := do
  match ← tyMap? decl.type with
  | none => throw (.typeOutsideFragment "boxed-Nat result type" (toString decl.type))
  | some t =>
      let l ← bindLocal decl.fvarId t (tyName? decl.type)
      let _p ← allocSeq boxSize
      emitI (.localset l)
      storeBoxTag l
      storeBoxPayload l r

/-- THE BOXED-NAT FAP LANE (the legacy's fap arms, inline-lowered).
    All rows arity 2 over the PAYLOADS (the boxes' i64 @8); the
    compares answer the raw i32 Bool, the arith allocates fresh
    boxes under the runtime cap discipline. -/
def emitNatFap (fn : Lean.Name) (k : NatFap) (decl : LetDecl .impure)
    (args : Array (Arg .impure)) : M Unit := do
  let (x, y) ← loadPayloads fn args
  match k with
  | .decEq | .beq | .decLt | .decLe =>
      match ← tyMap? decl.type with
      | none => throw (.typeOutsideFragment "fap result type" (toString decl.type))
      | some t =>
          let l ← bindLocal decl.fvarId t (tyName? decl.type)
          match k with
          | .decEq | .beq => natCompare .i64eq x y
          | .decLt => natCompare .i64ltu x y
          | .decLe => natCompare .i64leu x y
          | _ => pure ()
          emitI (.localset l)
  | .add | .sub | .mul =>
      match k with
      | .add =>
          emitI (.localget x); emitI (.localget y); emitI (.op .i64add)
          let r ← bindFresh .i64
          emitI (.localset r)
          -- both payloads < 2^62 ⇒ the true sum < 2^63 — no u64 wrap,
          -- the cap check is EXACT
          trapUnless [.localget r, .i64const natCap, .op .i64ltu]
          boxFromPayload decl r
      | .sub =>
          -- a − b with a < b would wrap (u64) — the trap fires first
          trapUnless [.localget x, .localget y, .op .i64ltu, .op .i32eqz]
          emitI (.localget x); emitI (.localget y); emitI (.op .i64sub)
          let r ← bindFresh .i64
          emitI (.localset r)
          -- x < 2^62 ⇒ x − y < 2^62 — no cap check needed (the
          -- underflow trap above is the only wrap risk)
          boxFromPayload decl r
      | .mul =>
          -- THE 128-BIT GUARD. x = xh·2³² + xl, y = yh·2³² + yl; the
          -- four quarter products give the full product's high word:
          -- high = hh + ((ll>>32) + lh + hl)>>32 ≠ 0 ⟺ the true product
          -- passed 2^64 (the u64 result would be a wrap-masquerade —
          -- e.g. 2⁴¹·2⁴¹ wraps to 0). Bounds: payloads < 2^62 ⇒
          -- xh,yh < 2^30 ⇒ ll,lh,hl < 2^62 ⇒ t < 2^63 (no wrap),
          -- hh < 2^60.
          emitI (.localget x); emitI (.i64const 32); emitI (.op .i64shru)
          let xh ← bindFresh .i64
          emitI (.localset xh)
          emitI (.localget y); emitI (.i64const 32); emitI (.op .i64shru)
          let yh ← bindFresh .i64
          emitI (.localset yh)
          emitI (.localget x); emitI (.localget xh)
          emitI (.i64const 4294967296); emitI (.op .i64mul); emitI (.op .i64sub)
          let xl ← bindFresh .i64
          emitI (.localset xl)
          emitI (.localget y); emitI (.localget yh)
          emitI (.i64const 4294967296); emitI (.op .i64mul); emitI (.op .i64sub)
          let yl ← bindFresh .i64
          emitI (.localset yl)
          emitI (.localget xl); emitI (.localget yl); emitI (.op .i64mul)
          let ll ← bindFresh .i64
          emitI (.localset ll)
          emitI (.localget xh); emitI (.localget yl); emitI (.op .i64mul)
          let lh ← bindFresh .i64
          emitI (.localset lh)
          emitI (.localget xl); emitI (.localget yh); emitI (.op .i64mul)
          let hl ← bindFresh .i64
          emitI (.localset hl)
          emitI (.localget xh); emitI (.localget yh); emitI (.op .i64mul)
          let hh ← bindFresh .i64
          emitI (.localset hh)
          emitI (.localget ll); emitI (.i64const 32); emitI (.op .i64shru)
          emitI (.localget lh); emitI (.op .i64add)
          emitI (.localget hl); emitI (.op .i64add)
          let t ← bindFresh .i64
          emitI (.localset t)
          emitI (.localget hh); emitI (.localget t)
          emitI (.i64const 32); emitI (.op .i64shru); emitI (.op .i64add)
          let hi ← bindFresh .i64
          emitI (.localset hi)
          -- r = the u64 product (the true low word when hi = 0)
          emitI (.localget x); emitI (.localget y); emitI (.op .i64mul)
          let r ← bindFresh .i64
          emitI (.localset r)
          -- the guard: hi = 0 AND the low word under the cap
          trapUnless [.localget hi, .i64const 0, .op .i64eq
                     , .localget r, .i64const natCap, .op .i64ltu
                     , .op .i32and]
          boxFromPayload decl r
      | _ => pure ()

/-! ## The literal rendering + the let emission -/

/-- The literal kinds' rendering (LitValue has no Repr — the closed
    universe's explicit spellings). -/
def litKind : LitValue → String
  | .nat _ => "nat" | .str _ => "str" | .uint8 _ => "uint8"
  | .uint16 _ => "uint16" | .uint32 _ => "uint32" | .uint64 _ => "uint64"
  | .usize _ => "usize"

/-- THE `let` lowering (the legacy `emitLet`'s slice, grown): the
    scalar literals, the copy, the payload-free-ctor tag, and the
    `binop?` faps; every other value form refuses with its named
    boundary. -/
def emitLet (decl : LetDecl .impure) : M Unit := do
  let ty? ← tyMap? decl.type
  match decl.value with
  | .lit (.uint64 v) =>
      let l ← bindLocal decl.fvarId .i64 (tyName? decl.type)
      emitI (.i64const v.toNat); emitI (.localset l)
  | .lit (.uint32 v) | .lit (.uint8 v) =>
      let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
      emitI (.i32const v.toNat); emitI (.localset l)
  | .lit (.nat v) =>
      -- THE BOXED-NAT LANE. The cap check is the model's pinned
      -- behavior (a literal at/above 2^62 is a design error — the
      -- legacy discipline, ported; the REAL pipeline's constant
      -- folding delivers statically-overflowing arithmetic as exactly
      -- such a literal). Below the cap: the runtime repr is a BOX —
      -- {rc reserved, tag 0, payload i64 @8} — allocated in the bump
      -- arena (no RC: never freed within a run — the named boundary).
      if v >= natCap then
        throw (.natLitCap v)
      else do
        let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
        let _p ← allocSeq boxSize
        emitI (.localset l)
        storeBoxTag l
        storeBoxPayloadLit l v
  | .lit v =>
      throw (.typeOutsideFragment "literal kind"
        s!"{litKind v} (only uint64/uint32/uint8 (+ the boxed Nat) are modeled)")
  | .erased =>
      -- binds nothing; an erased arg pushes nothing (the legacy arm)
      pure ()
  | .fvar fvarId args =>
      if args.isEmpty then
        match ty? with
        | some t =>
            let l ← bindLocal decl.fvarId t (tyName? decl.type)
            emitI (.localget (← load fvarId)); emitI (.localset l)
        | none =>
            throw (.typeOutsideFragment "copy type" (toString decl.type))
      else
        -- THE CLOSURE APPLICATION (the known-arity discipline): the
        -- applied fvar must carry pap provenance (the lowering state's
        -- `paps`); captured + fresh must total the callee's arity; the
        -- call lowers DIRECTLY to the callee's function-table index
        -- with the captured locals pushed FIRST, then the fresh args
        -- (the executor's param-i-to-local-i convention verbatim).
        match (← get).paps[fvarId]? with
        | none =>
            -- THE FIRST-CLASS APPLICATION (the indirect-call lane,
            -- landed): the applied fvar is an OPAQUE CLOSURE VALUE (the
            -- pipeline's tobj/obj rows; the fnIdx @8 IS the table
            -- index). A non-closure applied (a scalar/boxed-scalar fvar)
            -- refuses — never a silent wrong dispatch. The call: the
            -- fresh args push left to right, then the closure's fnIdx
            -- loads from @8 (the i32 on top), then `callindirect` at
            -- the SIGNATURE's type index — the signature (the fresh
            -- args' types → the result type) registers in the module's
            -- type section (the sig registry, `sigs`); the EXECUTOR's
            -- table discipline does the runtime type check (a
            -- mismatched entry — e.g. a partial pap applied first-class
            -- — traps `indirectSig`, an out-of-bounds index traps
            -- `tabOOB`, never a wrong call).
            match ← tyNameOf? fvarId with
            | some nm =>
                if closureRowName nm then
                  let mut argTys : List WasmCore.ValType := []
                  for a in args do
                    match a with
                    | .fvar af =>
                        match ← tyOf? af with
                        | some t => argTys := argTys ++ [t]
                        | none =>
                            throw (.argShape "an untyped closure-application \
                              arg (the signature would skew)")
                    | .erased =>
                        throw (.argShape "an erased closure-application arg \
                          (the stack would skew)")
                    | .type .. => throw (.argShape "a closure-application type argument")
                  match ty? with
                  | none =>
                      throw (.typeOutsideFragment "closure application result \
                        type" (toString decl.type))
                  | some rt =>
                      let sig : WasmCore.FuncType := ⟨argTys, [rt]⟩
                      let s ← get
                      let (k, sigs) := sigRegister s.sigs sig
                      set { s with sigs := sigs }
                      let tyIdx := s.sibs.length + k
                      for a in args do emitArg a
                      emitI (.localget (← load fvarId))
                      emitI (.mem .i32load closureFnIdxOff none)
                      emitI (.callindirect tyIdx)
                      let l ← bindLocal decl.fvarId rt (tyName? decl.type)
                      emitI (.localset l)
                else
                  -- the honesty: a non-closure applied refuses (a
                  -- scalar/boxed-scalar fvar has no fnIdx @8 — the
                  -- dispatch would be garbage)
                  throw (.closureApplyUnknown fvarId.name.toString)
            | none =>
                throw (.closureApplyUnknown fvarId.name.toString)
        | some (fn, caps) =>
            match (← get).sibs.lookup fn with
            | none => throw (.papUnknownFn fn.toString)
            | some (idx, arity) =>
                if caps.length + args.size != arity then
                  throw (.closureApplyArityDrift fn.toString
                    (caps.length + args.size) arity)
                for (loc, _t) in caps do emitI (.localget loc)
                for a in args do
                  match a with
                  | .erased =>
                      throw (.argShape "an erased closure-application arg \
                        (the stack would skew)")
                  | _ => emitArg a
                emitI (.call idx)
                match ty? with
                | none =>
                    throw (.typeOutsideFragment "closure application result \
                      type" (toString decl.type))
                | some t =>
                    let l ← bindLocal decl.fvarId t (tyName? decl.type)
                    emitI (.localset l)
  | .fap fn args =>
      -- THE BOXED-NAT FAP ROWS first (the legacy's fap dispatch
      -- order): the sanctioned Nat surface inline-lowers over the
      -- boxes' payloads.
      match natFap? fn with
      | some k => emitNatFap fn k decl args
      | none =>
      match binop? fn with
      | some (nargs, instrs) =>
          -- the legacy's arg order: args emitted left to right, the op
          -- pops the row's sig — `semOp`'s convention consumes them
          -- (first popped first)
          if args.size != nargs then
            throw (.unsupportedConstruct s!"fap {fn}"
              s!"arity {args.size} on a row of arity {nargs}")
          for a in args do emitArg a
          match ty? with
          | none =>
              throw (.typeOutsideFragment "fap result type" (toString decl.type))
          | some t =>
              let l ← bindLocal decl.fvarId t (tyName? decl.type)
              instrs.forM emitI
              emitI (.localset l)
      | none =>
          -- THE CROSS-DECL CALL LANE: a remaining `fap` on a KNOWN
          -- sibling decl lowers to wasm `call` at the callee's
          -- function-table index (`lowerFuncs`' decl order — a SELF-
          -- recursive decl calls its OWN index; the recursion's bound
          -- is the executor's fuel honesty, never a fabricated
          -- termination). The marshalling is the EXECUTOR'S calling
          -- convention exactly (the validator's `call` row is the
          -- shared contract): the args push LEFT TO RIGHT (param 0
          -- first), the executor pops against `ft.params.reverse` and
          -- binds `param i → local i` — the legacy
          -- `for a in args do emitArg a` discipline verbatim. The
          -- return: the callee's exit-frame discipline leaves the
          -- result on the callee's final stack; the call boundary
          -- joins it over the caller's retained stack, so the
          -- `localset` right here reads it — every value crossing the
          -- call rides a LOCAL on BOTH sides. The inliner honesty:
          -- this arm sees only what LCNF PRODUCES (small calls were
          -- inlined away); an arity drift or an erased arg is an
          -- ANF/typing inconsistency — the named refusal, never a
          -- silent stack skew.
          match (← get).sibs.lookup fn with
          | some (idx, arity) =>
              if args.size != arity then
                throw (.unsupportedConstruct s!"fap {fn}"
                  s!"arity {args.size} on a decl of arity {arity}")
              for a in args do
                match a with
                | .erased =>
                    throw (.argShape "an erased call argument (the scalar \
                      fragment's args are fvars — the stack would skew)")
                | _ => emitArg a
              emitI (.call idx)
              match ty? with
              | none =>
                  throw (.typeOutsideFragment "call result type"
                    (toString decl.type))
              | some t =>
                  let l ← bindLocal decl.fvarId t (tyName? decl.type)
                  emitI (.localset l)
          | none =>
              throw (.unsupportedConstruct s!"fap {fn}"
                "the primitive op surface (binop?) — everything else is the \
               named follow-up")
  | .ctor info args =>
      -- THE CTOR VALUE's two faces, keyed on the RESULT TYPE's row (the
      -- pipeline's impure-type law: an ENUM type's ctor value is a
      -- SCALAR — the u8/u16/u32 repr, the value IS the tag — while an
      -- OBJECT type's ctor value is a POINTER, even a payload-free one:
      -- the runtime's `lean_box`, an 8-byte {rc, tag} object, because
      -- the tag dispatch reads the tag @4 from MEMORY). The type row
      -- decides: a scalar-row result takes the tag face, an object-row
      -- result takes the object face.
      let objRow := match decl.type with | .const c _ => objectRowName c | _ => false
      if !objRow then
        -- THE TAG DISCIPLINE's value face: a payload-free ctor's value
        -- IS the unboxed tag (the same repr the scalar lane branches on).
        unless args.isEmpty do
          throw (.unsupportedConstruct "ctor"
            "a ctor with fields of scalar-row result type — an enum repr \
             has no fields (the layout law's classification)")
        match ty? with
        | some t =>
            let l ← bindLocal decl.fvarId t (tyName? decl.type)
            emitI (.i32const info.cidx); emitI (.localset l)
        | none =>
            throw (.typeOutsideFragment "ctor type" (toString decl.type))
      else if args.all (fun a => match a with | .fvar _ => true | _ => false) then
        -- THE OBJECT FACE: allocate the object — header {rc reserved
        -- @0, tag @4} — then store the fields at the PIPELINE'S
        -- PACKING-LAW coordinates (refs first, one 8-byte slot each;
        -- the scalar region after them, packed by size class largest
        -- first) — the same coordinates the field-binding reads ride
        -- (the oproj lane's @8+i*8, the sproj lane's 8+n*8+off). Every
        -- arg must be an fvar with a MAPPED type and a FIELD CLASS
        -- (an unclassifiable field — an enum/Char repr — refuses,
        -- `ctorFieldClass`). THE RC SEED: the allocation inits rc=1
        -- (one reference at birth) and the `inc`/`dec` forms maintain
        -- the cell — but no REUSE (the size-class freelist is the
        -- named follow-up; the object is never reclaimed within a
        -- run).
        let mut fs : List (Nat × FieldClass) := []
        let mut ok := true
        let mut badTy := ""
        for a in args do
          match a with
          | .fvar fvarId =>
              match ← tyOf? fvarId, ← tyNameOf? fvarId with
              | some _, nm =>
                  match fieldClass? nm with
                  | some cl => fs := fs ++ [(← load fvarId, cl)]
                  | none => ok := false; badTy := toString (nm.getD `anon)
              | _, _ => ok := false
          | _ => ok := false
        if !ok then
          throw (.ctorFieldClass badTy)
        -- the packing law: the ref fields take the slots 0..nRefs-1 in
        -- order; the scalar region rides base slot nRefs, packed by
        -- size class (each scalar's within-region offset = `scalarOff`
        -- over the scalars before it)
        let nRefs := (fs.filter (fun p => p.2 == FieldClass.obj)).length
        let mut pre : List FieldClass := []
        let mut rows : List (Nat × FieldClass × Nat) := []
        for (argLoc, cl) in fs do
          match cl with
          | .obj => rows := rows ++ [(argLoc, cl, 0)]
          | _ =>
              rows := rows ++ [(argLoc, cl, scalarOff pre cl)]
              pre := pre ++ [cl]
        let ssize := pre.foldl (fun n c => n + fieldSize c) 0
        match ty? with
        | some .i32 =>
            let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
            let _p ← allocSeq (8 + nRefs * 8 + ssize)
            emitI (.localset l)
            emitI (.localget l); emitI (.i32const info.cidx)
            emitI (.mem .i32store8 boxTagOff none)
            let mut refs := 0
            for (argLoc, cl, off) in rows do
              emitI (.localget l)
              emitI (.localget argLoc)
              let slot := match cl with | .obj => refs | _ => nRefs
              let addr := 8 + slot * 8 + off
              match cl with
              | .obj => emitI (.mem .i32store addr none); refs := refs + 1
              | .u64 => emitI (.mem .i64store addr none)
              | .u32 => emitI (.mem .i32store addr none)
              | .u8 => emitI (.mem .i32store8 addr none)
        | _ =>
            throw (.typeOutsideFragment
              "ctor type (the object face demands an object-pointer result)"
              (toString decl.type))
      else
        throw (.unsupportedConstruct "ctor"
          "the object face (fvar args; erased args are the named follow-up)")
  | .pap fn args =>
      -- THE CLOSURE DISCIPLINE's allocation face: the pap allocates the
      -- closure object — {rc (init 1 by allocSeq), tag 254, fnIdx (the
      -- callee's function-table index), captured slots @16 + i*8} — and
      -- records the PROVENANCE (the known-arity application reads it
      -- back; the closure object is the honest layout riding the landed
      -- object discipline, the legacy trampoline's proved offsets).
      match (← get).sibs.lookup fn with
      | none => throw (.papUnknownFn fn.toString)
      | some (_idx, arity) =>
          if args.size >= arity then
            throw (.papArityDrift fn.toString args.size arity)
          let mut caps : List (Nat × WasmCore.ValType) := []
          for a in args do
            match a with
            | .fvar fvarId =>
                match ← tyOf? fvarId with
                | some t => caps := caps ++ [(← load fvarId, t)]
                | none =>
                    throw (.typeOutsideFragment "pap captured arg type"
                      (toString decl.type))
            | .erased =>
                throw (.argShape "a pap captured argument (the stack would skew)")
            | .type .. => throw (.argShape "a pap type argument")
          match ty? with
          | some .i32 =>
              let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
              let _p ← allocSeq (closureSize args.size)
              emitI (.localset l)
              emitI (.localget l); emitI (.i32const closureTag)
              emitI (.mem .i32store8 boxTagOff none)
              emitI (.localget l); emitI (.i32const _idx)
              emitI (.mem .i32store closureFnIdxOff none)
              let mut slot := 0
              for (loc, ft) in caps do
                emitI (.localget l); emitI (.localget loc)
                if ft == .i64 then
                  emitI (.mem .i64store (closureCapOff + slot * 8) none)
                else
                  emitI (.mem .i32store (closureCapOff + slot * 8) none)
                slot := slot + 1
              modify fun s =>
                { s with paps := s.paps.insert decl.fvarId (fn, caps) }
          | _ =>
              throw (.typeOutsideFragment
                "pap result type (the closure object's pointer)"
                (toString decl.type))
  | .sproj n offset var _ =>
      -- THE OBJECT SEED's read face: the scalar region's coordinates —
      -- the load at `8 + n*8 + offset` (the pipeline's spelling:
      -- n = the region's base slot, offset = the packed byte offset;
      -- the hand-built face spells the slot directly, offset 0 — the
      -- SAME formula); the load width from the RESULT's mapped type
      -- (i64 → i64load, i32 → i32load, a u8 field → i32load8 — the
      -- packing law's 1-byte class).
      match ty?, decl.type with
      | some t, .const rty _ =>
          if t != .i64 && t != .i32 then
            throw (.typeOutsideFragment "sproj result type"
              (toString decl.type))
          let l ← bindLocal decl.fvarId t (tyName? decl.type)
          emitI (.localget (← load var))
          let base := 8 + n * 8 + offset
          if t == .i64 then
            emitI (.mem .i64load base none)
          else if rty == `UInt8 then
            emitI (.mem .i32load8u base none)
          else
            emitI (.mem .i32load base none)
          emitI (.localset l)
      | _, _ =>
          throw (.typeOutsideFragment "sproj result type"
            (toString decl.type))
  | .oproj i var =>
      -- THE REF-FIELD READ (the tag dispatch's payload lane): field i's
      -- 8-byte slot @8 + i*8 — the packing law's ref coordinates, the
      -- SAME ones the ctor face writes; the pipeline's field-binding
      -- lets (the cons arm's `head := oproj[0] l`) read them. The
      -- value is a POINTER (the i32 repr).
      match ty?, ← tyOf? var with
      | some .i32, some .i32 =>
          let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
          emitI (.localget (← load var))
          emitI (.mem .i32load (8 + i * 8) none)
          emitI (.localset l)
      | _, _ =>
          throw (.typeOutsideFragment "oproj operand types (the base's \
            object repr, the field's pointer result)"
            s!"{toString decl.type} ← field {i}")
  | .proj .. | .uproj .. =>
      throw (.unsupportedConstruct "projection"
        "the non-scalar payload shapes (proj/uproj — the pure-projection \
         and usize faces) — the tag dispatch's named refusal")
  | .box ty fvarId .. =>
      -- THE SCALAR-BOX LANE (the `box` value form): a scalar's box IS
      -- the landed boxed-Nat layout ({rc init 1, tag 0, payload @8}) —
      -- the width from the boxed type's map. An OBJECT-row boxed type
      -- (Nat/tobj/tagged/obj) is the IDENTITY copy: the value IS the
      -- box already under the model (the real pipeline's
      -- `._boxed_const_1` shape boxes a SCALAR — the probe's observed
      -- `box ty=UInt64`).
      let objRow := tyName? ty |> Option.map objectRowName |>.getD false
      if objRow then
        match ty?, ← tyOf? fvarId with
        | some .i32, some .i32 =>
            let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
            emitI (.localget (← load fvarId)); emitI (.localset l)
        | _, _ =>
            throw (.typeOutsideFragment "box (object-row) operand types"
              s!"{toString ty} ← {toString decl.type}")
      else
        match scalarTyOf? (match ty with | .const c _ => c | _ => `anon), ty?,
            ← tyOf? fvarId with
        | some .i64, some .i32, some .i64 =>
            let src ← load fvarId
            let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
            let _p ← allocSeq boxSize
            emitI (.localset l)
            storeBoxTag l
            storeBoxPayload l src
        | some .i32, some .i32, some .i32 =>
            let src ← load fvarId
            let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
            let _p ← allocSeq boxSize
            emitI (.localset l)
            storeBoxTag l
            emitI (.localget l); emitI (.localget src)
            emitI (.mem .i32store boxPayloadOff none)
        | _, _, _ =>
            throw (.typeOutsideFragment "box operand types (the boxed \
              scalar's width, the result's pointer repr, the source \
              local's bound width)"
              s!"{toString ty} → {toString decl.type}")
  | .unbox fvarId .. =>
      -- THE SCALAR-BOX's read face: the payload @8, the width from the
      -- RESULT's mapped type (the `_lam._boxed` adapters' unbox shape).
      -- The operand must be OBJECT-repr (the box pointer).
      match ← tyOf? fvarId, ty? with
      | some .i32, some .i64 =>
          let l ← bindLocal decl.fvarId .i64 (tyName? decl.type)
          emitI (.localget (← load fvarId))
          emitI (.mem .i64load boxPayloadOff none)
          emitI (.localset l)
      | some .i32, some .i32 =>
          let l ← bindLocal decl.fvarId .i32 (tyName? decl.type)
          emitI (.localget (← load fvarId))
          emitI (.mem .i32load boxPayloadOff none)
          emitI (.localset l)
      | _, _ =>
          throw (.typeOutsideFragment "unbox operand types (the box \
            pointer's object repr, the result's scalar width)"
            (toString decl.type))
  | .reset .. | .reuse .. | .isShared .. =>
      throw (.unsupportedConstruct "Perceus reset/reuse/isShared"
        "the object model (no object enters this fragment)")
  | .const fn _us args .. =>
      -- THE _CLOSED FIXPOINT's value face (the legacy's "0-ary const: a
      -- top-level closure constant"): a 0-ary const naming a 0-ary
      -- SIBLING is the producer's call (the probe's family arrives as
      -- 0-ary FAPS — the call lane handles those; the const face is the
      -- honest twin). Anything else refuses with its named boundary.
      if args.isEmpty then
        match (← get).sibs.lookup fn with
        | some (idx, arity) =>
            if arity != 0 then
              throw (.unsupportedConstruct s!"const {fn}"
                "a 0-ary const of an arity-{arity} callee — the \
                 eta-closure face (the pap lane's named follow-up)")
            match ty? with
            | none =>
                throw (.typeOutsideFragment "const result type"
                  (toString decl.type))
            | some t =>
                let l ← bindLocal decl.fvarId t (tyName? decl.type)
                emitI (.call idx)
                emitI (.localset l)
        | none =>
            throw (.unsupportedConstruct s!"const {fn}"
              "the callee is not a sibling decl of the module")
      else
        throw (.unsupportedConstruct s!"const {fn}"
          "a const with arguments (the pure-application face — the \
           impure pipeline delivers binops as faps)")

/-! ## The join-point discipline (jp/jmp) -/

/-- The LOOP-ENTRY discipline's splitter: the loop shape's `k` must
    be a straight-line let spine ending in the entry `jmp target` —
    a br cannot ENTER a frame, so the entry falls through into the
    loop's first iteration. -/
def splitEntry (target : Lean.FVarId) : Code .impure →
    Option (List (LetDecl .impure) × Array (Arg .impure))
  | .let decl k =>
      splitEntry target k |>.map (fun (ls, a) => (decl :: ls, a))
  | .jmp f args => if f == target then some ([], args) else none
  | _ => none

/-! ## The ONE code walk (the legacy foldImpure consolidation's
##    discipline) -/

-- Lower the LCNF `Code`. ONE traversal; the single parameter `d` is
-- the RUNTIME FRAME DEPTH at the emission point (how many wasm
-- frames will enclose the emitted instructions when they run — the
-- ONE AST's frame-depth discipline). `res`/`resTy` = the function's
-- result local (index + type) — every `.return` stores it and
-- branches out to the function level (the exit-frame discipline).
-- Well-founded over `codeSize`/`altSizes`.
mutual
def lowerCode (code : Code .impure) (d : Nat) (res : Nat)
    (resTy : WasmCore.ValType) : M Unit :=
  match code with
  | .let decl k => do
      emitLet decl
      lowerCode k d res resTy
  | .return fvarId => do
      let idx ← load fvarId
      let fty ← tyOf? fvarId
      if fty != some resTy then
        throw (.armTypeMismatch (WasmCore.renderValType resTy)
          (WasmCore.renderValType (fty.getD .i64)))
      emitI (.localget idx); emitI (.localset res)
      -- the exit-frame discipline: branch to the OUTERMOST frame
      if d >= 1 then
        emitI (.br (d - 1))
      else
        throw (.loopEntry "a return outside the exit frame (depth 0) — \
          the exit-frame discipline's own inconsistency")
  | .unreach _ => emitI .unreach
  | .cases c => do
      -- THE CTOR-CASE-ON-NAT THROW (the boxed-Nat model's pinned
      -- loud refusal): the generic tag dispatch would read the box's
      -- tag 0 and treat the payload as a POINTER — silently wrong.
      -- The real pipeline never produces one (Nat cases compile to
      -- decEq fap chains); the hand-built face can, and the model
      -- refuses.
      if c.typeName == `Nat then
        throw .natCtorCase
      -- THE SCRUTINEE DISPATCH. The SCALAR lane branches on the VALUE
      -- (a Bool match compiles to the U8 representation — observed:
      -- `cases UInt8` carrying Bool ctorAlts — and a scalar-repr
      -- enum's repr IS the ctor tag, the prescan's registry). The
      -- OBJECT TAG DISPATCH (this slice): the scrutinee is an object
      -- POINTER (the i32 repr) — read the tag u8 @4 (the landed
      -- layout's proved offset; the runtime's `lean_obj_tag` face)
      -- into a fresh scratch local and branch on IT. The per-alt
      -- payload projections ride the object layout (the oproj lane's
      -- @8+i*8, the sproj lane's region coordinates — the SAME
      -- coordinates the ctor face writes). Anything else refuses
      -- loudly.
      if c.typeName == `Bool || c.typeName == `UInt8
        || (← get).enums.contains c.typeName then
        let scrutIdx ← load c.discr
        -- the alt chain: arm i runs one chain link deeper (i+1 if_s)
        let altsI ← chainWalk scrutIdx c.alts (d + 1) 0 res resTy
        altsI.forM emitI
      else
        match ← tyOf? c.discr with
        | some .i32 =>
            let ptr ← load c.discr
            emitI (.localget ptr); emitI (.mem .i32load8u boxTagOff none)
            let tag ← bindFresh .i32
            emitI (.localset tag)
            let altsI ← chainWalk tag c.alts (d + 1) 0 res resTy
            altsI.forM emitI
        | _ =>
            throw (.unsupportedConstruct s!"cases on {c.typeName}"
              "the tag dispatch demands an object-repr (i32) scrutinee — \
               the scalar lanes are Bool/UInt8/the prescan's enums")
      -- the case is TERMINAL in LCNF's impure spine: every arm ends
      -- return/jmp/unreach or a nested case — nothing follows
  | .jp fd k => do
      -- THE JOIN-POINT DISCIPLINE. Shape dispatch on the loop
      -- detector: a body that jumps back to ITSELF lowers to the
      -- loop frame; anything else takes the legacy's
      -- block-and-fallthrough shape. Either way the jp's params bind
      -- to fresh locals and the registration (depth offset X, param
      -- locals) lives exactly as long as the structure's emission.
      let mut ps : List Nat := []
      for p in fd.params do
        -- THE BORROW HONESTY: `borrow` is the RC face's flag (the
        -- callee skips inc/dec). The no-RC slice has no decrements to
        -- elide — reading a borrowed param is safe, so the flag is
        -- recorded and IGNORED (the boxed-Nat lane's params arrive
        -- borrowed — the probe-observed tobj discipline).
        match ← tyMap? p.type with
        | some t => ps := ps ++ [← bindLocal p.fvarId t (tyName? p.type)]
        | none =>
            throw (.typeOutsideFragment "jp param type" (toString p.type))
      modify fun s => { s with jps := s.jps.insert fd.fvarId (d + 2, ps) }
      if jumpsTo fd.fvarId fd.value then
        -- THE LOOP SHAPE: the entry discipline (k = lets + entry jmp)
        match splitEntry fd.fvarId k with
        | none =>
            throw (.loopEntry "the loop shape's continuation must be a \
              straight-line let spine ending in the entry jmp (a br \
              cannot ENTER a frame; the entry-duplication transform is \
              the named follow-up)")
        | some (lets, args) =>
            for l in lets do emitLet l
            if args.size != ps.length then
              throw (.jpArityDrift fd.fvarId.name.toString args.size ps.length)
            -- the entry arg stores: the first iteration's params
            for (a, p) in args.toList.zip ps do
              emitArg a
              emitI (.localset p)
            let bodyI ← scopedOut (lowerCode fd.value (d + 2) res resTy)
            emitI (.block [.loop (bodyI ++ [.br 1])])
            emitI .unreach
      else
        -- THE BLOCK SHAPE (the legacy's block-and-fallthrough, in
        -- depths): k inside the inner block, the body after it, the
        -- fallthrough br skips the body, the seal closes.
        let kI ← scopedOut (lowerCode k (d + 2) res resTy)
        let bodyI ← scopedOut (lowerCode fd.value (d + 1) res resTy)
        emitI (.block ([.block (kI ++ [.br 1])] ++ bodyI))
        emitI .unreach
      -- the registration's scope ends with the structure
      modify fun s => { s with jps := s.jps.erase fd.fvarId }
  | .jmp fvarId args => do
      -- the goto: store the args into the jp's param locals, branch
      -- out to the jp's structure (br (d - X) — through any if_
      -- nesting)
      match (← get).jps[fvarId]? with
      | none =>
          throw (.jpUnregistered fvarId.name.toString)
      | some (x, ps) =>
          if args.size != ps.length then
            throw (.jpArityDrift fvarId.name.toString args.size ps.length)
          for (a, p) in args.toList.zip ps do
            emitArg a
            emitI (.localset p)
          if d >= x then
            emitI (.br (d - x))
          else
            throw (.jpUnregistered fvarId.name.toString)
  | .fun .. =>
      throw (.unsupportedConstruct "fun"
        "local function values (the closure model)")
  | .oset .. =>
      throw (.unsupportedConstruct "in-place mutation (oset)"
        "the object model (oset/uset/sset/setTag)")
  | .uset .. =>
      throw (.unsupportedConstruct "in-place mutation (uset)"
        "the object model (oset/uset/sset/setTag)")
  | .sset .. =>
      throw (.unsupportedConstruct "in-place mutation (sset)"
        "the object model (oset/uset/sset/setTag)")
  | .setTag .. =>
      throw (.unsupportedConstruct "in-place mutation (setTag)"
        "the object model (oset/uset/sset/setTag)")
  | .inc fvarId n _check _persistent k => do
      -- THE RC SEED: the rc cell's REAL arithmetic (the `check` and
      -- `persistent` flags ride recorded-and-ignored — the runtime's
      -- cross-run cache discipline, not modeled). The over-dec guard
      -- and the dead-marking live at `rcOp`.
      rcOp "inc" fvarId n true
      lowerCode k d res resTy
  | .dec fvarId n _check _persistent objs? k => do
      match objs? with
      | none => rcOp "dec" fvarId n false
      | some _ => throw .rcCascade
      lowerCode k d res resTy
  | .del .. =>
      throw (.unsupportedConstruct "Perceus RC (del)"
        "the freelist's size-class discipline (the rc seed's named \
         follow-up) — without it del could only drop the slot silently")
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def chainWalk (scrutIdx : Nat) (alts : Array (Alt .impure)) (d : Nat) (i : Nat)
    (res : Nat) (resTy : WasmCore.ValType) : M (List WasmCore.Instr) := do
  -- The alt-chain fold (the legacy `buildAlts`): nested `if_`s keyed
  -- on the ctor index, a `default` alt as the final else, an
  -- uncovered ctor set as `[unreach]` (the alt chain is exhaustive at
  -- runtime). LCNF impure alts carry NO `.alt` (the pure ctor's
  -- proof discharges like the legacy's `absurd`). Arm i of the chain
  -- lowers at depth `d` (each chain link is one `if_` frame).
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt info code => do
        let thenI ← scopedOut (lowerCode code d res resTy)
        let elseI ← chainWalk scrutIdx alts (d + 1) (i + 1) res resTy
        return ([.localget scrutIdx, .i32const info.cidx, .op .i32eq]
          ++ [.if_ thenI elseI])
    | .default code => scopedOut (lowerCode code d res resTy)
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    return [.unreach]
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The decl lowering -/

/-- The per-decl walk: bind the param locals (0..n-1 in order — the
    executor driver's binding discipline: param i lands in local i),
    bind the result local, walk the body at depth 1 (inside the exit
    frame), collect the emitted instructions + the result index. -/
def declWalk (code : Code .impure) (params : Array (Param .impure))
    (resTy : WasmCore.ValType) : M (List WasmCore.Instr × Nat) := do
  for p in params do
    -- THE BORROW HONESTY: `borrow` is the RC face's flag (the callee
    -- skips inc/dec). The no-RC slice has no decrements to elide —
    -- reading a borrowed param is safe, so the flag is recorded and
    -- IGNORED (the boxed-Nat lane's params arrive borrowed — the
    -- probe-observed tobj discipline).
    match ← tyMap? p.type with
    | some t => discard <| bindParam p.fvarId t (tyName? p.type)
    | none =>
        throw (.typeOutsideFragment "param type" (toString p.type))
  let res ← bindFresh resTy
  lowerCode code 1 res resTy
  let body ← emitted
  pure (body, res)

/-- Lower SEVERAL impure-phase LCNF decls into ONE module: one type +
    one function + one export per decl (the entry index = the decl
    order). The decls see each other through the CALL LANE: the
    sibling registry (`name → (function-table index, param arity)` —
    the index IS the decl order, a self-recursive decl's OWN index
    included) feeds every `fap` on a sibling to wasm `call` under the
    executor's calling convention; a fap naming a NON-sibling refuses
    (never a fabricated index-0 call). THE INDIRECT-CALL LANE: a
    decl's first-class applications register their signatures in the
    SIG REGISTRY (threaded across the fold — dedup at registration);
    the module's type section grows the sig types AFTER the decl
    types, and the ONE funcref table gets the IDENTITY entries (table
    i = function i — the closures' fnIdx discipline), present exactly
    when the lane fired (the validator's table-index discipline
    refuses a `callindirect` over an absent table). -/
def lowerFuncs (ds : List (Decl .impure)) : Except LowerError WasmCore.Module :=
  let sibs := ds.zipIdx.map (fun p => (p.1.name, p.2, p.1.params.size))
  let one (i : Nat) (d : Decl .impure) (sigs0 : List WasmCore.FuncType) :
      Except LowerError
        (WasmCore.FuncType × WasmCore.Func × String × List WasmCore.FuncType) :=
    match d.value with
    | .extern .. =>
        throw (.unsupportedConstruct "extern decl"
          "a decl with a body (a plain `def`)")
    | .code code =>
      let enums := collectScalarEnums code
      match wasmTyOf? enums d.type with
      | none => throw (.typeOutsideFragment "result type" (toString d.type))
      | some resTy =>
        match StateT.run (declWalk code d.params resTy)
            ({ fvars := {}, locals := [], next := 0, out := []
             , jps := {}, enums := enums, sibs := sibs, sigs := sigs0 } : LState) with
        | .error e => .error e
        | .ok ((bodyI, res), st) =>
            let ft : WasmCore.FuncType :=
              ⟨d.params.toList.filterMap (fun p => wasmTyOf? enums p.type), [resTy]⟩
            let f : WasmCore.Func :=
              { tyIdx := i, locals := st.locals
              , body := [.block bodyI, .localget res] }
            .ok (ft, f, d.name.toString, st.sigs)
  let accTy :=
    Except LowerError
      (List (WasmCore.FuncType × WasmCore.Func × String) × List WasmCore.FuncType)
  let step : accTy → (Decl .impure × Nat) → accTy := fun acc p =>
      match acc with
      | .error e => .error e
      | .ok (rows, sigs) =>
          match one p.2 p.1 sigs with
          | .error e => .error e
          | .ok (ft, f, nm, sigs') => .ok (rows ++ [(ft, f, nm)], sigs')
  match ds.zipIdx.foldl step (.ok ([], [])) with
  | .error e => .error e
  | .ok (rows, sigs) =>
    .ok
      { types := rows.map (·.1) ++ sigs
        funcs := rows.zipIdx.map (fun p => { p.1.2.1 with tyIdx := p.2 })
        exports := rows.zipIdx.map
          (fun p => { name := p.1.2.2, desc := WasmCore.ExportDesc.func p.2 })
        -- THE BUMP ARENA's page: the boxed-Nat lane allocates in the
        -- linear memory (the bump pointer lives at cell 0), so every
        -- module carries ONE wasm page (64KiB ≈ 4000 live 16-byte
        -- boxes; an exhausted arena is the bounded-memory memOOB
        -- trap — the honest ceiling, never corruption).
        memMin := 1
        -- THE INDIRECT-CALL LANE's table: the identity entries (table
        -- i = function i — the closures' fnIdx discipline), present
        -- exactly when a first-class application fired.
        tables := if sigs.isEmpty then [] else [{ init := List.range ds.length }] }

/-- Lower ONE impure-phase LCNF decl to a one-function module: one
    type (the params → the mapped scalars, the result → its mapped
    scalar), one function (the exit-frame discipline: the body inside
    the outermost frame, `localget res` after), exported under the
    decl's own name. The decl's `type` in the impure phase IS the
    return type (LCNF's erasure — the Basic.lean note); `extern`
    decls refuse (no body). -/
def lowerFunc (d : Decl .impure) : Except LowerError WasmCore.Module :=
  lowerFuncs [d]

end Guest
