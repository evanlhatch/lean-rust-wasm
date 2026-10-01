/-
# Guest.Lower — the IR → the ONE wasm AST (the lowering core)

Ported from `legacy/lean/wasm-backend/WasmBackend.lean` (the emitter's
INTENT; the new tree's substrate differs honestly — index-keyed
locals, the closed `WasmCore.Instr`, the frame-DEPTH discipline in
place of the legacy's WAT labels, the op meanings in
`WasmCore.OpTable`).

THE SPLIT'S DISCIPLINE (this file's contract): the input is
`Guest.IR` — the frontend-agnostic intermediate — and NOTHING
language-specific. The LCNF walking (the type map, the tag prescan,
the fap name dispatch, the honest drops) lives in the FRONTEND
(`Guest.Lcnf`); a second, toy frontend (hand-written IR) rides the
same lowering untouched — the proof the IR is the whole contract.
This file imports `Guest.IR`, `WasmCore`, `Kit.Diag` — no Lean, no
LCNF.

The lanes (each maps an `IR` constructor's discipline onto the wasm
AST; the full prose discipline is in the lanes' doc strings):

- **The type rows** (`tyRepr`): the IR's `Ty` rows → the wasm scalar
  or object-pointer repr — `.u64 → i64`; every other row `→ i32` (the
  ONE pointer repr for the object rows; the unboxed tag for the
  scalar-enum rows). The FRONTEND refuses a type outside the rows.
- **The tag discipline** (the scalar-representable enums): the IR's
  `cases_` carries the frontend's prescan verdict (`CaseVia.value` —
  branch on the VALUE; `CaseVia.tag` — read the tag byte @4 of the
  pointer repr).
- **The op surface** (`binopSeq`): the IR's `Binop` rows → the
  `WasmCore.Op` ctors (the ONE table, 07-extensibility R6). The u8
  arith rows carry the `and 0xFF` mask (i32 arithmetic wraps mod 2^32,
  a `UInt8` wraps mod 2^8).
- **The cross-decl call lane**: an `IR.LetValue.call` naming a SIBLING
  decl lowers to wasm `call` at the callee's FUNCTION-TABLE INDEX
  (`lowerFuncs`' decl order — a self-recursive decl calls its OWN
  index; the recursion's bound is the executor's fuel honesty,
  `outOfFuel`, never a fabricated termination). The marshalling is
  the EXECUTOR'S calling convention exactly: the args push LEFT TO
  RIGHT, the callee's exit-frame discipline leaves the result on its
  final stack, every value crossing the call rides a LOCAL on BOTH
  sides.
- **The boxed-Nat lane**: the IR's `litNat`/`NatFap` rows — the bump
  arena over the module's one memory page (the bump pointer lives IN
  the memory at cell 0), the `{rc, tag 0, i64 payload @8}` box, the
  2^62 cap at compile time AND runtime, the 128-bit mul guard, the
  sub-underflow trap.
- **The object seed** (the `ctor` object face + `sproj`/`oproj`): the
  header `{rc @0, tag @4}` + the fields at the PIPELINE'S PACKING-LAW
  coordinates (refs first, one 8-byte slot each; the scalar region
  after, packed by size class largest first). The ctor VALUE's two
  faces are keyed on the RESULT TYPE's row: a scalar-row ctor is the
  unboxed tag; an object-row ctor is a POINTER even when payload-free.
- **The closure discipline** (`pap` + `apply`): the closure object
  `{rc @0, tag 254 @4, fnIdx @8, captured @16 + i*8}`; the known-arity
  application calls DIRECTLY (the pap provenance in the lowering
  state); a first-class application lowers to the INDIRECT-CALL lane
  (the funcref table + `callindirect` + the sig registry).
- **The RC discipline** (`inc`/`dec`/`del`): the rc cell's REAL arithmetic
  under the over-dec guard; `dec`'s FIELD CASCADE — the ref fields' refs
  decrement when the object dies (the count rides the IR's `dec`; the
  ref slots are `0..count-1`, the packing law's coordinates — the DEEP
  cascade, a field's own fields, is the named follow-up); `del` — the
  ownership assertion `rc = 1` checked at runtime (the teeth) + the dead
  marking (rc = 0) + THE REUSE PUBLISH: a shape-known dead slot lands
  in the allocator's single dead-slot cache and the next same-size
  allocation hands it back (the HONESTY: reuse is a MEMORY discipline,
  invisible to the semantics — a live object's address never changes,
  so behavior is identical with and without reuse; the size-class
  freelist is the named follow-up).
- **The control flow** (`cases_`/`jp`/`jmp`): the frame-depth AST —
  the exit-frame discipline for `.ret`, the alt chain folding to
  nested `if_`s, the join points as the block shape (shared joins) or
  the loop shape (tail-recursive joins, the entry discipline).
- **The multi-decl module**: `lowerFuncs` lowers SEVERAL IR decls into
  ONE module (one type + one function + one export each; the entry
  index = the decl order).
- **The in-place writes** (`sset`/`oset`/`setTag`): the mutation
  family's landed face — the scalar-field write (the SAME coordinates
  the `sproj` read rides), the ref-field write, the tag byte's write.
  THE LEGALITY DISCIPLINE: every write guards the rc=1 uniqueness at
  RUNTIME (a shared cell's in-place write corrupts every other
  reference's view — the loud unreach trap, never a silent write; the
  copy-on-shared discipline is the named follow-up). The `uset` face
  (a USize slot write) is the named refusal (no modeled row).
- **The extern face** (`extern`): a DECLARED TRUST BOUNDARY — the
  contract rides the ctor as DATA (`IR.ExternSig`: the declared rows,
  the effect row, the trust note — an undeclared extern is
  unrepresentable), the decl's faces must MATCH it (`externSigDrift`),
  the call sites are type-checked against it (`externCallDrift`), the
  function + export land (the call lane's index like any sibling), and
  the body is NOT modeled: the emitted function is `unreach` (the host
  link step is the named follow-up).
- **The refusal discipline** (05 §4's envelope): every refusal is a
  closed `LowerError` ctor rendered into the ONE `Kit.Diag` (the
  GC-family E-codes) — the shared envelope in `Guest.IR`.

THE RECURSION IS STRUCTURAL (the honest split's dividend): the IR's
spine carries its recursive occurrences as DIRECT constructor
arguments (the alts ride a LIST; the jp's body is a `jp` ctor arg), so
every walker here — the lowering, the loop detector, the entry
splitter — is structurally recursive. The LCNF frontend needs the
well-founded measure machinery over ITS tree (`Guest.Lcnf`); the
lowering core needs none of it.

The five questions (notes/v3/01-core.md):

- **Root**: none — a lowering is a CROSSING (the IR decl read into
  the wasm module); its law face lands with the first correctness
  wave (the template pins are the tests' runtime face).
- **Carrier grade**: none new — the refusals ride `Kit.Diag` (the
  ONE envelope); the module output rides WasmCore's grades.
- **Spine reading**: the IR `Code` is the spine this module folds
  (one traversal, ONE parameter — the runtime frame depth `d`; the
  legacy `foldImpure` consolidation's discipline).
- **Ladder rung**: rung 1 (total folds over closed data; every
  non-fragment input refuses — at the frontend when reading, here
  when lowering).
- **Gate row**: `gates kernel-check` + lintkit's gated roots.

Consumer trail: rides `Guest.IR` (the ONE input face), `WasmCore`
(the ONE AST + the op table + the module model), `Kit.Diag` (the ONE
envelope). The composed pipeline (LCNF → IR → here) is
`Guest.Lcnf.compile`; the toy frontend (hand-written IR) calls
`lowerFunc`/`lowerFuncs` directly — the conformance evidence.
-/

import Guest.IR
import Guest.Layout
import Kit.Diag
import WasmCore
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Guest

/-! ## The scalar type map (the IR's rows → the wasm reprs) -/

/-- The IR type row → the wasm scalar or object-pointer type: the
    `u64` row is the ONE i64; every other row rides i32 (the machine
    scalars, the i32-repr source scalars, the prescan's enums — the
    unboxed tag — and the object rows — the ONE pointer repr). -/
def tyRepr : IR.Ty → WasmCore.ValType
  | .u64 => .i64
  | _ => .i32

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

/-! ## The field-layout law (the pipeline's `CtorLayout` packing) -/

/-- THE FIELD's size class: a ref field (an object-row type) rides one
    full 8-byte slot; a scalar rides the scalar region, packed by size
    class, largest first. An enum/Bool/Char-typed field has NO class
    here — the pipeline's enum repr (u8/u16/u32) depends on the ctor
    count, unknowable from the lowering's data — the named
    `ctorFieldClass` refusal. -/
inductive FieldClass where
  | obj | u64 | u32 | u8
deriving BEq, DecidableEq, Inhabited, Repr

def fieldClass? : IR.Ty → Option FieldClass
  | .u64 => some .u64
  | .u32 => some .u32
  | .u8 => some .u8
  | t => if t.isObjRow then some .obj else none

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

/-! ## The boxed-Nat lane's layout constants (the `Guest.Layout`
    emitter consumer) -/

/-- THE OBJECT SLOT GRID (the honest adapter — the `Guest.Layout`
    consumer the module head named): the guest object rides 8-byte
    SLOTS (the header slot, the payload slot, the capture slots — the
    legacy's proved offsets), so the slot grid IS a `Layout` record —
    one `.u64` field per slot. The SUB-SLOT faces (the u8 tag @4
    INSIDE the header slot) are the slot's internal layout, NOT Layout
    fields — the closed `Wit.Ty` grammar has no u8, and claiming the
    tag a Layout field would be the dishonest fit. -/
abbrev objectSlot : Wit.Ty := .atom .u64

/-- The boxed object's slot grid: the header slot (the rc u32 + the
    tag u8 packed) + the i64 payload slot. -/
abbrev boxTys : List Wit.Ty := [objectSlot, objectSlot]

/-- The closure object's slot grid: the header slot, the fnIdx slot,
    then the nCap captured slots (the captures ride the object
    discipline's 8-byte slots, width by mapped type). -/
def closureTys (nCap : Nat) : List Wit.Ty :=
  objectSlot :: objectSlot :: List.replicate nCap objectSlot

/-- THE bounded-Nat cap: 2^62 (the legacy's pinned design constant —
    a literal at/above it is a design error, refused before anything
    else is asked about it). -/
def natCap : Nat := 4611686018427387904

/-- THE BOXED OBJECT's header + payload layout: `{rc @0, tag u8 @4,
    i64 payload @8}` — the 8-byte header slot + the 8-byte payload
    slot (the legacy's proved offsets). THE RC SEED: the rc cell is
    REAL now — every allocation stores rc = 1 (one reference at
    birth), the `inc`/`dec` forms maintain it; a dec to ZERO marks the
    object DEAD (rc=0 observable) and the REUSE discipline hands the
    slot back (the single dead-slot cache below). -/
def boxSize : Nat := Layout.size boxTys

/-- THE heap base: the bump arena's first object address. Cell
    `0..4` holds the bump pointer ITSELF (the allocator's state lives
    IN the linear memory — the module model has no globals); a
    zeroed cell (fresh memory) bumps from here. The arena starts one
    full box-slot in — the null region `0..boxSize` (the bump cell
    inside it) is never allocated, so a box's payload (i64, 8-aligned)
    always clears the cell. -/
def heapBase : Nat := boxSize
-- The nolint row: the tag VALUE is SEMANTICALLY distinct from the
-- layout offsets sharing its numeric value — the dup-body linter's
-- opt-out, the named reason. `boxTagOff` stays a HAND row: the u8 tag
-- is a sub-slot face INSIDE the header slot (the objectSlot note —
-- no `Wit.Ty` field carries it), the one layout number the walk does
-- not derive.
@[nolint linter.guestlang.dupDefBodies "the Nat box's tag VALUE is its own boxed-Nat-model row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def boxTag : Nat := 0
@[nolint linter.guestlang.dupDefBodies "the coincidence, not a shared constant: boxTagOff's 4 is the box header's tag byte (the Layout discipline's documented sub-slot exception); rcCacheAddrOff's 4 is the RC cache's addr slot in the null region"]
def boxTagOff : Nat := 4
/-- The box payload's offset: slot 1 of the proved walk (the header
    slot's `width` later, the alignment pad zero — the `padded_ge`
    guarantee's zero-pad face). -/
def boxPayloadOff : Nat := (Layout.offsets boxTys)[1]

/-- THE RC CELL's facts: the u32 @0 (slot 0's head — the proved
    walk's first offset), one reference at birth. -/
-- The nolint rows: these are SEMANTICALLY distinct rows sharing
-- numeric values with unrelated constants — the dup-body linter's
-- opt-out, the named reason.
@[nolint linter.guestlang.dupDefBodies "the rc cell's offset is its own layout row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def rcCellOff : Nat := (Layout.offsets boxTys)[0]
@[nolint linter.guestlang.dupDefBodies "the birth reference count is its own RC-discipline row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def rcInit : Nat := 1

/-- THE REUSE CACHE's cells (the single dead-slot cache, inside the
    null region — never allocated): cell `4` holds the dead slot's
    ADDRESS, cell `8` its byte SIZE (0 = no dead slot). `del`
    PUBLISHES a shape-known dead slot here (under the rc=1 ownership
    assertion — the legality's first tooth); every allocation consults
    the cache and hands the slot back only when the requested size
    matches EXACTLY (the shape match — the second tooth). A second del
    before the reuse overwrites the cache (the displaced slot leaks —
    bounded by the arena's page; the size-class freelist is the named
    follow-up). -/
@[nolint linter.guestlang.dupDefBodies "the reuse cache's address cell is its own allocator-state row — a shared numeric value with the tag offset is coincidence, not duplication"]
def rcCacheAddrOff : Nat := 4
@[nolint linter.guestlang.dupDefBodies "the reuse cache's size cell is its own allocator-state row — a shared numeric value with the payload offset is coincidence, not duplication"]
def rcCacheSizeOff : Nat := 8

/-- THE CLOSURE OBJECT's layout (the legacy trampoline's proved
    offsets): `{rc @0, tag 254 @4, fnIdx u32 @8, captured slots
    @16 + i*8}`. The fnIdx is the pap callee's FUNCTION-TABLE INDEX —
    the known-arity application calls DIRECTLY (the indirect-call
    lane is the first-class face), so the stored index is the layout's
    honest face; the captured slots ride the object discipline's
    8-byte slots, width by mapped type. -/
def closureTag : Nat := 254
/-- The closure's fnIdx slot: slot 1 of the proved walk (the header
    slot's `width` later). -/
def closureFnIdxOff : Nat := (Layout.offsets (closureTys 1))[1]
/-- The closure's first captured slot: slot 2 of the proved walk. -/
def closureCapOff : Nat := (Layout.offsets (closureTys 1))[2]
/-- The closure's size: the proved walk's total over the slot grid —
    never the hand arithmetic. -/
def closureSize (nCap : Nat) : Nat := Layout.size (closureTys nCap)

/-- THE TEETH (the `Guest.Layout` consumer's pin — `offsets_sorted`'s
    first real consumer): the object slot grids' offsets are the proved
    non-overlap walk's output for EVERY capture count, so the emitter's
    stores to distinct slots cannot overlap BY CONSTRUCTION — the
    per-object numeric faces below. -/
theorem box_slots_sorted :
    (Layout.offsets boxTys).Pairwise (· < ·) := Layout.offsets_sorted boxTys

theorem closure_slots_sorted (nCap : Nat) :
    (Layout.offsets (closureTys nCap)).Pairwise (· < ·) :=
  Layout.offsets_sorted (closureTys nCap)

/-- The slot-level disjointness the emitted stores ride: the rc-cell
    store (`i32store @0`, the cell's 4 bytes inside slot 0) and the
    payload store (`i64store @8`, slot 1) — a store to one cannot
    touch the other, the walk having put a full `width` between the
    slots (`go_pairwise`'s gap law). -/
theorem rcCell_payload_disjoint :
    rcCellOff + Layout.width objectSlot ≤ boxPayloadOff := by decide

/-- The closure face of the same law: the fnIdx store (slot 1) and
    the first capture store (slot 2) are `width`-disjoint. -/
theorem fnIdx_cap_disjoint :
    closureFnIdxOff + Layout.width objectSlot ≤ closureCapOff := by decide

/-! ## The lowering state -/

/-- One lowering's state: the IR variable → (local index, type row)
    bindings, the DECLARED locals beyond the params (creation order —
    the encoder's local groups), the next fresh index, the emitted
    instructions (accumulated REVERSED; `emitted` reverses at the
    end), the LIVE jp registrations (target → the depth offset `X`
    with `br (d - X)` + the param locals), the module's SIBLING
    registry (the cross-decl call lane's function-index discipline:
    decl name → (function-table index, param arity) — `lowerFuncs`'s
    decl order, a self-recursive decl's OWN index included), the
    CLOSURE PROVENANCE (a pap-bound variable → the pap's callee name +
    the captured (local, width) slots — function-scoped, closures are
    read-only), the SIG REGISTRY (the indirect-call lane's
    type-index discipline, threaded across the decls), the
    ALLOCATION-SHAPE PROVENANCE (an allocated variable → its byte
    extent — the RC REUSE's del-side key; function-scoped like the
    locals), and the EXTERN CONTRACT REGISTRY (decl name → the
    declared `ExternSig` — the call lane's type-check against the
    declared trust boundary; module-scoped, threaded across the
    decls). -/
structure LState where
  /-- The IR variable → (local index, the bound TYPE ROW — the
      field-class law's key at the ctor arm, the closure-row check's
      key at the first-class application). -/
  fvars : Std.HashMap IR.Var (Nat × IR.Ty) := {}
  locals : List WasmCore.ValType := []
  next : Nat := 0
  out : List WasmCore.Instr := []
  jps : Std.HashMap IR.Var (Nat × List Nat) := {}
  /-- The module's sibling registry (the CALL LANE's function-index
      discipline): decl name → (the function-table index —
      `lowerFuncs`'s decl order — and the param arity). -/
  sibs : List (String × Nat × Nat) := []
  /-- THE CLOSURE PROVENANCE (the known-arity application's
      discipline): a pap-bound variable → (the pap's callee name, the
      captured (local, width) slots in order). Function-scoped like
      the locals (a second application reuses the same captured
      locals — closures are read-only under the model). -/
  paps : Std.HashMap IR.Var (String × List (Nat × WasmCore.ValType)) := {}
  /-- THE SIG REGISTRY (the indirect-call lane's type-index
      discipline): the closure signatures the first-class applications
      need, in registration order — appended to the module's type
      section AFTER the decl types (the application's type index =
      the decl count + the registry position). Module-scoped: the
      fold threads it across the decls (`lowerFuncs`). -/
  sigs : List WasmCore.FuncType := []
  /-- THE ALLOCATION-SHAPE PROVENANCE (the RC REUSE's del-side key):
      an allocated variable → its byte extent (the allocSeq size the
      variable was born with). Function-scoped: a shape-UNKNOWN del
      (a param, a copy's target) keeps the dead marking only. -/
  shapes : Std.HashMap IR.Var Nat := {}
  /-- THE EXTERN CONTRACT REGISTRY (the declared trust boundary's
      call-site teeth): decl name → the declared contract. Module-
      scoped: the fold threads it across the decls (`lowerFuncs`). -/
  exts : List (String × IR.ExternSig) := []
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

/-- Bind a fresh local of type `t` to the IR variable (the legacy
    `bindLocal`). The index is beyond the params (params bind first,
    0..n-1), so it lands in the DECLARED list. -/
def bindLocal (v : IR.Var) (t : IR.Ty) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with
    fvars := s.fvars.insert v (idx, t)
    locals := s.locals ++ [tyRepr t]
    next := s.next + 1 }
  return idx

/-- THE BINDING DISCIPLINE, written once: bind the result local, run
    the allocation face (`pre` — the box/ctor/pap layouts allocate
    BEFORE the store rides the bound slot), store. Returns the slot. -/
private def bindStore (decl : IR.LetDecl) (pre : M Unit := pure ()) : M Nat := do
  let l ← bindLocal decl.var decl.ty
  pre
  emitI (.localset l)
  return l

/-- Bind PARAM local i (index in order; NOT in the declared-locals
    list — wasmcore's `Func.locals` means locals BEYOND the params,
    and the validator/types read `params ++ locals`). -/
def bindParam (v : IR.Var) (t : IR.Ty) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with fvars := s.fvars.insert v (idx, t), next := s.next + 1 }
  return idx

/-- Bind a fresh local of wasm type `t` with NO variable (the
    function's result local — the exit-frame discipline's carrier;
    the rc/scratch locals of the lanes). -/
def bindFresh (t : WasmCore.ValType) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with locals := s.locals ++ [t], next := s.next + 1 }
  return idx

/-- The variable's local INDEX (the legacy `load`; unbound = the loud
    bug diagnostic, never a fabricated index). -/
def load (v : IR.Var) : M Nat := do
  match (← get).fvars[v]? with
  | some (n, _) => return n
  | none => throw (.unboundFVar v)

/-- The variable's BOUND TYPE ROW (the repr checks' lookup). -/
def tyOf? (v : IR.Var) : M (Option IR.Ty) := do
  return (← get).fvars[v]? |>.map (·.2)

/-- The operand-type guard (the doubled-throw teeth, written once):
    the operand's type must exist AND satisfy `ok` — else the named
    refusal (the detail string spelled per site). -/
private def guardTy (v : IR.Var) (ok : IR.Ty → Bool) (msg : String)
    (detail : String) : M IR.Ty := do
  match ← tyOf? v with
  | some t => if ok t then pure t else throw (.typeOutsideFragment msg detail)
  | none => throw (.typeOutsideFragment msg detail)

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

/-- Emit one argument's load (the IR is ANF: a real arg is always a
    variable; an erased arg pushes nothing — the legacy `emitArg`). -/
def emitArg : IR.Arg → M Unit
  | .var v => do emitI (.localget (← load v))
  | .erased => pure ()
  | .typeArg => throw (.argShape "a type argument")

/-! ## The boxed-Nat lane (the object discipline's seed) -/

/-- THE BUMP ALLOCATOR (inlined per allocation site): read the bump
    pointer from cell 0; the object's ADDRESS is the bump pointer
    itself (`max p heapBase` — a zeroed cell, fresh memory, allocates
    at `heapBase`); the bump then advances PAST the object
    (`addr + sz`) — the next allocation starts at this object's end,
    never inside it (the allocator's non-overlap law: object k occupies
    `addr .. addr + sz`, and the next object's base is exactly `addr +
    sz`). THE RC DISCIPLINE rides the allocation (rc = 1 at birth,
    the `inc`/`dec`/`del` forms maintain the cell). THE RC REUSE: the
    allocation first consults the single dead-slot cache (addr @4,
    size @8) — a dead slot of the EXACT requested size is handed back
    (the shape match, the runtime teeth) and the bump does NOT advance;
    otherwise the fresh bump path runs and the cache is untouched. The
    HONESTY: the reuse changes only WHERE the object lands — a live
    object's address never changes (only rc=0 slots publish, under the
    rc=1 del assertion), so the program's observable behavior is
    identical with and without the reuse (the behavior-identity pins
    in GuestTests). An exhausted arena stays the bounded-memory
    `memOOB` trap, never corruption. Returns the scratch local holding
    the address (also left on the stack). -/
def allocSeq (sz : Nat) : M Nat := do
  let s ← bindFresh .i32
  -- addr = max(p, heapBase) as PURE ARITHMETIC — never the select,
  -- never a value-yielding if_: the executor's select keeps the
  -- SECOND-pushed value on a true condition (WasmCore.Exec's
  -- `.i32 b :: v1 :: v2` arm) while the standard wasm's keeps the
  -- FIRST-pushed (the deepest), and the if_ cannot yield a value at
  -- all (the blocktype's [] shape — wasmtime refuses "values remaining
  -- on stack at end of block"; the executor's leniency hid both faces
  -- until the E6 component duel ran the object lanes under wasmtime).
  -- The arithmetic: cond = (p < base) ∈ {0,1}; mask = 0 - cond (0 or
  -- all-ones); addr = p + ((base - p) & mask) — max on both engines,
  -- the binops' operand order being the duel-verified standard.
  emitI (.i32const 0); emitI (.mem .i32load 0 none)              -- p
  emitI (.localset s)                                            -- s = p
  emitI (.i32const 0)                                            -- the mask sub's minuend
  emitI (.localget s); emitI (.i32const heapBase)                -- p, base
  emitI (.op .i32ltu)                                            -- cond = p < base
  emitI (.op .i32sub)                                            -- mask = 0 - cond
  emitI (.i32const heapBase); emitI (.localget s)                -- base, p
  emitI (.op .i32sub)                                            -- base - p
  emitI (.op .i32and)                                            -- (base - p) & mask
  emitI (.localget s); emitI (.op .i32add)                       -- addrF = p + …
  emitI (.localset s)                                            -- s = addrF (the FRESH path's address)
  -- THE REUSE CONSULT (the same pure-arithmetic shape — the mask
  -- trick the max above proved on both engines): eq = (cs == sz);
  -- takeReuse = 0 - eq (all-ones on the reuse path, 0 on the fresh);
  -- addr = addrF + ((c - addrF) & takeReuse) — the dead slot `c` on
  -- reuse, the fresh bump address otherwise.
  let c ← bindFresh .i32
  emitI (.i32const rcCacheAddrOff); emitI (.mem .i32load 0 none)
  emitI (.localset c)
  let cs ← bindFresh .i32
  emitI (.i32const rcCacheSizeOff); emitI (.mem .i32load 0 none)
  emitI (.localset cs)
  let eq ← bindFresh .i32
  emitI (.localget cs); emitI (.i32const sz); emitI (.op .i32eq)
  emitI (.localset eq)
  let m ← bindFresh .i32
  emitI (.i32const 0); emitI (.localget eq); emitI (.op .i32sub)
  emitI (.localset m)
  let a ← bindFresh .i32
  -- addr = addrF + ((c - addrF) & takeReuse) — the SAME pure-
  -- arithmetic conditional shape as the max above (the mask local is
  -- the push, the base rides the final add)
  emitI (.localget s)                                            -- addrF
  emitI (.localget c); emitI (.localget s); emitI (.op .i32sub)  -- c - addrF
  emitI (.localget m); emitI (.op .i32and)                       -- & takeReuse
  emitI (.op .i32add)                                            -- addr
  emitI (.localset a)
  -- THE SHAPE DISPATCH (the two arms' stores — the unit-block if_ the
  -- alt-chain lanes run stores inside; no value crosses; the
  -- CONDITION — `eq` — is popped by the if_ like every chainWalk
  -- link): on REUSE the cache CLEARS (the slot is spent; the bump
  -- does NOT advance — the reused slot sits below it) and on FRESH
  -- the bump ADVANCES (the cache is untouched — the dead slot stays
  -- published for a later same-size allocation).
  emitI (.localget eq)
  emitI (.if_
    [.i32const rcCacheSizeOff, .i32const 0, .mem .i32store 0 none]
    [.i32const 0, .localget a, .i32const sz, .op .i32add
    , .mem .i32store 0 none])
  -- THE RC DISCIPLINE: one reference at birth (the `inc`/`dec`/`del`
  -- forms maintain the cell) — on the reuse path the dead cell's rc
  -- (the observable 0) is rewritten to the birth value
  emitI (.localget a)
  emitI (.i32const rcInit)
  emitI (.mem .i32store rcCellOff none)
  emitI (.localget a)
  return a

/-- THE ALLOCATION-SHAPE PROVENANCE (the RC REUSE's del-side key):
    the allocated variable's byte extent — a del of a shape-KNOWN var
    publishes its slot to the cache; a shape-UNKNOWN del (a param, a
    copy's target — the allocation happened in another decl or behind
    a move) keeps the dead marking only, the honest boundary (the
    slot leaks, bounded by the arena's page; no wrong reuse ever
    fires from an unknown shape). -/
def noteShape (v : IR.Var) (sz : Nat) : M Unit :=
  modify fun s => { s with shapes := s.shapes.insert v sz }

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
    use-after-free bug, never a silent wrap). The target local must
    hold an OBJECT-repr value (the rc cell lives @0 of the object);
    the VAR face (`rcOp`) checks the bound row, THIS face is the
    CASCADE's (a ref field's pointer loaded into a scratch local). A
    dec to zero leaves rc=0 — the DEAD object is observable, and only
    a DEL (the rc=1 assertion) publishes the slot to the reuse cache
    (the size-class freelist is the named follow-up; the leak is
    bounded by the arena's page). -/
def rcOpLoc (_op : String) (ptr : Nat) (n : Nat) (isInc : Bool) : M Unit := do
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

/-- The VAR face: the bound row must be OBJECT-repr (the rc cell lives
    @0 of the object); a u64 scalar is the named `rcOnScalar`
    inconsistency. -/
def rcOp (op : String) (v : IR.Var) (n : Nat) (isInc : Bool) : M Unit := do
  match ← tyOf? v with
  | some t =>
      if tyRepr t == .i32 then
        rcOpLoc op (← load v) n isInc
      else
        throw (.rcOnScalar op)
  | none => throw (.rcOnScalar op)

/-- THE IN-PLACE WRITE's LEGALITY (the mutation family's rc=1
    discipline): the target object's rc must be exactly ONE at the
    write — a SHARED cell's in-place write would corrupt every other
    reference's view (the loud unreach trap, never a silent write).
    Compile-time uniqueness tracking does not exist in this slice (the
    Perceus borrow analysis is the named follow-up), so the guard is
    the RUNTIME teeth; the copy-on-shared discipline is the named
    follow-up. -/
def rcUnique (ptr : Nat) : M Unit := do
  trapUnless [.localget ptr, .mem .i32load rcCellOff none
             , .i32const 1, .op .i32eq]

/-- Both args' payloads loaded into fresh i64 scratch locals (the
    boxed-Nat faps' read discipline: ANF variable args, the payload
    i64 @8). -/
def loadPayloads (args : Array IR.Arg) : M (Nat × Nat) := do
  let mut ps : List Nat := []
  for a in args do
    match a with
    | .var _ =>
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
    under the model — every arith result is a NEW box). The shape is
    recorded (the reuse discipline's del-side key). -/
def boxFromPayload (decl : IR.LetDecl) (r : Nat) : M Unit := do
  let l ← bindStore decl do let _p ← allocSeq boxSize; pure ()
  noteShape decl.var boxSize
  storeBoxTag l
  storeBoxPayload l r

/-- THE BOXED-NAT FAP LANE (the legacy's fap arms, inline-lowered).
    All rows arity 2 over the PAYLOADS (the boxes' i64 @8); the
    compares answer the raw i32 Bool, the arith allocates fresh
    boxes under the runtime cap discipline. -/
def emitNatFap (k : IR.NatFap) (decl : IR.LetDecl)
    (args : Array IR.Arg) : M Unit := do
  let (x, y) ← loadPayloads args
  match k with
  | .decEq | .beq | .decLt | .decLe =>
      let l ← bindLocal decl.var decl.ty
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
          -- passed 2^64 (the u64 result is a wrap-masquerade —
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

/-! ## The op surface (the IR's Binop rows → the wasm instructions) -/

/-- THE OP SURFACE (the legacy `binop?`'s row set, grown): the IR's
    `Binop` rows → the wasm instruction sequences. The closed row set
    is the legacy's proven surface grown by the probe-mined rows; the
    FRONTEND refuses a fap outside it (the named boundary — never a
    silent wrong lowering). The u8 arith rows end in the `and 0xFF`
    mask (i32 arithmetic wraps mod 2^32; a `UInt8` wraps mod 2^8).
    Ops are consumed from `WasmCore.OpTable`'s projections everywhere
    downstream (the ONE table, 07-extensibility R6). -/
def binopSeq : IR.Binop → List WasmCore.Instr
  | .u64add => [.op .i64add]
  | .u64sub => [.op .i64sub]
  | .u64mul => [.op .i64mul]
  | .u64ltu => [.op .i64ltu]
  | .u64eq => [.op .i64eq]
  | .u64shru => [.op .i64shru]
  | .u64wrap => [.op .i32wrapi64]
  | .u32add => [.op .i32add]
  | .u32sub => [.op .i32sub]
  | .u32mul => [.op .i32mul]
  | .u32and => [.op .i32and]
  | .u32xor => [.op .i32xor]
  | .u32ltu => [.op .i32ltu]
  | .u32eq => [.op .i32eq]
  | .u32shru => [.op .i32shru]
  | .u32ext => [.op .i64extendi32u]
  | .u8add => [.op .i32add, .i32const 255, .op .i32and]
  | .u8sub => [.op .i32sub, .i32const 255, .op .i32and]
  | .u8mul => [.op .i32mul, .i32const 255, .op .i32and]
  | .u8ltu => [.op .i32ltu]
  | .u8eq => [.op .i32eq]
  | .u8and => [.op .i32and]
  | .u8xor => [.op .i32xor]
  | .u8shru => [.op .i32shru]
  | .u8ext => [.op .i64extendi32u]

/-! ## The literal rendering + the let emission -/

/-- THE `let` lowering (the legacy `emitLet`'s slice, grown): the IR
    value forms — the scalar literals, the copy, the boxed-Nat lane,
    the op surface, the sibling call, the closure application, the
    ctor faces, the field reads, the scalar-box lane, the RC seed's
    let-adjacent forms. The FRONTEND already refused what the IR
    cannot express; every refusal HERE is a wasm-model decision (the
    cap, the provenance, the arity discipline) or a lowering-internal
    inconsistency (an unbound variable). -/
def emitLet (decl : IR.LetDecl) : M Unit := do
  match decl.value with
  | .litU64 v =>
      let l ← bindLocal decl.var .u64
      emitI (.i64const v); emitI (.localset l)
  | .litU32 v | .litU8 v =>
      let _l ← bindStore decl (emitI (.i32const v))
  | .litNat v =>
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
        let l ← bindStore decl do let _p ← allocSeq boxSize; pure ()
        noteShape decl.var boxSize
        storeBoxTag l
        storeBoxPayloadLit l v
  | .copy v =>
      let _l ← bindStore decl (emitI (.localget (← load v)))
  | .apply f args =>
      -- THE CLOSURE APPLICATION (the known-arity discipline): the
      -- applied variable must carry pap provenance (the lowering
      -- state's `paps`); captured + fresh must total the callee's
      -- arity; the call lowers DIRECTLY to the callee's function-table
      -- index with the captured locals pushed FIRST, then the fresh
      -- args (the executor's param-i-to-local-i convention verbatim).
      match (← get).paps[f]? with
      | none =>
          -- THE FIRST-CLASS APPLICATION (the indirect-call lane):
          -- the applied variable is an OPAQUE CLOSURE VALUE (the
          -- tobj/obj rows; the fnIdx @8 IS the table index). A
          -- non-closure applied (a scalar/boxed-scalar variable)
          -- refuses — never a silent wrong dispatch. The call: the
          -- fresh args push left to right, then the closure's fnIdx
          -- loads from @8 (the i32 on top), then `callindirect` at
          -- the SIGNATURE's type index — the signature (the fresh
          -- args' reprs → the result repr) registers in the module's
          -- type section (the sig registry, `sigs`); the EXECUTOR's
          -- table discipline does the runtime type check (a
          -- mismatched entry — e.g. a partial pap applied first-class
          -- — traps `indirectSig`, an out-of-bounds index traps
          -- `tabOOB`, never a wrong call).
          match ← tyOf? f with
          | some fty =>
              if fty.isClosureRow then
                let mut argTys : List WasmCore.ValType := []
                for a in args do
                  match a with
                  | .var af =>
                      match ← tyOf? af with
                      | some t => argTys := argTys ++ [tyRepr t]
                      | none =>
                          throw (.argShape "an untyped closure-application \
                            arg (the signature would skew)")
                  | .erased =>
                      throw (.argShape "an erased closure-application arg \
                        (the stack would skew)")
                  | .typeArg => throw (.argShape "a closure-application type argument")
                let sig : WasmCore.FuncType := ⟨argTys, [tyRepr decl.ty]⟩
                let s ← get
                let (k, sigs) := sigRegister s.sigs sig
                set { s with sigs := sigs }
                let tyIdx := s.sibs.length + k
                for a in args do emitArg a
                emitI (.localget (← load f))
                emitI (.mem .i32load closureFnIdxOff none)
                emitI (.callindirect tyIdx)
                let _l ← bindStore decl
              else
                -- the honesty: a non-closure applied refuses (a
                -- scalar/boxed-scalar variable has no fnIdx @8 — the
                -- dispatch would be garbage)
                throw (.closureApplyUnknown f)
          | none =>
              throw (.closureApplyUnknown f)
      | some (fn, caps) =>
          match (← get).sibs.lookup fn with
          | none => throw (.papUnknownFn fn)
          | some (idx, arity) =>
              if caps.length + args.size != arity then
                throw (.closureApplyArityDrift fn
                  (caps.length + args.size) arity)
              for (loc, _t) in caps do emitI (.localget loc)
              for a in args do
                match a with
                | .erased =>
                    throw (.argShape "an erased closure-application arg \
                      (the stack would skew)")
                | _ => emitArg a
              emitI (.call idx)
              let _l ← bindStore decl
  | .natFap k args =>
      -- THE BOXED-NAT FAP ROWS first (the legacy's fap dispatch
      -- order): the sanctioned Nat surface inline-lowers over the
      -- boxes' payloads. (The name-level dispatch + the arity
      -- refusal live at the frontend; this defensive check fires
      -- only on a hand-written IR.)
      if args.size != 2 then
        throw (.unsupportedConstruct "natFap"
          s!"arity {args.size} on a boxed-Nat row of arity 2")
      emitNatFap k decl args
  | .binop op args =>
      -- THE OP SURFACE: the reified row's instructions (the legacy's
      -- arg order: args emitted left to right, the op pops the row's
      -- sig — `semOp`'s convention consumes them, first popped
      -- first). (The name-level dispatch + the arity refusal live at
      -- the frontend; this defensive check fires only on a
      -- hand-written IR.)
      if args.size != IR.Binop.arity op then
        throw (.unsupportedConstruct "binop"
          s!"arity {args.size} on a row of arity {IR.Binop.arity op}")
      for a in args do emitArg a
      let _l ← bindStore decl ((binopSeq op).forM emitI)
  | .call fn args =>
      -- THE CROSS-DECL CALL LANE: a `call` naming a KNOWN sibling
      -- decl lowers to wasm `call` at the callee's function-table
      -- index (`lowerFuncs`'s decl order — a SELF-recursive decl
      -- calls its OWN index; the recursion's bound is the executor's
      -- fuel honesty, never a fabricated termination). The
      -- marshalling is the EXECUTOR'S calling convention exactly (the
      -- validator's `call` row is the shared contract): the args push
      -- LEFT TO RIGHT (param 0 first), the executor pops against
      -- `ft.params.reverse` and binds `param i → local i` — the
      -- legacy `for a in args do emitArg a` discipline verbatim. The
      -- return: the callee's exit-frame discipline leaves the result
      -- on the callee's final stack; the call boundary joins it over
      -- the caller's retained stack, so the `localset` right here
      -- reads it — every value crossing the call rides a LOCAL on
      -- BOTH sides. The frontend's fap dispatch delivers a `call`
      -- ONLY for a known sibling; an unknown name here is the op-
      -- surface refusal (the hand-written IR's honesty face).
      match (← get).sibs.lookup fn with
      | some (idx, arity) =>
          if args.size != arity then
            throw (.unsupportedConstruct s!"fap {fn}"
              s!"arity {args.size} on a decl of arity {arity}")
          -- THE EXTERN CONTRACT's CALL-SITE TEETH: a call naming an
          -- extern decl is type-checked against the DECLARED contract
          -- (each arg's bound row must equal the contract's param row,
          -- in order) — a drift refuses, never a silently skewed
          -- marshalling at the trust boundary. Non-extern callees
          -- have no row here (the sibs arity check is theirs).
          match (← get).exts.lookup fn with
          | none => pure ()
          | some sig =>
              for (a, pt) in args.toList.zip sig.params do
                match a with
                | .var av =>
                    match ← tyOf? av with
                    | some t =>
                        if t != pt then
                          throw (.externCallDrift fn (IR.Ty.render t)
                            (IR.Ty.render pt))
                    | none =>
                        throw (.externCallDrift fn "unbound"
                          (IR.Ty.render pt))
                | _ =>
                    throw (.argShape "an erased extern-call argument \
                      (the contract's rows are fvar rows — the stack \
                      would skew)")
          for a in args do
            match a with
            | .erased =>
                throw (.argShape "an erased call argument (the scalar \
                  fragment's args are fvars — the stack would skew)")
            | _ => emitArg a
          emitI (.call idx)
          let _l ← bindStore decl
      | none =>
          throw (.unsupportedConstruct s!"fap {fn}"
            "the primitive op surface (binop?) — everything else is the \
             named follow-up")
  | .ctor cidx args =>
      -- THE CTOR VALUE's two faces, keyed on the RESULT TYPE's row
      -- (the pipeline's impure-type law: an ENUM type's ctor value is
      -- a SCALAR — the u8/u16/u32 repr, the value IS the tag — while
      -- an OBJECT type's ctor value is a POINTER, even a payload-free
      -- one: the runtime's `lean_box`, an 8-byte {rc, tag} object,
      -- because the tag dispatch reads the tag @4 from MEMORY). The
      -- type row decides.
      if decl.ty.isObjRow then
        -- THE OBJECT FACE: allocate the object — header {rc reserved
        -- @0, tag @4} — then store the fields at the PIPELINE'S
        -- PACKING-LAW coordinates (refs first, one 8-byte slot each;
        -- the scalar region after them, packed by size class largest
        -- first) — the same coordinates the field-binding reads ride
        -- (the oproj lane's @8+i*8, the sproj lane's 8+n*8+off). Every
        -- arg must be a variable with a bound type and a FIELD CLASS
        -- (an unclassifiable field — an enum/Bool/Char repr —
        -- refuses, `ctorFieldClass`). THE RC SEED: the allocation
        -- inits rc=1 (one reference at birth) and the `inc`/`dec`
        -- forms maintain the cell; the REUSE discipline's del-side
        -- publish keys on this allocation's recorded shape.
        if args.all (fun a => match a with | .var _ => true | _ => false) then
          let mut fs : List (Nat × FieldClass) := []
          let mut ok := true
          let mut badTy := ""
          for a in args do
            match a with
            | .var v =>
                match ← tyOf? v with
                | some t =>
                    match fieldClass? t with
                    | some cl => fs := fs ++ [(← load v, cl)]
                    | none => ok := false; badTy := t.render
                | none => ok := false
            | _ => ok := false
          if !ok then
            throw (.ctorFieldClass badTy)
          -- the packing law: the ref fields take the slots 0..nRefs-1
          -- in order; the scalar region rides base slot nRefs, packed
          -- by size class (each scalar's within-region offset =
          -- `scalarOff` over the scalars before it)
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
          let l ← bindStore decl do let _p ← allocSeq (8 + nRefs * 8 + ssize); pure ()
          noteShape decl.var (8 + nRefs * 8 + ssize)
          emitI (.localget l); emitI (.i32const cidx)
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
        else
          throw (.unsupportedConstruct "ctor"
            "the object face (fvar args; erased args are the named follow-up)")
      else
        -- THE TAG DISCIPLINE's value face: a payload-free ctor's value
        -- IS the unboxed tag (the same repr the scalar lane branches
        -- on).
        unless args.isEmpty do
          throw (.unsupportedConstruct "ctor"
            "a ctor with fields of scalar-row result type — an enum repr \
             has no fields (the layout law's classification)")
        let _l ← bindStore decl (emitI (.i32const cidx))
  | .pap fn args =>
      -- THE CLOSURE DISCIPLINE's allocation face: the pap allocates
      -- the closure object — {rc (init 1 by allocSeq), tag 254, fnIdx
      -- (the callee's function-table index), captured slots @16 + i*8}
      -- — and records the PROVENANCE (the known-arity application
      -- reads it back; the closure object is the honest layout riding
      -- the landed object discipline, the legacy trampoline's proved
      -- offsets).
      match (← get).sibs.lookup fn with
      | none => throw (.papUnknownFn fn)
      | some (_idx, arity) =>
          if args.size >= arity then
            throw (.papArityDrift fn args.size arity)
          let mut caps : List (Nat × WasmCore.ValType) := []
          for a in args do
            match a with
            | .var v =>
                match ← tyOf? v with
                | some t => caps := caps ++ [(← load v, tyRepr t)]
                | none =>
                    throw (.typeOutsideFragment "pap captured arg type"
                      (IR.Ty.render decl.ty))
            | .erased =>
                throw (.argShape "a pap captured argument (the stack would skew)")
            | .typeArg => throw (.argShape "a pap type argument")
          if tyRepr decl.ty == .i32 then
            let l ← bindStore decl do let _p ← allocSeq (closureSize args.size); pure ()
            noteShape decl.var (closureSize args.size)
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
              { s with paps := s.paps.insert decl.var (fn, caps) }
          else
            throw (.typeOutsideFragment
              "pap result type (the closure object's pointer)"
              (IR.Ty.render decl.ty))
  | .sproj n offset v =>
      -- THE OBJECT SEED's read face: the scalar region's coordinates
      -- — the load at `8 + n*8 + offset` (the pipeline's spelling:
      -- n = the region's base slot, offset = the packed byte offset;
      -- the hand-built face spells the slot directly, offset 0 — the
      -- SAME formula); the load width from the RESULT's row (u64 →
      -- i64load, a u8 field → i32load8 — the packing law's 1-byte
      -- class, the rest i32load).
      let _l ← bindStore decl do
        emitI (.localget (← load v))
        let base := 8 + n * 8 + offset
        match decl.ty with
        | .u64 => emitI (.mem .i64load base none)
        | .u8 => emitI (.mem .i32load8u base none)
        | _ => emitI (.mem .i32load base none)
  | .oproj i v =>
      -- THE REF-FIELD READ (the tag dispatch's payload lane): field
      -- i's 8-byte slot @8 + i*8 — the packing law's ref coordinates,
      -- the SAME ones the ctor face writes; the pipeline's
      -- field-binding lets (the cons arm's `head := oproj[0] l`) read
      -- them. The value is a POINTER (the i32 repr).
      let vt ← guardTy v (fun t => tyRepr decl.ty == .i32 && tyRepr t == .i32)
        "oproj operand types (the base's object repr, the field's pointer result)"
        s!"{IR.Ty.render decl.ty} ← field {i}"
      let _ := vt
      let _l ← bindStore decl do
        emitI (.localget (← load v))
        emitI (.mem .i32load (8 + i * 8) none)
  | .box bty v =>
      -- THE SCALAR-BOX LANE (the `box` value form): a scalar's box IS
      -- the landed boxed-Nat layout ({rc init 1, tag 0, payload @8})
      -- — the width from the boxed row. An OBJECT-row boxed type
      -- (nat/tobj/tagged/obj) is the IDENTITY copy: the value IS the
      -- box already under the model (the real pipeline's
      -- `_boxed_const_1` shape boxes a SCALAR — the probe's observed
      -- `box ty=UInt64`).
      if bty.isObjRow then
        let _vt ← guardTy v (fun t => tyRepr t == .i32)
          "box (object-row) operand types"
          s!"{IR.Ty.render bty} ← {IR.Ty.render decl.ty}"
        let l ← bindStore decl (emitI (.localget (← load v)))
        let _ := l
      else
        match ← tyOf? v, tyRepr bty, tyRepr decl.ty with
        | some vt, .i64, .i32 =>
            if tyRepr vt == .i64 then
              let src ← load v
              let l ← bindStore decl do let _p ← allocSeq boxSize; pure ()
              noteShape decl.var boxSize
              storeBoxTag l
              storeBoxPayload l src
            else
              throw (.typeOutsideFragment "box operand types (the boxed \
                scalar's width, the result's pointer repr, the source \
                local's bound width)"
                s!"{IR.Ty.render bty} → {IR.Ty.render decl.ty}")
        | some vt, .i32, .i32 =>
            if tyRepr vt == .i32 then
              let src ← load v
              let l ← bindLocal decl.var decl.ty
              let _p ← allocSeq boxSize
              noteShape decl.var boxSize
              emitI (.localset l)
              storeBoxTag l
              emitI (.localget l); emitI (.localget src)
              emitI (.mem .i32store boxPayloadOff none)
            else
              throw (.typeOutsideFragment "box operand types (the boxed \
                scalar's width, the result's pointer repr, the source \
                local's bound width)"
                s!"{IR.Ty.render bty} → {IR.Ty.render decl.ty}")
        | _, _, _ =>
            throw (.typeOutsideFragment "box operand types (the boxed \
              scalar's width, the result's pointer repr, the source \
              local's bound width)"
              s!"{IR.Ty.render bty} → {IR.Ty.render decl.ty}")
  | .unbox v =>
      -- THE SCALAR-BOX's read face: the payload @8, the width from
      -- the RESULT's row (the `_lam._boxed` adapters' unbox shape).
      -- The operand must be OBJECT-repr (the box pointer).
      match ← tyOf? v with
      | some vt =>
          match tyRepr vt, tyRepr decl.ty with
          | .i32, .i64 =>
              let l ← bindLocal decl.var decl.ty
              emitI (.localget (← load v))
              emitI (.mem .i64load boxPayloadOff none)
              emitI (.localset l)
          | .i32, .i32 =>
              let l ← bindLocal decl.var decl.ty
              emitI (.localget (← load v))
              emitI (.mem .i32load boxPayloadOff none)
              emitI (.localset l)
          | _, _ =>
              throw (.typeOutsideFragment "unbox operand types (the box \
                pointer's object repr, the result's scalar width)"
                (IR.Ty.render decl.ty))
      | none =>
          throw (.typeOutsideFragment "unbox operand types (the box \
            pointer's object repr, the result's scalar width)"
            (IR.Ty.render decl.ty))
  | .const fn args =>
      -- THE _CLOSED FIXPOINT's value face (the legacy's "0-ary const:
      -- a top-level closure constant"): a 0-ary const naming a 0-ary
      -- SIBLING is the producer's call (the probe's family arrives as
      -- 0-ary FAPS — the call lane handles those; the const face is
      -- the honest twin). Anything else refuses with its named
      -- boundary.
      if args.isEmpty then
        match (← get).sibs.lookup fn with
        | some (idx, arity) =>
            if arity != 0 then
              throw (.unsupportedConstruct s!"const {fn}"
                "a 0-ary const of an arity-{arity} callee — the \
                 eta-closure face (the pap lane's named follow-up)")
            let l ← bindLocal decl.var decl.ty
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
def splitEntry (target : IR.Var) : IR.Code →
    Option (List IR.LetDecl × Array IR.Arg)
  | .let_ decl k =>
      splitEntry target k |>.map (fun (ls, a) => (decl :: ls, a))
  | .jmp f args => if f == target then some ([], args) else none
  | _ => none

/-! ## The loop-shape detector (the audit's `jumpsTo`) -/

-- Does `code` contain a `jmp` to `target`? (The loop-shape
-- detector — the audit's `jumpsTo`, ported as a plain structural
-- fold over the IR's spine.)
mutual
def jumpsTo (target : IR.Var) (code : IR.Code) : Bool :=
  match code with
  | .jmp f _ => f == target
  | .jp _ _ value k => jumpsTo target value || jumpsTo target k
  | .cases_ _ _ _ alts => altJumps target alts
  | .let_ _ k | .inc _ _ k | .dec _ _ _ k | .del _ k
  | .sset _ _ _ _ _ k | .oset _ _ _ k | .setTag _ _ k =>
    jumpsTo target k
  | .ret _ | .unreach => false
  | .extern _ => false
def altJumps (target : IR.Var) (alts : List IR.Alt) : Bool :=
  match alts with
  | [] => false
  | .ctorAlt _ code :: rest => jumpsTo target code || altJumps target rest
  | .default code :: rest => jumpsTo target code || altJumps target rest
end

/-! ## The ONE code walk (the legacy foldImpure consolidation's
##    discipline) -/

-- Lower the IR `Code`. ONE traversal; the single parameter `d` is
-- the RUNTIME FRAME DEPTH at the emission point (how many wasm
-- frames will enclose the emitted instructions when they run — the
-- ONE AST's frame-depth discipline). `res`/`resTy` = the function's
-- result local (index + repr) — every `.ret` stores it and branches
-- out to the function level (the exit-frame discipline). Structurally
-- recursive over the IR's spine.
mutual
def lowerCode (code : IR.Code) (d : Nat) (res : Nat)
    (resTy : WasmCore.ValType) : M Unit :=
  match code with
  | .let_ decl k => do
      emitLet decl
      lowerCode k d res resTy
  | .ret v => do
      let idx ← load v
      let fty ← tyOf? v
      if fty.map tyRepr != some resTy then
        throw (.armTypeMismatch (WasmCore.renderValType resTy)
          (WasmCore.renderValType ((fty.map tyRepr).getD .i64)))
      emitI (.localget idx); emitI (.localset res)
      -- the exit-frame discipline: branch to the OUTERMOST frame
      if d >= 1 then
        emitI (.br (d - 1))
      else
        throw (.loopEntry "a return outside the exit frame (depth 0) — \
          the exit-frame discipline's own inconsistency")
  | .unreach => emitI .unreach
  | .cases_ name via discr alts => do
      -- THE CTOR-CASE-ON-NAT THROW (the boxed-Nat model's pinned
      -- loud refusal): the generic tag dispatch would read the box's
      -- tag 0 and treat the payload as a POINTER — silently wrong.
      -- The real pipeline never produces one (Nat cases compile to
      -- decEq fap chains); the hand-built face can, and the model
      -- refuses.
      if name == "Nat" then
        throw .natCtorCase
      -- THE SCRUTINEE DISPATCH. The SCALAR lane (the frontend's
      -- prescan verdict, `via = .value`) branches on the VALUE (a
      -- Bool match compiles to the U8 representation — observed:
      -- `cases UInt8` carrying Bool ctorAlts — and a scalar-repr
      -- enum's repr IS the ctor tag). The OBJECT TAG DISPATCH: the
      -- scrutinee is an object POINTER (the i32 repr) — read the tag
      -- u8 @4 (the landed layout's proved offset; the runtime's
      -- `lean_obj_tag` face) into a fresh scratch local and branch on
      -- IT. The per-alt payload projections ride the object layout
      -- (the oproj lane's @8+i*8, the sproj lane's region
      -- coordinates — the SAME coordinates the ctor face writes).
      -- Anything else refuses loudly.
      match via with
      | .value => do
          let scrutIdx ← load discr
          -- the alt chain: arm i runs one chain link deeper (i+1 if_s)
          let altsI ← chainWalk scrutIdx alts (d + 1) res resTy
          altsI.forM emitI
      | .tag =>
          match ← tyOf? discr with
          | some t =>
              if tyRepr t == .i32 then
                let ptr ← load discr
                emitI (.localget ptr); emitI (.mem .i32load8u boxTagOff none)
                let tag ← bindFresh .i32
                emitI (.localset tag)
                let altsI ← chainWalk tag alts (d + 1) res resTy
                altsI.forM emitI
              else
                throw (.unsupportedConstruct s!"cases on {name}"
                  "the tag dispatch demands an object-repr (i32) \
                   scrutinee — the scalar lanes are Bool/UInt8/the \
                   prescan's enums")
          | none =>
              throw (.unsupportedConstruct s!"cases on {name}"
                "the tag dispatch demands an object-repr (i32) scrutinee — \
                 the scalar lanes are Bool/UInt8/the prescan's enums")
      -- the case is TERMINAL in the IR's impure spine: every arm ends
      -- ret/jmp/unreach or a nested case — nothing follows
  | .jp name params value k => do
      -- THE JOIN-POINT DISCIPLINE. Shape dispatch on the loop
      -- detector: a body that jumps back to ITSELF lowers to the
      -- loop frame; anything else takes the legacy's
      -- block-and-fallthrough shape. Either way the jp's params bind
      -- to fresh locals and the registration (depth offset X, param
      -- locals) lives exactly as long as the structure's emission.
      let mut ps : List Nat := []
      for (pv, pt) in params do
        ps := ps ++ [← bindLocal pv pt]
      modify fun s => { s with jps := s.jps.insert name (d + 2, ps) }
      if jumpsTo name value then
        -- THE LOOP SHAPE: the entry discipline (k = lets + entry jmp)
        match splitEntry name k with
        | none =>
            throw (.loopEntry "the loop shape's continuation must be a \
              straight-line let spine ending in the entry jmp (a br \
              cannot ENTER a frame; the entry-duplication transform is \
              the named follow-up)")
        | some (lets, args) =>
            for l in lets do emitLet l
            if args.size != ps.length then
              throw (.jpArityDrift name args.size ps.length)
            -- the entry arg stores: the first iteration's params
            for (a, p) in args.toList.zip ps do
              emitArg a
              emitI (.localset p)
            let bodyI ← scopedOut (lowerCode value (d + 2) res resTy)
            emitI (.block [.loop (bodyI ++ [.br 1])])
            emitI .unreach
      else
        -- THE BLOCK SHAPE (the legacy's block-and-fallthrough, in
        -- depths): k inside the inner block, the body after it, the
        -- fallthrough br skips the body, the seal closes.
        let kI ← scopedOut (lowerCode k (d + 2) res resTy)
        let bodyI ← scopedOut (lowerCode value (d + 1) res resTy)
        emitI (.block ([.block (kI ++ [.br 1])] ++ bodyI))
        emitI .unreach
      -- the registration's scope ends with the structure
      modify fun s => { s with jps := s.jps.erase name }
  | .jmp target args => do
      -- the goto: store the args into the jp's param locals, branch
      -- out to the jp's structure (br (d - X) — through any if_
      -- nesting)
      match (← get).jps[target]? with
      | none =>
          throw (.jpUnregistered target)
      | some (x, ps) =>
          if args.size != ps.length then
            throw (.jpArityDrift target args.size ps.length)
          for (a, p) in args.toList.zip ps do
            emitArg a
            emitI (.localset p)
          if d >= x then
            emitI (.br (d - x))
          else
            throw (.jpUnregistered target)
  | .inc v n k => do
      -- THE RC DISCIPLINE: the rc cell's REAL arithmetic (the `check`
      -- and `persistent` flags ride recorded-and-ignored — the
      -- frontend dropped them). The over-dec guard and the
      -- dead-marking live at `rcOp`.
      rcOp "inc" v n true
      lowerCode k d res resTy
  | .dec v n cascade k => do
      -- THE RC DISCIPLINE: the object's own rc drops first, then THE
      -- FIELD CASCADE — `cascade = some nRefs` means the dying object
      -- had nRefs REF fields (the frontend's `objs?` count, riding the
      -- landed layout: the ref slots are `0..nRefs-1`); each field's
      -- pointer is loaded (@8 + i*8, the packing law's ref
      -- coordinates) and its rc decremented by 1 under the SAME
      -- over-dec guard (the counts stay honest — a cascaded field
      -- over-dec is the same use-after-free bug, the same loud trap).
      -- The DEEP cascade (a field's own fields) is the named
      -- follow-up: this slice's discipline is the immediate fields,
      -- exactly the count the LCNF frontend carries.
      rcOp "dec" v n false
      match cascade with
      | none => pure ()
      | some nRefs => do
          let ptr ← load v
          for i in List.range nRefs do
            emitI (.localget ptr)
            emitI (.mem .i32load (8 + i * 8) none)
            let fp ← bindFresh .i32
            emitI (.localset fp)
            rcOpLoc "dec" fp 1 false
      lowerCode k d res resTy
  | .del v k => do
      -- THE DEL (the honest deallocation within the arena's model):
      -- the OWNERSHIP ASSERTION checked at runtime — del fires only
      -- when the target's rc is exactly 1 (the statically-owned face;
      -- a del on a shared or dead object is a compiler bug, the loud
      -- trap) — then the DEAD MARKING: rc = 0, the slot observable.
      -- THE REUSE PUBLISH (the reuse discipline's del face): a
      -- shape-KNOWN del publishes its slot to the allocator's
      -- single-slot cache — (addr @4, size @8) — the next same-size
      -- allocation hands it back; a shape-UNKNOWN del (a param, a
      -- copy's target) keeps the dead marking only (the honest
      -- boundary — no wrong reuse ever fires from an unknown shape).
      -- The publish rides AFTER the rc=1 guard: a shared del traps
      -- before anything is published (the legality's ordering). The
      -- FIELD cascade is dec's discipline (del carries no objs?
      -- count in the LCNF — the fields' decs were emitted before it).
      let ptr ← load v
      rcUnique ptr
      emitI (.localget ptr); emitI (.i32const 0)
      emitI (.mem .i32store rcCellOff none)
      match (← get).shapes[v]? with
      | some sz => do
          emitI (.i32const rcCacheAddrOff); emitI (.localget ptr)
          emitI (.mem .i32store 0 none)
          emitI (.i32const rcCacheSizeOff); emitI (.i32const sz)
          emitI (.mem .i32store 0 none)
      | none => pure ()
      lowerCode k d res resTy
  | .sset v i offset val ty k => do
      -- THE IN-PLACE WRITE (the scalar field): the rc=1 legality
      -- guard, then the store at the SAME coordinates the `sproj`
      -- read rides (`8 + i*8 + offset`), the width from the field's
      -- row (u64 → i64store, a u8 field → i32store8 — the packing
      -- law's 1-byte class, the rest i32store). Both operands must
      -- carry the bound rows (the target object-repr; the value's
      -- width checked against the field row's repr — a u64 field
      -- needs an i64 local).
      match ← tyOf? v, ← tyOf? val with
      | some vt, some valTy =>
        if tyRepr vt == .i32 && tyRepr valTy == tyRepr ty then do
          let ptr ← load v
          rcUnique ptr
          emitI (.localget ptr)
          emitI (.localget (← load val))
          match ty with
          | .u64 => emitI (.mem .i64store (8 + i * 8 + offset) none)
          | .u8 => emitI (.mem .i32store8 (8 + i * 8 + offset) none)
          | _ => emitI (.mem .i32store (8 + i * 8 + offset) none)
        else
          throw (.typeOutsideFragment "sset operand types (the target's \
            object repr, the value's field width)"
            s!"{IR.Ty.render ty} ← {IR.Ty.render valTy}")
      | _, _ =>
          throw (.typeOutsideFragment "sset operand types (the target's \
            object repr, the value's field width)"
            (IR.Ty.render ty))
      lowerCode k d res resTy
  | .oset v i val k => do
      -- THE IN-PLACE WRITE (the ref field): the rc=1 legality guard,
      -- then the POINTER store at the packing law's ref coordinates
      -- (`8 + i*8` — the SAME slots the ctor face writes and the
      -- `oproj` read rides). Both operands object-repr (pointers).
      -- NOTE the RC HONESTY: the displaced reference's dec is the
      -- CALLEE's obligation (the Perceus stream decs the old value
      -- before the oset); the lowering stores exactly what the IR
      -- names, nothing else.
      match ← tyOf? v, ← tyOf? val with
      | some vt, some valTy =>
        if tyRepr vt == .i32 && tyRepr valTy == .i32 then do
          let ptr ← load v
          rcUnique ptr
          emitI (.localget ptr)
          emitI (.localget (← load val))
          emitI (.mem .i32store (8 + i * 8) none)
        else
          throw (.typeOutsideFragment "oset operand types (both \
            object-repr pointers)"
            s!"{IR.Ty.render valTy} ← field {i}")
      | _, _ =>
          throw (.typeOutsideFragment "oset operand types (both \
            object-repr pointers)" "unbound")
      lowerCode k d res resTy
  | .setTag v cidx k => do
      -- THE IN-PLACE WRITE (the tag byte): the rc=1 legality guard,
      -- then the u8 store @4 (the SAME tag cell the dispatch reads;
      -- a writable tag is the model's enum-in-object face). The
      -- target must be object-repr.
      match ← tyOf? v with
      | some vt =>
        if tyRepr vt == .i32 then do
          let ptr ← load v
          rcUnique ptr
          emitI (.localget ptr); emitI (.i32const cidx)
          emitI (.mem .i32store8 boxTagOff none)
        else
          throw (.typeOutsideFragment "setTag target type (the object \
            repr)" (IR.Ty.render vt))
      | none =>
          throw (.typeOutsideFragment "setTag target type (the object \
            repr)" "unbound")
      lowerCode k d res resTy
  | .extern _sig =>
      -- THE EXTERN FACE (the declared trust boundary): the contract
      -- rode the ctor as DATA (the declaration check against the
      -- decl's faces ran at `lowerFuncs`; the call sites are checked
      -- against it at the call lane); the function + export landed
      -- (the call lane's index); the body is NOT modeled — `unreach`
      -- is the honest placeholder (the host link step is the named
      -- follow-up; a call reaching it traps loudly, never a wrong
      -- answer).
      emitI .unreach
def chainWalk (scrutIdx : Nat) (alts : List IR.Alt) (d : Nat)
    (res : Nat) (resTy : WasmCore.ValType) : M (List WasmCore.Instr) := do
  -- The alt-chain fold (the legacy `buildAlts`): nested `if_`s keyed
  -- on the ctor index, a `default` alt as the final else, an
  -- uncovered ctor set as `[unreach]` (the alt chain is exhaustive at
  -- runtime). Arm i of the chain lowers at depth `d` (each chain
  -- link is one `if_` frame). Structurally recursive over the list.
  match alts with
  | [] => return [.unreach]
  | .ctorAlt cidx code :: rest => do
      let thenI ← scopedOut (lowerCode code d res resTy)
      let elseI ← chainWalk scrutIdx rest (d + 1) res resTy
      return ([.localget scrutIdx, .i32const cidx, .op .i32eq]
        ++ [.if_ thenI elseI])
  | .default code :: _ =>
      -- THE DEFAULT's depth (the order-preserving chain's honesty):
      -- the default runs in the LAST if_'s ELSE — the SAME depth as
      -- that link's then-arm, NOT one frame deeper (a default arm is
      -- not a chain LINK; it opens no if_). Lowering it at `d` would
      -- emit the exit-frame `br` one frame too shallow... one too
      -- DEEP — the executor answers `branch` past the function (the
      -- setTag control's teeth caught exactly that).
      scopedOut (lowerCode code (d - 1) res resTy)
end

/-! ## The decl lowering -/

/-- The per-decl walk: bind the param locals (0..n-1 in order — the
    executor driver's binding discipline: param i lands in local i),
    bind the result local, walk the body at depth 1 (inside the exit
    frame), collect the emitted instructions + the result index. -/
def declWalk (code : IR.Code) (params : List (IR.Var × IR.Ty))
    (resTy : WasmCore.ValType) : M (List WasmCore.Instr × Nat) := do
  for (v, t) in params do
    discard <| bindParam v t
  let res ← bindFresh resTy
  lowerCode code 1 res resTy
  let body ← emitted
  pure (body, res)

/-- Lower SEVERAL IR decls into ONE module: one type + one function +
    one export per decl (the entry index = the decl order). The decls
    see each other through the CALL LANE: the sibling registry
    (`name → (function-table index, param arity)` — the index IS the
    decl order, a self-recursive decl's OWN index included) feeds
    every `call` to wasm `call` under the executor's calling
    convention; a call naming a NON-sibling refuses (never a
    fabricated index-0 call). THE INDIRECT-CALL LANE: a decl's
    first-class applications register their signatures in the SIG
    REGISTRY (threaded across the fold — dedup at registration); the
    module's type section grows the sig types AFTER the decl types,
    and the ONE funcref table gets the IDENTITY entries (table i =
    function i — the closures' fnIdx discipline), present exactly when
    the lane fired (the validator's table-index discipline refuses a
    `callindirect` over an absent table). -/
def lowerFuncs (ds : List IR.Decl) : Except LowerError WasmCore.Module :=
  let sibs := ds.zipIdx.map (fun p => (p.1.name, p.2, p.1.params.length))
  -- THE EXTERN CONTRACT REGISTRY (module-scoped): the extern decls'
  -- contracts, keyed by name — the call lane's type-check face.
  let exts := ds.filterMap
    (fun d => match d.value with | .extern sig => some (d.name, sig) | _ => none)
  let one (i : Nat) (d : IR.Decl) (sigs0 : List WasmCore.FuncType) :
      Except LowerError
        (WasmCore.FuncType × WasmCore.Func × String × List WasmCore.FuncType) := do
    -- THE EXTERN CONTRACT's DECLARATION CHECK: the decl's faces must
    -- MATCH the contract the ctor carries (the params' rows in order,
    -- the result row) — a drift refuses BEFORE anything is emitted
    -- (a skewed boundary is a silently wrong marshalling; the
    -- contract-as-data's teeth at the declaration face).
    match d.value with
    | .extern sig =>
        let gotParams := d.params.map (fun p => p.2)
        if gotParams != sig.params || d.resultTy != sig.result then
          throw (.externSigDrift d.name
            s!"{gotParams.map IR.Ty.render} → {IR.Ty.render d.resultTy}"
            s!"{sig.params.map IR.Ty.render} → {IR.Ty.render sig.result}")
        else
          pure ()
    | _ => pure ()
    match StateT.run (declWalk d.value d.params (tyRepr d.resultTy))
        ({ fvars := {}, locals := [], next := 0, out := []
         , jps := {}, sibs := sibs, sigs := sigs0, exts := exts } : LState) with
    | .error e => .error e
    | .ok ((bodyI, res), st) =>
        let ft : WasmCore.FuncType :=
          ⟨d.params.map (fun p => tyRepr p.2), [tyRepr d.resultTy]⟩
        let f : WasmCore.Func :=
          { tyIdx := i, locals := st.locals
          , body := [.block bodyI, .localget res] }
        .ok (ft, f, d.name, st.sigs)
  let accTy :=
    Except LowerError
      (List (WasmCore.FuncType × WasmCore.Func × String) × List WasmCore.FuncType)
  let step : accTy → (IR.Decl × Nat) → accTy := fun acc p =>
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

/-- Lower ONE IR decl to a one-function module: one type (the params →
    the mapped reprs, the result → its repr), one function (the
    exit-frame discipline: the body inside the outermost frame,
    `localget res` after), exported under the decl's own name. -/
def lowerFunc (d : IR.Decl) : Except LowerError WasmCore.Module :=
  lowerFuncs [d]

end Guest
