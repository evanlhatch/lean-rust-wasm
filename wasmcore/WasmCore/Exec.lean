/-
# WasmCore.Exec — the executor over the ONE AST

The honest minimal executor: the machine-int values (the i64/i32
discipline — `UInt64`/`UInt32` native wrap IS the mod-2^k semantics),
index-keyed locals, the fuel-bounded step, the frame-depth structured
control, the DIRECT-CALL discipline over the module's function table
(calls as fuel-shared big steps — the legacy calls-layer shape), and
the memory ops with the bounds check IN the executor. It executes THE
SAME `Instr` tree the encoder emits — no `Sem.Instr` twin, no
lowering seam (notes/design-one-instr-ast.md §1: the emitter's output
IS the machine's input).

**The outcome discipline** (the layered Err discipline, mined from
`legacy/lean/wasm-backend/Sem.lean`): every run answers ONE closed
`Outcome` — `.ok s` (completed normally; the final stack carries the
results), `.branch d s` (the STRUCTURED branch signal: escape `d`
frames — `some d` — carrying the branch-point state, or `none` = the
RETURN signal (`ret` = the branch-to-outermost discipline: escape
every frame; the state's stack carries the results) — NOT a trap; the
frame cases of `execList` absorb/decrement/pass it, the call boundary
consumes `none` as the callee's return and answers `unmodeled` for a
`some` escape — branches do not cross calls), `.trap t` (a genuine
wasm trap: `unreach` or the out-of-bounds memory access — a RUNTIME
trap, never corruption), `.structural` (`step` applied to a frame
form: unreachable in practice — `execList` dispatches
`block`/`loop`/`if_` before ever calling `step`), `.unmodeled`
(explicitly outside the executed fragment: non-integer locals'
defaults, a call to an index the module does not resolve, and a `br`
escaping the callee's frames — the validator's documented
branch-depth gap, whose return convention the signal cannot name —
the R6 discipline: an unmodeled SEM is DISTINCT from a trap, never
conflated into it), or `.outOfFuel`.

**The fuel discipline** (01-core §3: the budget is SEMANTICS):
`execList` consumes one unit per flat step, frame entry, and loop
restart; exhaustion answers the honest `.outOfFuel` outcome — DATA
about the run, never a verdict about the program.

**The observer discipline** (04 §4: every claim names its observer):
`Outcome` is the apiObs face — final machine state (hence the return
values) + the trap kind + the budget answer. No events, no costs, no
principal views are claimed; compiler/lane correctness theorems state
exactly this observation and nothing more.

**The type-mismatch trap is unrepresentable post-validation** (the
type-safety discipline): `Trap.typeErr` (the stack-shape violation:
underflow or operand-type mismatch — legacy's `Err.underflow`, renamed
for what it is) can only fire on a stack whose static view does not
provide the op's pops. THE FULL TYPE-SAFETY THEOREM IS LANDED:
`step_preserves` pins the flat slice (a computing step of ANY
instruction rides the ONE op table's rows from a well-typed stack to a
well-typed stack); `exec_typed` lands the body-level induction grown
to the calls layer (the frame machine's preservation + the callee's
well-typed entry via the call-typing premise — the frame/branch/return
plumbing riding the `BodyTy` relation, the fuel honesty in the
statement: `.outOfFuel` is a possible answer, never a type trap — a
divergent recursion included); `runFunc_safe` lands the module-level
face (a validated module's function — its WHOLE call chain, the
premise discharged from `checkModule` — on `call`-rule-typed args,
never type-traps and completes at the declared results).

**The op-table integration** (07-extensibility R6): the executor's
operand shapes ride the table's `opPop`/`opPush`/`memPop`/`memPush`
projections — `popTys` pops EXACTLY the row's pops (types checked
against the row), `semOp` computes the row's push. The per-op VALUE
arithmetic (`semOp`) lives here, keyed on the closed `Op` universe
with explicit arms (R7: no wildcard — a new ctor breaks the build
until its row AND its arm exist). The table's `sem` note field stays
the prose face; upgrading it to carry the step function in-place
would invert the cone (OpTable cannot import Exec) — the one-row
claim is discharged by this file's explicit-arm + table-projection
structure instead (the honest note, per the work order's "OR").

The five questions (notes/v3/01-core.md):

- **Root**: the transition semantics — a FUNCTION (`execList`/`step`
  are plain defs, never relations). Determinism is free by
  construction: one state, one list, one budget ⇒ one outcome; there
  is no choice point to discharge and no triviality to prove
  elaborately. The name of the discipline is the definition's type.
- **Carrier grade**: none new — the executor rides `Validate`'s
  proved bridge (`step_preserves`' statement cites `stepFlag`); the
  theorem is a hand theorem with named relational content (rung 6).
- **Spine reading**: the AST + the op table read into machine runs —
  the LAST consumer of the one-AST spine.
- **Ladder rung**: rung 1 for the machine (total folds) + rung 6 for
  `step_preserves`/`step_store_inBounds` and the type-safety chain
  (`exec_typed`, `runFunc_safe` — hand theorems with named relational
  content).
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set) + WasmCoreTests' execution pins
  (the worked module runs; the trap teeth; the fuel honesty; the
  negative controls).

Consumer trail: rides `WasmCore.Types`, `WasmCore.Instr`,
`WasmCore.OpTable` (the ONE table's sig projections),
`WasmCore.Module`, `WasmCore.Validate` (the checker the theorem
rides). Core-only (the cone rule — no mathlib, no Batteries).
-/

import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module
import WasmCore.Validate

namespace WasmCore

/-! ## Values — the machine-int discipline -/

/-- A runtime value. The fragment is integer-only: `i32` rides
    `UInt32`, `i64` rides `UInt64` — the native wrap IS the mod-2^k
    semantics (no `wrap64` re-derivation, legacy R2's lesson). -/
inductive Val where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
deriving BEq, DecidableEq, Repr, Inhabited

/-- The dynamic type of a value (a `ValType` — the SAME universe the
    validator's rows speak). -/
def tyOf : Val → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64

/-- The static view of an operand stack (head = TOP). Pattern-matched
    so the per-cons equations are simp-usable. -/
def stackTys : List Val → List ValType
  | [] => []
  | v :: vs => tyOf v :: stackTys vs

@[simp] theorem tyOf_i32 (n : UInt32) : tyOf (.i32 n) = .i32 := rfl
@[simp] theorem tyOf_i64 (n : UInt64) : tyOf (.i64 n) = .i64 := rfl

/-- `stackTys` splits over append (the load/store proofs' bridge). -/
theorem stackTys_append (a b : List Val) :
    stackTys (a ++ b) = stackTys a ++ stackTys b := by
  induction a with
  | nil => rfl
  | cons v vs ih => simp [stackTys, ih]

/-- Only the empty stack has the empty static view. -/
theorem nil_of_stackTys_nil (l : List Val) (h : stackTys l = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons v vs => simp [stackTys] at h

/-! ## Machine state -/

/-- One machine state. Locals = a total `Nat → Val` map (index-keyed;
    "every local exists" is definitional — the unbound-local READ is
    the validator's refusal, never a runtime event); operand stack =
    a `List Val` (head = TOP); memory = a total byte function + its
    size (valid addresses are `< memSize` — the bounded-memory
    discipline). -/
structure State where
  /-- The locals (function-scoped). -/
  locals : Nat → Val
  /-- The operand stack, head = TOP. -/
  stack : List Val
  /-- The (linear) memory bytes. -/
  mem : Nat → UInt8
  /-- The memory size in bytes. -/
  memSize : Nat
deriving Inhabited

/-! ## The outcome discipline -/

/-- The trap kinds. `typeErr` is the stack-shape violation (underflow
    or operand-type mismatch — legacy's `Err.underflow`, renamed for
    what it is): UNREPRESENTABLE post-validation (the type-safety
    discipline). `memOOB` is the bounded-memory runtime trap (never
    corruption). `unreach` is `unreachable`. The INDIRECT-CALL lane's
    two RUNTIME traps (the table discipline's teeth — both
    data-dependent checks the validator cannot do statically, both
    DISTINCT from `typeErr` so the type-safety theorem survives the
    new arm): `tabOOB` — the callee index is past the table's entries
    (a null entry); `indirectSig` — the entry's resolved type differs
    from the declared one (a mismatched closure applied; never a wrong
    call). -/
inductive Trap where
  | unreach
  | memOOB
  | typeErr
  | tabOOB
  | indirectSig
deriving BEq, DecidableEq, Repr, Inhabited

/-- THE layered outcome of a run — the honest ledger, never a bare
    Bool:

- `.ok s` — completed normally; `s.stack` carries the results.
- `.branch d s` — the structured branch signal: escape `d` frames
  (`some d`, carrying the branch-point state) or the RETURN signal
  (`none` — `ret` = the branch-to-outermost discipline: escape every
  frame; the carried state's stack holds the results). NOT a trap: the
  frame cases of `execList` absorb (`some 0`), decrement
  (`some (n+1)`), or pass (`none`) it; the call boundary consumes
  `none` as the callee's return.
- `.trap t` — a genuine wasm trap (`unreach`/`memOOB`) or the
  type-error (`typeErr`, unrepresentable post-validation).
- `.structural` — `step` saw a frame form; `execList` dispatches
  those, so this never escapes a run (totality arm only).
- `.unmodeled` — explicitly outside the executed fragment:
  non-integer locals' defaults, a call to an index the module does not
  resolve (unreachable post-validation — the validator's
  `unboundFunc`), and a `br` escaping the callee's frames (the
  validator's documented branch-depth gap — wasm rejects it
  statically; the escape signal names no return convention, so the
  call boundary refuses to fabricate one): DISTINCT from `trap` (the
  R6 discipline — an unmodeled SEM is never laundered into a wasm
  trap).
- `.outOfFuel` — the budget ran out: honest DATA about the run
  (01-core §3), never a verdict about the program. -/
inductive Outcome where
  | ok (s : State)
  | branch (depth : Option Nat) (s : State)
  | trap (t : Trap)
  | structural
  | unmodeled
  | outOfFuel
deriving Inhabited

/-! ## The typed pop engine (the op table's runtime face) -/

/-- Pop `pops` (head = top, FIRST popped FIRST — the ONE op table's
    pop convention) from the stack, checking each popped value's type
    against the row. Answers the popped values (in pop order) + the
    rest. This is the executor's operand discipline: the shapes come
    from `opPop`/`memPop` (the table's rows), never re-spelled. -/
def popTys : List ValType → List Val → Option (List Val × List Val)
  | [], l => some ([], l)
  | _ :: _, [] => none
  | t :: ts, v :: vs =>
      if tyOf v = t then
        match popTys ts vs with
        | some (args, rest) => some (v :: args, rest)
        | none => none
      else none

/-- A successful pop's types: the popped values have EXACTLY the
    requested types, and the split accounts for the whole stack. -/
theorem popTys_typed : ∀ (pops : List ValType) (l args rest : List Val),
    popTys pops l = some (args, rest) →
    stackTys args = pops ∧ stackTys l = stackTys args ++ stackTys rest := by
  intro pops
  induction pops with
  | nil =>
      intro l args rest h
      rw [popTys, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      intro l args rest h
      cases l with
      | nil => simp [popTys] at h
      | cons v vs =>
        simp only [popTys] at h
        split at h
        · next ht =>
            cases hp : popTys ts vs with
            | none => simp [hp] at h
            | some p =>
                obtain ⟨a2, r2⟩ := p
                obtain ⟨h1, h2⟩ := ih vs a2 r2 hp
                rw [hp, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨h3, h4⟩ := h
                subst h3
                subst h4
                exact ⟨by simp [stackTys, ht, h1], by simp [stackTys, ht, h2]⟩
        · simp at h

/-- A well-typed stack provides the pops: the pop succeeds with the
    row's types and the demanded tail. (The type-safety theorem's
    executor-side bridge: the validator's `pop ++ ts` shape is exactly
    what `popTys` consumes.) -/
theorem popTys_of_stackTys : ∀ (pops : List ValType) (l : List Val) (ts : List ValType),
    stackTys l = pops ++ ts →
    ∃ args rest, popTys pops l = some (args, rest) ∧ stackTys args = pops ∧ stackTys rest = ts := by
  intro pops
  induction pops with
  | nil =>
      intro l ts h
      rw [List.nil_append] at h
      exact ⟨[], l, rfl, rfl, h⟩
  | cons p ps ih =>
      intro l ts h
      cases l with
      | nil => simp [stackTys] at h
      | cons v vs =>
        have h2 : tyOf v :: stackTys vs = p :: (ps ++ ts) := h
        injection h2 with hty hvs
        obtain ⟨args, rest, hp, ha, hr⟩ := ih vs ts hvs
        by_cases hcond : tyOf v = p
        · rw [popTys, if_pos hcond, hp]
          exact ⟨v :: args, rest, rfl, by simp [stackTys, ha, hty], hr⟩
        · rw [popTys, if_neg hcond]
          exact absurd hty hcond

/-- The memory byte-width of each mem op (the number the bounds check
    couples — the row's sig fixes it). -/
def memBytes : MemOp → Nat
  | .i32load8u | .i32store8 => 1
  | .i32load | .i32store => 4
  | .i64load | .i64store | .i64store8 => 8

/-- Read `n` bytes little-endian from the memory (the loads' fold). -/
def readLE : Nat → Nat → (Nat → UInt8) → Nat
  | 0, _, _ => 0
  | n + 1, addr, m => (m addr).toNat + 256 * readLE n (addr + 1) m

/-- Write `n` bytes little-endian into the memory (the stores' fold):
    a TOTAL memory update — the bounds check is the CALLER's guard
    (`step`'s `if`), so an out-of-bounds write is never constructed. -/
def writeLE : Nat → Nat → Nat → (Nat → UInt8) → (Nat → UInt8)
  | 0, _, _, m => m
  | n + 1, v, addr, m =>
      fun i => if i = addr then (v % 256).toUInt8
               else writeLE n (v / 256) (addr + 1) m i

/-! ## The op arithmetic (the closed 19-op universe, explicit arms) -/

/-- ONE op's value semantics, keyed on the closed `Op` universe with
    EXPLICIT arms per ctor (R7: no wildcard over `Op` — a new ctor
    breaks the build until its arm exists). Arguments are in POP order
    (the first-popped value FIRST = the stack's top); the operand-shape
    and the pushed type are the ONE op table's row (`opPop`/`opPush`)
    — the row's `sem` note is this function's prose face. The `none`
    arms are the type-mismatch fallback (a malformed argument list —
    `Trap.typeErr` at the step; UNREPRESENTABLE post-validation). -/
def semOp : Op → List Val → Option Val
  | .i64add, [.i64 a, .i64 b] => some (.i64 (b + a))
  | .i64add, _ => none
  | .i64sub, [.i64 a, .i64 b] => some (.i64 (b - a))
  | .i64sub, _ => none
  | .i64mul, [.i64 a, .i64 b] => some (.i64 (b * a))
  | .i64mul, _ => none
  | .i64ltu, [.i64 a, .i64 b] => some (.i32 (if b < a then 1 else 0))
  | .i64ltu, _ => none
  | .i64leu, [.i64 a, .i64 b] => some (.i32 (if b ≤ a then 1 else 0))
  | .i64leu, _ => none
  | .i64eq, [.i64 a, .i64 b] => some (.i32 (if a == b then 1 else 0))
  | .i64eq, _ => none
  | .i32add, [.i32 a, .i32 b] => some (.i32 (b + a))
  | .i32add, _ => none
  | .i32sub, [.i32 a, .i32 b] => some (.i32 (b - a))
  | .i32sub, _ => none
  | .i32mul, [.i32 a, .i32 b] => some (.i32 (b * a))
  | .i32mul, _ => none
  | .i32and, [.i32 a, .i32 b] => some (.i32 (b &&& a))
  | .i32and, _ => none
  | .i32xor, [.i32 a, .i32 b] => some (.i32 (b ^^^ a))
  | .i32xor, _ => none
  | .i32shru, [.i32 a, .i32 b] => some (.i32 (UInt32.shiftRight b (a % 32)))
  | .i32shru, _ => none
  | .i64shru, [.i64 a, .i64 b] => some (.i64 (UInt64.shiftRight b (a % 64)))
  | .i64shru, _ => none
  | .i32eqz, [.i32 a] => some (.i32 (if a == 0 then 1 else 0))
  | .i32eqz, _ => none
  | .i32eq, [.i32 a, .i32 b] => some (.i32 (if a == b then 1 else 0))
  | .i32eq, _ => none
  | .i32ltu, [.i32 a, .i32 b] => some (.i32 (if b < a then 1 else 0))
  | .i32ltu, _ => none
  | .i32gtu, [.i32 a, .i32 b] => some (.i32 (if b > a then 1 else 0))
  | .i32gtu, _ => none
  | .i32wrapi64, [.i64 a] => some (.i32 a.toUInt32)
  | .i32wrapi64, _ => none
  | .i64extendi32u, [.i32 a] => some (.i64 a.toUInt64)
  | .i64extendi32u, _ => none

/-! ## step — the flat small-step semantics -/

/-- One FLAT instruction, one state transition. The structural forms
    (`block`/`loop`/`if_`) are NOT stepped here — `execList` dispatches
    them (the `.structural` arms keep `step` total, legacy's ledger).
    `call` is likewise the execList layer's (it needs the module's
    function table — `step`'s arm is the totality arm). `ret` IS flat:
    it raises the branch-to-outermost signal (`.branch none`) — the
    frames pass it, the call boundary and the driver consume it.

    The operand shapes ride the ONE op table: `popTys (opPop o)` /
    `popTys (memPop m)` pop EXACTLY the row's pops (types checked
    against the row); `semOp` computes; the row's push is what lands.
    The memory ops carry the bounds check IN the executor: an access
    whose effective-address range `[ea, ea + memBytes)` exceeds
    `memSize` answers `.trap .memOOB` — a runtime trap, NEVER a write
    (the bounded-memory honesty; `step_store_inBounds` pins it).

    The fuel discipline does NOT enter here: `step` never answers
    `.outOfFuel` — the budget is `execList`'s alone. -/
def step : State → Instr → Outcome
  | s, .i32const n => .ok { s with stack := .i32 n.toUInt32 :: s.stack }
  | s, .i64const n => .ok { s with stack := .i64 n.toUInt64 :: s.stack }
  | s, .localget n => .ok { s with stack := s.locals n :: s.stack }
  | s, .localset n =>
      match s.stack with
      | v :: rest =>
          .ok { s with locals := fun m => if m = n then v else s.locals m
                      , stack := rest }
      | [] => .trap .typeErr
  | s, .localtee n =>
      match s.stack with
      | v :: _ =>
          .ok { s with locals := fun m => if m = n then v else s.locals m }
      | [] => .trap .typeErr
  | _, .call _ => .unmodeled
  | _, .callindirect _ => .unmodeled
  | s, .mem op offset _ =>
      match op, popTys (memPop op) s.stack with
      | .i32load8u, some ([.i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 1 ≤ s.memSize
          then .ok { s with stack := .i32 (s.mem ea).toUInt32 :: rest }
          else .trap .memOOB
      | .i32load, some ([.i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 4 ≤ s.memSize
          then .ok { s with stack := .i32 (readLE 4 ea s.mem).toUInt32 :: rest }
          else .trap .memOOB
      | .i64load, some ([.i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 8 ≤ s.memSize
          then .ok { s with stack := .i64 (readLE 8 ea s.mem).toUInt64 :: rest }
          else .trap .memOOB
      | .i32store, some ([.i32 v, .i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 4 ≤ s.memSize
          then .ok { s with mem := writeLE 4 v.toNat ea s.mem, stack := rest }
          else .trap .memOOB
      | .i64store, some ([.i64 v, .i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 8 ≤ s.memSize
          then .ok { s with mem := writeLE 8 v.toNat ea s.mem, stack := rest }
          else .trap .memOOB
      | .i32store8, some ([.i32 v, .i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 1 ≤ s.memSize
          then .ok { s with mem := writeLE 1 v.toNat ea s.mem, stack := rest }
          else .trap .memOOB
      | .i64store8, some ([.i64 v, .i32 a], rest) =>
          let ea := a.toNat + offset
          if ea + 1 ≤ s.memSize
          then .ok { s with mem := writeLE 1 v.toNat ea s.mem, stack := rest }
          else .trap .memOOB
      | _, none => .trap .typeErr
      | _, some _ => .trap .typeErr
  | s, .op o =>
      match popTys (opPop o) s.stack with
      | some (args, rest) =>
          match semOp o args with
          | some v => .ok { s with stack := v :: rest }
          | none => .trap .typeErr
      | none => .trap .typeErr
  | s, .br d => .branch (some d) s
  | s, .brif d =>
      match s.stack with
      | .i32 b :: rest =>
          if b != 0 then .branch (some d) { s with stack := rest }
          else .ok { s with stack := rest }
      | _ => .trap .typeErr
  | _, .block _ => .structural
  | _, .loop _ => .structural
  | _, .if_ _ _ => .structural
  | s, .ret => .branch none s
  | s, .drop =>
      match s.stack with
      | _ :: rest => .ok { s with stack := rest }
      | [] => .trap .typeErr
  | s, .select =>
      match s.stack with
      | .i32 b :: v1 :: v2 :: rest =>
          if b != 0 then .ok { s with stack := v1 :: rest }
          else .ok { s with stack := v2 :: rest }
      | _ => .trap .typeErr
  | _, .unreach => .trap .unreach

/-! ## execList — the structured execution (the frame machine) -/

/-- The machine-default value for a declared local. The closed `Val`
    universe is integer-only, so a float/reference local is OUTSIDE the
    executed fragment: `none` refuses it at the driver (`.unmodeled` —
    the honest ledger), never a fabricated value. -/
def valDefault? : ValType → Option Val
  | .i32 => some (.i32 0)
  | .i64 => some (.i64 0)
  | _ => none

/-- The declared locals' defaults (all-or-nothing). -/
def localsDefault? : List ValType → Option (List Val)
  | [] => some []
  | t :: ts =>
      match valDefault? t with
      | none => none
      | some v => (localsDefault? ts).map (v :: ·)

/-- The call's JOIN: the callee's final state (its stack carries the
    results — `.ok` completion or the `.branch none` return signal)
    resumes the caller — the caller's LOCALS (frame separation: the
    callee's local writes never persist), the results pushed over the
    caller's retained stack, the SHARED memory (the callee's stores
    persist — one memory per module instance). -/
def callJoin (caller : State) (rest : List Val) (callee : State) : State :=
  { callee with locals := caller.locals, stack := callee.stack ++ rest }

/-- Run a body list of module `m`. Every flat step and every frame
    entry consumes one fuel unit; a loop RESTART consumes one via
    re-entry at the same instruction (the only backward edge — the
    fuel bounds the run).

    The branch discipline: `step`'s `.branch d s` signals pass through
    the flat arms unchanged; each frame case absorbs `.branch (some 0)`
    (restore the frame's ENTRY stack, take the branch-point state's
    locals), decrements `.branch (some (n+1))` to `.branch (some n)`
    for the parent frame, and PASSES `.branch none` — the return signal
    (`ret`) ignores the frame depth. Explicit arms everywhere — no
    wildcard over `Outcome`.

    THE CALL DISCIPLINE (the calls layer, legacy v1's fuel-shared big
    step over the module's function table): the callee's args are
    popped top-first against ITS resolved type's `params.reverse` (the
    validator's own `call` row — the executor rides it), bound
    `param i → local i` over the defaults, and the callee's body runs
    as a sub-exec at THIS budget (the call consumes the caller's unit;
    each nesting level descends strictly — a divergent recursion
    exhausts the budget and answers the honest `.outOfFuel`). The
    callee's return — `.ok` or the `.branch none` signal — joins via
    `callJoin`; a `br` escaping the callee's frames (the validator's
    documented depth gap) answers `.unmodeled` — branches do not cross
    calls, and the escape signal names no return convention.

    THE DETERMINISM, named where it lives (01-core §3): `execList` is a
    plain FUNCTION — one module, one state, one list, one budget ⇒ one
    outcome. There is no choice point, so there is nothing to prove:
    the determinism claim is this definition's type, not a theorem. -/
def execList (m : Module) : Nat → State → List Instr → Outcome
  | 0, _, _ => .outOfFuel
  | _ + 1, s, [] => .ok s
  | fuel + 1, s, .block body :: is =>
      match execList m fuel s body with
      | .ok s' => execList m fuel s' is
      | .branch (some 0) s2 =>
          -- the frame absorbs the branch: the branch-point LOCALS ride
          -- in, the frame-ENTRY stack is restored — and the MEMORY
          -- stays the branch-point's (memory is GLOBAL in wasm
          -- semantics: a frame's stores persist across its branches;
          -- the boxed-object lanes' stores ride exactly this path)
          execList m fuel
            { s with locals := s2.locals, stack := s.stack, mem := s2.mem } is
      | .branch (some (n + 1)) s2 => .branch (some n) s2
      | .branch none s2 => .branch none s2
      | .trap r => .trap r
      | .structural => .structural
      | .unmodeled => .unmodeled
      | .outOfFuel => .outOfFuel
  | fuel + 1, s, .loop body :: is =>
      match execList m fuel s body with
      | .ok s' => execList m fuel s' is
      | .branch (some 0) s2 =>
          -- the restart: re-run the loop instruction itself from the
          -- frame-ENTRY stack (the branch-point locals; the memory as
          -- above — global, the branch-point's)
          execList m fuel
            { s with locals := s2.locals, stack := s.stack, mem := s2.mem }
            (.loop body :: is)
      | .branch (some (n + 1)) s2 => .branch (some n) s2
      | .branch none s2 => .branch none s2
      | .trap r => .trap r
      | .structural => .structural
      | .unmodeled => .unmodeled
      | .outOfFuel => .outOfFuel
  | fuel + 1, s, .if_ t e :: is =>
      match s.stack with
      | .i32 b :: rest =>
          let chosen := if b != 0 then t else e
          match execList m fuel { s with stack := rest } chosen with
          | .ok s' => execList m fuel s' is
          | .branch (some 0) s2 =>
              execList m fuel
                { s with locals := s2.locals, stack := rest, mem := s2.mem } is
          | .branch (some (n + 1)) s2 => .branch (some n) s2
          | .branch none s2 => .branch none s2
          | .trap r => .trap r
          | .structural => .structural
          | .unmodeled => .unmodeled
          | .outOfFuel => .outOfFuel
      | _ => .trap .typeErr
  | fuel + 1, s, .call fn :: is =>
      -- the calls layer: the args popped against the callee's resolved
      -- type (the validator's `call` row), the callee run as a
      -- fuel-shared sub-exec, the return joined into the caller
      match m.funcs[fn]? with
      | none => .unmodeled
      | some f =>
          match m.typeAt f.tyIdx with
          | none => .unmodeled
          | some ft =>
              match popTys ft.params.reverse s.stack with
              | some (bound, rest) =>
                  match localsDefault? f.locals with
                  | none => .unmodeled
                  | some defaults =>
                      match execList m fuel
                          { locals := fun n =>
                              (bound.reverse ++ defaults).getD n (.i32 0)
                          , stack := []
                          , mem := s.mem
                          , memSize := s.memSize } f.body with
                      | .ok s' =>
                          execList m fuel (callJoin s rest s') is
                      | .branch none s' =>
                          execList m fuel (callJoin s rest s') is
                      | .branch (some _) _ => .unmodeled
                      | .trap r => .trap r
                      | .structural => .structural
                      | .unmodeled => .unmodeled
                      | .outOfFuel => .outOfFuel
              | none => .trap .typeErr
  | fuel + 1, s, .callindirect ty :: is =>
      -- THE INDIRECT-CALL LAYER (the table discipline): the callee's
      -- index is RUNTIME data — the i32 on top (the first-class
      -- application's face: the closure object's fnIdx @8) — resolved
      -- through the module's ONE table (`Module.tableAt`); the type
      -- check pins the entry's resolved type to the declared one (a
      -- mismatch TRAPS `indirectSig`, an out-of-bounds index TRAPS
      -- `tabOOB` — never a wrong call); the args pop against the
      -- DECLARED type (the validator's `callindirect` row), the callee
      -- runs as the direct call's fuel-shared sub-exec.
      match m.typeAt ty with
      | none => .unmodeled
      | some ft =>
          match s.stack with
          | .i32 ix :: rest =>
              match m.tableAt ix.toNat with
              | none => .trap .tabOOB
              | some fn =>
                  match m.funcs[fn]? with
                  | none => .unmodeled
                  | some f =>
                      match m.typeAt f.tyIdx with
                      | none => .unmodeled
                      | some ft' =>
                          if ft' = ft then
                            match popTys ft.params.reverse rest with
                            | some (bound, rest2) =>
                                match localsDefault? f.locals with
                                | none => .unmodeled
                                | some defaults =>
                                    match execList m fuel
                                        { locals := fun n =>
                                            (bound.reverse ++ defaults).getD n (.i32 0)
                                        , stack := []
                                        , mem := s.mem
                                        , memSize := s.memSize } f.body with
                                    | .ok s' =>
                                        execList m fuel (callJoin s rest2 s') is
                                    | .branch none s' =>
                                        execList m fuel (callJoin s rest2 s') is
                                    | .branch (some _) _ => .unmodeled
                                    | .trap r => .trap r
                                    | .structural => .structural
                                    | .unmodeled => .unmodeled
                                    | .outOfFuel => .outOfFuel
                            | none => .trap .typeErr
                          else .trap .indirectSig
          | _ => .trap .typeErr
  | fuel + 1, s, i :: is =>
      match step s i with
      | .ok s' => execList m fuel s' is
      | .branch d s2 => .branch d s2
      | .trap r => .trap r
      | .structural => .structural
      | .unmodeled => .unmodeled
      | .outOfFuel => .outOfFuel

/-! ## The module driver -/

/-- The zero-initialized linear memory. -/
def zeroMem : Nat → UInt8 := fun _ => 0

/-- One wasm page, in bytes (the memory section's granularity). -/
def wasmPage : Nat := 65536

/-- The driver's completion face: the body's `.branch none` return
    signal is a normal completion (the returned stack IS the results,
    per the validator's `ret` rule); everything else passes through. -/
def finishRun : Outcome → Outcome
  | .ok s' => .ok s'
  | .branch none s' => .ok s'
  | .branch (some d) s' => .branch (some d) s'
  | .trap r => .trap r
  | .structural => .structural
  | .unmodeled => .unmodeled
  | .outOfFuel => .outOfFuel

theorem finishRun_trap (o : Outcome) (t : Trap) :
    finishRun o = .trap t ↔ o = .trap t := by
  cases o with
  | ok s => simp [finishRun]
  | branch d s => cases d <;> simp [finishRun]
  | trap r => simp [finishRun]
  | structural => simp [finishRun]
  | unmodeled => simp [finishRun]
  | outOfFuel => simp [finishRun]

theorem finishRun_ok (o : Outcome) (s' : State) :
    finishRun o = .ok s' ↔ (o = .ok s' ∨ ∃ s2, o = .branch none s2 ∧ s2 = s') := by
  cases o with
  | ok s => simp [finishRun]
  | branch d s => cases d <;> simp [finishRun]
  | structural => simp [finishRun]
  | unmodeled => simp [finishRun]
  | outOfFuel => simp [finishRun]
  | trap r => simp [finishRun]

/-- Run function `fn` of module `m` on `args` with budget `fuel`.

    - args are type-checked against the function's params — a mismatch
      (or an arity mismatch) is `Trap.typeErr`, the same shape
      violation the body's ops answer; the pop convention is the
      `call` rule's OWN (`params.reverse` — head = TOP = the last
      param), so a caller validated by `stepFlag`'s `.call` row and
      the driver agree on the stack (the module-level type-safety
      theorem's binding discipline: param i lands in local i);
    - the locals are the bound params ++ the defaults (the unbound
      READ is the validator's refusal; the map's fallback `.i32 0` is
      the legacy "every local exists" convention, unreachable for a
      validated module);
    - the memory is zero-initialized at `memMin` pages;
    - the module's functions are visible to each other: the body's
      `call`s execute through the calls layer (the callee's return —
      `.ok` or the `.branch none` signal — joins into the caller);
    - the body's own `.branch none` (a top-level `ret`) is a normal
      completion — the driver maps it to `.ok` (the returned stack IS
      the results, per the validator's `ret` rule);
    - an uncaught `.branch (some d)` here is the branch-escape signal —
      it surfaces as the `.branch` outcome, never laundered into a
      trap;
    - a call to an index the module does not resolve, and non-integer
      locals' defaults, answer `.unmodeled` (the honest fragment
      ledger — DISTINCT from trap). -/
def runFunc (m : Module) (fn : Nat) (args : List Val) (fuel : Nat) : Outcome :=
  match m.funcs[fn]? with
  | none => .unmodeled
  | some f =>
    match m.typeAt f.tyIdx with
    | none => .unmodeled
    | some _ft =>
      match popTys _ft.params.reverse args with
      | some (bound, []) =>
          match localsDefault? f.locals with
          | none => .unmodeled
          | some defaults =>
              finishRun (execList m fuel
                { locals := fun n => (bound.reverse ++ defaults).getD n (.i32 0)
                , stack := []
                , mem := zeroMem
                , memSize := m.memMin * wasmPage }
                f.body)
      | _ => .trap .typeErr

/-! ## The memory-safety theorems (the bounded-memory honesty) -/

/-- The store8 byte bridge (the low 8 bits): `UInt32.toUInt8` truncates
    by the `UInt8.ofNat` wrap (core's `UInt8.ofNat_mod_size`). -/
theorem u32_toUInt8 (v : UInt32) : v.toUInt8 = (v.toNat % 2 ^ 8).toUInt8 := by
  show UInt8.ofNat v.toNat = UInt8.ofNat (v.toNat % 2 ^ 8)
  rw [UInt8.ofNat_mod_size]

/-- THE MEMORY-SAFETY THEOREM (the bounded-memory variant, stated
    honestly — legacy `Sem.storeInBounds`'s heir): a successful
    one-byte store happened at an address strictly inside the memory,
    changed exactly ONE byte, and left the locals and the rest of the
    stack intact. Out-of-bounds = a trap, never a write — by
    construction (the bounds check is IN `step`), and this theorem
    pins it. -/
theorem step_store_inBounds (s s' : State) (v a : UInt32) (rest : List Val) (offset : Nat)
    (hstack : s.stack = .i32 v :: .i32 a :: rest)
    (h : step s (.mem .i32store8 offset none) = .ok s') :
    a.toNat + offset + 1 ≤ s.memSize
    ∧ s'.mem (a.toNat + offset) = v.toUInt8
    ∧ (∀ i : Nat, i ≠ a.toNat + offset → s'.mem i = s.mem i)
    ∧ s'.stack = rest
    ∧ s'.locals = s.locals := by
  simp only [step, hstack, memPop, memSig, memRow] at h
  simp [popTys] at h
  split at h
  · next hb =>
      rw [Outcome.ok.injEq, State.mk.injEq] at h
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := h
      refine ⟨hb, ?_, ?_, hstk.symm, hloc.symm⟩
      · rw [← hmem]
        simp only [writeLE]
        simp [u32_toUInt8]
      · intro i hi
        rw [← hmem]
        simp only [writeLE]
        by_cases hea : i = a.toNat + offset
        · exact absurd hea hi
        · rw [if_neg hea]
  · next hb =>
      simp at h

/-- The trap direction, pinned exactly: the out-of-bounds one-byte
    store TRAPS with the named trap (`.memOOB`) — it never writes
    (the converse face of `step_store_inBounds`; the check fires
    exactly there). -/
theorem step_store_oob_traps (s : State) (v a : UInt32) (rest : List Val) (offset : Nat)
    (hstack : s.stack = .i32 v :: .i32 a :: rest)
    (hoob : ¬ (a.toNat + offset + 1 ≤ s.memSize)) :
    step s (.mem .i32store8 offset none) = .trap .memOOB := by
  simp [step, hstack, memPop, memSig, memRow, popTys, if_neg hoob]

/-! ## The type-safety discipline (the flat slice) -/

/-- THE OP-ARITHMETIC SPEC (the closed-universe law, proved in ONE
    args-case scaffold): args with EXACTLY the row's pop types always
    compute, and the computed value has EXACTLY the row's push type.
    (The ONE op table is the law's content: pop and push are the row's
    projections; the per-op arms of `semOp` are the machine face.)
    `semOp_typed`/`semOp_exists` are its two projections — the scaffold
    is proved once, not twice. -/
theorem semOp_spec (o : Op) (args : List Val) (hty : stackTys args = opPop o) :
    ∃ v, semOp o args = some v ∧ opPush o = [tyOf v] := by
  cases args with
  | nil => cases o <;> simp [stackTys, opPop, opSig, opRow] at hty
  | cons v1 vs =>
    cases vs with
    | nil =>
      cases v1 <;> cases o <;>
        (simp [semOp, stackTys, opPop, opPush, opSig, opRow] at hty ⊢
         try exact absurd hty (by simp)) <;>
        exact ⟨_, rfl, rfl⟩
    | cons v2 vs2 =>
      cases vs2 with
      | nil =>
        cases v1 <;> cases v2 <;> cases o <;>
          (simp [semOp, stackTys, opPop, opPush, opSig, opRow] at hty ⊢
           try exact absurd hty (by simp)) <;>
          exact ⟨_, rfl, rfl⟩
      | cons v3 vs3 =>
        cases o <;> simp [stackTys, opPop, opSig, opRow] at hty

/-- The op arithmetic's typing law (the spec's typing projection):
    when the popped arguments have EXACTLY the row's pop types, the
    computed value has EXACTLY the row's push type. This is the
    per-op-step preservation slice. -/
theorem semOp_typed (o : Op) (args : List Val) (v : Val)
    (hty : stackTys args = opPop o)
    (h : semOp o args = some v) :
    opPush o = [tyOf v] := by
  obtain ⟨v0, h0, hp⟩ := semOp_spec o args hty
  rw [h, Option.some.injEq] at h0
  subst h0
  exact hp

/-- The op STEP's preservation (the pipeline lemma): an op step that
    computes at all, computes on the row's pop shape to the row's push
    shape, locals untouched. -/
theorem step_op_preserves (o : Op) (ts : List ValType) (s s' : State)
    (hstep : step s (.op o) = .ok s')
    (hstack : stackTys s.stack = opPop o ++ ts) :
    stackTys s'.stack = opPush o ++ ts ∧ (∀ n, s'.locals n = s.locals n) := by
  obtain ⟨args, rest, hpop, hargs, hrest⟩ :=
    popTys_of_stackTys (opPop o) s.stack ts hstack
  simp only [step, hpop] at hstep
  split at hstep
  · next v0 hsem =>
      have ht := semOp_typed o args v0 hargs hsem
      rw [Outcome.ok.injEq, State.mk.injEq] at hstep
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hstep
      refine ⟨?_, fun n => by rw [hloc]⟩
      rw [← hstk]
      simp [stackTys, ht, hrest]
  · next => simp at hstep

/-- A one-value static view forces a singleton `i32` stack (the mem
    loads' arg inversion — the family's scaffold is the row's pop
    shape, decided once per shape). -/
theorem args_i32_inv (args : List Val) (h : stackTys args = [.i32]) :
    ∃ a, args = [.i32 a] := by
  cases args with
  | nil => simp [stackTys] at h
  | cons v vs =>
      cases v <;> cases vs <;> simp [stackTys] at h
      exact ⟨_, rfl⟩

/-- A two-value static view forces an `[.i32, .i32]` stack (the
    i32-stores' arg inversion). -/
theorem args_i32i32_inv (args : List Val) (h : stackTys args = [.i32, .i32]) :
    ∃ v a, args = [.i32 v, .i32 a] := by
  cases args with
  | nil => simp [stackTys] at h
  | cons v vs =>
      cases vs with
      | nil => cases v <;> simp [stackTys] at h
      | cons w ws =>
          cases ws with
          | nil =>
              cases v <;> cases w <;> simp [stackTys] at h
              exact ⟨_, _, rfl⟩
          | cons _ _ => simp [stackTys] at h

/-- A two-value static view forces an `[.i64, .i32]` stack (the
    i64-stores' arg inversion). -/
theorem args_i64i32_inv (args : List Val) (h : stackTys args = [.i64, .i32]) :
    ∃ v a, args = [.i64 v, .i32 a] := by
  cases args with
  | nil => simp [stackTys] at h
  | cons v vs =>
      cases vs with
      | nil => cases v <;> simp [stackTys] at h
      | cons w ws =>
          cases ws with
          | nil =>
              cases v <;> cases w <;> simp [stackTys] at h
              exact ⟨_, _, rfl⟩
          | cons _ _ => simp [stackTys] at h

/-- THE ONE MEM-OP SPEC (the mem family's single 7-ctor case
    analysis): on a typed stack the mem step answers trap-or-compute
    (the bounded-memory honesty), and any computing answer pushes
    EXACTLY the row's push types with the locals untouched. The
    per-ctor content is the width constant and the pushed value;
    `step_mem_preserves`/`step_mem_outcome` are its two projections —
    the family's case scaffold is proved ONCE, not four times. -/
theorem step_mem_spec (m : MemOp) (off : Nat) (al : Option Nat) (ts : List ValType)
    (s : State) (hstack : stackTys s.stack = memPop m ++ ts) :
    (step s (.mem m off al) = .trap .memOOB ∨ ∃ s', step s (.mem m off al) = .ok s')
    ∧ (∀ s', step s (.mem m off al) = .ok s' →
        stackTys s'.stack = memPush m ++ ts ∧ (∀ n, s'.locals n = s.locals n)) := by
  obtain ⟨args, rest, hpop, hargs, hrest⟩ :=
    popTys_of_stackTys (memPop m) s.stack ts hstack
  cases m
  case i32load8u =>
    obtain ⟨a, rfl⟩ := args_i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 1 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [stackTys, hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i32load =>
    obtain ⟨a, rfl⟩ := args_i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 4 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [stackTys, hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i64load =>
    obtain ⟨a, rfl⟩ := args_i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 8 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [stackTys, hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i32store =>
    obtain ⟨v, a, rfl⟩ := args_i32i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 4 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i64store =>
    obtain ⟨v, a, rfl⟩ := args_i64i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 8 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i32store8 =>
    obtain ⟨v, a, rfl⟩ := args_i32i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 1 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx
  case i64store8 =>
    obtain ⟨v, a, rfl⟩ := args_i64i32_inv args hargs
    simp only [step, hpop]
    by_cases h : a.toNat + off + 1 ≤ s.memSize
    · refine ⟨Or.inr ⟨_, if_pos h⟩, ?_⟩
      intro s' hx
      rw [if_pos h] at hx
      rw [Outcome.ok.injEq, State.mk.injEq] at hx
      obtain ⟨hloc, hstk, hmem, hmsz⟩ := hx
      exact ⟨by rw [← hstk]; simp [hrest, memPush, memSig, memRow],
        fun n => by rw [hloc]⟩
    · refine ⟨Or.inl (if_neg h), ?_⟩
      intro s' hx
      rw [if_neg h] at hx
      simp at hx

/-- The mem STEP's preservation (the pipeline lemma): a mem step that
    computes at all, computes on the row's pop shape to the row's push
    shape (the bounds check only chooses trap vs compute — the
    bounded-memory honesty does not disturb the types), locals
    untouched. `step_mem_spec`'s preservation projection. -/
theorem step_mem_preserves (m : MemOp) (off : Nat) (ts : List ValType) (s s' : State)
    (hstep : step s (.mem m off none) = .ok s')
    (hstack : stackTys s.stack = memPop m ++ ts) :
    stackTys s'.stack = memPush m ++ ts ∧ (∀ n, s'.locals n = s.locals n) :=
  (step_mem_spec m off none ts s hstack).2 s' hstep

/-- The structure-update reductions (the preservation proofs' bridge:
    `with`-updates are `State.mk` applications — definitional). -/
theorem stateWith (s : State) (stack : List Val) :
    ({ s with stack := stack } : State) = State.mk s.locals stack s.mem s.memSize := rfl

theorem stateWithL (s : State) (f : Nat → Val) :
    ({ s with locals := f } : State) = State.mk f s.stack s.mem s.memSize := rfl

theorem stateWith2 (s : State) (f : Nat → Val) (stack : List Val) :
    ({ s with locals := f, stack := stack } : State)
      = State.mk f stack s.mem s.memSize := rfl

/-- The stack's cons inversion (the shape the stack-matching step arms
    need — `cases` on a projection term is not available). -/
theorem stackTys_cons_inv (l : List Val) (t : ValType) (ts : List ValType)
    (h : stackTys l = t :: ts) : ∃ v rest, l = v :: rest := by
  cases l with
  | nil => simp [stackTys] at h
  | cons v rest => exact ⟨v, rest, rfl⟩

/-- `drop`'s checker shape (the third stack-matching arm; the rw-form
    the flat case rides). -/
theorem stepFlag_drop_shape (c : Ctx) (b mid : List ValType)
    (h : stepFlag c Instr.drop b = .ok (false, mid)) :
    ∃ t ts, b = t :: ts ∧ mid = ts := by
      rw [stepFlag.eq_def] at h
      cases b with
      | nil => simp at h
      | cons t ts =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨t, ts, rfl, h.2.symm⟩

/-- THE PER-OP-STEP PRESERVATION LEMMA (the type-safety discipline's
    flat slice, riding the validator's proved bridge): a flat step that
    computes AT ALL — of ANY instruction — takes a stack the checker
    types `b → mid` to a stack typed `mid`, with the locals'
    well-typedness preserved. The op/mem shapes are the ONE op table's
    rows (the inversions of Validate's `stepFlag` + the pipeline
    lemmas above). `call`/the frame forms never compute here (`step`
    answers `.unmodeled`/`.structural` — the call layer is
    `execList`'s), and `ret` computes to the `.branch none` return
    signal (never `.ok`), so their `.ok`-cases are vacuous — this
    lemma is `exec_typed`'s per-step engine (the body-level frame
    induction + the module-level `runFunc_safe` are landed below it). -/
theorem step_preserves (s s' : State) (i : Instr) (b mid : List ValType)
    (lty : Nat → Option ValType) (tny : Nat → Option FuncType)
    (hstep : step s i = .ok s')
    (hstack : stackTys s.stack = b)
    (hloc : ∀ n t, lty n = some t → tyOf (s.locals n) = t)
    (hchk : stepFlag (Ctx.mk lty (fun _ => none) tny []) i b = .ok (false, mid)) :
    stackTys s'.stack = mid ∧ (∀ n t, lty n = some t → tyOf (s'.locals n) = t) := by
  cases i with
  | i32const n =>
      simp only [step, Outcome.ok.injEq] at hstep
      subst hstep
      simp only [stepFlag, Except.ok.injEq, Prod.mk.injEq, true_and] at hchk
      subst hchk
      exact ⟨by simp [stackTys, hstack], fun n' t' h => hloc n' t' h⟩
  | i64const n =>
      simp only [step, Outcome.ok.injEq] at hstep
      subst hstep
      simp only [stepFlag, Except.ok.injEq, Prod.mk.injEq, true_and] at hchk
      subst hchk
      exact ⟨by simp [stackTys, hstack], fun n' t' h => hloc n' t' h⟩
  | localget n =>
      simp only [step, Outcome.ok.injEq] at hstep
      subst hstep
      simp only [stepFlag] at hchk
      cases hl : lty n with
      | none => rw [hl] at hchk; simp at hchk
      | some t =>
          rw [hl] at hchk
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hchk
          subst hchk
          exact ⟨by simp [stackTys, hloc n t hl, hstack], fun n' t' h => hloc n' t' h⟩
  | localset n =>
      obtain ⟨ts0, t, hb, hln, hmid, -⟩ := stepFlag_localset_shape _ n b _ _ hchk
      subst hb
      obtain ⟨v, rest, hstack2⟩ := stackTys_cons_inv s.stack t ts0 hstack
      rw [hstack2] at hstack
      simp only [step, hstack2, Outcome.ok.injEq] at hstep
      subst hstep
      have hv : tyOf v = t ∧ stackTys rest = ts0 := by
        have h2 : tyOf v :: stackTys rest = t :: ts0 := hstack
        injection h2 with ha hres
        exact ⟨ha, hres⟩
      refine ⟨by simp [hv.2, hmid], ?_⟩
      intro n' u hu
      show tyOf (if n' = n then v else s.locals n') = u
      by_cases hn : n' = n
      · rw [if_pos hn, hv.1]
        rw [hn] at hu
        injection hln.symm.trans hu with htu
      · rw [if_neg hn]
        exact hloc n' u hu
  | localtee n =>
      obtain ⟨ts0, t, hb, hln, hmid, -⟩ := stepFlag_localtee_shape _ n b _ _ hchk
      subst hb
      obtain ⟨v, rest, hstack2⟩ := stackTys_cons_inv s.stack t ts0 hstack
      rw [hstack2] at hstack
      simp only [step, hstack2, Outcome.ok.injEq] at hstep
      subst hstep
      have hv : tyOf v = t ∧ stackTys rest = ts0 := by
        have h2 : tyOf v :: stackTys rest = t :: ts0 := hstack
        injection h2 with ha hres
        exact ⟨ha, hres⟩
      refine ⟨by simp [stackTys, hv.1, hv.2, hmid], ?_⟩
      intro n' u hu
      show tyOf (if n' = n then v else s.locals n') = u
      by_cases hn : n' = n
      · rw [if_pos hn, hv.1]
        rw [hn] at hu
        injection hln.symm.trans hu with htu
      · rw [if_neg hn]
        exact hloc n' u hu
  | call _ => simp [step] at hstep
  | callindirect _ => simp [step] at hstep
  | mem m off al =>
      obtain ⟨ts', hs, hmid⟩ :=
        stepFlag_popPush_shape _ _ (memPop m) (memPush m) b mid (by simp only [stepFlag]) hchk
      have h2 := step_mem_preserves m off ts' s s' hstep (by rw [hstack, hs])
      obtain ⟨hst, hloc2⟩ := h2
      exact ⟨by rw [hst, hmid], fun n' t' h => by
        rw [hloc2 n']
        exact hloc n' t' h⟩
  | op o =>
      obtain ⟨ts', hs, hmid⟩ :=
        stepFlag_popPush_shape _ _ (opPop o) (opPush o) b mid (by simp only [stepFlag]) hchk
      have h2 := step_op_preserves o ts' s s' hstep (by rw [hstack, hs])
      obtain ⟨hst, hloc2⟩ := h2
      exact ⟨by rw [hst, hmid], fun n' t' h => by
        rw [hloc2 n']
        exact hloc n' t' h⟩
  | br d => simp [step] at hstep
  | brif d =>
      obtain ⟨-, ts', hv, hmid⟩ := stepFlag_brif_shape _ _ _ _ _ hchk
      subst hv
      obtain ⟨c, rest, hstack2⟩ := stackTys_cons_inv s.stack .i32 ts' hstack
      rw [hstack2] at hstack
      have hcty : tyOf c = .i32 ∧ stackTys rest = ts' := by
        have h2 : tyOf c :: stackTys rest = ValType.i32 :: ts' := hstack
        injection h2 with ha hres
        exact ⟨ha, hres⟩
      cases c with
      | i32 x =>
          simp only [step, hstack2] at hstep
          split at hstep
          · simp at hstep
          · rw [Outcome.ok.injEq] at hstep
            subst hstep
            exact ⟨by simp [hcty.2, hmid], fun n' t' h => hloc n' t' h⟩
      | i64 =>
          exfalso
          simp [tyOf] at hcty
  | block _ => simp [step] at hstep
  | loop _ => simp [step] at hstep
  | if_ _ _ => simp [step] at hstep
  | ret => simp [step] at hstep
  | drop =>
      obtain ⟨t, ts, hb, hmid⟩ := stepFlag_drop_shape _ _ _ hchk
      subst hb
      obtain ⟨v, rest, hstack2⟩ := stackTys_cons_inv s.stack t ts hstack
      rw [hstack2] at hstack
      simp only [step, hstack2, Outcome.ok.injEq] at hstep
      subst hstep
      have hv : tyOf v = t ∧ stackTys rest = ts := by
        have h3 : tyOf v :: stackTys rest = t :: ts := hstack
        injection h3 with ha hres
        exact ⟨ha, hres⟩
      exact ⟨by simp [hv.2, hmid], fun n' t' h => hloc n' t' h⟩
  | select =>
      obtain ⟨-, ts', t, hv, hmid, htor⟩ := stepFlag_select_shape _ _ _ _ hchk
      subst hv
      obtain ⟨c, rest, hstack2⟩ := stackTys_cons_inv s.stack .i32 (t :: t :: ts') hstack
      rw [hstack2] at hstack
      have hcty : tyOf c = .i32 ∧ stackTys rest = t :: t :: ts' := by
        have h2 : tyOf c :: stackTys rest = ValType.i32 :: (t :: t :: ts') := hstack
        injection h2 with ha hres
        exact ⟨ha, hres⟩
      obtain ⟨v1, rest1, hrest1⟩ := stackTys_cons_inv rest t (t :: ts') hcty.2
      have hcty2 : stackTys rest = t :: t :: ts' := hcty.2
      rw [hrest1] at hcty2
      have hv1 : tyOf v1 = t ∧ stackTys rest1 = t :: ts' := by
        have h3 : tyOf v1 :: stackTys rest1 = t :: t :: ts' := hcty2
        injection h3 with h4 h5
        exact ⟨h4, h5⟩
      obtain ⟨v2, rest2, hrest22⟩ := stackTys_cons_inv rest1 t ts' hv1.2
      have hcty3 : stackTys rest1 = t :: ts' := hv1.2
      rw [hrest22] at hcty3
      have hv2 : tyOf v2 = t ∧ stackTys rest2 = ts' := by
        have h3 : tyOf v2 :: stackTys rest2 = t :: ts' := hcty3
        injection h3 with h4 h5
        exact ⟨h4, h5⟩
      cases c with
      | i32 x =>
          simp only [step, hstack2, hrest1, hrest22] at hstep
          split at hstep
          · rw [Outcome.ok.injEq] at hstep
            subst hstep
            exact ⟨by simp [stackTys, hv1.1, hv2.2, hmid], fun n' t' h => hloc n' t' h⟩
          · rw [Outcome.ok.injEq] at hstep
            subst hstep
            exact ⟨by simp [stackTys, hv2.1, hv2.2, hmid], fun n' t' h => hloc n' t' h⟩
      | i64 =>
          exfalso
          simp [tyOf] at hcty
  | unreach => simp [step] at hstep

/-! ## The type-safety discipline (the frame machine) -/

/-- The static view's length law (the getD bridge's measure). -/
theorem stackTys_length (l : List Val) : (stackTys l).length = l.length := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp only [stackTys, List.length_cons, ih]

/-- `stackTys` commutes with reverse (the arg-binding bridge: the
    driver's `bound.reverse ++ defaults` reads the params in order). -/
theorem stackTys_reverse (l : List Val) :
    stackTys l.reverse = (stackTys l).reverse := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
      rw [List.reverse_cons, stackTys_append, ih]
      simp [stackTys]

/-- A getD inside the list reads the static view's element (the
    locals-map typing's atom). -/
theorem tyOf_getD (l : List Val) (d : Val) (n : Nat) (h : n < l.length) :
    tyOf (l.getD n d) = (stackTys l)[n]'(by rw [stackTys_length]; exact h) := by
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons v vs => simp [List.getD, stackTys]
  | succ n ih =>
      cases l with
      | nil => simp at h
      | cons v vs =>
          have hv : n < vs.length := by simp at h; omega
          simp only [List.getD_cons_succ, stackTys, List.getElem_cons_succ]
          exact ih vs hv

/-- The op arithmetic is TOTAL on well-typed arguments: args with
    EXACTLY the row's pop types always compute (the per-op arms cover
    every typed shape — the type-safety theorem's op face). -/
theorem semOp_exists (o : Op) (args : List Val) (hty : stackTys args = opPop o) :
    ∃ v, semOp o args = some v := by
  cases args with
  | nil => cases o <;> simp [stackTys, opPop, opSig, opRow] at hty
  | cons v1 vs =>
    cases vs with
    | nil =>
      cases v1 <;> cases o <;>
        (simp [semOp, stackTys, opPop, opSig, opRow] at hty ⊢
         try exact absurd hty (by simp)) <;>
        exact ⟨_, rfl⟩
    | cons v2 vs2 =>
      cases vs2 with
      | nil =>
        cases v1 <;> cases v2 <;> cases o <;>
          (simp [semOp, stackTys, opPop, opSig, opRow] at hty ⊢
           try exact absurd hty (by simp)) <;>
          exact ⟨_, rfl⟩
      | cons v3 vs3 =>
        cases o <;> simp [stackTys, opPop, opSig, opRow] at hty

/-- The mem STEP is total-and-honest on a typed stack: it answers
    `.ok` or the out-of-bounds trap — NEVER the type error (the
    bounds check is the only rejection, the bounded-memory honesty).
    `step_mem_spec`'s outcome projection. -/
theorem step_mem_outcome (m : MemOp) (off : Nat) (al : Option Nat) (ts : List ValType)
    (s : State) (hstack : stackTys s.stack = memPop m ++ ts) :
    step s (.mem m off al) = .trap .memOOB ∨ ∃ s', step s (.mem m off al) = .ok s' :=
  (step_mem_spec m off al ts s hstack).1

/-- The checker's stepFlag reads ONLY `lty` for the flag-false
    non-call steps (the frame induction's bridge: the core theorem
    rides the plain-lty context `step_preserves` is stated against,
    while the module driver's context carries the real `fenv`). The
    `callindirect` step reads only `tenv` — carried unchanged, so its
    transport is free. -/
theorem stepFlag_congr (lty : Nat → Option ValType)
    (fenv fenv' tenv : Nat → Option FuncType) (r r' : List ValType)
    (i : Instr) (s mid : List ValType)
    (h : stepFlag (Ctx.mk lty fenv tenv r) i s = .ok (false, mid))
    (hnc : ∀ fn, i ≠ Instr.call fn)
    (hff : FrameForm i = False) :
    stepFlag (Ctx.mk lty fenv' tenv r') i s = .ok (false, mid) := by
  cases i with
  | call fn => exact absurd rfl (hnc fn)
  | callindirect ty => simp only [stepFlag.eq_def] at h ⊢; exact h
  | ret => simp only [stepFlag.eq_def] at h; split at h <;> simp at h
  | br d => simp only [stepFlag.eq_def] at h; simp at h
  | unreach => simp only [stepFlag.eq_def] at h; simp at h
  | block b => simp [FrameForm] at hff
  | loop b => simp [FrameForm] at hff
  | if_ t e => simp [FrameForm] at hff
  | i32const n => simp only [stepFlag.eq_def] at h ⊢; exact h
  | i64const n => simp only [stepFlag.eq_def] at h ⊢; exact h
  | localget n => simp only [stepFlag.eq_def] at h ⊢; exact h
  | localset n => simp only [stepFlag.eq_def] at h ⊢; exact h
  | localtee n => simp only [stepFlag.eq_def] at h ⊢; exact h
  | mem mop offset al => simp only [stepFlag.eq_def] at h ⊢; exact h
  | op o => simp only [stepFlag.eq_def] at h ⊢; exact h
  | brif d => simp only [stepFlag.eq_def] at h ⊢; exact h
  | drop => simp only [stepFlag.eq_def] at h ⊢; exact h
  | select => simp only [stepFlag.eq_def] at h ⊢; exact h

/-- A `StepTy`-related instruction is never a frame form (the
    relation's rules are the flat rows; the frames own their `BodyTy`
    ctors). -/
theorem stepTy_frameFalse (c : Ctx) (base mid : List ValType) (i : Instr)
    (h : StepTy c base i mid) : FrameForm i = False := by
  cases h <;> rfl

/-! ### The execList equations (the induction's reduction face) -/

theorem execList_zero (m : Module) (s : State) (body : List Instr) :
    execList m 0 s body = .outOfFuel := rfl

theorem execList_nil (m : Module) (fuel : Nat) (s : State) :
    execList m (fuel + 1) s [] = .ok s := rfl

theorem execList_flat (m : Module) (fuel : Nat) (s : State) (i : Instr) (is : List Instr)
    (hff : FrameForm i = False) (hnc : ∀ fn, i ≠ Instr.call fn)
    (hci : ∀ ty, i ≠ Instr.callindirect ty) :
    execList m (fuel + 1) s (i :: is)
      = match step s i with
        | .ok s' => execList m fuel s' is
        | .branch d s2 => .branch d s2
        | .trap r => .trap r
        | .structural => .structural
        | .unmodeled => .unmodeled
        | .outOfFuel => .outOfFuel := by
  cases i with
  | i32const n => simp [execList]
  | i64const n => simp [execList]
  | localget n => simp [execList]
  | localset n => simp [execList]
  | localtee n => simp [execList]
  | call fn => exact absurd rfl (hnc fn)
  | callindirect ty => exact absurd rfl (hci ty)
  | mem mop offset al => simp [execList]
  | op o => simp [execList]
  | br d => simp [execList]
  | brif d => simp [execList]
  | block b => simp [FrameForm] at hff
  | loop b => simp [FrameForm] at hff
  | if_ t e => simp [FrameForm] at hff
  | ret => simp [execList]
  | unreach => simp [execList]
  | drop => simp [execList]
  | select => simp [execList]

/-- The call arm's equation (the calls layer's reduction face: the
    fuel-shared sub-exec + the join + the honest ledger arms). -/
theorem execList_call (m : Module) (fuel : Nat) (s : State) (fn : Nat) (is : List Instr) :
    execList m (fuel + 1) s (Instr.call fn :: is)
      = match m.funcs[fn]? with
        | none => .unmodeled
        | some f =>
            match m.typeAt f.tyIdx with
            | none => .unmodeled
            | some ft =>
                match popTys ft.params.reverse s.stack with
                | some (bound, rest) =>
                    match localsDefault? f.locals with
                    | none => .unmodeled
                    | some defaults =>
                        match execList m fuel
                            { locals := fun n =>
                                (bound.reverse ++ defaults).getD n (.i32 0)
                            , stack := []
                            , mem := s.mem
                            , memSize := s.memSize } f.body with
                        | .ok s' =>
                            execList m fuel (callJoin s rest s') is
                        | .branch none s' =>
                            execList m fuel (callJoin s rest s') is
                        | .branch (some _) _ => .unmodeled
                        | .trap r => .trap r
                        | .structural => .structural
                        | .unmodeled => .unmodeled
                        | .outOfFuel => .outOfFuel
                | none => .trap .typeErr := rfl

/-- The INDIRECT-call arm's equation (the table layer's reduction
    face: the runtime index → the table entry → the type check → the
    fuel-shared sub-exec + the join; the trap teeth named). -/
theorem execList_callindirect (m : Module) (fuel : Nat) (s : State) (ty : Nat)
    (is : List Instr) :
    execList m (fuel + 1) s (Instr.callindirect ty :: is)
      = match m.typeAt ty with
        | none => .unmodeled
        | some ft =>
            match s.stack with
            | .i32 ix :: rest =>
                match m.tableAt ix.toNat with
                | none => .trap .tabOOB
                | some fn =>
                    match m.funcs[fn]? with
                    | none => .unmodeled
                    | some f =>
                        match m.typeAt f.tyIdx with
                        | none => .unmodeled
                        | some ft' =>
                            if ft' = ft then
                              match popTys ft.params.reverse rest with
                              | some (bound, rest2) =>
                                  match localsDefault? f.locals with
                                  | none => .unmodeled
                                  | some defaults =>
                                      match execList m fuel
                                          { locals := fun n =>
                                              (bound.reverse ++ defaults).getD n (.i32 0)
                                          , stack := []
                                          , mem := s.mem
                                          , memSize := s.memSize } f.body with
                                      | .ok s' =>
                                          execList m fuel (callJoin s rest2 s') is
                                      | .branch none s' =>
                                          execList m fuel (callJoin s rest2 s') is
                                      | .branch (some _) _ => .unmodeled
                                      | .trap r => .trap r
                                      | .structural => .structural
                                      | .unmodeled => .unmodeled
                                      | .outOfFuel => .outOfFuel
                              | none => .trap .typeErr
                            else .trap .indirectSig
            | _ => .trap .typeErr := rfl

theorem execList_block (m : Module) (fuel : Nat) (s : State) (b is : List Instr) :
    execList m (fuel + 1) s (Instr.block b :: is)
      = match execList m fuel s b with
        | .ok s' => execList m fuel s' is
        | .branch (some 0) s2 =>
            execList m fuel
              { s with locals := s2.locals, stack := s.stack, mem := s2.mem } is
        | .branch (some (n + 1)) s2 => .branch (some n) s2
        | .branch none s2 => .branch none s2
        | .trap r => .trap r
        | .structural => .structural
        | .unmodeled => .unmodeled
        | .outOfFuel => .outOfFuel := rfl

theorem execList_loop (m : Module) (fuel : Nat) (s : State) (b is : List Instr) :
    execList m (fuel + 1) s (Instr.loop b :: is)
      = match execList m fuel s b with
        | .ok s' => execList m fuel s' is
        | .branch (some 0) s2 =>
            execList m fuel
              { s with locals := s2.locals, stack := s.stack, mem := s2.mem }
              (Instr.loop b :: is)
        | .branch (some (n + 1)) s2 => .branch (some n) s2
        | .branch none s2 => .branch none s2
        | .trap r => .trap r
        | .structural => .structural
        | .unmodeled => .unmodeled
        | .outOfFuel => .outOfFuel := rfl

theorem execList_if_ (m : Module) (fuel : Nat) (s : State) (t e is : List Instr) :
    execList m (fuel + 1) s (Instr.if_ t e :: is)
      = match s.stack with
        | .i32 b :: rest =>
            match execList m fuel { s with stack := rest } (if b != 0 then t else e) with
            | .ok s' => execList m fuel s' is
            | .branch (some 0) s2 =>
                execList m fuel
                  { s with locals := s2.locals, stack := rest, mem := s2.mem } is
            | .branch (some (n + 1)) s2 => .branch (some n) s2
            | .branch none s2 => .branch none s2
            | .trap r => .trap r
            | .structural => .structural
            | .unmodeled => .unmodeled
            | .outOfFuel => .outOfFuel
        | _ => .trap .typeErr := rfl

/-! ### The StepTy inversions (the shape facts the flat cases ride) -/

/-- The inversion lemmas are stated over EXISTENTIALS — never
    substituting the caller's variables (the `cases`-direction
    discipline: the caller's `base`/`mid` survive). -/
theorem stepTy_localset_inv (c : Ctx) (base mid : List ValType) (n : Nat)
    (h : StepTy c base (Instr.localset n) mid) :
    ∃ t ts, base = t :: ts ∧ mid = ts ∧ c.lty n = some t := by
  cases h
  exact ⟨_, _, rfl, rfl, by assumption⟩

theorem stepTy_localtee_inv (c : Ctx) (base mid : List ValType) (n : Nat)
    (h : StepTy c base (Instr.localtee n) mid) :
    ∃ t ts, base = t :: ts ∧ mid = t :: ts ∧ c.lty n = some t := by
  cases h
  exact ⟨_, _, rfl, rfl, by assumption⟩

theorem stepTy_op_inv (c : Ctx) (base mid : List ValType) (o : Op)
    (h : StepTy c base (Instr.op o) mid) :
    ∃ ts, base = opPop o ++ ts ∧ mid = opPush o ++ ts := by
  cases h
  exact ⟨_, rfl, rfl⟩

theorem stepTy_mem_inv (c : Ctx) (base mid : List ValType) (m : MemOp) (off : Nat)
    (al : Option Nat) (h : StepTy c base (Instr.mem m off al) mid) :
    ∃ ts, base = memPop m ++ ts ∧ mid = memPush m ++ ts := by
  cases h
  exact ⟨_, rfl, rfl⟩

theorem stepTy_brif_inv (c : Ctx) (base mid : List ValType) (d : Nat)
    (h : StepTy c base (Instr.brif d) mid) :
    ∃ ts, base = ValType.i32 :: ts ∧ mid = ts := by
  cases h
  exact ⟨_, rfl, rfl⟩

theorem stepTy_drop_inv (c : Ctx) (base mid : List ValType)
    (h : StepTy c base Instr.drop mid) :
    ∃ t ts, base = t :: ts ∧ mid = ts := by
  cases h
  exact ⟨_, _, rfl, rfl⟩

theorem stepTy_select_inv (c : Ctx) (base mid : List ValType)
    (h : StepTy c base Instr.select mid) :
    ∃ ts t t', t = t' ∧ (t = ValType.i32 ∨ t = ValType.i64)
      ∧ base = ValType.i32 :: t :: t' :: ts ∧ mid = t :: ts := by
  cases h
  exact ⟨_, _, _, by assumption, by assumption, rfl, rfl⟩

/-- The fenv's resolution face: a resolved entry names the function
    record and its type (the calls layer's lookup bridge). -/
theorem fenv_some (m : Module) (fn : Nat) (ft : FuncType)
    (h : m.fenv fn = some ft) :
    ∃ f, m.funcs[fn]? = some f ∧ m.typeAt f.tyIdx = some ft := by
  have h' : m.fenv fn = match m.funcs[fn]? with
      | some g => m.typeAt g.tyIdx
      | none => none := rfl
  rw [h'] at h
  cases hf : m.funcs[fn]? with
  | none => rw [hf] at h; simp at h
  | some f => rw [hf] at h; exact ⟨f, rfl, h⟩

theorem stepTy_call_inv (c : Ctx) (base mid : List ValType) (fn : Nat)
    (h : StepTy c base (Instr.call fn) mid) :
    ∃ ft ts, c.fenv fn = some ft ∧ base = ft.params.reverse ++ ts
      ∧ mid = ft.results.reverse ++ ts := by
  cases h
  exact ⟨_, _, by assumption, rfl, rfl⟩

theorem stepTy_callindirect_inv (c : Ctx) (base mid : List ValType) (ty : Nat)
    (h : StepTy c base (Instr.callindirect ty) mid) :
    ∃ ft ts, c.tenv ty = some ft
      ∧ base = .i32 :: (ft.params.reverse ++ ts)
      ∧ mid = ft.results.reverse ++ ts := by
  cases h
  exact ⟨_, _, by assumption, rfl, rfl⟩

/-- The defaults' static view (the driver's locals-map typing). -/
theorem valDefault_typed (t : ValType) (v : Val) (h : valDefault? t = some v) :
    tyOf v = t := by
  cases t <;> simp only [valDefault?] at h <;> cases h <;> rfl

theorem localsDefault_typed (ts : List ValType) (vs : List Val)
    (h : localsDefault? ts = some vs) : stackTys vs = ts := by
  induction ts generalizing vs with
  | nil => simp [localsDefault?] at h; subst h; rfl
  | cons t ts ih =>
      simp only [localsDefault?] at h
      split at h
      · simp at h
      · next v hv =>
          cases hd : localsDefault? ts with
          | none => rw [hd] at h; simp at h
          | some vs' =>
              rw [hd] at h
              have hvsv : vs = v :: vs' := by simp at h; exact h.symm
              subst hvsv
              simp only [stackTys, valDefault_typed t v hv, ih vs' hd]

/-- The getD-on-append split (the driver's locals map reads the bound
    params up to the bound's length, the defaults beyond). -/
theorem getD_append_val (l1 l2 : List Val) (d : Val) (n : Nat) :
    (l1 ++ l2).getD n d
      = if n < l1.length then l1.getD n d else l2.getD (n - l1.length) d := by
  induction n generalizing l1 with
  | zero =>
      cases l1 with
      | nil => simp [List.getD]
      | cons a l1 => simp [List.getD]
  | succ n ih =>
      cases l1 with
      | nil => simp [List.getD]
      | cons a l1 =>
          simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
          rw [ih l1]
          by_cases h : n < l1.length
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]
            have hx : n + 1 - (l1.length + 1) = n - l1.length := by omega
            rw [hx]

/-- getElem transfers along list equality (the side conditions are
    Props — proof irrelevance makes the transfers definitional). -/
theorem getElem_congr {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) (i : Nat)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁[i]'h₁ = l₂[i]'h₂ := by
  subst h
  rfl

/-- The driver's locals map reads the declared types in order: param i
    into local i (the `bound.reverse ++ defaults` discipline, typed). -/
theorem localsMap_typed (params lcls : List ValType) (bound defaults : List Val) (n : Nat)
    (t : ValType)
    (hbd : stackTys bound = params.reverse)
    (hdf : stackTys defaults = lcls)
    (hn : (params ++ lcls)[n]? = some t) :
    tyOf ((bound.reverse ++ defaults).getD n (.i32 0)) = t := by
  have hni : n < (params ++ lcls).length := (List.getElem?_eq_some_iff.mp hn).1
  have hget : (params ++ lcls)[n]'hni = t := (List.getElem?_eq_some_iff.mp hn).2
  have hlen : params.length = bound.length := by
    have h1 := stackTys_length bound
    rw [hbd, List.length_reverse] at h1
    exact h1
  have hrev : stackTys bound.reverse = params := by
    rw [stackTys_reverse, hbd, List.reverse_reverse]
  have hrevlen : bound.reverse.length = bound.length := by simp
  by_cases hnk : n < bound.length
  · -- the param range: the reversed bound's n-th value carries params' n-th type
    rw [List.getElem_append_left (by rw [hlen]; omega)] at hget
    have hval : (bound.reverse ++ defaults).getD n (.i32 0)
        = bound.reverse.getD n (.i32 0) := by
      rw [getD_append_val, if_pos (by rw [hrevlen]; omega)]
    rw [hval, tyOf_getD bound.reverse (.i32 0) n
      (by have h := stackTys_length bound.reverse; simp at h; omega),
      getElem_congr hrev n
        (by have h := stackTys_length bound.reverse; simp at h; omega)
        (by omega)]
    exact hget
  · -- the declared range: the defaults' (n - len)-th value carries lcls' type
    have hval : (bound.reverse ++ defaults).getD n (.i32 0)
        = defaults.getD (n - params.length) (.i32 0) := by
      rw [getD_append_val, if_neg (by rw [hrevlen]; omega), hrevlen, ← hlen]
    have hlt : n - params.length < defaults.length := by
      have hs := stackTys_length defaults
      rw [hdf] at hs
      have hn2 := hni
      rw [List.length_append] at hn2
      omega
    rw [List.getElem_append_right (by rw [hlen]; omega)] at hget
    rw [hval, tyOf_getD defaults (.i32 0) (n - params.length) hlt,
      getElem_congr hdf (n - params.length)
        (by have hs := stackTys_length defaults; omega)
        (by rw [← hdf]; rw [stackTys_length]; exact hlt)]
    exact hget

/-! ### The exec_typed machinery (the quadruple + the dispatches, named once) -/

/-- THE QUADRUPLE (exec_typed's four-part conclusion, named once): the
    no-type-trap guarantee, the completion face, the branch-locals
    face, and the return face. A def, not a structure — the theorem's
    statement keeps its shape; the proof cites the name. -/
def ExecQuad (c : Ctx) (final : List ValType) (X : Outcome) : Prop :=
  X ≠ Outcome.trap Trap.typeErr
    ∧ (∀ s', X = Outcome.ok s' →
          stackTys s'.stack = final
          ∧ (∀ n t, c.lty n = some t → tyOf (s'.locals n) = t))
    ∧ (∀ d s2, X = Outcome.branch (some d) s2 →
          (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t))
    ∧ (∀ s2, X = Outcome.branch none s2 →
          stackTys s2.stack = c.resRev
          ∧ (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t))

/-- The dead-arm discharge (the quadruple's non-computing face:
    structural/unmodeled/outOfFuel, killed once). -/
theorem execQuad_dead (c : Ctx) (final : List ValType) (X : Outcome)
    (hneT : X ≠ Outcome.trap Trap.typeErr)
    (hok : ∀ s', X ≠ Outcome.ok s')
    (hbr : ∀ d s2, X ≠ Outcome.branch (some d) s2)
    (hret : ∀ s2, X ≠ Outcome.branch none s2) :
    ExecQuad c final X :=
  ⟨hneT, fun s' hX => absurd hX (hok s'), fun d s2 hX => absurd hX (hbr d s2),
    fun s2 hX => absurd hX (hret s2)⟩

/-- The always-dead arms (the three dead outcomes, each killed once
    here — the per-case blocks repeat them no more). -/
theorem execQuad_structural (c : Ctx) (final : List ValType) :
    ExecQuad c final Outcome.structural :=
  execQuad_dead c final _ (by simp) (by simp) (by simp) (by simp)

theorem execQuad_unmodeled (c : Ctx) (final : List ValType) :
    ExecQuad c final Outcome.unmodeled :=
  execQuad_dead c final _ (by simp) (by simp) (by simp) (by simp)

theorem execQuad_outOfFuel (c : Ctx) (final : List ValType) :
    ExecQuad c final Outcome.outOfFuel :=
  execQuad_dead c final _ (by simp) (by simp) (by simp) (by simp)

/-- The branch-decrement face: a `.branch (some d)` outcome answers
    the quadruple from the branch-point locals' typing alone. -/
theorem execQuad_branchSome (c : Ctx) (final : List ValType) (d : Nat) (s2 : State)
    (hl : ∀ n t, c.lty n = some t → tyOf (s2.locals n) = t) :
    ExecQuad c final (Outcome.branch (some d) s2) := by
  refine ⟨by simp, fun s' h => by simp at h, ?_, fun s3 h => by simp at h⟩
  intro d' s3 h
  rw [Outcome.branch.injEq] at h
  obtain ⟨-, hs3⟩ := h
  rw [← hs3]
  exact hl

/-- The return-pass face: a `.branch none` outcome answers the
    quadruple from the returned stack's typing alone. -/
theorem execQuad_branchNone (c : Ctx) (final : List ValType) (s2 : State)
    (hstk : stackTys s2.stack = c.resRev)
    (hl : ∀ n t, c.lty n = some t → tyOf (s2.locals n) = t) :
    ExecQuad c final (Outcome.branch none s2) := by
  refine ⟨by simp, fun s' h => by simp at h, fun d s3 h => by simp at h, ?_⟩
  intro s3 h
  rw [Outcome.branch.injEq] at h
  obtain ⟨-, hs3⟩ := h
  rw [← hs3]
  exact ⟨hstk, hl⟩

/-- The trap face: a non-type trap answers the quadruple. -/
theorem execQuad_trap (c : Ctx) (final : List ValType) (r : Trap)
    (hne : r ≠ Trap.typeErr) :
    ExecQuad c final (Outcome.trap r) :=
  ⟨fun h => hne (by rw [Outcome.trap.injEq] at h; exact h),
    fun s' h => by simp at h, fun d s3 h => by simp at h, fun s3 h => by simp at h⟩

/-- The flat cases' checker bridge (the congr + complete composition —
    the per-instr blocks repeat it modulo ctor, so it is named once).
    The tenv is CARRIED (only `callindirect` reads it; the flat steps
    are tenv-blind — but the ctx shape must line up with
    `step_preserves`' statement). -/
theorem flat_chk (c : Ctx) (base mid : List ValType) (i : Instr)
    (hst : StepTy c base i mid) (hff : FrameForm i = False)
    (hnc : ∀ fn, i ≠ Instr.call fn) :
    stepFlag (Ctx.mk c.lty (fun _ => none) c.tenv []) i base = .ok (false, mid) :=
  stepFlag_congr c.lty c.fenv (fun _ => none) c.tenv c.resRev [] i base mid
    (stepFlag_complete c base mid i hst) hnc hff

/-- The flat push bridge (the consts' + localget's shared face): a
    flat step that computes to a push rides `step_preserves` into the
    tail's quadruple. -/
theorem flat_push (c : Ctx) (m : Module) (fuel : Nat) (s s' : State) (i : Instr)
    (b mid final : List ValType) (is : List Instr)
    (hst : StepTy c b i mid) (hff : FrameForm i = False)
    (hnc : ∀ fn, i ≠ Instr.call fn)
    (hci : ∀ ty, i ≠ Instr.callindirect ty)
    (hx : step s i = .ok s')
    (hstack : stackTys s.stack = b)
    (hloc : ∀ n t, c.lty n = some t → tyOf (s.locals n) = t)
    (htail : BodyTy c mid is final)
    (hok : ∀ (is : List Instr) (s2 : State) (mid final : List ValType),
        BodyTy c mid is final → stackTys s2.stack = mid →
        (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t) →
        ExecQuad c final (execList m fuel s2 is)) :
    ExecQuad c final (execList m (fuel + 1) s (i :: is)) := by
  rw [execList_flat m fuel s i is hff hnc hci]
  obtain ⟨hstk2, hloc2⟩ := step_preserves s s' i b mid c.lty c.tenv hx hstack hloc
    (flat_chk c b mid i hst hff hnc)
  simp only [hx]
  exact hok is s' mid final htail hstk2 hloc2

/-- THE FRAME DISPATCH (the absorb/decrement/pass machine, named
    once): a frame's sub-run outcome either joins the tail (`.ok`),
    passes as the return signal (`.branch none`), is absorbed into the
    re-entry state (`.branch (some 0)` — the entry stack `esk`, the
    branch-point locals, the continuation `abs`), decrements
    (`.branch (some (k+1))`), propagates the trap, or is dead.
    `block`/`loop`/`if_` instantiate the equation, the entry stack and
    the continuations. -/
theorem frame_dispatch (m : Module) (fuel : Nat) (c : Ctx)
    (s : State) (b : List Instr) (is abs : List Instr) (esk : List Val)
    (base final : List ValType) (X : Outcome)
    (hbodyQ : ExecQuad c base (execList m fuel s b))
    (hgenT : ∀ s' : State, stackTys s'.stack = base →
        (∀ n t, c.lty n = some t → tyOf (s'.locals n) = t) →
        ExecQuad c final (execList m fuel s' is))
    (hgenA : ∀ s' : State, stackTys s'.stack = base →
        (∀ n t, c.lty n = some t → tyOf (s'.locals n) = t) →
        ExecQuad c final (execList m fuel s' abs))
    (hesk : stackTys esk = base)
    (heq : X = match execList m fuel s b with
      | .ok s' => execList m fuel s' is
      | .branch (some 0) s2 =>
          execList m fuel { s with locals := s2.locals, stack := esk, mem := s2.mem } abs
      | .branch (some (n + 1)) s2 => .branch (some n) s2
      | .branch none s2 => .branch none s2
      | .trap r => .trap r
      | .structural => .structural
      | .unmodeled => .unmodeled
      | .outOfFuel => .outOfFuel) :
    ExecQuad c final X := by
  rw [heq]
  cases hx : execList m fuel s b with
  | ok s2 =>
      obtain ⟨hstk2, hloc2⟩ := hbodyQ.2.1 s2 hx
      exact hgenT s2 hstk2 hloc2
  | branch k s2 =>
      cases k with
      | none =>
          obtain ⟨hstkR, hlocR⟩ := hbodyQ.2.2.2 s2 hx
          exact execQuad_branchNone c final s2 hstkR hlocR
      | some k0 =>
          cases k0 with
          | zero =>
              exact hgenA { s with locals := s2.locals, stack := esk, mem := s2.mem } hesk
                (hbodyQ.2.2.1 0 s2 hx)
          | succ k' =>
              exact execQuad_branchSome c final k' s2 (hbodyQ.2.2.1 (k' + 1) s2 hx)
  | trap r =>
      exact execQuad_trap c final r (fun h0 => hbodyQ.1 (by rw [hx, h0]))
  | structural => exact execQuad_structural c final
  | unmodeled => exact execQuad_unmodeled c final
  | outOfFuel => exact execQuad_outOfFuel c final

/-! ### THE BODY-LEVEL TYPE SAFETY (the frame machine's preservation) -/

/-- THE CORE THEOREM (legacy `Sem.exec_typed`'s content, ported to the
    landed Exec + Validate shapes, grown to the calls layer): the
    bodies of a module whose call environment is body-valid — every
    fenv-resolved function's body types `[] → results.reverse` (the
    premise is `hcal`; `runFunc_safe` discharges it from `checkModule`
    via `checkFuncs_some` + `checkFunc_sound`) — execute at ANY budget,
    in ANY well-typed context over the module's fenv, without ever
    answering the TYPE-MISMATCH trap; the fuel discipline is honest
    (`.outOfFuel` is a possible answer, never laundered into a trap —
    a divergent recursion included); and:

    - IF the run completes (`.ok s'`), the final stack is EXACTLY the
      static `final`, locals well-typed;
    - a branch signal (`some d`) carries well-typed branch-point
      locals (the frame-absorption clause);
    - a return signal (`none` — the `ret` discipline) carries the
      function's results on its stack (`c.resRev` — the validator's
      `ret` rule, preserved through the frames).

    The proof: induction on the fuel (the loop RESTART re-enters at the
    same instruction list one budget down — part 2 packages exactly the
    restart's hypotheses; the CALL re-enters at the callee's body at
    the same reduced budget — the callee's ctx rides the same IH). The
    flat cases ride `step_preserves` (the per-op engine) through
    `stepFlag_congr`; the call case rides `hcal` + `localsMap_typed`
    (the callee's entry state is well-typed) + the join's stack
    composition; the frame cases are the branch-depth discipline:
    absorb `some 0`, decrement `some (n+1)`, pass `none` (the return
    clause), propagate traps/fuel untouched. -/
theorem exec_typed (m : Module)
    (hcal : ∀ fn : Nat, ∀ (ft : FuncType) (f : Func),
      m.fenv fn = some ft → m.funcs[fn]? = some f →
      BodyTy (fnCtx m.fenv m.typeAt ft f) [] f.body ft.results.reverse) :
    ∀ (fuel : Nat) (c : Ctx), c.fenv = m.fenv → c.tenv = m.typeAt →
      (∀ body base final s,
          BodyTy c base body final →
          stackTys s.stack = base →
          (∀ n t, c.lty n = some t → tyOf (s.locals n) = t) →
          execList m fuel s body ≠ Outcome.trap Trap.typeErr
          ∧ (∀ s', execList m fuel s body = .ok s' →
                stackTys s'.stack = final
                ∧ (∀ n t, c.lty n = some t → tyOf (s'.locals n) = t))
          ∧ (∀ d s2, execList m fuel s body = .branch (some d) s2 →
                (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t))
          ∧ (∀ s2, execList m fuel s body = .branch none s2 →
                stackTys s2.stack = c.resRev
                ∧ (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t)))
      ∧ (∀ b is base final s,
          BodyTy c base b base →
          BodyTy c base is final →
          stackTys s.stack = base →
          (∀ n t, c.lty n = some t → tyOf (s.locals n) = t) →
          execList m fuel s (Instr.loop b :: is) ≠ Outcome.trap Trap.typeErr
          ∧ (∀ s', execList m fuel s (Instr.loop b :: is) = .ok s' →
                stackTys s'.stack = final
                ∧ (∀ n t, c.lty n = some t → tyOf (s'.locals n) = t))
          ∧ (∀ d s2, execList m fuel s (Instr.loop b :: is) = .branch (some d) s2 →
                (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t))
          ∧ (∀ s2, execList m fuel s (Instr.loop b :: is) = .branch none s2 →
                stackTys s2.stack = c.resRev
                ∧ (∀ n t, c.lty n = some t → tyOf (s2.locals n) = t))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c _ _
      refine ⟨?_, ?_⟩
      · intro body base final s _ _ _
        rw [execList_zero]
        exact ⟨by simp, fun s2 h => by simp at h, fun d s2 h => by simp at h,
          fun s2 h => by simp at h⟩
      · intro b is base final s _ _ _ _
        rw [execList_zero]
        exact ⟨by simp, fun s2 h => by simp at h, fun d s2 h => by simp at h,
          fun s2 h => by simp at h⟩
  | succ fuel ih =>
      intro c hfenv htenv
      have ihc := ih c hfenv htenv
      -- the tail's quadruple (the induction's part 1, ExecQuad-faced)
      have hok : ∀ (is : List Instr) (s2 : State) (mid final : List ValType)
          (htail : BodyTy c mid is final)
          (hstk2 : stackTys s2.stack = mid)
          (hloc2 : ∀ n t, c.lty n = some t → tyOf (s2.locals n) = t),
          ExecQuad c final (execList m fuel s2 is) :=
        fun is s2 mid final htail hstk2 hloc2 => ihc.1 is mid final s2 htail hstk2 hloc2
      constructor
      · intro body base final s hbody hstack hloc
        cases hbody with
        | nil =>
            rw [execList_nil]
            refine ⟨by simp, ?_, ?_, ?_⟩
            · intro s2 h
              rw [Outcome.ok.injEq] at h
              subst h
              exact ⟨hstack, hloc⟩
            · intro d s2 h; simp at h
            · intro s2 h; simp at h
        | cons _ i is mid _ hst htail =>
            have hff : FrameForm i = False := stepTy_frameFalse c base mid i hst
            cases i with
            | i32const n =>
                exact flat_push c m fuel s { s with stack := .i32 n.toUInt32 :: s.stack }
                  (Instr.i32const n) base mid final is hst hff (by intro fn h; cases h)
                  (by intro ty h; cases h) (by simp [step]) hstack hloc htail hok
            | i64const n =>
                exact flat_push c m fuel s { s with stack := .i64 n.toUInt64 :: s.stack }
                  (Instr.i64const n) base mid final is hst hff (by intro fn h; cases h)
                  (by intro ty h; cases h) (by simp [step]) hstack hloc htail hok
            | localget n =>
                exact flat_push c m fuel s { s with stack := s.locals n :: s.stack }
                  (Instr.localget n) base mid final is hst hff (by intro fn h; cases h)
                  (by intro ty h; cases h) (by simp [step]) hstack hloc htail hok
            | localset n =>
                rw [execList_flat m fuel s (Instr.localset n) is hff (by simp) (by simp)]
                obtain ⟨t, ts, hb, hm, hl⟩ := stepTy_localset_inv c base mid n hst
                have hchk := flat_chk c base mid (Instr.localset n) hst hff
                  (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨v, rest, h2⟩ := stackTys_cons_inv s.stack t ts hstack
                have hx : step s (Instr.localset n)
                    = .ok { s with locals := fun m => if m = n then v else s.locals m
                                   , stack := rest } := by
                  simp only [step, h2]
                obtain ⟨hstk2, hloc2⟩ := step_preserves s
                  { s with locals := fun m => if m = n then v else s.locals m, stack := rest }
                  (Instr.localset n) (t :: ts) ts c.lty c.tenv hx hstack hloc hchk
                rw [hm] at htail
                simp only [hx]
                exact hok is _ ts final htail hstk2 hloc2
            | localtee n =>
                rw [execList_flat m fuel s (Instr.localtee n) is hff (by simp) (by simp)]
                obtain ⟨t, ts, hb, hm, hl⟩ := stepTy_localtee_inv c base mid n hst
                have hchk := flat_chk c base mid (Instr.localtee n) hst hff
                  (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨v, rest, h2⟩ := stackTys_cons_inv s.stack t ts hstack
                have hx : step s (Instr.localtee n)
                    = .ok { s with locals := fun m => if m = n then v else s.locals m } := by
                  simp only [step, h2]
                obtain ⟨hstk2, hloc2⟩ := step_preserves s
                  { s with locals := fun m => if m = n then v else s.locals m }
                  (Instr.localtee n) (t :: ts) (t :: ts) c.lty c.tenv hx hstack hloc hchk
                rw [hm] at htail
                simp only [hx]
                exact hok is _ (t :: ts) final htail hstk2 hloc2
            | call fn =>
                -- the calls layer: the callee's entry state is
                -- well-typed (`hcal` + `localsMap_typed`), the callee's
                -- run rides the SAME IH at its own ctx, and the join
                -- composes the stacks (the ok/return faces named once)
                obtain ⟨ft, ts, hfenvFn, hb, hm⟩ := stepTy_call_inv c base mid fn hst
                rw [hm] at htail
                rw [hb] at hstack
                have hf' : m.fenv fn = some ft := by rw [← hfenv]; exact hfenvFn
                obtain ⟨f, hfIdx, hftIdx⟩ := fenv_some m fn ft hf'
                have hcB : BodyTy (fnCtx m.fenv m.typeAt ft f) [] f.body ft.results.reverse :=
                  hcal fn ft f hf' hfIdx
                obtain ⟨bound, rest, hpop, hbd, hrest⟩ :=
                  popTys_of_stackTys ft.params.reverse s.stack ts hstack
                -- the join's stack composition (the ok + return faces)
                have hjoinQ : ∀ (sC : State)
                    (hface : stackTys sC.stack = ft.results.reverse),
                    ExecQuad c final
                      (execList m fuel (callJoin s rest sC) is) :=
                  fun sC hface =>
                    hok is (callJoin s rest sC) (ft.results.reverse ++ ts) final htail
                      (by simp only [callJoin, stackTys_append, hface, hrest]) hloc
                cases hd : localsDefault? f.locals with
                | none =>
                    -- non-integer locals: outside the fragment (honest)
                    simp only [execList_call, hfIdx, hftIdx, hpop, hd]
                    exact execQuad_unmodeled c final
                | some defaults =>
                    have hdf : stackTys defaults = f.locals :=
                      localsDefault_typed f.locals defaults hd
                    have hlocC : ∀ n t, (fnCtx m.fenv m.typeAt ft f).lty n = some t →
                        tyOf ((bound.reverse ++ defaults).getD n (.i32 0)) = t :=
                      fun n t hn =>
                        localsMap_typed ft.params f.locals bound defaults n t hbd hdf hn
                    have hresC : (fnCtx m.fenv m.typeAt ft f).resRev = ft.results.reverse := rfl
                    obtain ⟨hneC, hokC, -, hretC⟩ :=
                      (ih (fnCtx m.fenv m.typeAt ft f) rfl rfl).1 f.body [] ft.results.reverse
                        { locals := fun n =>
                            (bound.reverse ++ defaults).getD n (.i32 0)
                        , stack := []
                        , mem := s.mem
                        , memSize := s.memSize }
                        hcB (by simp [stackTys]) hlocC
                    simp only [execList_call, hfIdx, hftIdx, hpop, hd]
                    cases hx : execList m fuel
                        { locals := fun n =>
                            (bound.reverse ++ defaults).getD n (.i32 0)
                        , stack := []
                        , mem := s.mem
                        , memSize := s.memSize } f.body with
                    | ok s' => exact hjoinQ s' (hokC s' hx).1
                    | branch d s2 =>
                        cases d with
                        | none =>
                            -- the callee's `ret`: the return signal joins
                            -- the caller (the results are on the callee's
                            -- stack, per the return clause)
                            exact hjoinQ s2 ((hretC s2 hx).1.trans hresC)
                        | some _ =>
                            -- the br-escape: the validator's depth gap —
                            -- the honest unmodeled (branches do not cross
                            -- calls)
                            exact execQuad_unmodeled c final
                    | trap r =>
                        exact execQuad_trap c final r (fun h0 => hneC (by rw [hx, h0]))
                    | structural => exact execQuad_structural c final
                    | unmodeled => exact execQuad_unmodeled c final
                    | outOfFuel => exact execQuad_outOfFuel c final
            | callindirect ty =>
                -- THE INDIRECT-CALL LAYER (the table discipline's type
                -- safety): the callee index is RUNTIME data — the
                -- table entry names the function, the type check pins
                -- the entry's resolved type to the declared one, and
                -- the callee's well-typed entry rides `hcal` at the
                -- RESOLVED type (equal to the declared in the
                -- computing branch). The runtime's declared type IS
                -- the validator's (`htenv` — the tenv premise pins
                -- c.tenv = m.typeAt). The traps (`tabOOB`/
                -- `indirectSig`) are RUNTIME checks — distinct from
                -- `typeErr` (the honest statement over the new arm: a
                -- validated body never answers the TYPE error; the
                -- table's runtime teeth stay possible, never a wrong
                -- call).
                obtain ⟨ft, ts, hten, hb, hm⟩ := stepTy_callindirect_inv c base mid ty hst
                rw [hm] at htail
                rw [hb] at hstack
                have htyR : m.typeAt ty = some ft := htenv ▸ hten
                obtain ⟨ix, rest0, hstack2⟩ := stackTys_cons_inv s.stack .i32 _ hstack
                rw [hstack2] at hstack
                have hcty : tyOf ix = .i32 ∧ stackTys rest0 = ft.params.reverse ++ ts := by
                  have h2 : tyOf ix :: stackTys rest0
                      = ValType.i32 :: (ft.params.reverse ++ ts) := hstack
                  injection h2 with ha hres
                  exact ⟨ha, hres⟩
                cases ix with
                | i32 ix =>
                    simp only [execList_callindirect, htyR, hstack2]
                    cases htab : m.tableAt ix.toNat with
                    | none =>
                        -- out of bounds: the named RUNTIME trap
                        simp only [htab]
                        exact execQuad_trap c final .tabOOB (by simp)
                    | some fn =>
                        cases hfIdx : m.funcs[fn]? with
                        | none =>
                            simp only [htab, hfIdx]
                            exact execQuad_unmodeled c final
                        | some f =>
                            cases hftR : m.typeAt f.tyIdx with
                            | none =>
                                simp only [htab, hfIdx, hftR]
                                exact execQuad_unmodeled c final
                            | some ft' =>
                                -- the table's TYPE CHECK: the entry's
                                -- resolved type against the declared one
                                by_cases hEq : ft' = ft
                                · -- the computing branch: the runtime's
                                  -- pops ride the DECLARED type; the
                                  -- entry's resolved type agrees (`hEq`),
                                  -- so the callee's typing converts
                                  simp only [if_pos hEq, hfIdx, hftR]
                                  obtain ⟨bound, rest2, hpop, hbd, hrest⟩ :=
                                    popTys_of_stackTys ft.params.reverse rest0 ts hcty.2
                                  have hf' : m.fenv fn = some ft' := by
                                    simp only [Module.fenv, hfIdx]
                                    rw [hftR]
                                  have hcB : BodyTy (fnCtx m.fenv m.typeAt ft' f) []
                                      f.body ft'.results.reverse := hcal fn ft' f hf' hfIdx
                                  rw [hEq] at hcB
                                  cases hd : localsDefault? f.locals with
                                  | none =>
                                      simp only [hpop, hd]
                                      exact execQuad_unmodeled c final
                                  | some defaults =>
                                      have hdf : stackTys defaults = f.locals :=
                                        localsDefault_typed f.locals defaults hd
                                      have hlocC : ∀ n t,
                                          (fnCtx m.fenv m.typeAt ft f).lty n = some t →
                                          tyOf ((bound.reverse ++ defaults).getD n (.i32 0)) = t :=
                                        fun n t hn =>
                                          localsMap_typed ft.params f.locals bound defaults n t
                                            hbd hdf hn
                                      have hresC :
                                          (fnCtx m.fenv m.typeAt ft f).resRev
                                            = ft.results.reverse := rfl
                                      obtain ⟨hneC, hokC, -, hretC⟩ :=
                                          (ih (fnCtx m.fenv m.typeAt ft f) rfl rfl).1 f.body []
                                            ft.results.reverse
                                            { locals := fun n =>
                                                (bound.reverse ++ defaults).getD n (.i32 0)
                                            , stack := []
                                            , mem := s.mem
                                            , memSize := s.memSize }
                                            hcB (by simp [stackTys]) hlocC
                                      have hjoinQ : ∀ (sC : State)
                                          (hface : stackTys sC.stack = ft.results.reverse),
                                          ExecQuad c final
                                            (execList m fuel (callJoin s rest2 sC) is) :=
                                        fun sC hface =>
                                          hok is (callJoin s rest2 sC)
                                            (ft.results.reverse ++ ts) final htail
                                            (by simp only [callJoin, stackTys_append, hface,
                                              hrest]) hloc
                                      simp only [hpop, hd]
                                      cases hx : execList m fuel
                                          { locals := fun n =>
                                              (bound.reverse ++ defaults).getD n (.i32 0)
                                          , stack := []
                                          , mem := s.mem
                                          , memSize := s.memSize } f.body with
                                      | ok s' => exact hjoinQ s' (hokC s' hx).1
                                      | branch d s2 =>
                                          cases d with
                                          | none =>
                                              exact hjoinQ s2 ((hretC s2 hx).1.trans hresC)
                                          | some _ =>
                                              exact execQuad_unmodeled c final
                                      | trap r =>
                                          exact execQuad_trap c final r
                                            (fun h0 => hneC (by rw [hx, h0]))
                                      | structural => exact execQuad_structural c final
                                      | unmodeled => exact execQuad_unmodeled c final
                                      | outOfFuel => exact execQuad_outOfFuel c final
                                · -- the sig mismatch: the named RUNTIME trap
                                  simp only [if_neg hEq, hfIdx, hftR]
                                  exact execQuad_trap c final .indirectSig (by simp)
                | i64 => exfalso; simp [tyOf] at hcty
            | mem mop offset al =>
                rw [execList_flat m fuel s (Instr.mem mop offset al) is hff (by simp) (by simp)]
                obtain ⟨ts, hb, hm⟩ := stepTy_mem_inv c base mid mop offset al hst
                have hchk := flat_chk c base mid (Instr.mem mop offset al) hst hff
                  (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                rcases step_mem_outcome mop offset al ts s hstack with htrap | ⟨s2, hx⟩
                · rw [htrap]
                  exact execQuad_dead c final (.trap .memOOB) (by simp) (by simp)
                    (by simp) (by simp)
                · obtain ⟨hstk2, hloc2⟩ := step_preserves s s2
                    (Instr.mem mop offset al) (memPop mop ++ ts) (memPush mop ++ ts) c.lty c.tenv hx
                    hstack hloc hchk
                  rw [hm] at htail
                  simp only [hx]
                  exact hok is _ (memPush mop ++ ts) final htail hstk2 hloc2
            | op o =>
                rw [execList_flat m fuel s (Instr.op o) is hff (by simp) (by simp)]
                obtain ⟨ts, hb, hm⟩ := stepTy_op_inv c base mid o hst
                have hchk := flat_chk c base mid (Instr.op o) hst hff (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨args, rest, hp, ha, hr⟩ :=
                  popTys_of_stackTys (opPop o) s.stack ts hstack
                obtain ⟨v, hv⟩ := semOp_exists o args ha
                have hx : step s (Instr.op o) = .ok { s with stack := v :: rest } := by
                  simp [step, hp, hv]
                obtain ⟨hstk2, hloc2⟩ := step_preserves s { s with stack := v :: rest }
                  (Instr.op o) (opPop o ++ ts) (opPush o ++ ts) c.lty c.tenv hx hstack hloc hchk
                rw [hm] at htail
                simp only [hx]
                exact hok is _ (opPush o ++ ts) final htail hstk2 hloc2
            | br d => cases hst
            | brif d =>
                rw [execList_flat m fuel s (Instr.brif d) is hff (by simp) (by simp)]
                obtain ⟨ts, hb, hm⟩ := stepTy_brif_inv c base mid d hst
                have hchk := flat_chk c base mid (Instr.brif d) hst hff (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨c0, rest, hstack2⟩ := stackTys_cons_inv s.stack .i32 ts hstack
                rw [hstack2] at hstack
                have hcty : tyOf c0 = .i32 ∧ stackTys rest = ts := by
                  have h3 : tyOf c0 :: stackTys rest = ValType.i32 :: ts := hstack
                  injection h3 with ha hres
                  exact ⟨ha, hres⟩
                cases c0 with
                | i32 b =>
                    by_cases hb : b != 0
                    · have hx : step s (Instr.brif d)
                        = .branch (some d) { s with stack := rest } := by
                        simp only [step, hstack2, if_pos hb]
                      rw [hx]
                      exact execQuad_branchSome c final d { s with stack := rest } hloc
                    · have hx : step s (Instr.brif d) = .ok { s with stack := rest } := by
                        simp only [step, hstack2, if_neg hb]
                      obtain ⟨hstk2, hloc2⟩ := step_preserves s
                        { s with stack := rest } (Instr.brif d) (ValType.i32 :: ts) ts c.lty c.tenv hx
                        (by rw [hstack2]; exact hstack) hloc hchk
                      rw [hm] at htail
                      simp only [hx]
                      exact hok is _ ts final htail hstk2 hloc2
                | i64 => simp [tyOf] at hcty
            | block b => cases hst
            | loop b => cases hst
            | if_ t e => cases hst
            | ret => cases hst
            | unreach => cases hst
            | drop =>
                rw [execList_flat m fuel s Instr.drop is hff (by simp) (by simp)]
                obtain ⟨t, ts, hb, hm⟩ := stepTy_drop_inv c base mid hst
                have hchk := flat_chk c base mid Instr.drop hst hff (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨v, rest, h2⟩ := stackTys_cons_inv s.stack t ts hstack
                have hx : step s Instr.drop = .ok { s with stack := rest } := by
                  simp only [step, h2]
                obtain ⟨hstk2, hloc2⟩ := step_preserves s { s with stack := rest }
                  Instr.drop (t :: ts) ts c.lty c.tenv hx hstack hloc hchk
                rw [hm] at htail
                simp only [hx]
                exact hok is _ ts final htail hstk2 hloc2
            | select =>
                rw [execList_flat m fuel s Instr.select is hff (by simp) (by simp)]
                obtain ⟨ts, t, t', heq, htor, hb, hm⟩ :=
                  stepTy_select_inv c base mid hst
                have hchk := flat_chk c base mid Instr.select hst hff (by intro fn h; cases h)
                rw [hb, hm] at hchk
                rw [hb] at hstack
                obtain ⟨c0, rest1, hstack2⟩ :=
                  stackTys_cons_inv s.stack .i32 (t :: t' :: ts) hstack
                rw [hstack2] at hstack
                have hcty : tyOf c0 = .i32 ∧ stackTys rest1 = t :: t' :: ts := by
                  have h3 : tyOf c0 :: stackTys rest1 = ValType.i32 :: (t :: t' :: ts) := hstack
                  injection h3 with ha hres
                  exact ⟨ha, hres⟩
                obtain ⟨v2, rest2, hrest2⟩ := stackTys_cons_inv rest1 t (t' :: ts) hcty.2
                have hcty2 : stackTys rest1 = t :: t' :: ts := hcty.2
                rw [hrest2] at hcty2
                have hv2 : tyOf v2 = t ∧ stackTys rest2 = t' :: ts := by
                  have h4 : tyOf v2 :: stackTys rest2 = t :: t' :: ts := hcty2
                  injection h4 with ha hb
                  exact ⟨ha, hb⟩
                obtain ⟨v3, rest3, hrest3⟩ := stackTys_cons_inv rest2 t' ts hv2.2
                have hcty3 : stackTys rest2 = t' :: ts := hv2.2
                rw [hrest3] at hcty3
                have hv3 : tyOf v3 = t' ∧ stackTys rest3 = ts := by
                  have h5 : tyOf v3 :: stackTys rest3 = t' :: ts := hcty3
                  injection h5 with ha hb
                  exact ⟨ha, hb⟩
                cases c0 with
                | i32 b =>
                    have hx : step s Instr.select
                        = .ok { s with stack := (if b != 0 then v2 else v3) :: rest3 } := by
                      simp only [step, hstack2, hrest2, hrest3]
                      split <;> rfl
                    obtain ⟨hstk2, hloc2⟩ := step_preserves s
                      { s with stack := (if b != 0 then v2 else v3) :: rest3 }
                      Instr.select (ValType.i32 :: t :: t' :: ts) (t :: ts) c.lty c.tenv hx
                      (by rw [hstack2]; exact hstack) hloc hchk
                    rw [hm] at htail
                    simp only [hx]
                    exact hok is _ (t :: ts) final htail hstk2 hloc2
                | i64 => simp [tyOf] at hcty
        | br _ is d =>
            have hx : step s (Instr.br d) = .branch (some d) s := by simp [step]
            rw [execList_flat m fuel s (Instr.br d) is (by simp [FrameForm]) (by simp) (by simp), hx]
            exact execQuad_branchSome c base d s hloc
        | unreach _ is =>
            have hx : step s Instr.unreach = .trap Trap.unreach := by simp [step]
            rw [execList_flat m fuel s Instr.unreach is (by simp [FrameForm]) (by simp) (by simp), hx]
            exact execQuad_dead c base (.trap .unreach) (by simp) (by simp)
              (by simp) (by simp)
        | ret _ is heq =>
            -- the return signal: the ret-point stack IS the results
            -- (the validator's ret rule, `heq`)
            have hx : step s Instr.ret = .branch none s := by simp [step]
            rw [execList_flat m fuel s Instr.ret is (by simp [FrameForm]) (by simp) (by simp), hx]
            exact execQuad_branchNone c base s (by rw [← heq]; exact hstack) hloc
        | block _ b is _ hb htail =>
            exact frame_dispatch m fuel c s b is is s.stack base final
              (execList m (fuel + 1) s (Instr.block b :: is))
              (ihc.1 b base base s hb hstack hloc)
              (fun s2 h1 h2 => ihc.1 is base final s2 htail h1 h2)
              (fun s2 h1 h2 => ihc.1 is base final s2 htail h1 h2)
              hstack (execList_block m fuel s b is)
        | loop _ b is _ hb htail =>
            exact frame_dispatch m fuel c s b is (Instr.loop b :: is) s.stack base final
              (execList m (fuel + 1) s (Instr.loop b :: is))
              (ihc.1 b base base s hb hstack hloc)
              (fun s2 h1 h2 => ihc.1 is base final s2 htail h1 h2)
              (fun s2 h1 h2 => ihc.2 b is base final s2 hb htail h1 h2)
              hstack (execList_loop m fuel s b is)
        | if_ ts t e is _ hb1 hb2 htail =>
            obtain ⟨c0, rest, hstack2⟩ := stackTys_cons_inv s.stack .i32 ts hstack
            rw [hstack2] at hstack
            have hcty : tyOf c0 = .i32 ∧ stackTys rest = ts := by
              have h3 : tyOf c0 :: stackTys rest = ValType.i32 :: ts := hstack
              injection h3 with ha hres
              exact ⟨ha, hres⟩
            cases c0 with
            | i32 b =>
                rw [execList_if_ m fuel s t e is, hstack2]
                by_cases hb : b != 0
                · simp only [if_pos hb]
                  exact frame_dispatch m fuel c { s with stack := rest } t is is rest ts final _
                    (ihc.1 t ts ts { s with stack := rest } hb1 hcty.2 hloc)
                    (fun s2 h1 h2 => ihc.1 is ts final s2 htail h1 h2)
                    (fun s2 h1 h2 => ihc.1 is ts final s2 htail h1 h2)
                    hcty.2 rfl
                · simp only [if_neg hb]
                  exact frame_dispatch m fuel c { s with stack := rest } e is is rest ts final _
                    (ihc.1 e ts ts { s with stack := rest } hb2 hcty.2 hloc)
                    (fun s2 h1 h2 => ihc.1 is ts final s2 htail h1 h2)
                    (fun s2 h1 h2 => ihc.1 is ts final s2 htail h1 h2)
                    hcty.2 rfl
            | i64 => simp [tyOf] at hcty
      · intro b is base final s hb htail hstack hloc
        exact frame_dispatch m fuel c s b is (Instr.loop b :: is) s.stack base final
          (execList m (fuel + 1) s (Instr.loop b :: is))
          (ihc.1 b base base s hb hstack hloc)
          (fun s2 h1 h2 => ihc.1 is base final s2 htail h1 h2)
          (fun s2 h1 h2 => ihc.2 b is base final s2 hb htail h1 h2)
          hstack (execList_loop m fuel s b is)

/-! ## The module-level type safety -/


/-- THE MODULE-LEVEL TYPE SAFETY (the deliverable's driver face): a
    VALIDATED module's function, run by the driver on args typed the
    `call` rule's way (`stackTys args = params.reverse` — head = TOP =
    the last param), never answers the type-mismatch trap; and IF it
    completes, the final stack is EXACTLY the declared results
    (reversed for the head-top convention). The calls layer rides
    along: `hcal` — the call-typing premise `exec_typed` needs — is
    discharged from `checkModule` (`checkFuncs_some` +
    `checkFunc_sound`), so a validated module's WHOLE call chain is
    covered. Fuel-honest: `.outOfFuel` and the runtime traps
    (`.unreach`/`.memOOB`) stay possible answers — the theorem excludes
    the TYPE error alone. -/
theorem runFunc_safe (m : Module) (i : Nat) (f : Func) (ft : FuncType)
    (args : List Val) (fuel : Nat)
    (hf : m.funcs[i]? = some f)
    (hft : m.typeAt f.tyIdx = some ft)
    (hval : checkModule m = .ok ())
    (hargs : stackTys args = ft.params.reverse) :
    runFunc m i args fuel ≠ Outcome.trap Trap.typeErr
    ∧ (∀ s', runFunc m i args fuel = .ok s' →
          stackTys s'.stack = ft.results.reverse) := by
  -- the module check's unfold: the table discipline first, the
  -- per-function fold second (the driver's two stages)
  have hv2 : checkFuncs m 0 m.funcs = .ok () := by
    rw [checkModule] at hval
    cases htab : checkTables m with
    | error e => rw [htab] at hval; simp at hval
    | ok _ => rw [htab] at hval; exact hval
  obtain ⟨ft2, hft2, hcf⟩ := checkFuncs_some m m.funcs 0 i f hv2 hf
  have hftE : some ft = some ft2 := hft.symm.trans hft2
  injection hftE with hftE2
  subst hftE2
  obtain ⟨bound, rest, hpop, hbd, hrest⟩ :=
    popTys_of_stackTys ft.params.reverse args []
      (by rw [List.append_nil]; exact hargs)
  have hrest0 : rest = [] := nil_of_stackTys_nil rest hrest
  subst hrest0
  cases hd : localsDefault? f.locals with
  | none =>
      simp only [runFunc, hf, hft, hpop, hd]
      exact ⟨by simp, fun s2 h => by simp at h⟩
  | some defaults =>
      simp only [runFunc, hf, hft, hpop, hd]
      have hdf : stackTys defaults = f.locals := localsDefault_typed f.locals defaults hd
      -- the call-typing premise, discharged from the module check
      have hcal : ∀ fn : Nat, ∀ (ft' : FuncType) (g : Func),
          m.fenv fn = some ft' → m.funcs[fn]? = some g →
          BodyTy (fnCtx m.fenv m.typeAt ft' g) [] g.body ft'.results.reverse := by
        intro fn ft' g hf hfIdx
        obtain ⟨ft2, hft2, hcf2⟩ := checkFuncs_some m m.funcs 0 fn g hv2 hfIdx
        have hf2 : m.fenv fn = m.typeAt g.tyIdx := by
          simp only [Module.fenv, hfIdx]
        rw [hf2, hft2] at hf
        simp only [Option.some.injEq] at hf
        subst hf
        exact checkFunc_sound m.fenv m.typeAt _ g hcf2
      have hbody := checkFunc_sound m.fenv m.typeAt ft f hcf
      have hloc : ∀ n t, (fnCtx m.fenv m.typeAt ft f).lty n = some t →
          tyOf ((bound.reverse ++ defaults).getD n (.i32 0)) = t := by
        intro n t hn
        exact localsMap_typed ft.params f.locals bound defaults n t hbd hdf hn
      obtain ⟨hnet, hokc, -, hretc⟩ :=
        (exec_typed m hcal fuel (fnCtx m.fenv m.typeAt ft f) rfl rfl).1
        f.body [] ft.results.reverse
        { locals := fun n => (bound.reverse ++ defaults).getD n (.i32 0), stack := []
        , mem := zeroMem, memSize := m.memMin * wasmPage }
        hbody (by simp [stackTys]) hloc
      refine ⟨?_, ?_⟩
      · intro hcon
        rw [finishRun_trap] at hcon
        apply hnet
        exact hcon
      · intro s' h
        rw [finishRun_ok] at h
        rcases h with h | ⟨s2, h, hs2⟩
        · exact (hokc s' h).1
        · have hk := (hretc s2 h).1
          cases hs2
          exact hk
