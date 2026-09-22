/-
# WasmBackend.SemOp — THE PER-OP SEMANTICS TABLE (the M3 unification)

Owner: this lane (M3, 2026-12). THE ONE place a per-op semantic is
read from for every consumer: one row per `Wat.Op` carrying (a) the
wasm text spelling (the renderer's `opW` row — NOT duplicated) and (b)
the Sem-level stack transform (the step function). The row's transform
is DELEGATED to `Sem.step` over the op's `Sem.Instr` row (`opInstr`) —
the flat machine's value semantics live EXACTLY ONCE, in `Sem.step`'s
arms (Sem.lean imports nothing but Init, so the table cannot live
literally inside Wat.lean next to `Op` without an import cycle; this
module is the bench beside it, importing both — the task held
`Wat.Op`'s ctors and every renderer byte-identical).

WHY THIS KILLED THE SECOND INTERPRETER: the edgepython frontend's
evaluator (EdgePython.Eval — `WEval`, ~231 lines of unproved frame
machine) had its OWN per-op arms (i64sub/i64mul/i64ltu/i64eq/i32eqz).
That evaluator is DELETED in this work. The edgepython adapter
(EdgePython.SemExec) translates the compiled programs' `.op o` through
`opInstr` — so the compiled fixtures run on the ONE machine, and a
future `Sem.Instr ↔ Wat.Instr` translation-correctness theorem reads
the SAME rows.

MODELED ROWS (the Sem fragment's op set): i64.add/sub/mul/lt_u/eq (the
edgepython compiler's arithmetic + comparisons), i32.add, i32.eq,
i32.eqz. Every other `Op` ctor is a `none` row — EXPLICIT, never a
catch-all: a new `Op` ctor breaks this match until a decision is made
(the fail-loud discipline, compiler-enforced). Filling a row = first
adding the `Sem.Instr` ctor + its step/checkStack/exec_typed arms (the
Sem.lean fragment owns the semantics); the table row then points at it.
-/

import WasmBackend.Sem
import WasmBackend.Wat

namespace WasmBackend.SemOp

open WasmBackend.Sem

/-- One semantic row: the op's wasm-text spelling + its Sem-level stack
    transform. -/
structure OpSem where
  /-- The wasm-text spelling — the renderer's row (`Wat.opW`), so the
      spelling exists exactly once. -/
  spelled : String
  /-- The Sem-level stack transform (the step function): `some vs` =
      the resulting stack (operands popped, result pushed); `none` =
      an unmodeled op or an operand-stack shape violation (a static
      type error — Sem's `underflow`). -/
  stack : List Val → Option (List Val)

/-- The op's `Sem.Instr` row: the fragment's ctor whose `step` arm IS
    the op's semantics. `none` = an unmodeled op (explicit — see the
    header). -/
def opInstr : Wat.Op → Option Sem.Instr
  | .i64add => some .i64add
  | .i64sub => some .i64sub
  | .i64mul => some .i64mul
  | .i64ltu => some .i64ltu
  | .i64eq => some .i64eq
  | .i32add => some .i32add
  | .i32eq => some .i32eq
  | .i32eqz => some .i32eqz
  -- the unmodeled rows, EXPLICIT (no catch-all — a new `Op` ctor
  -- breaks this match until a decision is made; the fail-loud
  -- discipline, compiler-enforced): the fragment's op set stops at
  -- the eight rows above. These are the comparisons beyond the
  -- edgepython surface (le/gt), the i32 arithmetic (sub/mul/and/xor/
  -- shru), the i64 shift, and the i64→i32 conversions.
  | .i64leu => none
  | .i32sub => none
  | .i32mul => none
  | .i32and => none
  | .i32xor => none
  | .i32shru => none
  | .i64shru => none
  | .i32ltu => none
  | .i32gtu => none
  | .i32wrapi64 => none
  | .i64extendi32u => none

/-- The stack transform, DELEGATED to `Sem.step` on the op's row. The
    carrier state's locals/mem are irrelevant: the fragment's ops never
    touch them (no store/load in the row set). -/
def opStack (o : Wat.Op) (stk : List Val) : Option (List Val) :=
  match opInstr o with
  | none => none
  | some i =>
      match Sem.step { locals := fun _ => .i64 0, stack := stk
                     , mem := fun _ => (0 : UInt8), memSize := 0 } i with
      | .ok s' => some s'.stack
      | .error _ => none

/-- THE TABLE: per op, the wasm text + the Sem-level stack transform. -/
def opSem (o : Wat.Op) : OpSem :=
  { spelled := Wat.opW o, stack := opStack o }

/-- The spelling column IS the renderer's row (nothing duplicated). -/
theorem opSem_spelled (o : Wat.Op) : (opSem o).spelled = Wat.opW o := rfl

/-- The index: the table's `stack` column IS `opStack`. -/
theorem opSem_stack_eq_opStack (o : Wat.Op) : (opSem o).stack = opStack o := rfl

/-! ## The per-op mechanics (the M3 pin)

For each modeled op, the table's transform on a correctly-shaped
operand stack IS the pushed result — the assertions are symbolic
(binders, not concrete values — UInt64's `<` does not reduce in the
kernel, probed 2026-12, so these are PROOFS by reduction-of-shape, not
evaluations). The delegate-through-`Sem.step` design makes them
definitional. `unmodeled` and the short-stack shapes are `none`.

BINDER CONVENTION (normalized 2026-12 from the pack's mixed order):
every statement spells the stack `[top, deeper]` = `[a, b]` with `a` =
the TOP (the SECOND-pushed operand) — the SAME binder semantics as
`Sem.step`'s own arm patterns. Arithmetic thus reads exactly as the
step arm: wasm's `x y i64.sub` (x = first-pushed = deeper = `b`, y =
second-pushed = top = `a`) computes `b - a`, and `x y i64.lt_u`
computes `b < a` (the `_u` in `lt_u` = the unsigned order). The four
`a op b` results (add/mul/eq) are commutative, so the order is
irrelevant there — the sub/lt rows are the ones the operand-order
lesson pins. `rfl`-reduction after `simp [opStack, opInstr, Sem.step]`
makes every one definitional. -/

theorem opStack_i64add (a b : UInt64) (rest : List Val) :
    opStack .i64add (.i64 a :: .i64 b :: rest) = some (.i64 (a + b) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i64sub (a b : UInt64) (rest : List Val) :
    opStack .i64sub (.i64 a :: .i64 b :: rest) = some (.i64 (b - a) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i64mul (a b : UInt64) (rest : List Val) :
    opStack .i64mul (.i64 a :: .i64 b :: rest) = some (.i64 (a * b) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i64ltu (a b : UInt64) (rest : List Val) :
    opStack .i64ltu (.i64 a :: .i64 b :: rest) = some (.i32 (if b < a then 1 else 0) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i64eq (a b : UInt64) (rest : List Val) :
    opStack .i64eq (.i64 a :: .i64 b :: rest) = some (.i32 (if a == b then 1 else 0) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i32add (a b : UInt32) (rest : List Val) :
    opStack .i32add (.i32 a :: .i32 b :: rest) = some (.i32 (a + b) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i32eq (a b : UInt32) (rest : List Val) :
    opStack .i32eq (.i32 a :: .i32 b :: rest) = some (.i32 (if a == b then 1 else 0) :: rest) := by
  simp [opStack, opInstr, Sem.step]
theorem opStack_i32eqz (a : UInt32) (rest : List Val) :
    opStack .i32eqz (.i32 a :: rest) = some (.i32 (if a == 0 then 1 else 0) :: rest) := by
  simp [opStack, opInstr, Sem.step]

/-- An UNMODELED op has no row (explicit, never a catch-all). -/
theorem opStack_unmodeled (o : Wat.Op) (stk : List Val) (h : opInstr o = none) :
    opStack o stk = none := by
  simp [opStack, h]

/-- A shape mismatch on a MERELY modeled op is `none` (the stack
    transform's only error class — Sem's `underflow`; the `trap`/
    `branch` classes belong to the memory/structural ops, none of which
    are rows). -/
theorem opStack_i64ltu_short (a : UInt64) :
    opStack .i64ltu [.i64 a] = none := by
  simp [opStack, opInstr, Sem.step]

end WasmBackend.SemOp
