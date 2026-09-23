/-
# WasmCore.Instr — the ONE instruction AST

One untyped instruction tree serves emission, validation, and (at the
later execution order) semantics — no `Sem.Instr` twin, no lowering
seam (notes/design-one-instr-ast.md §1: the emitter's output IS the
machine's input). The design doc's shape decisions applied:

- **Untyped tree, validated by a separate judgment**: instructions do
  not carry their types (the design doc keeps one plain AST; typing is
  `Validate`'s relation + checker, pattern #1 through Kit.CheckedProp).
- **The block discipline**: the structural forms (`block`/`loop`/
  `if_`) own their bodies as subterms; `br`/`brif` carry the FRAME
  DEPTH (the design doc §1: "the frame-depth discipline replaces the
  label" — legacy Sem never resolved labels syntactically; the binary
  format's labelidx IS the depth). Frames are no-result (the value-
  returning-frame extension is later-order, per the design doc R5).
- **Locals are indices** (`Nat`): the wire is index-keyed and the ONE
  AST keys on the wire's key. The design doc's name-keyed locals were
  the LEGACY emitter's convention (`l{n}`); that convention resolves at
  the LCNF-lowering order, not in this AST — the resolution seam is not
  recreated here (design doc §1: it dissolves).
- **Structured mem fields**: `offset`/`align` are fields, never baked
  into strings (the two hand-number clobber bugs of legacy lived in
  string literals — Wat.lean's header).
- **Explicit arms everywhere**: no wildcard matches over `Op`/`MemOp`
  (design doc R7 — the fail-loud discipline, compiler-enforced).

The subset is MINED from `legacy/lean/wasm-backend/WasmBackend/Wat.lean`
(the emitter AST) narrowed to the honest seed: consts, arithmetic
(the 19 `Op` ctors, verbatim), locals, direct calls, control flow,
one-page memory ops. DELIBERATE EXCLUSIONS (each lands with its first
consumer — the leftover rule): globals, `return_call`,
`call_indirect`, `memory.copy`, `select`'s typed/reference extension,
float and SIMD ops (floats are VALUE types here; float instructions
arrive with the op table), block result types, `raw` (the legacy
splice escape hatch has no consumer in a fresh core).

The five questions (notes/v3/01-core.md):

- **Root**: Universe (finite data; closed codes + total denotation —
  the size functions `iSize`/`lSize` are the structural measure every
  consumer's termination rides).
- **Carrier grade**: none here; the crossings are Encode (Codec) and
  Validate (CheckedProp).
- **Spine reading**: the AST is the registry-content the emitter folds
  and the checker walks.
- **Ladder rung**: rung 1 (closed data); the laws live at the
  consumers' rungs.
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set) + the golden byte-tie in
  WasmCoreTests.

Imports: `WasmCore.Types` only (cone-ordered).
-/

import WasmCore.Types

namespace WasmCore

/-- Memory load/store ops (mined verbatim from legacy `Wat.MemOp`).
    The `offset`/`align` operands are structured fields on `Instr.mem`. -/
inductive MemOp where
  | i32load8u | i32load | i64load
  | i32store | i64store | i32store8 | i64store8
deriving BEq, DecidableEq, Repr, Inhabited

/-- The plain (stack-machine) operations the legacy backend emits —
    binops, comparisons, conversions (mined verbatim from legacy
    `Wat.Op`, all 19 ctors). -/
inductive Op where
  | i64add | i64sub | i64mul | i64ltu | i64leu | i64eq
  | i32add | i32sub | i32mul | i32and | i32xor | i32shru | i64shru
  | i32eqz | i32eq | i32ltu | i32gtu
  | i32wrapi64 | i64extendi32u
deriving BEq, DecidableEq, Repr, Inhabited

/-- ONE instruction. Structural forms own their bodies; everything
    else is flat. `br`/`brif` carry the frame DEPTH, not a label. -/
inductive Instr where
  | i32const (n : Nat)
  | i64const (n : Nat)
  | localget (n : Nat) | localset (n : Nat) | localtee (n : Nat)
  | call (fn : Nat)
  | mem (op : MemOp) (offset : Nat) (align : Option Nat)
  | op (o : Op)
  | br (depth : Nat) | brif (depth : Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  | if_ (thenI : List Instr) (elseI : List Instr)
  | ret
  | drop
  | select
  | unreach
deriving BEq, Repr, Inhabited

/-! ## The size measure (the sizeI/sizeL pattern, 06-lean-rules §6) -/

mutual
/-- Instruction size: flat forms are leaves; a structural form's body
    counts. This is the explicit measure Validate's checker terminates
    on (kernel-transparent consumers prove against its equations). -/
def iSize : Instr → Nat
  | .i32const _ => 1
  | .i64const _ => 1
  | .localget _ => 1
  | .localset _ => 1
  | .localtee _ => 1
  | .call _ => 1
  | .mem _ _ _ => 1
  | .op _ => 1
  | .br _ => 1
  | .brif _ => 1
  | .block b => lSize b + 1
  | .loop b => lSize b + 1
  | .if_ t e => lSize t + lSize e + 1
  | .ret => 1
  | .drop => 1
  | .select => 1
  | .unreach => 1

/-- Body size (the mutual sibling). -/
def lSize : List Instr → Nat
  | [] => 0
  | i :: is => iSize i + lSize is
end

theorem iSize_pos : ∀ i : Instr, 0 < iSize i := by
  intro i
  cases i <;> simp [iSize] <;> omega

theorem lSize_cons (i : Instr) (is : List Instr) :
    lSize (i :: is) = iSize i + lSize is := rfl

end WasmCore
