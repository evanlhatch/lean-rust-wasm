/-
# WasmCore.OpTable — the ONE op table (notes/v3/07-extensibility.md R6)

"A row in the ONE op table (name, arity, semantics, spellings,
renderings, contracts) — expression eval, raw/compiled readings,
emission, oracle, proof are all folds of it." This module is that
table for the wasm ops: ONE match over each closed ctor universe
(`Op`, `MemOp`), one row per ctor, and every consumed facet as a
projection of the row.

The row shape (`OpRow`/`MemRow`):

- `name` — the WAT spelling (the renderer's fold; the wasm toolchain
  is the text consumer — WasmCore.Wat's boundary note).
- `opcode` — the binary encoding (the encoder's fold).
- `sig` — pops × pushes, head = top (the validator's fold; the
  FIRST pop is popped FIRST — the arity/kind discipline is the sig:
  pops.length operands, pushes.length results).
- `sem` — the execution-semantics NOTE. Honest call, named: the sem
  facet lands as a ROW FIELD now (a true prose note per row) because
  the Sem order's machine semantics has no type yet — an `Option`
  note is content, a fake step function would be a stub; when the
  Sem order lands, this field's type is upgraded in place (one
  mechanical edit per row, exhaustiveness-enforced). It is NOT a
  facet-family table: that would put "add an op" back in N places,
  the parallel-table failure R6 forbids.

Completeness authority: the table is the exhaustive match over the
closed ctor set — adding a ctor without a row is a TYPE error, and
the well-formedness pins (`opRow_wf`/`memRow_wf`) are decide over
the closed universe. The R6 acceptance: adding an op = ONE ctor in
`Instr.lean` + ONE row here; every consumer (validator, encoder,
the later renderer/executor/oracle) folds the row — no per-op hand
places anywhere else. The `Instr.lean` header is the signpost
("where ops get their meaning").

The five questions (notes/v3/01-core.md):

- **Root**: Universe (closed data; the total match is the
  completeness authority).
- **Carrier grade**: none here — plain data; the drift guards are
  theorems (rung 1).
- **Spine reading**: the registry-content every op consumer folds
  (Validate's checker, Encode's emitter, the later orders).
- **Ladder rung**: rung 1 (closed data); laws live at the consumers.
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set) + WasmCoreTests' sig/opcode pins.

Imports: `WasmCore.Types`, `WasmCore.Instr` only (cone-ordered).
-/

import WasmCore.Types
import WasmCore.Instr

namespace WasmCore

/-! ## The rows -/

/-- ONE plain-op row: every facet with a consumer (or a named later
    order) lives here — see the module header for the sem call. -/
structure OpRow where
  /-- The WAT spelling (the renderer's fold — WasmCore.Wat). -/
  name : String
  /-- The binary opcode byte(s) — a list because prefixed opcodes
      (e.g. `0xFC`-space) are multi-byte. -/
  opcode : List UInt8
  /-- pops × pushes, head = top: the FIRST pop is popped FIRST.
      The arity/kind discipline (comparisons yield i32; conversions
      widen/narrow) is this field's shape. -/
  sig : List ValType × List ValType
  /-- The execution-semantics note (the Sem order's slot — see the
      module header). -/
  sem : Option String

/-- ONE mem-op row (same discipline; mem ops add the memarg's
    elided-default alignment and are single-byte). -/
structure MemRow where
  /-- The WAT spelling (the renderer's fold — WasmCore.Wat). -/
  name : String
  /-- The binary opcode byte. -/
  opcode : UInt8
  /-- The natural alignment (log2) the text format elides; the
      binary format carries the alignment explicitly. -/
  alignDefault : Nat
  /-- pops × pushes (the value sits on top of the address for
      stores; loads only push). -/
  sig : List ValType × List ValType
  /-- The execution-semantics note (the Sem order's slot). -/
  sem : Option String

/-! ## THE table (one match per closed universe, one row per ctor) -/

/-- THE op table: adding an op edits ONE row here (07-extensibility
    R6) — the sig, opcode, name, and sem note of every consumer is
    this row's projection. Row order follows `Op`'s ctor order. -/
def opRow : Op → OpRow
  | .i64add => ⟨"i64.add", [0x7C], ([.i64, .i64], [.i64]), some "pop b, a; push a + b mod 2^64"⟩
  | .i64sub => ⟨"i64.sub", [0x7D], ([.i64, .i64], [.i64]), some "pop b, a; push a - b mod 2^64"⟩
  | .i64mul => ⟨"i64.mul", [0x7E], ([.i64, .i64], [.i64]), some "pop b, a; push a * b mod 2^64"⟩
  | .i64ltu => ⟨"i64.lt_u", [0x54], ([.i64, .i64], [.i32]), some "pop b, a; push (a < b, unsigned) as i32"⟩
  | .i64leu => ⟨"i64.le_u", [0x58], ([.i64, .i64], [.i32]), some "pop b, a; push (a ≤ b, unsigned) as i32"⟩
  | .i64eq => ⟨"i64.eq", [0x51], ([.i64, .i64], [.i32]), some "pop b, a; push (a = b) as i32"⟩
  | .i32add => ⟨"i32.add", [0x6A], ([.i32, .i32], [.i32]), some "pop b, a; push a + b mod 2^32"⟩
  | .i32sub => ⟨"i32.sub", [0x6B], ([.i32, .i32], [.i32]), some "pop b, a; push a - b mod 2^32"⟩
  | .i32mul => ⟨"i32.mul", [0x6C], ([.i32, .i32], [.i32]), some "pop b, a; push a * b mod 2^32"⟩
  | .i32and => ⟨"i32.and", [0x71], ([.i32, .i32], [.i32]), some "pop b, a; push a && b (bitwise)"⟩
  | .i32xor => ⟨"i32.xor", [0x73], ([.i32, .i32], [.i32]), some "pop b, a; push a xor b (bitwise)"⟩
  | .i32shru => ⟨"i32.shr_u", [0x76], ([.i32, .i32], [.i32]), some "pop b, a; push a >> (b mod 2^32), logical"⟩
  | .i64shru => ⟨"i64.shr_u", [0x88], ([.i64, .i64], [.i64]), some "pop b, a; push a >> (b mod 2^64), logical"⟩
  | .i32eqz => ⟨"i32.eqz", [0x45], ([.i32], [.i32]), some "pop a; push (a = 0) as i32"⟩
  | .i32eq => ⟨"i32.eq", [0x46], ([.i32, .i32], [.i32]), some "pop b, a; push (a = b) as i32"⟩
  | .i32ltu => ⟨"i32.lt_u", [0x49], ([.i32, .i32], [.i32]), some "pop b, a; push (a < b, unsigned) as i32"⟩
  | .i32gtu => ⟨"i32.gt_u", [0x4B], ([.i32, .i32], [.i32]), some "pop b, a; push (a > b, unsigned) as i32"⟩
  | .i32wrapi64 => ⟨"i32.wrap_i64", [0xA7], ([.i64], [.i32]), some "pop a; push a mod 2^32"⟩
  | .i64extendi32u => ⟨"i64.extend_i32_u", [0xAD], ([.i32], [.i64]), some "pop a; push a zero-extended to 64 bits"⟩

/-- THE mem-op table (same discipline). -/
def memRow : MemOp → MemRow
  | .i32load8u => ⟨"i32.load8_u", 0x2D, 0, ([.i32], [.i32]),
      some "pop a; push the zero-extended byte at ea = a + offset (trap if out of bounds)"⟩
  | .i32load => ⟨"i32.load", 0x28, 2, ([.i32], [.i32]),
      some "pop a; push the 32-bit value at ea = a + offset (trap if out of bounds)"⟩
  | .i64load => ⟨"i64.load", 0x29, 3, ([.i32], [.i64]),
      some "pop a; push the 64-bit value at ea = a + offset (trap if out of bounds)"⟩
  | .i32store => ⟨"i32.store", 0x36, 2, ([.i32, .i32], []),
      some "pop a (address), v (value); store v's 32 bits at ea = a + offset (trap if out of bounds)"⟩
  | .i64store => ⟨"i64.store", 0x37, 3, ([.i64, .i32], []),
      some "pop a (address), v (value); store v's 64 bits at ea = a + offset (trap if out of bounds)"⟩
  | .i32store8 => ⟨"i32.store8", 0x3A, 0, ([.i32, .i32], []),
      some "pop a (address), v (value); store v's low 8 bits at ea = a + offset (trap if out of bounds)"⟩
  | .i64store8 => ⟨"i64.store8", 0x3B, 0, ([.i64, .i32], []),
      some "pop a (address), v (value); store v's low 8 bits at ea = a + offset (trap if out of bounds)"⟩

/-! ## The R6 pins (decide over the closed universe) -/

/-- THE R6 acceptance pin: every ctor's row is present and
    well-formed (a real spelling, a real opcode). Adding an op
    without its row is a type error at `opRow` (the exhaustive
    match); a hollow row (empty name/opcode) fails here. -/
theorem opRow_wf : ∀ o : Op, (opRow o).name ≠ "" ∧ (opRow o).opcode ≠ [] := by
  intro o
  cases o <;> decide

/-- The mem rows' well-formedness pin (same decide). -/
theorem memRow_wf : ∀ m : MemOp,
    (memRow m).name ≠ "" ∧ (memRow m).sig ≠ ([], []) := by
  intro m
  cases m <;> decide

/-! ## The per-facet projections (what the consumers fold) -/

/-- The WAT spelling (the renderer facet). -/
def opName (o : Op) : String := (opRow o).name

/-- The binary opcode (the encoder facet). -/
def opOpcode (o : Op) : List UInt8 := (opRow o).opcode

/-- The stack signature — pops × pushes, head = top (the validator
    facet; rfl-eliminable per ctor: `opSig .i32add = ([.i32, .i32],
    [.i32])` by `rfl`). -/
def opSig (o : Op) : List ValType × List ValType := (opRow o).sig

/-- `opSig`'s pops — the projection the checker and the relation ride
    (rfl-eliminable: `opPop .i32add = [.i32, .i32]` by `rfl`). -/
def opPop (o : Op) : List ValType := (opSig o).1

/-- `opSig`'s pushes (same discipline). -/
def opPush (o : Op) : List ValType := (opSig o).2

/-- The WAT spelling (the renderer facet, mem ops). -/
def memName (m : MemOp) : String := (memRow m).name

/-- The binary opcode byte (the encoder facet, mem ops). -/
def memOpcode (m : MemOp) : UInt8 := (memRow m).opcode

/-- The memarg's elided-default alignment (the encoder facet). -/
def memAlignDefault (m : MemOp) : Nat := (memRow m).alignDefault

/-- The stack signature (the validator facet, mem ops). -/
def memSig (m : MemOp) : List ValType × List ValType := (memRow m).sig

/-- `memSig`'s pops (same discipline). -/
def memPop (m : MemOp) : List ValType := (memSig m).1

/-- `memSig`'s pushes (same discipline). -/
def memPush (m : MemOp) : List ValType := (memSig m).2

end WasmCore
