/-
# WasmCore.Module — the module structure

The minimal module model the subset needs: types, functions, exports,
the ONE funcref table, and the one-page memory limit (`memMin = 0`
omits the memory section — the memory ops are optional surface).
Functions reference their type by INDEX (the binary format's native
reference — the type section and the function section share it); a
dangling index is a validation error (`WasmCore.Validate.checkModule`
refuses it), never an encoder guess.

THE TABLE (the indirect-call lane's discipline — `Instr.callindirect`'s
arrival): a funcref table whose ENTRIES are the module's own function
indices (`Table.init` — the active-element face, initialized at offset
0 in order; the wire encoding rides the table section 4 + the element
section 9). The size IS the entries' length — no nulls, no min/init
drift to validate. `Module.tableAt` is the executor's ONE lookup: an
index past the entries is `none` — the RUNTIME `tabOOB` trap
(`WasmCore.Exec`), never a wrong call. The table is IMMUTABLE at
runtime (no `table.set` — the exclusion holds); the guest's closures
register their callees there (`Guest.Lower.lowerFuncs`' identity
entries — table i = function i).

Deliberate exclusions (the leftover rule — each lands with its first
consumer): imports, element SEGMENT forms beyond the one active
offset-0 face, multiple tables, element/data segments for memory,
globals, start, the custom section, name sections.

The five questions (notes/v3/01-core.md):

- **Root**: Universe (finite data, closed codes).
- **Carrier grade**: none here; Encode carries the wire crossing.
- **Spine reading**: the module is the registry-content two readers
  fold: `WasmCore.Encode` (the byte face) and `WasmCore.Wat`
  (`watEmitter`, the Kit.Emit artifact-spine row over `Module` — the
  WAT text face).
- **Ladder rung**: rung 1 (closed data).
- **Gate row**: WasmCore's row in Gates.Packages' gated set (the
  per-library axiom sweep covers it) + the golden byte-tie in
  WasmCoreTests.

Consumer trail: rides `WasmCore.Types` + `WasmCore.Instr`; consumed by
`WasmCore.Validate` (the per-function judgment + the module driver)
and `WasmCore.Encode` (the byte emission). Core-only (the cone rule).
-/
module


public import WasmCore.Types
public import WasmCore.Instr


@[expose] public section
namespace WasmCore

/-- One function: its type (by index into `Module.types`), its
    declared locals (BEYOND the type's params — local i < params.length
    is param i), and its body. -/
structure Func where
  tyIdx : Nat
  locals : List ValType
  body : List Instr
deriving BEq, Repr, Inhabited

/-- The export target. The memory arm lands with its first consumer:
    the canonical-ABI adapter face — the component lane's string lift
    aliases the guest's exported linear memory (`Guest.Component`'s
    canon options name the instance's memory; the module must export
    it). One memory exists per module (`memMin`), so the index is 0
    in every honest use. -/
inductive ExportDesc where
  | func (idx : Nat)
  | memory (idx : Nat)
deriving BEq, DecidableEq, Repr, Inhabited

/-- One named export. -/
structure Export where
  name : String
  desc : ExportDesc
deriving BEq, DecidableEq, Repr, Inhabited

/-- ONE function IMPORT: the two-level wire name (`mod.name` — the
    core binary's import section entry), the declared type (by index),
    and the MODEL's provision row: the closed `Op` the executor's host
    answers with (`none` = no modeled provision — the honest ledger's
    `.unmodeled`; the HOST's real provision is the linker's, the wire
    carries none of it). The provision reuses the ONE op table
    (`semOp`) — never a parallel semantics table (07-extensibility R6).
    The IR's extern discipline (`Guest.IR.ExternSig`) is the declared
    trust boundary this models the far side of. -/
structure Import where
  mod : String
  name : String
  tyIdx : Nat
  /-- The model's provision row (the executor's extern-call answer;
      `none` = the unprovisioned model run — `.unmodeled`, never a
      wrong answer). Default `none`: every import-less module literal
      is untouched. -/
  impl : Option Op := .none
deriving BEq, Repr, Inhabited

/-- ONE funcref table: the entries are the module's own FUNCTION
    INDICES (the active-element face — initialized at offset 0 in
    order, the only shape the consumer needs). The table's size IS the
    entries' length; an access past it is the runtime `tabOOB` trap,
    never a fabricated entry. The element type is `funcref` in every
    honest use (the wire byte is the encoder's 0x70). -/
structure Table where
  /-- The initialized entries, in order: function indices. -/
  init : List Nat
deriving BEq, DecidableEq, Repr, Inhabited

/-- The module: the minimal sections. `memMin = 0` omits the memory
    section entirely (the ops that need it refuse at validation when
    there is no memory — the later memory-order owns the limit check);
    `tables = []` omits the table section (the indirect-call lane's
    validator row refuses a `callindirect` over an absent table);
    `imports = []` omits the import section (THE IMPORT FACE: the
    wasm imports-first function-index space — imported functions take
    indices 0..k-1, the local funcs shift by k; every import-less
    module literal is index-identical to the pre-import model). -/
structure Module where
  types : List FuncType
  funcs : List Func
  exports : List Export
  memMin : Nat := 0
  tables : List Table := []
  imports : List Import := []
deriving BEq, Repr, Inhabited

/-- Resolve a type index (total; `none` = dangling — validation
    refuses, the encoder is never asked to guess). -/
def Module.typeAt (m : Module) (i : Nat) : Option FuncType :=
  m.types[i]?

/-- THE IMPORT FACE's index resolution: an absolute function index
    resolves to a LOCAL func only — an index below the import count is
    an imported function (no local body; the executor's provision row
    answers it). Total; `imports = []` reduces to `m.funcs[fn]?`. -/
def Module.funcAt (m : Module) (fn : Nat) : Option Func :=
  if fn < m.imports.length then none else m.funcs[fn - m.imports.length]?

/-- The import-less reduction (every pre-import module's `funcAt` IS
    the local lookup — the no-import byte-tie's proof face). -/
theorem Module.funcAt_of_imports_nil (m : Module) (fn : Nat) (h : m.imports = []) :
    m.funcAt fn = m.funcs[fn]? := by
  rw [Module.funcAt, h]
  simp

/-- The module's call environment: function index → its resolved type
    (the imports' declared types included — the validator's call rows
    type-check against the IMPORTED signature exactly as against a
    local one; the trust boundary is type-checked, never skipped). -/
def Module.fenv (m : Module) : Nat → Option FuncType := fun fn =>
  match m.imports[fn]? with
  | some imp => m.typeAt imp.tyIdx
  | none =>
      match m.funcs[fn - m.imports.length]? with
      | some f => m.typeAt f.tyIdx
      | none => none

/-- THE TABLE's ONE lookup (the executor's indirect-call face): entry
    `i` of table 0 = the function index it names; past the entries =
    `none` (the runtime `tabOOB` trap — never a fabricated entry). -/
def Module.tableAt (m : Module) (i : Nat) : Option Nat :=
  match m.tables[0]? with
  | some t => t.init[i]?
  | none => none

end WasmCore

end -- public section

