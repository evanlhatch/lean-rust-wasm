/-
# WasmCore.Module — the module structure

The minimal module model the subset needs: types, functions, exports,
and the one-page memory limit (`memMin = 0` omits the memory section —
the memory ops are optional surface). Functions reference their type
by INDEX (the binary format's native reference — the type section and
the function section share it); a dangling index is a validation error
(`WasmCore.Validate.checkModule` refuses it), never an encoder guess.

Deliberate exclusions (the leftover rule — each lands with its first
consumer): imports, tables, element/data segments, globals, start,
the custom section, name sections.

The five questions (notes/v3/01-core.md):

- **Root**: Universe (finite data, closed codes).
- **Carrier grade**: none here; Encode carries the wire crossing.
- **Spine reading**: the module is the registry-content two readers
  fold: `WasmCore.Encode` (the byte face) and `WasmCore.Wat`
  (`watEmitter`, the Kit.Emit artifact-spine row over `Module` — the
  WAT text face).
- **Ladder rung**: rung 1 (closed data).
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set) + the golden byte-tie in WasmCoreTests.

Consumer trail: rides `WasmCore.Types` + `WasmCore.Instr`; consumed by
`WasmCore.Validate` (the per-function judgment + the module driver)
and `WasmCore.Encode` (the byte emission). Core-only (the cone rule).
-/

import WasmCore.Types
import WasmCore.Instr

namespace WasmCore

/-- One function: its type (by index into `Module.types`), its
    declared locals (BEYOND the type's params — local i < params.length
    is param i), and its body. -/
structure Func where
  tyIdx : Nat
  locals : List ValType
  body : List Instr
deriving BEq, Repr, Inhabited

/-- The export target — the subset exports functions only. -/
inductive ExportDesc where
  | func (idx : Nat)
deriving BEq, DecidableEq, Repr, Inhabited

/-- One named export. -/
structure Export where
  name : String
  desc : ExportDesc
deriving BEq, DecidableEq, Repr, Inhabited

/-- The module: the minimal sections. `memMin = 0` omits the memory
    section entirely (the ops that need it refuse at validation when
    there is no memory — the later memory-order owns the limit check). -/
structure Module where
  types : List FuncType
  funcs : List Func
  exports : List Export
  memMin : Nat := 0
deriving BEq, Repr, Inhabited

/-- Resolve a type index (total; `none` = dangling — validation
    refuses, the encoder is never asked to guess). -/
def Module.typeAt (m : Module) (i : Nat) : Option FuncType :=
  m.types[i]?

/-- The module's call environment: function index → its resolved type. -/
def Module.fenv (m : Module) : Nat → Option FuncType := fun fn =>
  match m.funcs[fn]? with
  | some f => m.typeAt f.tyIdx
  | none => none

end WasmCore
