/-
# WasmCore.Types — the wasm value-type universe

The closed boundary universe of the wasm MVP subset WasmCore models
(15-patterns #15: a new ctor breaks every fold's exhaustiveness and the
compiler drives the extension).

The doctrine's five questions (notes/v3/01-core.md):

- **Root**: Universe (data — the closed-code side of the initial
  algebra; there is no behavior or crossing here).
- **Carrier grade**: none — this module declares no crossing. The
  crossings that consume it live in `WasmCore.Encode` (Kit.Codec, the
  wire grade) and `WasmCore.Validate` (Kit.CheckedProp, the statement
  grade).
- **Spine reading**: accumulated, then read — the type is the alphabet
  both later readers fold over (Validate's stack typing; Encode's byte
  emission).
- **Ladder rung**: rung 1 — the closed inductive makes non-wasm types
  unrepresentable; no instance, no decide, no theorem needed yet.
- **Gate row**: none at the gates yet — WasmCore is NOT in
  Gates.Packages' gated set (the axiom report has no WasmCore
  section); the WasmCoreTests pins (the core-triple axiom self-check
  + the golden byte-tie) are the standing evidence.

Consumer trail: `WasmCore.Instr`, `WasmCore.Module`,
`WasmCore.Validate`, `WasmCore.Encode` all fold over this universe.
The module is core-only (no mathlib, no Batteries — the cone rule);
it imports nothing.
-/

namespace WasmCore

/-- The wasm value types: the four numerics + the two reference types.
    Closed on purpose (15-patterns #15). -/
inductive ValType where
  | i32 | i64 | f32 | f64
  | funcref | externref
deriving BEq, DecidableEq, Repr, Inhabited

/-- A function signature: params in order, results in order. -/
structure FuncType where
  params : List ValType
  results : List ValType
deriving BEq, DecidableEq, Repr, Inhabited

end WasmCore
