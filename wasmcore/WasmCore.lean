/-
# WasmCore — the umbrella module

One import point for the library (root-module imports are NOT
re-exported — this module re-exports by importing):

- `WasmCore.Types` — the closed value-type universe + FuncType.
- `WasmCore.Instr` — the ONE instruction AST (untyped tree, structural
  forms own their bodies, frame-depth branches, index-keyed locals).
- `WasmCore.OpTable` — the ONE op table (07-extensibility R6): name,
  opcode, stack signature, sem note — one row per op ctor; the
  consumers (validator, encoder, the later renderer/executor) fold it.
- `WasmCore.Module` — the minimal module model.
- `WasmCore.Validate` — the stack-typing judgment: Kit.CheckedProp
  (relation + checker + proved bridge, both directions).
- `WasmCore.Encode` — the binary emission: Kit.Codec (LEB128 pair with
  the append-form law) + the total module encoder.
- `WasmCore.Wat` — the WAT text rendering: the total structural fold
  (the op spellings ride the ONE op table's `name` field) + the
  Kit.Emit Emitter row (`watEmitter`, the artifact spine).
- `WasmCore.Slice` — the wasm slice module: the FIRST committed binary
  artifact through the spine's binary lane (`wasmSliceEmitter` + the
  shared `regen` with the validator at generation).
- `WasmCore.Exec` — the executor over the ONE AST: the machine-int
  values, the fuel-bounded frame machine, the layered `Outcome`
  discipline (ok/branch/trap/structural/unmodeled/outOfFuel), the
  memory ops with the bounds check IN the executor, and the
  deliverable theorems (`step_preserves`, the store-bounds pair).
- `WasmCore.Duel` — the execution duel's Lean half: the vector family
  (arithmetic / control flow / memory / the trap + invalid controls),
  the executor-computed expectations, and the shared `regen` (the
  manifest's text lane + the vectors' binary lane through Kit.Duel —
  the host duel runner in crates/mandate-host is the consumer).

NOT here (later orders, the leftover rule): the LCNF lowering, the
executor/oracle, the guest adapter.

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import
point. Gate row: none at the gates yet — WasmCore is not in
Gates.Packages' gated set; the WasmCoreTests pins (the core-triple
axiom self-check + the golden byte-tie) are the standing evidence.
-/

import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module
import WasmCore.Validate
import WasmCore.Encode
import WasmCore.Wat
import WasmCore.Slice
import WasmCore.Exec
import WasmCore.Duel
