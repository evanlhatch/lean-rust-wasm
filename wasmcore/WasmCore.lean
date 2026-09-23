/-
# WasmCore — the umbrella module

One import point for the library (root-module imports are NOT
re-exported — this module re-exports by importing):

- `WasmCore.Types` — the closed value-type universe + FuncType.
- `WasmCore.Instr` — the ONE instruction AST (untyped tree, structural
  forms own their bodies, frame-depth branches, index-keyed locals).
- `WasmCore.Module` — the minimal module model.
- `WasmCore.Validate` — the stack-typing judgment: Kit.CheckedProp
  (relation + checker + proved bridge, both directions).
- `WasmCore.Encode` — the binary emission: Kit.Codec (LEB128 pair with
  the append-form law) + the total module encoder.

NOT here (later orders, the leftover rule): the LCNF lowering, the
executor/oracle, the guest adapter, the artifact-spine emitter.

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import
point. Gate row: none at the gates yet — WasmCore is not in
Gates.Packages' gated set; the WasmCoreTests pins (the core-triple
axiom self-check + the golden byte-tie) are the standing evidence.
-/

import WasmCore.Types
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Validate
import WasmCore.Encode
