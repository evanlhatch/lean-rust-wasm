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
- `WasmCore.ExecMachine` — the executor AS a machine (wave 30's A4):
  the step/run faces as `Machines.Machine` instances (the graph of
  the landed executor's own functions), the outcome ledger's
  trichotomy face, the witness/observer disciplines applied, and the
  duel's restatement as a machine simulation (`execSelfSim` + the
  carrier-as-graph bridge).
- `WasmCore.Profile` — the deterministic profile AS DATA (D1): the ONE
  profile table (fuel on, floats off, the memory axes off, the
  simd feature axis off, lazy-translation pinned) both engines'
  configs ride — the rendered rows committed through the duel
  emitter's text lane (`gen/wasm-duel/profile.txt`), byte-tied by
  `gates gen-check`.
- `WasmCore.WitnessFragment` — the witness checker's guest-compile
  judgment (SchemaCore.Witness's follow-up order's substrate): the
  claim language's op surface judged op-by-op against the ONE op
  table's closed ctor set — every operation lowers except the NAMED
  `boolOr` gap (no `i32.or` row; the de Morgan derivation is pinned),
  and the row-CARRIER judgment (the honest verdict: outside the
  guest's scalar fragment) is stated in SchemaCore.Witness's header.

NOT here (later orders, the leftover rule): the LCNF lowering, the
executor/oracle, the guest adapter.

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import
point. Gate row: WasmCore's row in Gates.Packages' gated set — the
per-library axiom sweep + the lint driver cover every root; the
WasmCoreTests pins (the core-triple axiom self-check + the golden
byte-tie) are the standing evidence.
-/

import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module
import WasmCore.Validate
import WasmCore.Encode
import WasmCore.Decode
import WasmCore.Wat
import WasmCore.Slice
import WasmCore.Exec
import WasmCore.Profile
import WasmCore.Duel
import WasmCore.ExecMachine
import WasmCore.WitnessFragment
