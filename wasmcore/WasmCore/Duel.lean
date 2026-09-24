/-
# WasmCore.Duel — the wasm execution duel (the Lean half)

THE EXECUTION DUEL (notes/v3/03-bidirectional.md §3's differential
level; notes/v3/04-verification.md §6's tier honesty): a vector set of
(module-input, expected-output) rows over the slice module + a small
grown family. The LEAN side computes each expected output by RUNNING
the landed executor (`WasmCore.Exec.runFunc`) — the expectations are
NEVER hand-spelled; the HOST side (crates/mandate-host, the duel
runner) executes the same bytes in the real wasmtime engine and
answers agree / diverge-with-witness per row.

THE FAMILY (the op coverage — arithmetic, control flow, memory — plus
the two standing controls):

- `wasmSliceModule` — the committed slice (the seed row: `i64.const 42`).
- `arithModule` — straight-line arithmetic: `i32.mul`/`i32.add`/
  `i32.shr_u`, the `i64.extend_i32_u` seam, `i64.mul`/`i64.sub` → 42.
- `controlModule` — the loop-restart discipline (`brif 0` at the loop
  frame), accumulator locals, and the `if_`/`else` selection → 100.
- `memoryModule` — `i64.store` + `i32.store8`, the loads back, the
  extend + add → 305420151 (one page, in-bounds).
- `trapModule` — `unreachable`: the typed trap, BOTH engines (the trap
  lane's agreement row).
- `invalidModule` — the NEGATIVE CONTROL: an operand-type mismatch the
  validator refuses at generation and wasmtime's compiler refuses at
  consumption. Its refusal IS its expectation (`.refuse`) — an
  expected refusal is the negative control passing (Kit.Duel's
  consumer contract).

THE TIER HONESTY (04 §6): the duel's verdict is TESTED AGREEMENT —
`oracleSwept`, a regression surface, never a theorem over unbounded
inputs; the report's rendering says so (the host's duel runner carries
the same sentence). The verdicts are ctors (Kit.Duel.Verdict), never
strings.

THE BYTE-TIE: the vectors (each member's encoded bytes) and the
manifest ride the Kit.Emit spine — the manifest the TEXT lane
(`Kit.Duel.manifestRows`, the ONE format), the vectors the BINARY lane
(each with its `.hdr` sidecar; the host re-derives the hash tie per
vector before the engine sees a byte). `regen` below is the ONE copy
shared by the `wasmgen` writer and `gates gen-check` (Slice.regen's
discipline, duel-shaped); the VALIDATOR RUNS AT GENERATION over every
valid family member — an invalid member is a generation failure, never
an artifact (the invalid control is the one deliberate exception: its
refusal is its expectation).

The five questions (notes/v3/01-core.md):
- root: Crossing — the executor's computed outputs vs the real
  engine's, coupled through committed vectors + the shared verdict
  vocabulary (Kit.Duel).
- carrier grade: none new — the expectations are computed data; the
  honesty is the TIER (tested agreement), stated here and in the host.
- spine reading: the artifact spine — the manifest's text lane + the
  vectors' binary lane through `Kit.Emit.runEmitters`/
  `runBinaryEmitters`; `gates gen-check` byte-ties both.
- ladder rung: rung 1 — pure data + total folds; nothing here is
  proved, everything is tested (the tier note above).
- gate row: `gates gen-check`'s duel rows + `gates ownership`'s
  `duelEmitter` declaration. WasmCoreTests' duel spec pins the family's
  known answers + the negative controls.
-/

import Kit.Duel
import WasmCore.Encode
import WasmCore.Exec
import WasmCore.Module
import WasmCore.Slice
import WasmCore.Validate

namespace WasmCore.Duel

/-! ## The family — arithmetic, control flow, memory, the two controls -/

/-- The duel's fuel budget (the executor's honest data: exhaustion is
    a generation failure for the family — every member is finite). -/
def duelFuel : Nat := 5000

/-- The arithmetic row: 6·7 = 42, +8 = 50, >>3 = 6, widened, ·36 =
    216, −174 = 42. Covers `i32.mul`/`i32.add`/`i32.shr_u`,
    `i64.extend_i32_u`, `i64.mul`/`i64.sub`. -/
def arithModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    [ .i32const 6, .i32const 7, .op .i32mul
    , .i32const 8, .op .i32add
    , .i32const 3, .op .i32shru
    , .op .i64extendi32u
    , .i64const 36, .op .i64mul
    , .i64const 174, .op .i64sub ]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The control-flow row: a loop counts 5..1 into an accumulator
    (locals survive the restart; the frame-ENTRY stack does not), then
    the `if_`/`else` selects on `acc = 15` → 100. Frames are
    stack-balanced (the validator's frame discipline). -/
def controlModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i32, .i64, .i32],
    [ .i32const 5, .localset 0
    , .i64const 0, .localset 1
    , .loop [ .localget 1, .localget 0, .op .i64extendi32u, .op .i64add
            , .localset 1
            , .localget 0, .i32const 1, .op .i32sub, .localset 0
            , .localget 0, .op .i32eqz, .op .i32eqz, .brif 0 ]
    , .localget 1, .i64const 15, .op .i64eq, .localset 2
    , .localget 2, .if_ [ .i64const 100, .localset 1 ]
                        [ .i64const 200, .localset 1 ]
    , .localget 1 ]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The memory row: an `i64` and a byte stored into page 0, loaded
    back, extended, added: 0x12345678 + 255 = 305420151. The bounds
    are IN the executor (and in wasmtime); both stores are in-bounds. -/
def memoryModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    [ .i32const 16, .i64const 305419896, .mem .i64store 0 none
    , .i32const 24, .i32const 255, .mem .i32store8 0 none
    , .i32const 16, .mem .i64load 0 none
    , .i32const 24, .mem .i32load8u 0 none, .op .i64extendi32u
    , .op .i64add ]⟩]
  exports := [{ name := "answer", desc := .func 0 }]
  memMin := 1

/-- The trap row: `unreachable` after a dead value — the typed trap
    in BOTH engines (the executor answers `.trap .unreach`, wasmtime
    traps on the call). The dead `i64.const` keeps the module in the
    validator's fragment (the checker's final-stack discipline: a
    body's exit stack must match the results — the stop flag does not
    excuse it; the honest declared strictness of the seed validator). -/
def trapModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i64const 1, .unreach]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The NEGATIVE CONTROL: the operand-type mismatch (`i64.add` over an
    `i32`) — Lean's checker refuses it at generation, wasmtime's
    compiler refuses it at consumption. NOT in `duelFamily` (the
    validator-at-generation would refuse the whole regen); its
    expectation is the `.refuse` row. -/
def invalidModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i32const 1, .i64const 2, .op .i64add]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The VALID family: each member validated at generation, each
    expectation computed by the executor. -/
def duelFamily : List (String × Module) :=
  [ ("slice", wasmSliceModule)
  , ("arith", arithModule)
  , ("control", controlModule)
  , ("memory", memoryModule)
  , ("trap", trapModule) ]

/-! ## The executor's expected outputs (the Lean side's half of every row) -/

/-- The duel's value vocabulary: one rendered value (`i64:42`). -/
def valNote : Val → String
  | .i32 n => s!"i32:{n.toUInt64}"
  | .i64 n => s!"i64:{n}"

/-- The result values, comma-joined (head = top — the rendered order is
    bottom-up, the return order). -/
def resultNote : List Val → String :=
  String.intercalate "," ∘ (·.map valNote)

/-- The expectation for one valid family member — the executor's
    computed output (NEVER hand-spelled). A completed run pins its
    result values; a trap pins the trap; ANY OTHER outcome is a
    GENERATION FAILURE (the family is finite and total: a `branch`/
    `unmodeled`/`outOfFuel` answer means the family member is a
    generator bug — fail loudly, never emit an expectation). -/
def duelExpect (n : String) (m : Module) : Except String Kit.Duel.Expect :=
  match runFunc m 0 [] duelFuel with
  | .ok s => .ok (.run (resultNote s.stack))
  | .trap _ => .ok .trap
  | .branch _ _ => .error s!"duel: {n} branched past the driver — a generator bug"
  | .structural => .error s!"duel: {n} answered structural — a generator bug"
  | .unmodeled => .error s!"duel: {n} answered unmodeled — a generator bug"
  | .outOfFuel => .error s!"duel: {n} exhausted {duelFuel} fuel — a generator bug"

/-- The validator AT GENERATION over every valid family member (the
    CheckedProp discipline's driver face — an invalid member is a
    generation failure carrying the validator's rendered Diag, never
    an artifact). -/
def validateFamily : Except String Unit :=
  duelFamily.foldl (fun acc (n, m) =>
    match acc with
    | .error e => .error e
    | .ok () =>
      match checkModule m with
      | .ok () => .ok ()
      | .error e => .error s!"duel: module {n} does not validate — {ValidateError.render e}")
    (.ok ())

/-! ## The vector paths + the bytes (the binary lane) -/

/-- The duel's directory (repo-root-relative — ONE directory per
    duel, Kit.Duel's convention). -/
def duelDir : String := "gen/wasm-duel"

/-- One vector's path. -/
def duelVecName (n : String) : String := duelDir ++ "/" ++ n ++ ".wasm"

/-- The duel's vector paths, row order (the slice, the family, the
    invalid control last). -/
def duelPaths : List String :=
  ["gen/wasm-duel/slice.wasm", "gen/wasm-duel/arith.wasm",
   "gen/wasm-duel/control.wasm", "gen/wasm-duel/memory.wasm",
   "gen/wasm-duel/trap.wasm", "gen/wasm-duel/invalid.wasm"]

/-- THE one-writer discipline over the vector paths (the emitter's
    declared `binaryOutputs` — nodup in the type via this). -/
theorem duelPaths_nodup : duelPaths.Nodup := by decide

/-- The duel's rows: path + the computed expectation, family order,
    the invalid control LAST (`.refuse` — its refusal is its
    expectation). -/
def duelRows : Except String (List (String × Kit.Duel.Expect)) := do
  let _ ← validateFamily
  let valid ← duelFamily.mapM fun (n, m) =>
    (duelVecName n, ·) <$> duelExpect n m
  .ok (valid ++ [(duelVecName "invalid", .refuse)])

/-- The shape check over the computed rows: every expectation names a
    duel vector — a manifest row over an absent vector is a generator
    bug (testable; WasmCoreTests pins it `true`, the fixture pins the
    `false`). -/
def duelRowsCovered : Bool :=
  match duelRows with
  | .ok es => es.all fun (p, _) => duelPaths.contains p
  | .error _ => false

/-- The vectors: each family member's encoded bytes + the invalid
    control's bytes (the encoder is total — the control's bytes are
    well-formed wire, the VALIDATOR is what refuses them; wasmtime's
    compiler makes the same refusal the host-side control). -/
def duelVectors : List Kit.Emit.BinaryFile :=
  (duelPaths.zip (duelFamily.map (·.2) ++ [invalidModule])).map
    fun (p, m) => { path := p, contents := ByteArray.mk (encodeModule m).toArray }

/-- The duel's item count (the manifest rows + the vectors — the
    ledger's at-a-glance size). -/
def duelItems : Nat := duelPaths.length * 2

/-! ## The emitter row (the artifact spine) -/

/-- The duel's emitter: the manifest the TEXT lane
    (`Kit.Duel.manifestRows` — the ONE format, the VectorSet face
    bypassed because the expectations are computed), the vectors the
    BINARY lane. The spec is the computed expectation list — the
    writer and the gate obtain it from `duelRows` (the ONE copy; a
    generation failure writes nothing). -/
def duelEmitter : Kit.Emit.Emitter (List (String × Kit.Duel.Expect)) where
  name := "duel:wasm-exec"
  style := .hash
  specSource := "WasmCore.Duel"
  outputs := [duelDir ++ "/manifest.txt"]
  -- The vectors AND their sidecars (the binary driver writes one
  -- `.hdr` per byte file — the declaration covers BOTH writes, the
  -- ownership gate's one-writer surface; the slice emitter's
  -- precedent).
  binaryOutputs := duelPaths ++ duelPaths.map Kit.Emit.sidecarPath
  binaryOutputs_nodup := by decide
  run expects :=
    [{ path := duelDir ++ "/manifest.txt"
     , contents := Kit.Duel.manifestRows "WasmCore.Duel" expects }]
  runBinary := some fun _ => duelVectors
  rev := "wasm-duel-r1"
  reads := [`WasmCore.OpTable]

/-! ## THE regen — the writer's and the gate's ONE copy -/

/-- The regen both the `wasmgen` writer and `gates gen-check` run
    (Slice.regen's discipline, duel-shaped): the validator runs at
    generation, the expectations are the executor's computed outputs,
    and a generation failure produces NOTHING. -/
def regen : Except String (List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile) := do
  let expects ← duelRows
  .ok (duelEmitter.run expects, duelVectors)

end WasmCore.Duel
