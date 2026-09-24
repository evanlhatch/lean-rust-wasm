/-
# WasmCore.Slice — the wasm slice module (the FIRST committed binary artifact)

The worked example, promoted to the committed artifact: the tiny
validated module WasmCoreTests pins byte-exact, now emitted through the
Kit.Emit artifact spine's BINARY lane. Three landed pieces:

- `wasmSliceModule` — the module fixture (one type `() -> i64`, one
  function `i64.const 42`, exported as `"answer"`); the SAME module
  WasmCoreTests' golden vector pins, so the committed bytes have an
  independent pin outside the spine.
- `wasmSliceEmitter` — the binary emitter row (05 §2): `runBinary`
  folds `encodeModule` into `gen/wasm-slice.wasm`; the `.hdr` sidecar
  (`gen/wasm-slice.wasm.hdr`) rides the driver (Kit.Emit's binary
  discipline — the magic number leads the bytes, the 2-line GENERATED
  header lives in the sidecar; BOTH paths are declared, one-writer).
- `regen` — THE regen, shared by the writer (`wasmgen` exe) and the
  gate (`gates gen-check`): ONE copy, never two (a gate that
  re-encodes the writer would tie two encodings, not the artifact to
  the spec — GenCheck's discipline, notes/v3/09-gates-ops.md §2).

VALIDATOR AT GENERATION (the CheckedProp discipline's driver face):
`regen` checks the module through `WasmCore.Validate.checkModule`
BEFORE producing anything — an invalid module is a GENERATION
FAILURE, never an artifact. The emitter's `law` field states the
obligation; kit's `runCertified` covers the text lane only, so the
binary lane's discharge IS `regen`'s runtime check. The compile-time
`decide` pin was attempted and is NOT available: the checker's
derived list-equality `Decidable` instances do not reduce in the
kernel — the validity pin is runtime (the regen check + the test
battery), the note above is the declared boundary, never a silent
gap.

THE ROUND-TRIP BOUNDARY, HONESTLY: Encode's lane is emission-side
(`sleb` has no decoder — the declared gap in Encode.lean's header);
there is NO binary decode direction yet, so the byte-tie is the
committed artifact's discipline, not a `decode ∘ encode = id` proof.
The decode direction lands with the binary-decoder order; until then
this note is the declared hole, never a silent gap. (The WAT text
lane, by contrast, IS tied through the same regen — two faces of the
ONE module, both artifacts of one writer.)

The five questions (notes/v3/01-core.md):
- root: Crossing — the module read into exact committed bytes (+ the
  WAT text twin) through the artifact spine.
- carrier grade: the validator's bridge (Validate.lean's proved
  CheckedProp) discharged at generation; the byte-tie pins the bytes.
- spine reading: the artifact spine — Kit.Emit's binary lane
  (`runBinaryEmitters` + `tieBytes` + the `.hdr` sidecar), first
  consumer.
- ladder rung: rung 1-3 — total folds + one `decide` discharge.
- gate row: `gates gen-check`'s binary lane (the tieBytes adoption) +
  `gates ownership` (the declared set's wasm rows).

Consumer trail: rides `WasmCore.Encode` (the bytes),
`WasmCore.Validate` (the generation gate), `WasmCore.Wat` (the text
twin's emitter row), `Kit.Emit` (the spine). Core-only (the cone
rule).
-/

import Kit.Emit
import WasmCore.Encode
import WasmCore.Module
import WasmCore.Validate
import WasmCore.Wat

namespace WasmCore

/-! ## The fixture -/

/-- The wasm slice module — the worked example, promoted to the
    committed artifact: one type `() -> i64`, one function
    (`i64.const 42`), exported as `"answer"`. The SAME module
    WasmCoreTests pins byte-exact (`goldenBytes` — the committed
    artifact's independent pin). -/
def wasmSliceModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i64const 42]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The module judgment's Bool face (the driver's runtime check —
    core carries no `DecidableEq (Except …)`, and the checker's
    derived list-equality `Decidable` instances are kernel-opaque, so
    there is NO compile-time `decide` pin of the fixture's validity:
    the pin is RUNTIME — the regen check below + WasmCoreTests'
    validator battery. The honest face of the CheckedProp discipline
    here: the bridge is proved in Validate.lean; the generation-time
    discharge is this check.) -/
def moduleValid (m : Module) : Bool :=
  match checkModule m with
  | .ok () => true
  | .error _ => false

/-! ## The binary emitter row (05 §2 — the artifact spine) -/

/-- The wasm slice's BINARY emitter: `runBinary` folds `encodeModule`
    into the committed bytes. The law states the validator-at-generation
    obligation (its runtime discharge is `regen`'s check — kit's
    `runCertified` covers the text lane only); the output paths carry
    the one-writer declaration for BOTH writes — the bytes and their
    `.hdr` sidecar (nodup in the type). -/
def wasmSliceEmitter : Kit.Emit.Emitter Module where
  name := "wasmcore.slice"
  style := .wat
  specSource := "WasmCore.Module"
  outputs := []
  run := fun _ => []
  law := some fun m => moduleValid m = true
  binaryOutputs := ["gen/wasm-slice.wasm", "gen/wasm-slice.wasm.hdr"]
  runBinary := some fun m =>
    [{ path := "gen/wasm-slice.wasm"
     , contents := ByteArray.mk (encodeModule m).toArray }]
  rev := "wasm-slice-r1"
  reads := [`WasmCore.OpTable]

/-! ## THE regen — the writer's and the gate's ONE copy -/

/-- The regen both the `wasmgen` writer and `gates gen-check` run
    (never a second encoding). The validator runs AT GENERATION: an
    invalid module is a generation failure carrying the validator's
    rendered Diag, never an artifact. On success: the text lane's
    artifacts (the WAT twin, `watEmitter`'s row) and the binary lane's
    (the wasm bytes). -/
def regen (m : Module) :
    Except String (List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile) :=
  match checkModule m with
  | .error e =>
      .error s!"the module does not validate — {ValidateError.render e}"
  | .ok () =>
      .ok (watEmitter.run m, (wasmSliceEmitter.runBinary).getD (fun _ => []) m)

end WasmCore
