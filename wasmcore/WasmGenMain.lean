/-
WasmGenMain — the `wasmgen` exe: the BINARY byte-tie's writer side.

    lake exe wasmgen

Runs `WasmCore.regen` — the ONE regen shared with `gates gen-check`
(never a second encoding) — and writes the wasm slice's artifacts
through the Kit.Emit spine:

- the TEXT lane: the WAT twin (`watEmitter`'s landed row →
  `gen/wasm-slice.wat`, its 2-line GENERATED header inline);
- the BINARY lane: the module's bytes (`wasmSliceEmitter`'s row →
  `gen/wasm-slice.wasm`) PLUS the `.hdr` sidecar carrying the same
  2-line GENERATED header in text (the magic number must lead the
  bytes — Emit.lean's header-in-binary decision).

VALIDATOR AT GENERATION: `regen` checks the module through
`WasmCore.Validate.checkModule` FIRST — an invalid module is a
generation failure (the validator's rendered Diag on stderr, exit 1),
never an artifact. Nothing is written on refusal.

Safe main: no env replay (WasmCore is core-only — no initializers, no
`@[schema]` extensions; the module fixture is a pure constant). The
returned ledger rows have NO file consumer yet — the leftover rule
(the ledger file lands when its reader does; SchemaMain's precedent).

The five questions (notes/v3/01-core.md): none of its own — the IO
shell over `WasmCore.regen` (the answers live in WasmCore.Slice). Gate
row: none — this exe is gen-check's binary-lane WRITER side, not a gate.
-/
import WasmCore

open WasmCore

def main : IO UInt32 := do
  match regen wasmSliceModule with
  | .error e =>
    IO.eprintln s!"wasmgen: REGEN FAILED — {e}"
    return 1
  | .ok (texts, bins) => do
    let items :=
      wasmSliceModule.types.length + wasmSliceModule.funcs.length
        + wasmSliceModule.exports.length
    -- The text lane (the WAT twin): the kit's shared driver loop owns
    -- the IO — the header rides the emitter's `.wat` style.
    let _textRows ← Kit.Emit.runEmitters "wasmgen"
      [(watEmitter, wasmSliceModule)]
      (fun _ f => pure { items := items, contentHash := f.contents.hash })
    -- The binary lane: the bytes + the `.hdr` sidecar — the content
    -- hash hashes the BYTES (`bytesHash`, the ledger's pinned digest).
    let _binRows ← Kit.Emit.runBinaryEmitters "wasmgen"
      [(wasmSliceEmitter, wasmSliceModule)]
      (fun _ f =>
        pure { items := items, contentHash := Kit.Emit.bytesHash f.contents })
    -- THE DUEL's lanes (WasmCore.Duel's row): the manifest (text) +
    -- the family vectors (binary, each with its sidecar). The
    -- executor-computed expectations come from `duelRows` — the SAME
    -- copy `regen` composes and the gate runs; a generation failure
    -- (an invalid family member, a non-total outcome) writes NOTHING.
    match WasmCore.Duel.duelRows with
    | .error e =>
      IO.eprintln s!"wasmgen: DUEL REGEN FAILED — {e}"
      return 1
    | .ok expects => do
      let _duelText ← Kit.Emit.runEmitters "wasmgen"
        [(WasmCore.Duel.duelEmitter, expects)]
        (fun _ f =>
          pure { items := WasmCore.Duel.duelItems
               , contentHash := f.contents.hash })
      let _duelBin ← Kit.Emit.runBinaryEmitters "wasmgen"
        [(WasmCore.Duel.duelEmitter, expects)]
        (fun _ f =>
          pure { items := WasmCore.Duel.duelItems
               , contentHash := Kit.Emit.bytesHash f.contents })
      IO.println s!"wasmgen: duel manifest + {WasmCore.Duel.duelPaths.length} \
        vector(s) written"
    IO.println s!"wasmgen: {texts.length} text + {bins.length} binary \
      artifact(s) written"
    return 0
