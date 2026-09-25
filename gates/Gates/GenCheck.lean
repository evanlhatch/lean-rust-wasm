/-
Gates.GenCheck — the byte-tie gate (`gates gen-check`).

The artifact's committed bytes vs a fresh regen — THE stripped compare:
the volatile header lines (the 2-line GENERATED block: clock, spec sha)
are exempt; the artifact BODY must tie byte-exact, and the committed
header's content-hash line must still name the fresh body's hash. The
regen is `SchemaCore.regen` — the SAME semantics the `schema` writer
runs (one copy, never two; a gate that re-encodes the writer would tie
two encodings, not the artifact to the spec).

THE BINARY LANE (Emit.lean's named follow-up, landed with the first
committed binary artifact — `gen/wasm-slice.wasm`): the same regen
semantics over `WasmCore.regen` (the writer `wasmgen`'s ONE copy; the
validator rides it — an invalid module is a regen failure, never an
artifact), compared through `Kit.Emit.tieBytes` — the kit-side binary
compare the gate ADOPTS (never re-encodes): the bytes tie EXACTLY (a
binary has no volatile region) and the committed `.hdr` sidecar must
name the fresh bytes' hash. The text lane's `tieOf` is untouched.

THE COMPONENT LANE (the re-audit's finding: the component artifacts'
byte-tie ran ONLY inside ComponentTests — outside the gates spine, a
tampered `gen/component-slice.wasm` passed every gate). The same two
loops fold the component lane's regen — `Guest.Component.regen` over
`ComponentTests.Pipeline`'s ONE pipeline copy (the writer
`componentgen`'s own; the LCNF re-run rides it — the writer and the
gate share one encoding), the text lane through `tieOf`, the binary
lane + `.hdr` sidecars through `tieBytes`.

The teeth: hand-edit the committed artifact → gen-check fails →
`just gen` restores. A gate without teeth is decoration (09).

Provenance: fresh (the gate arrives with its first emitter — the
doctrine's nothing-without-a-consumer rule; the stripped-compare
discipline is Kit.Emit's header + notes/v3/09-gates-ops.md).

The five questions (notes/v3/01-core.md):
- root: Crossing — the artifact's committed bytes vs the fresh reading.
- carrier grade: the tie law (Kit.Golden's stripped-compare shape) —
body byte-equality + the header hash naming the fresh body.
- spine reading: the artifact stage's check face over the ONE regen
(never a second encoding).
- ladder rung: n/a — the gate's teeth are the byte equality.
- gate row: the gen-check row itself (`gates gen-check`).
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore
import WasmCore
import ComponentTests.Pipeline

open Lean

namespace Gates.GenCheck

/-- The byte-tie verdict for one artifact (ctors, never strings). -/
inductive Tie where
  | tied
  | absent
  | drifted (why : String)

/-- The stripped compare for one generated file: the committed file's
    body (the 2 header lines dropped) must be byte-equal to the fresh
    body, and the committed header's content-hash line must name the
    fresh body's hash. -/
def tieOf (committed fresh : String) : Tie :=
  let lines := committed.splitOn "\n"
  match lines[1]? with
  | none => .drifted "committed file has no 2-line GENERATED header"
  | some headerLine =>
    let committedBody := String.intercalate "\n" (lines.drop 2)
    if committedBody != fresh then
      .drifted "artifact body drifted"
    else if !(headerLine.contains (toString fresh.hash)) then
      .drifted "header content hash does not name the fresh body's hash"
    else
      .tied

/-- `gates gen-check` — regen over the replayed registry, compare each
    artifact's committed bytes. Exit 1 on any drift/absence/load
    failure; the clean line names the tied artifact count. -/
unsafe def run : IO UInt32 := do
  -- The registration module's olean carries the `@[schema]` appends;
  -- withPkgEnv replays the extensions (loadExts := true) and absorbs the
  -- sysroot init + the LOAD FAILED exit (this gate's name kept in the
  -- failure line).
  let pkg : PkgSpec := { dir := "SchemaCore", srcDir := "schemacore", roots := #[`SchemaCore.Slice] }
  Gates.withPkgEnv "gen-check" pkg fun env => do
    match SchemaCore.regen env with
    | .error e =>
      IO.eprintln s!"gen-check: REGEN FAILED — {e}"
      return 1
    | .ok r => do
      let mut failed := false
      let mut tied := 0
      -- THE WASM SLICE's regen (pure, env-free — the module fixture is
      -- a constant): the writer (`wasmgen`) and the gate share this ONE
      -- regen; the validator rides it, so a regen failure here is the
      -- validator's refusal, not a gate bug.
      let mut wasmFresh :
          List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile := ([], [])
      match WasmCore.regen WasmCore.wasmSliceModule with
      | .error e =>
          IO.eprintln s!"gen-check: WASM REGEN FAILED — {e}"
          failed := true
      | .ok fb => wasmFresh := fb
      -- THE DUEL's regen (the same ONE copy the `wasmgen` writer runs;
      -- the validator + the executor's computed expectations ride it):
      -- the manifest joins the text compare, the vectors the binary
      -- loop (each vector's own `.hdr` sidecar).
      let mut duelFresh :
          List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile := ([], [])
      match WasmCore.Duel.regen with
      | .error e =>
          IO.eprintln s!"gen-check: DUEL REGEN FAILED — {e}"
          failed := true
      | .ok db => duelFresh := db
      -- THE JOURNAL DUEL's regen (env-free — a pinned-constant vector
      -- set cannot fail; SchemaCore.Emit.Journal.regen is the writer's
      -- and the gate's ONE copy, WasmCore.Duel.regen's shape): the
      -- manifest joins the text compare, the vectors the binary loop.
      let journalFresh := SchemaCore.Emit.Journal.regen
      -- THE COMPONENT LANE's regen (the same ONE pipeline the
      -- `componentgen` writer runs — ComponentTests.Pipeline, shared;
      -- the skew check rides each regen, so a regen failure here is the
      -- checker's refusal, not a gate bug): the scalar lane (the LCNF
      -- re-run's product) + the string lane (the pure-data fixture).
      let mut compFresh :
          List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile := ([], [])
      match ← ComponentTests.Pipeline.loadCoreModule with
      | .error e =>
          IO.eprintln s!"gen-check: COMPONENT PIPELINE FAILED — {e}"
          failed := true
      | .ok core => do
        match Guest.Component.regen (ComponentTests.Pipeline.scalarSpec core) with
        | .error e =>
            IO.eprintln s!"gen-check: COMPONENT REGEN FAILED — {e}"
            failed := true
        | .ok cf =>
          -- the string lane: the skew CHECK rides regen; the ROWS come
          -- from the writer's write path (Pipeline.stringRows — regen is
          -- the SCALAR emitter's, its string-spec rows name scalar paths)
          match Guest.Component.regen ComponentTests.Pipeline.stringSpec with
          | .error e =>
              IO.eprintln s!"gen-check: COMPONENT STRING REGEN FAILED — {e}"
              failed := true
          | .ok _ =>
            let sf := ComponentTests.Pipeline.stringRows
              ComponentTests.Pipeline.stringSpec
            compFresh := (cf.1 ++ sf.1, cf.2 ++ sf.2)
      for f in r.files ++ wasmFresh.1 ++ duelFresh.1 ++ compFresh.1
          ++ journalFresh.1 do
        let path : System.FilePath := f.path
        unless ← path.pathExists do
          IO.eprintln s!"gen-check: {f.path} ABSENT — run `just gen` and commit"
          failed := true
          continue
        let committed ← IO.FS.readFile path
        match tieOf committed f.contents with
        | .tied => tied := tied + 1
        | .drifted why => do
          IO.eprintln s!"gen-check: {f.path} DRIFTED ({why}) — \
            run `just gen` and commit (never hand-edit a generated file)"
          failed := true
        | .absent => pure ()
      -- THE BINARY LANE (Kit.Emit's named follow-up): the committed
      -- `.wasm` bytes vs the fresh regen — `tieBytes` IS the compare
      -- (no volatile region; the bytes tie EXACTLY) — and the committed
      -- `.hdr` sidecar must name the fresh bytes' hash (the sidecar's
      -- own hash check rides the same verdict).
      for f in wasmFresh.2 ++ duelFresh.2 ++ journalFresh.2 do
        let path : System.FilePath := f.path
        unless ← path.pathExists do
          IO.eprintln s!"gen-check: {f.path} ABSENT — run `just wasmgen` and commit"
          failed := true
          continue
        let committed ← IO.FS.readBinFile path
        let sidecar : System.FilePath := Kit.Emit.sidecarPath f.path
        unless ← sidecar.pathExists do
          IO.eprintln s!"gen-check: {sidecar} ABSENT — the binary lane's \
            header sidecar; run `just wasmgen` and commit"
          failed := true
          continue
        let sidecarText ← IO.FS.readFile sidecar
        match Kit.Emit.tieBytes sidecarText committed f.contents with
        | .tied => tied := tied + 1
        | .drifted why => do
          IO.eprintln s!"gen-check: {f.path} DRIFTED ({why}) — \
            run `just wasmgen` and commit (never hand-edit a generated file)"
          failed := true
      -- the component lane's binaries: the same tieBytes loop, the
      -- component writer's regen command named (the lanes' writers differ)
      for f in compFresh.2 do
        let path : System.FilePath := f.path
        unless ← path.pathExists do
          IO.eprintln s!"gen-check: {f.path} ABSENT — run `just componentgen` and commit"
          failed := true
          continue
        let committed ← IO.FS.readBinFile path
        let sidecar : System.FilePath := Kit.Emit.sidecarPath f.path
        unless ← sidecar.pathExists do
          IO.eprintln s!"gen-check: {sidecar} ABSENT — the component lane's \
            header sidecar; run `just componentgen` and commit"
          failed := true
          continue
        let sidecarText ← IO.FS.readFile sidecar
        match Kit.Emit.tieBytes sidecarText committed f.contents with
        | .tied => tied := tied + 1
        | .drifted why => do
          IO.eprintln s!"gen-check: {f.path} DRIFTED ({why}) — \
            run `just componentgen` and commit (never hand-edit a generated file)"
          failed := true
      if failed then return 1
      IO.println s!"gen-check: clean — {tied} artifact(s) byte-tied \
        (text + binary lanes; the duel's manifest + vectors and the \
        component lane's world text + bytes included)"
      return 0

end Gates.GenCheck
