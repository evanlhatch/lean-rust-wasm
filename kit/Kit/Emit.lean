/-
# Kit.Emit — the emitter spine

The emitter-plugin model (15-patterns #10): ONE parsed spec, MANY
emitter plugins; each is a PURE TOTAL function from spec to files with
its declared outputs (nodup IN THE TYPE — the v3 upgrade: a colliding
`outputs` list fails to elaborate, there is no runtime rejection path);
the DRIVER owns IO (`runEmitters`); the artifact's header is the
GENERATED block whose content hash is the byte-tie anchor (the
byte-tie strips the header and hashes the content — ANY metadata is
safe; the header = information, the byte-tie = the content).

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/Emit/Core.lean` — the header
discipline, the plugin structure, the certified lane, the driver loop.
Deliberately excluded (no consumer in this landing; each lives at its
own layer, not core): name mangling (target-specific — one module per
TARGET), the JSON manifest builders, and the driver's git/clock
metadata assembly (tree-specific pathspecs — the driver's `mkGm`
callback supplies GenMeta; the pure core stays IO-free except at the
write).

THE BINARY LANE (the byte-valued artifacts: wasm modules, vortex
files, codec byte-vectors, oracle manifests). SHAPE DECISION: a
PARALLEL `BinaryFile`, not a `String ⊕ ByteArray` sum on `contents` —
the sum fights the text discipline (every existing String emitter
literal, here and in the consumer packages, would stop elaborating);
the text lane is untouched and the two shapes share ONE discipline:
the same one-writer nodup, the same law field, the same driver fold.
HEADER-IN-BINARY DECISION: NO inline text header, ever — the magic
number must lead the bytes (wasm's `\0asm`, the vortex magic); the
same 2-line GENERATED header rides a committed `.hdr` SIDECAR next to
each binary artifact. The byte-tie compare for binaries (`tieBytes`)
lives HERE (kit-side) so the gen-check gate ADOPTS it rather than
re-encoding it — the gate's text `tieOf` is untouched; wiring the
sidecar check into Gates.GenCheck is the named follow-up for when the
first binary artifact is committed through `just gen`.

The hash is core's `String.hash` (deterministic, 64-bit, zero code) —
NOT a crypto digest (the store's job); this one is the artifact's
self-description ("which spec state am I").

THE LEDGER (provenance, notes/v3/09-gates-ops.md §4 — the write-path
extension): every artifact a driver writes gets a `Kit.Ledger.LedgerRow`
RECORDED BY THE DRIVER FOLD ITSELF — the rows cannot drift from what
was written, because they are computed in the same loop from the same
`GenMeta`. The demand set's honest face at this generic layer: the
emitter DECLARES its collection dependencies (`reads` — the
registries/extensions it folds AS A SET, whose growth invalidates) and
its own code identity (`rev` — a closure has no hashable face, the
declaration IS the record) plus the obligation labels it attests
(`attests`); all three are defaulted fields, so every existing emitter
literal compiles unchanged. The row-level face (`demand.rows`, the
exact spec rows) is populated by the emitters that can name their rows
— the fold's reads at the emitter's layer. The drivers RETURN the rows
(`runEmitters* : … → IO (List LedgerRow)`); the per-package driver
owns the ledger FILE — `writeLedger` canonicalizes (sorted by path,
the snapshot discipline) and rewrites through tmp+rename: ONE WRITER,
atomic; `Kit.Ledger.selfStable` is the hand-edit detection face.
Consumers of the file (gates/inspector) read it, never re-derive it;
the committed ledger file lands when the first driver wiring writes it
(the byte-tie wave) — until then `Kit.Ledger.checkHeader` is the pure
header↔ledger agreement check its gate consumes.

Core-only.

The five questions (notes/v3/01-core.md):
- root: Crossing — the artifact spine: a spec read into files (the
  target grammar's text).
- carrier grade: the emitter's law field — a correspondence instance
  cited per emitter (or an honest header note why not); the content
  hash is the byte-tie anchor.
- spine reading: THE spine — Registry → Interpretation → artifact
  (01 §5: an emitter IS an interpretation); the driver owns IO.
- ladder rung: the fold machinery is structural/total; the laws live
  at the emitters that instantiate it.
- gate row: gen-check (Gates.GenCheck) — the byte-tie row over the
  generated artifacts (SchemaCore's emitter is the first consumer).
-/

import Lean
import TestingKit.Lcg
import Kit.Ledger

namespace Kit.Emit

/-! ## The generated-file header -/

/-- Comment prefix per target: Lean/SQL `--`, Rust/WIT `//`,
    YAML/Python `#`, WAT `;;`. -/
inductive CommentStyle where
  | lean | doubleSlash | hash | wat

def CommentStyle.prefix : CommentStyle → String
  | .lean => "-- "
  | .doubleSlash => "// "
  | .hash => "# "
  | .wat => ";; "

def CommentStyle.line (s : CommentStyle) (text : String) : String :=
  s.prefix ++ text

/-- The generation metadata — assembled by the DRIVER (the only IO
    point: the clock + git); the emitters stay pure. -/
structure GenMeta where
  /-- The regen's wall-clock (ISO-ish, `YYYY-MM-DDTHH:MMZ`). -/
  time : String := "-"
  /-- The spec source's git short sha + the dirty marker (`+` = the
      working copy drifted past the sha). -/
  specSha : String := "unknown"
  /-- The registered item count (the spec's size, at a glance). -/
  items : Nat := 0
  /-- `String.hash` over the artifact's body (the header excluded) —
      the content's self-verification seed. -/
  contentHash : UInt64 := 0

/-- The generated-file header: TWO lines, dense metadata. `tool` names
    the emitting package, `specSource` the spec module. (TRAP honored:
    the binder cannot be named `meta` — a Lean keyword.) -/
def header (style : CommentStyle) (tool specSource : String) (gm : GenMeta) : String :=
  CommentStyle.line style
    (s!"GENERATED by {tool} (lean-{Lean.versionString}) at {gm.time} — DO NOT EDIT") ++ "\n"
    ++ CommentStyle.line style
      (s!"spec {gm.specSha} | {specSource} | {gm.items} item(s) | "
        ++ s!"content hash {gm.contentHash} | regen: just gen; drift fails CI")
    ++ "\n"

/-- One generated artifact: repo-root-relative path + content (header
    prepended by the driver, not by the emitter). -/
structure GeneratedFile where
  path : String
  contents : String

/-! ## The binary lane's data — the byte-valued artifacts (declared
    BEFORE the emitter plugin: the plugin's optional binary fields
    reference them) -/

/-- One binary generated artifact: repo-root-relative path + raw bytes
    (wasm modules, vortex files, codec byte-vectors, oracle manifests).
    The PARALLEL of `GeneratedFile`, not a sum — the module header
    names the decision. -/
structure BinaryFile where
  path : String
  contents : ByteArray

/-- The binary content hash: the bytes folded through the LCG — the
    byte-valued twin of TestingKit.Golden's digest discipline (the ONE
    recurrence, `TestingKit.lcg`'s; never a hand-copied constant table).
    Same bytes → same hash, always. -/
def bytesHash (bs : ByteArray) : UInt64 :=
  bs.toList.foldl (fun h b => TestingKit.lcg (h + b.toUInt64))
    1442695040888963407

/-- The sidecar path: the binary artifact's header file. The
    header-in-binary DECISION in its one line: the magic number leads
    the bytes, so the 2-line GENERATED header rides `<path>.hdr` — a
    committed TEXT artifact under the same byte-tie discipline. -/
def sidecarPath (path : String) : String := path ++ ".hdr"

/-- The binary lane's byte-tie verdict (ctors, never strings — 04 §6).
    `tied` = the committed bytes ARE the fresh bytes and the sidecar
    names them; `drifted` carries the why. -/
inductive ByteTie where
  | tied
  | drifted (why : String)

/-- The binary stripped compare — the gen-check gate's adoption path
    for the binary lane (the gate calls this; it never re-encodes it).
    A binary has NO volatile region (the header lives in the sidecar):
    the committed bytes must equal the fresh bytes EXACTLY, and the
    committed sidecar's text must name the fresh bytes' hash. -/
def tieBytes (committedSidecar : String) (committed fresh : ByteArray) : ByteTie :=
  if committed != fresh then .drifted "artifact bytes drifted"
  else if !(committedSidecar.contains (toString (bytesHash fresh))) then
    .drifted "sidecar content hash does not name the fresh bytes' hash"
  else
    .tied

/-! ## The emitter plugin — outputs nodup IN THE TYPE -/

/-- An emitter plugin: one language target. Pure and total — `run` is
    a fold over the spec into files; the driver writes. The declared
    output paths carry their uniqueness AS A PROOF FIELD (the
    one-writer discipline, per emitter): a duplicate-path literal fails
    to elaborate. -/
structure Emitter (Spec : Type) where
  /-- Plugin name. -/
  name : String
  /-- Comment prefix for the generated header. -/
  style : CommentStyle
  /-- The spec module the artifacts derive from (audit provenance). -/
  specSource : String
  /-- Declared output paths, repo-root-relative. -/
  outputs : List String
  /-- THE one-writer discipline, in the type: no emitter declares the
      same output path twice. Default `by decide` over concrete lists. -/
  outputs_nodup : outputs.Nodup := by decide
  /-- Fold the spec into files. Pure and deterministic (tested). -/
  run : Spec → List GeneratedFile
  /-- OPTIONAL emission law. When `some L`, the driver SHOULD discharge
      `L spec` over the concrete spec and emit via `runCertified` — the
      artifact is unemittable without the discharged certificate.
      Defaults to `none` so plain `Emitter` literals compile unchanged. -/
  law : Option (Spec → Prop) := none
  /-- OPTIONAL binary lane: fold the spec into byte files (wasm
      modules, vortex files, codec byte-vectors, oracle manifests).
      Defaults to `none` = text-only (every existing emitter literal
      compiles unchanged). The law field covers BOTH lanes — one
      emitter, one law, whatever it emits. -/
  runBinary : Option (Spec → List BinaryFile) := none
  /-- The declared binary output paths (the one-writer audit surface
      for the binary lane; empty for text-only emitters). Text and
      binary outputs share ONE path namespace — no two lanes may write
      one path. -/
  binaryOutputs : List String := []
  /-- THE one-writer discipline for the binary lane, in the type (same
      shape as `outputs_nodup`). -/
  binaryOutputs_nodup : binaryOutputs.Nodup := by decide
  /-- The COLLECTION dependencies (09 §4's demand-set correction): the
      registries/extensions the fold reads AS A SET — a fold over a
      registry depends on its contents-as-a-set, not just the rows it
      returned, so the collection's GROWTH invalidates the artifacts
      (`Ledger.forward_growthInvalidates` is that tooth). Empty default:
      every existing emitter literal compiles unchanged. (Lean.Name
      QUALIFIED: unqualified `Name` here auto-bound an implicit type
      variable — no `open Lean` in this module — so the field could
      never hold a real name; the wasm slice's binary row was the first
      literal to populate it and caught the latent bug.) -/
  reads : List Lean.Name := []
  /-- The emitter's own revision: the code identity of the fold (a
      closure has no hashable face — the declaration IS the record).
      An emitter edit that can move artifacts bumps this, or the
      ledger's invalidation under-reports. -/
  rev : String := "-"
  /-- The obligation labels the emitter attests (the ledger row's
      forward face for the gates' audit). -/
  attests : List String := []

/-- The certificate an emitter demands over a concrete spec: `some L`
    requires the discharged `L spec`; `none` is trivially certified. -/
def Emitter.Cert (e : Emitter Spec) (spec : Spec) : Prop :=
  match e.law with
  | some L => L spec
  | none => True

/-- Proof-carrying emission: the certified lane. Plain `run` stays
    available (backward compatibility); certified drivers call here
    with the discharged certificate. -/
def Emitter.runCertified (e : Emitter Spec) (spec : Spec) (_cert : e.Cert spec) :
    List GeneratedFile := e.run spec

/-- Cross-emitter one-writer audit, data-level (the per-emitter nodup
    is in the type; the CROSS-emitter disjointness is a registry-level
    check — a `true` verdict is the discharge): no two emitters in the
    list declare the same output path. -/
def outputsDisjoint (es : List (Emitter Spec)) : Bool :=
  ((es.flatMap (·.outputs)) ++ (es.flatMap (·.binaryOutputs))).Nodup

/-! ## The driver's write path -/

/-! ## The ledger row the write path records -/

/-- The ledger row for one written artifact (09 §4): path + emitter +
    the DECLARED demand (the collection face `reads`, the code identity
    `rev`) + the content hash (the SAME `GenMeta` value the header
    names — the agreement is by construction, checked by
    `Kit.Ledger.checkHeader`) + the attested obligation labels. The
    row-level demand face (`demand.rows`, the exact spec rows) is the
    emitter's layer to name — the generic driver cannot see the fold's
    per-row reads; an emitter that can name them populates its own
    rows (the queued SchemaCore wiring does). -/
def ledgerRowOf {Spec : Type} (e : Emitter Spec) (gm : GenMeta)
    (path : String) : Ledger.LedgerRow :=
  { path := path
    emitter := e.name
    demand := { rows := []
              , collections := e.reads
              , emitterRev := e.rev }
    contentHash := gm.contentHash
    obligations := e.attests }

/-- Create the parent directories of `path` (all generated paths are
    slash-separated, so the drop-last computation always names a real
    directory). -/
def createParentDirs (path : System.FilePath) : IO Unit :=
  let dir := String.intercalate "/" ((path.toString.splitOn "/").dropLast)
  IO.FS.createDirAll dir

/-- Write one generated file, creating parent directories first. -/
def writeFileCreatingDirs (path : System.FilePath) (contents : String) : IO Unit := do
  createParentDirs path
  IO.FS.writeFile path contents

/-- Write one binary generated file, creating parent directories first. -/
def writeBinaryFileCreatingDirs (path : System.FilePath) (contents : ByteArray) : IO Unit := do
  createParentDirs path
  IO.FS.writeBinFile path contents

/-- The shared driver loop: for each (emitter, spec) job, run the
    emitter, prepend the header, and write each generated file,
    RECORDING each artifact's ledger row (the demand set from the
    emitter's declarations, the hash from the same GenMeta the header
    got — the rows cannot drift from the write). `tool` = the emitting
    package name. `mkGm` gives the driver control over per-file GenMeta
    (the clock + git + content hash — the ONLY IO point; the emitters
    stay pure). The RETURN is the recorded rows (the caller — the
    per-package driver — owns the ledger file via `writeLedger`). -/
def runEmitters {Spec : Type} (tool : String)
    (jobs : List (Emitter Spec × Spec))
    (mkGm : Emitter Spec → GeneratedFile → IO GenMeta) : IO (List Ledger.LedgerRow) := do
  let mut rows : List Ledger.LedgerRow := []
  for (e, spec) in jobs do
    for f in e.run spec do
      let gm ← mkGm e f
      writeFileCreatingDirs f.path (header e.style tool e.specSource gm ++ f.contents)
      rows := ledgerRowOf e gm f.path :: rows
      IO.println s!"wrote {f.path}"
  pure rows.reverse

/-- The binary driver loop: for each (emitter, spec) job, run the
    emitter's binary lane (if declared) and write each byte file PLUS
    its `.hdr` sidecar (the same 2-line GENERATED header, text),
    RECORDING BOTH rows. `mkGm` supplies the GenMeta per binary file —
    the content hash hashes the BYTES (`bytesHash`, or the ledger's
    pinned digest). The sidecar's row carries the SAME hash: the
    sidecar's content IS the pointer to the bytes' hash (the agreement
    check reads consistently). -/
def runBinaryEmitters {Spec : Type} (tool : String)
    (jobs : List (Emitter Spec × Spec))
    (mkGm : Emitter Spec → BinaryFile → IO GenMeta) : IO (List Ledger.LedgerRow) := do
  let mut rows : List Ledger.LedgerRow := []
  for (e, spec) in jobs do
    match e.runBinary with
    | none => pure ()
    | some run =>
      for f in run spec do
        let gm ← mkGm e f
        writeBinaryFileCreatingDirs f.path f.contents
        writeFileCreatingDirs (sidecarPath f.path) (header .lean tool e.specSource gm)
        rows := ledgerRowOf e gm (sidecarPath f.path)
          :: ledgerRowOf e gm f.path :: rows
        IO.println s!"wrote {f.path} (+ {sidecarPath f.path})"
  pure rows.reverse

/-- The both-lanes driver: one (emitter, spec) job list, BOTH write
    paths — the text loop then the binary loop. The duel vector-sets'
    shape (manifest text + vector bytes) is the first consumer; the
    per-lane `mkGm` callbacks stay separate (the hash's carrier
    differs: text body vs bytes). Returns BOTH lanes' recorded rows
    (text lane first, then binary). -/
def runEmittersAll {Spec : Type} (tool : String)
    (jobs : List (Emitter Spec × Spec))
    (mkGmText : Emitter Spec → GeneratedFile → IO GenMeta)
    (mkGmBinary : Emitter Spec → BinaryFile → IO GenMeta) : IO (List Ledger.LedgerRow) := do
  let textRows ← runEmitters tool jobs mkGmText
  let binRows ← runBinaryEmitters tool jobs mkGmBinary
  pure (textRows ++ binRows)

/-- THE LEDGER FILE's one-writer face: rewrite from the emitted set —
    canonicalized (sorted by path; `Kit.Ledger.wf` also refuses
    duplicate paths, so a cross-emitter collision fails the ledger's
    own parse) and written atomically (tmp + rename — a reader never
    sees the half-written file). The committed ledger's bytes are the
    snapshot discipline's: `Kit.Ledger.selfStable` must hold on them
    (a hand-edited ledger fails its own stability check). -/
def writeLedger (path : String) (rows : List Ledger.LedgerRow) : IO Unit := do
  let canon := (rows.toArray.qsort (fun a b => a.path <= b.path)).toList
  createParentDirs path
  IO.FS.writeFile (path ++ ".tmp") (Kit.Ledger.print canon)
  IO.FS.rename (path ++ ".tmp") path

end Kit.Emit
