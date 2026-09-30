/-
SchemaMain — the `schema` exe: the byte-tie's WRITER side.

    lake exe schema

Replays the registration module's olean (`SchemaCore.Slice`, with
extensions loaded — without the replay the registry comes back empty),
discharges the slice's obligation row (the item's field names are
nodup, at the `decidableNow` tier via Kit's backend — the run REFUSES
loudly if the discharge does not fire), then emits (the naming
invariant is the registry's own nodup-in-the-type — the
inherited-correctness audit retired the vacuous certified-lane
literal) and writes the artifact with the kit's standard header. The gate
(`gates gen-check`) re-runs the SAME `SchemaCore.regen` and byte-ties
the committed artifact against it.

Unsafe: executes imported initializers (the runtime replay preamble).

The five questions (notes/v3/01-core.md): none of its own — the IO
shell over `SchemaCore.regen` (root/carrier/spine answers live in
SchemaCore.Emit). It discharges the fields-nodup obligation at
decidableNow or refuses, then writes through the certified lane. Gate
row: none — this exe is gen-check's WRITER side (the byte-tie's other
half), not a gate.
-/
import Lean
import SchemaCore
import SchemaCore.Emit.Witness
import SchemaCore.Emit.Bench

open SchemaCore

/-- The runtime replay preamble: initSearchPath + initializers +
    importModules with `loadExts := true`. -/
unsafe def loadReplayEnv : IO Lean.Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  Lean.importModules #[{ module := `SchemaCore.Slice }] {} (loadExts := true)

unsafe def main : IO UInt32 := do
  let env ← loadReplayEnv
  match ← Kit.Lane.runCoreIO env (SchemaCore.regen env) with
  | .error e =>
    IO.eprintln s!"schema: regen failed — {e}"
    return 1
  | .ok r => do
    -- The obligation: every registered item's field names are nodup —
    -- discharged at the tightest honest tier (decidableNow).
    for item in r.reg.items do
      match SchemaCore.dischargeFieldNodup item with
      | some (.decided true) =>
        IO.println s!"obligation discharged: \
          {(SchemaCore.fieldNodupObligation item).label} (decidable-now)"
      | _ =>
        IO.eprintln s!"schema: obligation NOT discharged: \
          {item.name}/fields-nodup — the backend refused (loud gap)"
        return 1
    -- The write path: regen's files ride the kit's shared loop —
    -- each artifact under ITS emitter's style/specSource, the same
    -- hand-rolled `header ++ contents` shape runEmitters encapsulates.
    -- (The returned ledger rows have NO file consumer yet — the
    -- leftover rule: the ledger lane lands when its reader does.)
    let _rows ← Kit.Emit.runEmitters "schema"
      [(SchemaCore.witEmitter, r.reg), (SchemaCore.Emit.Rust.rustEmitter, r.reg),
       -- the TYPESCRIPT lane (the SECOND CodeTarget row — the JSON
       -- interop face's artifact rides the same regen + byte-tie)
       (SchemaCore.Emit.Ts.tsEmitter, r.reg),
       (SchemaCore.Emit.Rust.commitSliceEmitter, r.reg),
       -- the FUZZ lane (wave-30 C3 — the contracts→fuzz face: the
       -- generated Arbitrary face + the boundary properties, the same
       -- regen + byte-tie)
       (SchemaCore.Emit.Fuzz.fuzzGenEmitter, r.reg),
       -- the BENCH/E2E lane (wave-30 C2 — the bench face: the codec
       -- round-trip bench + the commit-path bench + the e2e
       -- validator, the manifests the consumer contract's one copy;
       -- the same regen + byte-tie)
       (SchemaCore.Emit.Bench.benchEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    -- The WITNESS REGISTRY's write (the producer face's table — the
    -- self-check rides the emitter's run path; the spec is Unit — a
    -- pinned-constant seed registry). Its ledger rows ride the same
    -- recorded-row discipline as the certified loop's.
    let _witnessRows ← Kit.Emit.runEmitters "schema"
      [(SchemaCore.Emit.Witness.witnessRegistryEmitter, ())]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    -- The DUEL vector-set's write (Kit.Duel's convention — the duel
    -- emitter's job): the manifest rides the text lane, the vectors
    -- the binary loop (+ their .hdr sidecars, Emit.lean's binary
    -- discipline). Same GenMeta shapes — the text hash over the body,
    -- the binary hash over the bytes (`bytesHash`).
    let _duelRows ← Kit.Emit.runEmitters "schema"
      [(SchemaCore.Emit.Rust.duelEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    let _duelBinRows ← Kit.Emit.runBinaryEmitters "schema"
      [(SchemaCore.Emit.Rust.duelEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length
             , contentHash := Kit.Emit.bytesHash f.contents })
    -- The COMMIT DUEL's write (the bidirectional slice's differential —
    -- SchemaCore.Commit's vector set; the same text+binary loop shape).
    let _commitDuelRows ← Kit.Emit.runEmitters "schema"
      [(commitDuelEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    let _commitDuelBinRows ← Kit.Emit.runBinaryEmitters "schema"
      [(commitDuelEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length
             , contentHash := Kit.Emit.bytesHash f.contents })
    -- The JOURNAL DUEL's write (the Event lane's duel — the
    -- mandate-delta crate's vectors: the manifest rides the text
    -- lane, the vectors the binary loop; the SAME loop shape; the
    -- spec is Unit — a pinned-constant vector set).
    let _journalDuelRows ← Kit.Emit.runEmitters "schema"
      [(SchemaCore.Emit.Journal.journalDuelEmitter, ())]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    let _journalDuelBinRows ← Kit.Emit.runBinaryEmitters "schema"
      [(SchemaCore.Emit.Journal.journalDuelEmitter, ())]
      (fun _ f =>
        pure { items := r.reg.items.length
             , contentHash := Kit.Emit.bytesHash f.contents })
    -- The WITNESS DUEL's write (the producer face's vectors + manifest:
    -- the SAME loop shape; the registry table rode the text loop above).
    let _witnessDuelRows ← Kit.Emit.runEmitters "schema"
      [(SchemaCore.Emit.Witness.witnessDuelEmitter, ())]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    let _witnessDuelBinRows ← Kit.Emit.runBinaryEmitters "schema"
      [(SchemaCore.Emit.Witness.witnessDuelEmitter, ())]
      (fun _ f =>
        pure { items := r.reg.items.length
             , contentHash := Kit.Emit.bytesHash f.contents })
    -- The GOLDEN MODULE (the byte-tie's theorem face, 09 §2): the same
    -- regen run writes the committed goldens' Lean-side twin — the
    -- embedded bodies + the kernel-discharged tie theorems + the teeth
    -- (the pinned registry IS the live registration). One writer, one
    -- regen: the artifact bytes and the golden module move together.
    let goldens := SchemaCore.goldensBody r.reg
    Kit.Emit.writeFileCreatingDirs "schemacore/SchemaCore/Goldens.lean"
      (Kit.Emit.header .lean "schema" "SchemaCore.Slice"
        { items := r.reg.items.length, contentHash := goldens.hash }
        ++ goldens)
    IO.println "wrote schemacore/SchemaCore/Goldens.lean"
    return 0
