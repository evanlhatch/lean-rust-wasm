/-
SchemaMain — the `schema` exe: the byte-tie's WRITER side.

    lake exe schema

Replays the registration module's olean (`SchemaCore.Slice`, with
extensions loaded — without the replay the registry comes back empty),
discharges the slice's obligation row (the item's field names are
nodup, at the `decidableNow` tier via Kit's backend — the run REFUSES
loudly if the discharge does not fire), then emits through the
CERTIFIED lane (the law: the registry's closed-world naming invariant;
`runCertified` is uncallable without the discharged certificate) and
writes the artifact with the kit's standard header. The gate
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

open SchemaCore

/-- The runtime replay preamble: initSearchPath + initializers +
    importModules with `loadExts := true`. -/
unsafe def loadReplayEnv : IO Lean.Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  Lean.importModules #[{ module := `SchemaCore.Slice }] {} (loadExts := true)

unsafe def main : IO UInt32 := do
  let env ← loadReplayEnv
  match SchemaCore.regen env with
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
    -- The certified write path: regen routed BOTH emitters through
    -- runCertified (the law's discharge rode regen — it ran loud on a
    -- failed one); the driver owns the IO via the kit's shared loop —
    -- each artifact under ITS emitter's style/specSource, the same
    -- hand-rolled `header ++ contents` shape runEmitters encapsulates.
    Kit.Emit.runEmitters "schema"
      [(SchemaCore.witEmitter, r.reg), (SchemaCore.Emit.Rust.rustEmitter, r.reg)]
      (fun _ f =>
        pure { items := r.reg.items.length, contentHash := f.contents.hash })
    return 0
