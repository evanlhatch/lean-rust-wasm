/-
# Faults.Spec — the declared faults (the host's refusal surface, as data)

The first registered faults: the HOST's model-level refusals (the mandate
host's typed-error surface — notes/v3/12-construction.md §8's discipline:
the faults are DECLARED here, the host's Rust consumes the generated enum;
never hand-written there). The `@[fault]` entries append into the lane's
extension at THIS module's elaboration; the replay is the consumers'
(`Faults.Regen` — the writer exe's and gen-check's env, the tests' pins).

The four rows map onto `crates/mandate-host`'s HostError variants — the
honest integration: HostError STAYS the structural envelope (its io/engine
surfaces are implementation plumbing, not declared faults — the judgment
recorded in the host's lib.rs); the four model-level refusals report their
allocated E-codes through the generated `FaultError`.

The allocation rows live in notes/code-registry.txt (the keys
`fault.<name>`, codes appended in the gate's replay order) — the codes'
SSOT, never this file.

Five questions (notes/v3/01-core.md): none of its own — the spec VALUES
(the answers live in Item/Alloc/Emit). Gate row: FaultsTests (the replay
pins + the curated-failure controls).
-/

import Faults.Registry

/-- THE skew tooth's fault: the bytes the host would run do not hash to the
    sidecar's declaration — the artifact in hand is not the artifact the
    toolchain committed. `content`: the caller's surface is stale; rebuild,
    never retry unchanged. -/
@[fault]
def contentHashMismatch : Faults.FaultItem where
  name := "content_hash_mismatch"
  display := "artifact content hash mismatch: the sidecar declares {declared}, the bytes compute {computed}"
  category := .content
  advice := "rebuild the artifacts (`just gen` / `just wasmgen`) and reload — the bytes in hand are not the committed ones"
  payload := [("declared", .u64), ("computed", .u64)]

/-- The persistence seam's corruption fault: a delta-log frame failed its
    check — the journal refuses, never truncates silently. `content`: the
    record's bytes are the record; restore or replay from genesis. -/
@[fault]
def journalCorrupt : Faults.FaultItem where
  name := "journal_corrupt"
  display := "journal: a delta-log frame is corrupt — recovery refused"
  category := .content
  advice := "the journal's bytes are the record — restore from the golden or replay from genesis, never truncate silently"
  payload := []

/-- THE lifecycle tooth's fault: an event the implementation was asked to
    run from the phase it is in is not a row of the model's transition table
    (`Machines.HostLifecycle`). `invariant`: a model refusal — never retry. -/
@[fault]
def lifecycleIllegalTransition : Faults.FaultItem where
  name := "lifecycle_illegal_transition"
  display := "illegal lifecycle transition: {event} from {phase} (the model: Machines.HostLifecycle)"
  category := .invariant
  advice := "a model refusal — check the transition table's rows, never retry; the host landed in Failed instead"
  payload := [("phase", .string), ("event", .string)]

/-- The guest's own bug surfacing as a runtime trap. `fatal`: the trap
    poisons the instance — inspect the module, the host refused nothing. -/
@[fault]
def wasmTrap : Faults.FaultItem where
  name := "wasm_trap"
  display := "wasm trap: {detail}"
  category := .fatal
  advice := "the trap is the guest module's own bug — inspect the module; the host refused nothing and cannot recover the instance"
  payload := [("detail", .string)]
