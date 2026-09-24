/- # SchemaCore.Event — the journal: the event log, the replay, the
   codec, the machine, the migration seed

Owner: the event-sourcing lane agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/08-capabilities.md #7 (event sourcing —
delta variant + journal codec + replay + upcasters; the
replay/inversion/codec laws GENERATED once, cited per record) +
notes/v3/03-bidirectional.md §7 (THE TRICHOTOMY: a COMMAND is
requested intent, a DELTA is the accepted net change, an EVENT is a
RECORDED OCCURRENCE with identity + causality — never collapsed) +
notes/v3/01-core.md §2 (replay IS the Change ladder's I operator) +
the fusion bridges (`machines/Machines/Fusion.lean`: journal = D∘run,
replay = I∘journal — the additive STREAM face, LANDED and cited
below).

Provenance: mined from
`legacy/lean/schema-lang/SchemaLang/EventSourced.lean` (the canon row:
an event log = delta variant + journal codec + replay + upcasters),
ported fresh at the row layer over `SchemaCore.Delta`'s keyed
semantics:

- `Event` — the trichotomy's EVENT face: occurrence identity (`seq`,
  the log position) + the recorded intent (the delta). Not a command
  (nothing is requested — the journal records what happened), not a
  bare delta (the identity IS the replay's causal order);
- `replay` — the I operator (the fold), with `replay_snoc` (the legacy
  law) and the event-level `replayEvents`;
- `esMachine` — the event-sourced machine assembly: the machine whose
  states are keyed tables and whose every step is total (the legacy
  `esMachine`'s every-guard-true convention — the RewindableMachine
  FLAVOR; the rewind family lands with the first rewind consumer) —
  and `replay_of_run`: the run over the journal ENDS AT the replay.
- `runStates` + `journal_differentiates` + `replay_of_run` — THE
  EVENT-SOURCING FUSION, keyed-table face (the legacy §8 cluster,
  ported). THE FUSION CITATION: the landed stream bridges
  `Machines.Fusion.journal_eq_D_run` / `Fusion.replay_eq_run` prove
  journal = D∘run and replay = I∘journal at the ADDITIVE rung
  (`Kit.Additive`, delta-as-state); the keyed-table replay is the
  NONLINEAR fold of the same cluster (keyed upsert is not a group
  operation — the legacy's own note), so the two theorems below STATE
  the same bridge where the shapes meet, and the tests exercise the
  keyed face on the fixture.
- the journal codec — `encDelta`/`decDelta?`/`encJournal`/
  `decJournal?` with the APPEND-FORM laws (15-patterns #2): the tag
  byte in CTOR ORDER (reordering the ctors is a WIRE-BREAKING change —
  the EnumWire rule), the payloads self-delimiting, the journal the
  length-prefixed list over `SchemaCore.encList`/`decManyBind?`.
- the migration seed — `MigrationRefusal`/`MigrationSeed`/
  `replayMigrated?`: the replay-with-upcast shape; an UNWITNESSED
  migration REFUSES, loudly, naming its obligation; the events are NOT
  applied (the legacy's classified-refusal discipline — owner decision
  2: no silent skip, no host fallback). The `diverged`/`fuelExhausted`
  classes ride the WitnessCheck seam — not landed in this tree; they
  follow their consumer (the legacy's own W9.5 scoping). The identity
  seed is the doctrine's LOCAL MIGRATION LAW (`Kit.Migration`,
  Kit.Change) at the trivial upcaster — the hook every versioned
  migration specializes.

Deliberate exclusions (the leftover rule): the per-record derivation
surface (`@[event_sourced]` — the laws here are the generated form's
target; the attribute lands with the first schema consumer that
declares it); the rewind/undo family (the machine's step is total, so
rewind-K = the witnessed inverse fold — `witnessedReversible` in
Delta.lean is its substrate; lands with the first undo consumer);
wire-level witness bytes (Delta.lean's named exclusion).

The five questions (notes/v3/01-core.md): root = Change (01 §2) crossed
with TraceModel (01 §3) — the journal IS the differentiation of the
run, the replay IS its integration (the fusion bridges' exact claim);
carrier grade = `Machines.Machine` (the landed carrier, inherited by
citation) + the append-form codec grade; spine reading = none — the
lane rides Delta.lean's semantics + Machines.Basic's fold; ladder rung
= `replay_of_run`/`journal_differentiates` are hand theorems over the
landed fold (rung 6), the codec laws compose the element laws (the
append-form pattern's one-induction face), the migration gate is a
decidable dispatch (rung 3); gate row = SchemaTests' eventSourcedSpec
(the fusion exercise + the codec pins + the refusal teeth + the
mandatory negative controls) + the axiom report (SchemaTests.Axioms).

Core-only (imports SchemaCore.Delta/Codec + Machines.Basic — the cone
rule; Machines shares SchemaCore's cone).
-/

import SchemaCore.Delta
import SchemaCore.Codec
import Kit.Varint
import Machines.Basic

namespace SchemaCore

open Kit.Varint

/-! ## The event + the journal -/

/-- THE EVENT (03 §7's trichotomy): a RECORDED OCCURRENCE — occurrence
    identity + the intent it records. -/
structure Event (fs : List Field) where
  /-- The occurrence identity: the log position (append-only order). -/
  seq : Nat
  /-- The recorded intent: the accepted net change. -/
  delta : RowDelta fs

/-- The journal: the event log, in occurrence order (append-only). -/
abbrev Journal (fs : List Field) := List (Event fs)

/-- The journal's delta projection (what the replay folds). -/
def journalDeltas {fs : List Field} (log : Journal fs) : List (RowDelta fs) :=
  log.map (·.delta)

/-! ## The replay (the I operator) -/

/-- REPLAY — the I operator: fold the log to state (the
    materialization/snapshot-reconstruction reading; the same fold as
    `journalApply` — the name is the doctrine's reading). -/
def replay {fs : List Field} (key : String) (log : List (RowDelta fs))
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  journalApply key log rows

@[simp] theorem replay_nil {fs : List Field} (key : String)
    (rows : List (RowVals fs)) : replay key [] rows = rows := rfl

/-- THE REPLAY LAW (the legacy `replay_snoc`): replaying `log ++ [e]`
    IS one more apply after replaying `log`. -/
theorem replay_snoc {fs : List Field} (key : String) (log : List (RowDelta fs))
    (d : RowDelta fs) (rows : List (RowVals fs)) :
    replay key (log ++ [d]) rows
      = deltaApply key d (replay key log rows) :=
  journalApply_snoc key log d rows

/-- The event-level replay: the journal folds its deltas. -/
def replayEvents {fs : List Field} (key : String) (log : Journal fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  replay key (journalDeltas log) rows

/-! ## The event-sourced machine (the RewindableMachine-flavored shape) -/

/-- THE EVENT-SOURCED MACHINE: states are keyed tables, labels are the
    delta variant, EVERY step is total (the legacy `esMachine`'s
    every-guard-true convention: insert/update ARE upsert, remove
    erases). The machine whose state is the replay of its journal —
    `replay_of_run` is the tie. -/
def esMachine (key : String) {fs : List Field} :
    Machines.Machine (List (RowVals fs)) (RowDelta fs) where
  step? := fun s d => some (deltaApply key d s)

theorem esMachine_step?_eq {fs : List Field} (key : String) (d : RowDelta fs)
    (s : List (RowVals fs)) :
    (esMachine key).step? s d = some (deltaApply key d s) := rfl

/-- **REPLAY = I ∘ JOURNAL** — THE FUSION, keyed face: the event-sourced
    machine's run over the journal ENDS AT the replay (the legacy
    `replay_of_run`). Cites the landed stream bridges:
    `Machines.Fusion.replay_eq_run` proves the same integration at the
    additive rung (`replay = I ∘ journal`, riding `Machines.I_D`); this
    is the nonlinear fold's reading — keyed upsert is not additive —
    proved directly over the landed `Machine.run` fold (one induction,
    the run_cons equation). -/
theorem replay_of_run (key : String) {fs : List Field} :
    ∀ (log : List (RowDelta fs)) (s0 fin : List (RowVals fs)),
      (esMachine key).run s0 log = some fin → replay key log s0 = fin := by
  intro log
  induction log with
  | nil =>
      intro s0 fin h
      rw [Machines.Machine.run_nil] at h
      exact Option.some.inj h
  | cons d rest ih =>
      intro s0 fin h
      show replay key (d :: rest) s0 = fin
      rw [show replay key (d :: rest) s0
            = replay key rest (deltaApply key d s0) from rfl]
      exact ih _ fin h

/-- The state stream a journal run generates: the state at time t IS
    the replay of the journal's first t entries (the states ARE the
    partial integrals — snapshot = partial I; the legacy `runStates`). -/
def runStates (key : String) {fs : List Field} (s0 : List (RowVals fs))
    (log : List (RowDelta fs)) (t : Nat) : List (RowVals fs) :=
  replay key (log.take t) s0

/-- **JOURNAL = D ∘ RUN** (the fusion, keyed face): each entry's apply
    advances the state exactly one tick — the witnessed finite
    difference (`apply_eq_patchW` is the difference's DATA). Cites
    `Machines.Fusion.journal_eq_D_run` (the additive stream bridge; the
    same differentiation, one rung down the honesty ladder). -/
theorem journal_differentiates (key : String) {fs : List Field}
    (s0 : List (RowVals fs)) (log : List (RowDelta fs)) (t : Nat)
    (h : t < log.length) :
    runStates key s0 log (t + 1)
      = deltaApply key log[t] (runStates key s0 log t) := by
  show replay key (log.take (t + 1)) s0
    = deltaApply key log[t] (replay key (log.take t) s0)
  -- core's take/succ lemma, statement-identical (06 §8: no re-proofs
  -- of core's library)
  rw [List.take_succ_eq_append_getElem h, replay_snoc]

/-! ## The journal codec (the append-form laws) -/

/-- The event codec: a tag byte in CTOR ORDER (0 insert / 1 update /
    2 remove — the EnumWire wire-breaking rule: reordering the ctors
    is a WIRE-BREAKING change) followed by the self-delimiting
    payload (the legacy `encDelta`). -/
def encDelta {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) : RowDelta fs → List UInt8
  | .insert r => 0 :: encR r
  | .update r => 1 :: encR r
  | .remove k => 2 :: encK k

/-- The event decoder: the tag byte dispatches; unknown tags refuse
    (the legacy `decDelta?`). -/
def decDelta? {fs : List Field}
    (decR : List UInt8 → Option (RowVals fs × List UInt8))
    (decK : List UInt8 → Option (FieldVal × List UInt8)) :
    List UInt8 → Option (RowDelta fs × List UInt8)
  | 0 :: rest => (decR rest).map fun p => (.insert p.1, p.2)
  | 1 :: rest => (decR rest).map fun p => (.update p.1, p.2)
  | 2 :: rest => (decK rest).map fun p => (.remove p.1, p.2)
  | _ => none

/-- THE EVENT ROUND TRIP, append form: the row and key round trips
    compose through the tag dispatch (the legacy law). -/
theorem decDelta?_encDelta_append {fs : List Field}
    (encR : RowVals fs → List UInt8) (encK : FieldVal → List UInt8)
    (decR : List UInt8 → Option (RowVals fs × List UInt8))
    (decK : List UInt8 → Option (FieldVal × List UInt8))
    (hR : ∀ (r : RowVals fs) (rest : List UInt8),
      decR (encR r ++ rest) = some (r, rest))
    (hK : ∀ (k : FieldVal) (rest : List UInt8),
      decK (encK k ++ rest) = some (k, rest))
    (d : RowDelta fs) (rest : List UInt8) :
    decDelta? decR decK (encDelta encR encK d ++ rest) = some (d, rest) := by
  cases d <;> simp [encDelta, decDelta?, hR, hK]

/-- The journal codec: the length-prefixed list of events (the Codec
    combinator's shape, over `SchemaCore.encList`). -/
def encJournal {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (log : List (RowDelta fs)) : List UInt8 :=
  encList (encDelta encR encK) log

/-- The journal decoder: the varint length, then that many events
    (truncation refuses — the element decoder's `none` propagates). -/
def decJournal? {fs : List Field}
    (decR : List UInt8 → Option (RowVals fs × List UInt8))
    (decK : List UInt8 → Option (FieldVal × List UInt8)) (bs : List UInt8) :
    Option (List (RowDelta fs) × List UInt8) :=
  match decVarNat? bs with
  | some (n, rest) => decManyBind? (decDelta? decR decK) n rest
  | none => none

/-- THE JOURNAL ROUND TRIP, append form: the event log survives the
    wire — the codec law the per-record round trip cites (the legacy
    `decJournal_encJournal_append`). -/
theorem decJournal?_encJournal_append {fs : List Field}
    (encR : RowVals fs → List UInt8) (encK : FieldVal → List UInt8)
    (decR : List UInt8 → Option (RowVals fs × List UInt8))
    (decK : List UInt8 → Option (FieldVal × List UInt8))
    (hR : ∀ (r : RowVals fs) (rest : List UInt8),
      decR (encR r ++ rest) = some (r, rest))
    (hK : ∀ (k : FieldVal) (rest : List UInt8),
      decK (encK k ++ rest) = some (k, rest))
    (log : List (RowDelta fs)) (rest : List UInt8) :
    decJournal? decR decK (encJournal encR encK log ++ rest)
      = some (log, rest) := by
  unfold encJournal decJournal? encList
  rw [List.append_assoc, decVarNat?_encVarNat_append]
  exact decManyBind?_enc_append _ _
    (fun d r => decDelta?_encDelta_append encR encK decR decK hR hK d r)
    log rest

/-! ## The migration seed (the upcaster's refusal discipline) -/

/-- THE REFUSAL (the classified-refusal discipline's seed): an
    unwitnessed migration refuses, NAMING its obligation — the events
    are not applied, there is no silent skip and no fallback (the
    legacy's owner decision 2). The `diverged`/`fuelExhausted` classes
    ride the WitnessCheck seam — they follow their consumer. -/
inductive MigrationRefusal where
  | /-- The migration carries no witness: the gate refuses. -/
    unwitnessed (label : String)

deriving Repr, BEq, DecidableEq

/-- The migration seed: the upcaster + its witness slot (the honest
    minimal — the versioned envelope and the witness-certificate lane
    land with their first consumer). -/
structure MigrationSeed (fs₁ fs₂ : List Field) where
  /-- The obligation's label (the refusal names it). -/
  label : String
  /-- The upcaster: an old-schema delta becomes a new-schema delta. -/
  upcast : RowDelta fs₁ → RowDelta fs₂
  /-- The witness: `none` = unwitnessed (the gate refuses). -/
  witness? : Option String

/-- THE APPLY-GATE: replay the migrated segment ONLY under a witness.
    Upcast the committed log; an unwitnessed migration REFUSES, loudly,
    naming its obligation — the events are NOT applied. -/
def replayMigrated? {fs₁ fs₂ : List Field} (key₂ : String)
    (m : MigrationSeed fs₁ fs₂) (log : List (RowDelta fs₁))
    (state : List (RowVals fs₂)) :
    Except MigrationRefusal (List (RowVals fs₂)) :=
  match m.witness? with
  | none => .error (.unwitnessed m.label)
  | some _ => .ok (replay key₂ (log.map m.upcast) state)

/-- The refusal, pinned: an unwitnessed seed refuses with ITS label —
    before any replay (the gate's order is the discipline). -/
theorem replayMigrated?_unwitnessed {fs₁ fs₂ : List Field} (key₂ : String)
    (m : MigrationSeed fs₁ fs₂) (log : List (RowDelta fs₁))
    (state : List (RowVals fs₂)) (h : m.witness? = none) :
    replayMigrated? key₂ m log state = .error (.unwitnessed m.label) := by
  unfold replayMigrated?
  rw [h]

/-- THE ACCEPTANCE THEOREM (the soundness-cited wrapper's seed shape):
    a witnessed gate returns EXACTLY the replay of the upcast log —
    nothing else is ever applied. -/
theorem replayMigrated?_ok {fs₁ fs₂ : List Field} (key₂ : String)
    (m : MigrationSeed fs₁ fs₂) (log : List (RowDelta fs₁))
    (state : List (RowVals fs₂)) (hw : m.witness?.isSome = true) :
    replayMigrated? key₂ m log state
      = .ok (replay key₂ (log.map m.upcast) state) := by
  unfold replayMigrated?
  cases hw' : m.witness? with
  | none => rw [hw'] at hw; exact absurd hw (by simp)
  | some _ => rfl

/-- The identity upcaster is the doctrine's LOCAL MIGRATION LAW
    (`Kit.Migration.localLaw` — Kit.Change's stated equation) at the
    trivial migration: `migrate = id`, `upcast = id` — the hook every
    versioned migration specializes. -/
def idMigration (key : String) {fs : List Field} :
    Kit.Migration (S₀ := List (RowVals fs)) (Δ₀ := List (RowDelta fs))
        (S₁ := List (RowVals fs)) (Δ₁ := List (RowDelta fs))
        (journalApplicable (fs := fs) key).toComposable.toApplicable
        (journalApplicable (fs := fs) key).toComposable.toApplicable where
  migrate := id
  upcast := id
  localLaw _s _e := rfl

end SchemaCore
