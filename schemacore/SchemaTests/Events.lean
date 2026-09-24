/- # SchemaTests.Events — the event-sourcing lane's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The fixture is a SMALL ENTITY — declare (the field
list) → the delta variant → the journal → REPLAY ≡ THE DIRECT RUN (the
fusion citation exercised at the keyed face) → the witnessed journal
round-trips (the Reversible rung, live) → the codec survives the wire
(append form) → the migration gate refuses the unwitnessed. Suites:

1. `eventSourcedSpec` — the replay + the machine run + `replay_snoc` +
   the fusion's keyed face + the witness + the net-zero discipline.
2. `esCodecSpec` — the journal codec: the tag bytes in CTOR ORDER, the
   append-form round trips, the truncation/unknown-tag refusals.
3. `esMigrationSpec` — the gate: unwitnessed REFUSES (loud, named),
   witnessed replays exactly the upcast log.

Evidence, not architecture — the five-question block lives in the
modules under test (SchemaCore.Delta / SchemaCore.Event).
-/

import TestingKit.Harness
import SchemaCore

open SchemaCore TestingKit

/-! ## The fixture: a small entity -/

/-- The entity's declaration: two fields, keyed on `id`. -/
def esFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string }]

/-- The entity's row. -/
def esRow (n : UInt64) (nm : String) : RowVals esFields :=
  .cons (.u64 n) (.cons (.string nm) .nil)

/-- The base table. -/
def esRows0 : List (RowVals esFields) := [esRow 1 "ann", esRow 2 "bob"]

/-- The events: insert a row, update a row, delete a row. -/
def dIns : RowDelta esFields := .insert (esRow 3 "cat")
def dUpd : RowDelta esFields := .update (esRow 2 "bob2")
def dDel : RowDelta esFields := .remove ⟨.u64, .u64 1⟩
def esLog : List (RowDelta esFields) := [dIns, dUpd, dDel]

/-- The journal as EVENTS (the trichotomy's event face: identity +
    recorded intent). -/
def esEvents : Journal esFields :=
  [ { seq := 0, delta := dIns }
  , { seq := 1, delta := dUpd }
  , { seq := 2, delta := dDel } ]

/-- Render a table (the comparison surface — RowVals carries no BEq;
    the GADT's index makes cross-shape comparison unrepresentable). -/
def renderTable {fs : List Field} (rows : List (RowVals fs)) : String :=
  String.intercalate ";" (rows.map (Pred.renderRow fs))

/-- Render a delta (the codec comparisons' surface). -/
def renderLog {fs : List Field} : RowDelta fs → String
  | .insert r => "insert(" ++ Pred.renderRow fs r ++ ")"
  | .update r => "update(" ++ Pred.renderRow fs r ++ ")"
  | .remove k => "remove(" ++ toString k.val ++ ")"

/-- The replayed table's expectation: insert appends, update replaces
    the keyed row, remove erases it. -/
def esReplayed : List (RowVals esFields) := [esRow 2 "bob2", esRow 3 "cat"]

/-! ## Suite 1 — the replay, the machine, the fusion, the witness -/

def eventSourcedSpec : Spec :=
  Spec.ofList "the event-sourcing lane: replay ≡ run, witnesses, fusion"
    (fun _ => do
      -- the replay folds the journal to the expected table
      assert (renderTable (replay "id" esLog esRows0) == renderTable esReplayed)
        "the replay drifted"
      -- REPLAY ≡ THE DIRECT RUN (the machine assembly; replay_of_run's
      -- runtime face — the fusion citation exercised)
      assert (match (esMachine "id").run esRows0 esLog with
        | some fin => renderTable fin == renderTable esReplayed
        | none => false)
        "the machine's run is not the replay"
      -- the events replay as their deltas (the journal's projection)
      assert (renderTable (replayEvents "id" esEvents esRows0)
          == renderTable esReplayed)
        "the event-level replay drifted"
      -- replay_snoc, live
      assert (renderTable (replay "id" (esLog ++ [dIns]) esRows0)
          == renderTable (deltaApply "id" dIns (replay "id" esLog esRows0)))
        "replay_snoc drifted"
      -- the fusion, keyed face: each entry advances one tick
      -- (journal_differentiates, live at t = 1)
      assert (renderTable (runStates "id" esRows0 esLog 1)
          == renderTable
              (deltaApply "id" esLog[0] (runStates "id" esRows0 esLog 0)))
        "journal_differentiates drifted"
      -- the witness: the update records the OLD row at the matched position
      let w := witnessOf "id" dUpd esRows0
      assert (w.idx == 1
          && w.old?.any (fun o => renderTable [o] == renderTable [esRow 2 "bob"])
          && w.new?.any (fun o => renderTable [o] == renderTable [esRow 2 "bob2"]))
        "the witness drifted"
      -- the witnessed journal applies AND undoes (the Reversible rung, live)
      let W : List (WDelta esFields) := esLog.map (witnessOf "id" · esRows0)
      assert (match witnessedApply esFields W (some esRows0) with
        | some t => renderTable t == renderTable esReplayed
        | none => false)
        "the witnessed apply drifted"
      assert (match witnessedApply esFields W (some esRows0) with
        | some t =>
            match witnessedApply esFields (witnessedInv esFields W) (some t) with
            | some back => renderTable back == renderTable esRows0
            | none => false
        | none => false)
        "the witnessed inverse does not restore"
      -- NET-ZERO ≠ NOTHING HAPPENED (the trichotomy's discipline): a
      -- nonempty journal can be a net zero — the journal is the
      -- occurrences, not the diff
      assert (renderTable (journalApply "id" [.update (esRow 1 "ann")] esRows0)
          == renderTable esRows0)
        "the net-zero update drifted")
    [ ("the unwitnessed remove keeps states distinguishable",
        fun _ =>
          assert (renderTable (journalApply "x" [RowDelta.remove ⟨.u64, .u64 9⟩]
                    [UpdateItem.cxRow 5])
              != renderTable (journalApply "x" [RowDelta.remove ⟨.u64, .u64 9⟩]
                    [UpdateItem.cxRow 5, UpdateItem.cxRow 9]))
          "control fired: the remove of an ABSENT key loses information — \
            the two states land together (journal_notReversible's data)")
    , ("the witnessed inverse forgets",
        fun _ =>
          let W : List (WDelta esFields) := esLog.map (witnessOf "id" · esRows0)
          assert (match witnessedApply esFields W (some esRows0) with
            | some t =>
                match witnessedApply esFields (witnessedInv esFields W) (some t) with
                | some back => renderTable back != renderTable esRows0
                | none => true
            | none => true)
          "control fired: the witnessed inverse RESTORES the base table — \
            the Reversible rung is lawful exactly because the old row \
            was recorded")
    , ("the net-zero journal is the empty journal",
        fun _ =>
          assert (renderTable (journalApply "id" [.update (esRow 1 "ann")] esRows0)
            == "")
          "control fired: the net-zero journal is NONEMPTY — the \
            occurrences are not the diff (03 §7)")
    , ("the witness forgets the old row",
        fun _ =>
          let w := witnessOf "id" dUpd esRows0
          assert (w.old?.isNone)
          "control fired: the witness records the OLD row — that is what \
            makes the inverse lawful") ]
    4 42

/-! ## Suite 2 — the journal codec (the append-form laws, live) -/

/-- The codec fixture: the one-field schema (its own key) — the row
    codec rides `encVal`/`decVal`'s PROVED append-form law. -/
def esFs1 : List Field := [{ name := "id", ty := .u64 }]

def esRow1 (n : UInt64) : RowVals esFs1 := .cons (.u64 n) .nil

def esEncR : RowVals esFs1 → List UInt8
  | .cons v .nil => encVal .u64 v

def esDecR : List UInt8 → Option (RowVals esFs1 × List UInt8)
  | bs => (decVal .u64 bs).map fun p => (.cons p.1 .nil, p.2)

def esEncK : FieldVal → List UInt8
  | ⟨.u64, v⟩ => encVal .u64 v
  | _ => []

def esDecK : List UInt8 → Option (FieldVal × List UInt8)
  | bs => (decVal .u64 bs).map fun p => (⟨.u64, p.1⟩, p.2)

/-- The codec fixture's log: one of each ctor. -/
def esLog1 : List (RowDelta esFs1) :=
  [.insert (esRow1 7), .update (esRow1 8), .remove ⟨.u64, .u64 9⟩]

/-- The append-form round trip at one delta + suffix (the codec
    fixture's schema). -/
def decDeltaRtOk (d : RowDelta esFs1) (rest : List UInt8) : Bool :=
  match decDelta? esDecR esDecK (encDelta esEncR esEncK d ++ rest) with
  | some (d', rest') => renderLog d' == renderLog d && rest' == rest
  | none => false

def esCodecSpec : Spec :=
  Spec.ofList "the journal codec: tag bytes in ctor order + append form"
    (fun _ => do
      -- THE TAG BYTES, IN CTOR ORDER (the wire-breaking rule's pin:
      -- 0 insert / 1 update / 2 remove)
      assert (encDelta esEncR esEncK (.insert (esRow1 7)) == [0, 7])
        "the insert tag drifted"
      assert (encDelta esEncR esEncK (.update (esRow1 7)) == [1, 7])
        "the update tag drifted"
      assert (encDelta esEncR esEncK (.remove ⟨.u64, .u64 7⟩) == [2, 7])
        "the remove tag drifted"
      -- THE APPEND-FORM ROUND TRIPS, one per ctor, suffix live
      -- (decDelta?_encDelta_append's runtime face)
      assert (decDeltaRtOk (.insert (esRow1 7)) [0xFF]
          && decDeltaRtOk (.update (esRow1 8)) []
          && decDeltaRtOk (.remove ⟨.u64, .u64 9⟩) [0x00, 0x01])
        "a delta round trip drifted"
      -- THE JOURNAL ROUND TRIP, append form
      -- (decJournal?_encJournal_append's runtime face)
      assert (match decJournal? esDecR esDecK
              (encJournal esEncR esEncK esLog1 ++ [0xFF]) with
        | some (log, rest) =>
            rest == [0xFF] && log.map renderLog == esLog1.map renderLog
        | none => false)
        "the journal round trip drifted")
    [ ("an unknown tag decodes",
        fun _ =>
          assert ((decDelta? esDecR esDecK [5]).isSome)
          "control fired: the unknown tag must refuse")
    , ("a truncated journal decodes",
        fun _ =>
          -- the length prefix promises 2 events; the payload is empty
          assert ((decJournal? esDecR esDecK [0x02]).isSome)
          "control fired: the promised events are absent — truncation \
            must refuse, never short-parse")
    , ("the tag order is free",
        fun _ =>
          -- reordering the ctors is a WIRE-BREAKING change (EnumWire):
          -- the insert's tag is 0, not 1
          assert (encDelta esEncR esEncK (.insert (esRow1 7)) == [1, 7])
          "control fired: the tag bytes are in CTOR ORDER — reordering \
            the ctors breaks the wire")
    , ("the journal round trip loses the remove",
        fun _ =>
          assert (match decJournal? esDecR esDecK
                    (encJournal esEncR esEncK esLog1 ++ []) with
            | some (log, _) => log.map renderLog != esLog1.map renderLog
            | none => false)
          "control fired: every ctor's event survives the wire") ]
    4 42

/-! ## Suite 3 — the migration gate (the refusal discipline) -/

/-- The UNWITNESSED seed: the gate must refuse. -/
def esSeedUnwitnessed : MigrationSeed esFields esFields :=
  { label := "es/seed", upcast := id, witness? := none }

/-- The WITNESSED seed: the gate replays the upcast log. -/
def esSeedWitnessed : MigrationSeed esFields esFields :=
  { label := "es/seed", upcast := id, witness? := some "w1" }

def esMigrationSpec : Spec :=
  Spec.ofList "the migration gate: unwitnessed refuses, witnessed replays"
    (fun _ => do
      -- the refusal: LOUD, TOTAL, NAMING the obligation
      assert (match replayMigrated? "id" esSeedUnwitnessed esLog esRows0 with
        | .error (.unwitnessed "es/seed") => true
        | _ => false)
        "the unwitnessed refusal drifted"
      -- the acceptance: EXACTLY the replay of the upcast log — nothing
      -- else is ever applied (replayMigrated?_ok's runtime face)
      assert (match replayMigrated? "id" esSeedWitnessed esLog esRows0 with
        | .ok t => renderTable t == renderTable esReplayed
        | .error _ => false)
        "the witnessed acceptance drifted")
    [ ("the unwitnessed gate accepts",
        fun _ =>
          assert (match replayMigrated? "id" esSeedUnwitnessed esLog esRows0 with
            | .ok _ => true
            | .error _ => false)
          "control fired: an unwitnessed migration must REFUSE — the \
            events are not applied (no silent skip, no fallback)")
    , ("the witnessed gate refuses",
        fun _ =>
          assert (match replayMigrated? "id" esSeedWitnessed esLog esRows0 with
            | .error _ => true
            | .ok _ => false)
          "control fired: a witnessed migration REPLAYS — the gate is a \
            gate, not a wall")
    , ("the refusal is anonymous",
        fun _ =>
          assert (match replayMigrated? "id" esSeedUnwitnessed esLog esRows0 with
            | .error (.unwitnessed label) => label != "es/seed"
            | .ok _ => false)
          "control fired: the refusal NAMES its obligation — the label is \
            the operator-facing fault text") ]
    4 42
