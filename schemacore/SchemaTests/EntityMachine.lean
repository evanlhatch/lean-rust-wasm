/-
# SchemaTests.EntityMachine — the entity-machine preset's end-to-end suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The worked example: an order-flavored record (a u64
status column + a declared key) → `schema_entity_machine` derives THE
MACHINE (the `machine!` entourage, emitted), the keyed transitions
(the update lane's deltas on the state column), the legality (the
journal antijoin), the obligations (the Prop-indexed rows), and the
preservation citation. Suites:

1. `entityMachineSpec` — the generated machine exists + the battery
   runs GREEN (deadlock-freedom / guard-coverage / non-vacuity, all
   `.proved` by construction), the journal is legal + replays, the
   obligations all discharge, the code tie holds.
2. The negative controls — the illegal journal REFUSES with the named
   diagnostic (the antijoin isolates it, `EM`-coded), the refused decl
   (a non-u64 state column) does NOT discharge, and the vacuous
   default invariant is honestly REFUTED by the battery.

The preset's limits (the hand-written-reason check): what the preset
REFUSES is pinned below — a state column that is not `u64` (the code
discipline), an undeclared endpoint (the closed world), a duplicate
transition name (one Label ctor per name). What it does NOT express:
a machine whose discipline exceeds the preset (the legacy
OrderMachine precedent — the stray-state exclusion invariant, the
hand rank) stays HAND-BUILT WITH A WRITTEN REASON — the tree's
instance is `MachinesTests.Main`'s `m3i` block; the preset's default
`Inv := True` is reported by the battery's non-vacuity row honestly
(`ticketMachine` below).

Evidence, not architecture — the five-question block lives in the
module under test (SchemaCore.EntityMachine).
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.EntityMachine

open SchemaCore TestingKit

/-! ## The worked example: the order lifecycle -/

/- The order-flavored entity: a keyed record (id) with a u64 status
column; five states in code order, with `void` the DECLARED state the
lifecycle never occupies — the invariant excludes it (the battery's
non-vacuity has something to see; the legacy OrderMachine `stray`
precedent, preset-sized). The recovery edge (`reopen`) keeps the
terminal state off the deadlock sweep's refutation. -/
schema_entity_machine orderMachine for Order where
  states: [draft, placed, shipped, delivered, void]
  fields: [{ name := "id", ty := .u64 }, { name := "status", ty := .u64 }]
  column: status
  key: id
  Inv: fun s => s ≠ .void
  initial: draft
  transition: place (draft → placed)
  transition: ship (placed → shipped)
  transition: deliver (shipped → delivered)
  transition: reopen (delivered → draft)

/-- THE GENERATED MACHINE EXISTS: the table lookup IS the machine's
    `step?` (the generated tie, cited — never re-proved). -/
theorem orderTie (e : orderMachine.Label) (s : orderMachine.State) :
    orderMachineTableStep? e s = Machines.MachineWithInv.step? orderMachine s e :=
  orderMachineTableStep?_eq_step? e s

/-- The generated table, pinned in values (label-major, code order). -/
theorem orderTrans_pin :
    orderMachineTrans
      = [(orderMachine.Label.place, .draft, .placed),
         (orderMachine.Label.ship, .placed, .shipped),
         (orderMachine.Label.deliver, .shipped, .delivered),
         (orderMachine.Label.reopen, .delivered, .draft)] := by rfl

/-- THE BATTERY RUNS GREEN, all three rows `.proved` by construction:
    the reachable fragment never wedges, every event fires somewhere,
    and the invariant excludes the declared-but-unoccupied `void`. -/
theorem orderBattery_proved :
    orderMachine.battery .draft 10
      = [("deadlock-freedom", .proved),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .proved)] := by rfl

/-- The generic table-honesty law, INSTANTIATED by citation (the
    command emitted `rfl` against the defining fold). -/
theorem orderTrans_honest_cited :
    ∀ e ∈ orderMachineTrans,
      Machines.MachineWithInv.step? orderMachine e.2.1 e.1 = some e.2.2 :=
  orderMachineTrans_honest

/-- THE CODE TIE: the declared edge table IS the generated machine's
    table, under the code bridge — the journal face and the machine
    face are the SAME table. -/
theorem orderEdges_generated_pin :
    orderMachineEdges
      = [("place", 0, 1), ("ship", 1, 2), ("deliver", 2, 3), ("reopen", 3, 0)] := by
  rw [orderMachineEdges_generated]
  decide

/-! ## The legality: the journal antijoin + replay -/

/-- The legal journal: the full lifecycle's deltas. -/
def orderJournalOk : List (String × UInt64 × UInt64) :=
  [("place", 0, 1), ("ship", 1, 2), ("deliver", 2, 3), ("reopen", 3, 0)]

/-- The journal legality check (the antijoin is empty). -/
theorem orderJournal_legal : orderMachineLegalJournal orderJournalOk = true := rfl

/-- Legality at the machine's face: the run accepts. -/
theorem orderLegalFrom_pin :
    orderMachineLegalFrom .draft [.place, .ship, .deliver, .reopen] = true
    ∧ orderMachineLegalFrom .draft [.ship] = false := by decide

/-- Replay integrates the legal journal. -/
theorem orderReplay_pin : orderMachineReplay 0 orderJournalOk = some 0 := rfl

/-- THE REPLAY LAW, cited at the instance: legality + chaining ⇒ the
    journal replays to a final state (proved once in
    `replay_of_legalJournal`; the generated theorem instantiates it
    with the decided determinacy premise). -/
theorem orderReplay_ok_cited :
    ∃ fin, orderMachineReplay 0 orderJournalOk = some fin :=
  orderMachineReplay_ok 0 orderJournalOk rfl ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩⟩

/-! ## The obligations: the Prop-indexed rows all discharge -/

/-- The generic fires law, INSTANTIATED by citation: the `place`
    transition's keyed update fires on its from-row. -/
theorem orderPlace_fires_law :
    (EntityClaim.fires orderMachineDecl orderMachineFields
      (⟨"place", "draft", "placed"⟩ : EntityTransition) 0).holds = true :=
  fires_of_transition (by rfl) (by rfl) (by rfl) (by decide) (by decide)

/-- The generic moves law, INSTANTIATED by citation: the `place`
    transition's keyed update moves the state column 0 → 1. -/
theorem orderPlace_moves_law :
    (EntityClaim.moves orderMachineDecl orderMachineFields
      (⟨"place", "draft", "placed"⟩ : EntityTransition) 0 1).holds = true :=
  moves_of_transition (by rfl) (by rfl) (by rfl) (by decide) (by decide)

/-- All nine obligation rows (the table's WF + four transitions'
    fires/moves) discharge to `.decided true` — the decidableNow
    backend, decided not assumed. -/
theorem orderObligations_discharge :
    orderMachineObligations.all
      (fun r => r.discharge = some (Kit.Evidence.decided true)) = true := by
  decide

/-- The invariant's preservation, realized by the CITED generic
    theorem (`MachineWithInv.step?_preserves` — proved once). -/
example :
    ∀ (s : orderMachine.State) (i : orderMachine.Label) (s' : orderMachine.State),
      Machines.MachineWithInv.step? orderMachine s i = some s' →
      orderMachine.inv s → orderMachine.inv s' :=
  orderMachinePreserves

/- The generated tie is CORE-TRIPLE-clean: its own proof is the
    kernel's `cases <;> rfl` (the generated DecidableEq's rewrites ride
    propext — the axiom gate's allowed triple). -/
/-- info: 'orderMachineTableStep?_eq_step?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms orderMachineTableStep?_eq_step?

/- The replay law's instance rides the core triple only (the generic
    laws' simp-cited core lemmas — no new trust base). -/
/-- info: 'orderMachineReplay_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orderMachineReplay_ok

/- The preservation citation rides propext only (it IS the cited
    theorem's proof object). -/
/-- info: 'orderMachinePreserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms orderMachinePreserves

/-! ## The negative controls (15-patterns #5) -/

/-- THE ILLEGAL JOURNAL REFUSES WITH THE NAMED DIAGNOSTIC: the
    antijoin ISOLATES the illegal delta as data (the closed-world
    refusal's payload — `("ship", 0, 2)` fires from `placed`, not
    `draft`), and the journal is refused. -/
theorem orderAntijoin_isolates :
    orderMachineAntijoin ([("ship", 0, 2)] ++ orderJournalOk)
      = [("ship", 0, 2)] := rfl

theorem orderJournal_illegal :
    orderMachineLegalJournal [("ship", 0, 2)] = false := rfl

/-- Replay is the audit: the broken journal does NOT replay. -/
theorem orderReplay_broken :
    orderMachineReplay 0 [("ship", 0, 2)] = none := rfl

/- THE REFUSED DECL: the preset's state-column gate — a record whose
`status` column is a STRING (the wire carries strings, not state
codes) is REFUSED: the keyed updates are `none`, the WF Diag envelope
carries the named `EM0001` diagnostic (the closed-world refusal: the
u64 columns enumerated + the did-you-mean), and the obligation rows do
NOT discharge (the loud gap). -/

schema_entity_machine ghostMachine for Ghost where
  states: [drafted]
  fields: [{ name := "status", ty := .string }]
  column: status
  initial: drafted
  transition: noop (drafted → drafted)

set_option maxRecDepth 8000 in
theorem ghostUpdates_refused : ghostMachineUpdates = none := rfl

theorem ghostDiags_named :
    ghostMachineDiags.length = 1
    ∧ ghostMachineDiags.head!.code.code = "EM0001"
    ∧ ghostMachineDiags.head!.got = some "status" := by decide

/-- The refused decl's obligation rows do NOT discharge — the loud
    gap, never a laundered pass (the conditional fire-theorem's
    antecedent is false here, so it stays honest). -/
theorem ghostObligations_gap :
    ghostMachineObligations.all (fun r => r.discharge = none) = true := by
  decide

/- THE VACUOUS DEFAULT: the preset's invariant clause defaults to the
    trivial one (the closed enum IS the invariant) — and the battery
    honestly REFUTES the non-vacuity row (the author does not get a
    silent pass), plus the terminal state wedges the deadlock sweep. -/
schema_entity_machine ticketMachine for Ticket where
  states: [active, closed]
  fields: [{ name := "status", ty := .u64 }]
  column: status
  initial: active
  transition: close (active → closed)

theorem ticketBattery_control :
    ticketMachine.battery .active 6
      = [("deadlock-freedom", .refuted (.wedged .closed)),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .refuted .vacuous)] := by rfl

/- THE PRESET'S CURATED FAILURES (the closed-world elaboration gates) —
the teeth: undeclared endpoints + duplicate transition names, each
with the valid space enumerated (the ONE did-you-mean engine). -/

/-- error: schema_entity_machine `oopsMachine`: transition `pay`: `draff` is not a declared state — did you mean: draft? -/
#guard_msgs in
schema_entity_machine oopsMachine for Oops where
  states: [draft, placed]
  fields: [{ name := "status", ty := .u64 }]
  column: status
  initial: draft
  transition: pay (draft → draff)

/-- error: schema_entity_machine `oopsMachine`: duplicate transition name `pay` — the events are the Label constructors (one ctor per name) -/
#guard_msgs in
schema_entity_machine oopsMachine for Oops where
  states: [draft, placed]
  fields: [{ name := "status", ty := .u64 }]
  column: status
  initial: draft
  transition: pay (draft → placed)
  transition: pay (placed → draft)

/-- error: schema_entity_machine `oopsMachine`: unknown clause `evnt:` — legal clauses: `states:`, `fields:`, `column:`, `key:`, `Inv:`, `initial:`, `transition:` — did you mean: Inv? -/
#guard_msgs in
schema_entity_machine oopsMachine for Oops where
  states: [draft]
  fields: [{ name := "status", ty := .u64 }]
  column: status
  evnt: nothing

/-- error: schema_entity_machine `oopsMachine`: missing `initial:` clause — the lifecycle's start state -/
#guard_msgs in
schema_entity_machine oopsMachine for Oops where
  states: [draft]
  fields: [{ name := "status", ty := .u64 }]
  column: status
  transition: pay (draft → draft)

/-! ## The suite -/

/-- The preset's end-to-end: declare → the machine exists → the
    battery runs green → the illegal transition refuses with the named
    diagnostic. The controls: the refused decl's gap + the illegal
    journal's teeth must FIRE (the vacuity tripwire). -/
def entityMachineSpec : Spec :=
  Spec.ofList "the preset's generated surface is honest end-to-end"
    (fun _ =>
      if orderMachineLegalJournal orderJournalOk = true
        && orderMachineReplay 0 orderJournalOk = some 0
        && (orderMachineDiags.isEmpty)
      then .ok ()
      else .error "the legal journal must pass, replay, and leave the WF empty")
    [ ("control: the antijoin blunted (the illegal journal passes)",
        fun _ =>
          assert (orderMachineLegalJournal [("ship", 0, 2)] = true)
            ("control fired: the illegal journal was refused — the antijoin " ++
              "isolated it (the closed world has teeth)"))
    , ("control: the refused decl's WF row discharges",
        fun _ =>
          assert ((ghostMachineObligations.map (·.discharge)).all (·.isSome))
            ("control fired: the refused decl's rows do NOT discharge — " ++
              "the loud gap is loud"))
    , ("control: the battery's teeth blunted (the broken machine passes)",
        fun _ =>
          let v : CheckResult := match ticketMachine.battery .active 6 with
            | [("deadlock-freedom", .proved), ("guard-coverage", .proved),
               ("invariant-non-vacuity", .proved)] => .ok ()
            | _ => .error ("control fired: the battery refuted the broken machine " ++
              "(the wedged terminal + the vacuous default were seen)")
          v) ]
    4 42
