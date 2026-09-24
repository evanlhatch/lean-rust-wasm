/-
# Machines.Dsl — the `machine!` authoring surface (15-patterns #9)

One declaration generates THE ENTOURAGE: the state enum + the event
Label inductive + the EventSpec family + the `MachineWithInv` assembly
+ the transition table computed from `step?` + the table↔step tie
theorem + the `DecidablePred` instance + the conformance-battery
registration. The generated surface IS the law-carrying surface —
nothing hand-written sits between the clauses and the battery.

Provenance: mined from `legacy/lean/Machines/Machines/Dsl.lean` (the
proven entourage), ported fresh over the LANDED substrate (`Events`'s
`MachineWithInv` — the macro is the seam both `Events.lean` and
`Testing.lean` name; the safety-PO default lands HERE, per their named
exclusions).

## The clause surface

```lean
machine! lamp where
  states: [off, on, broke]              -- the state enum (generated)
  Inv: fun s => s ≠ .broke              -- the invariant (mandatory)
  event: switchOn  guard: (fun s => s = .off) action: (fun _ _ => .on)
  event: switchOff guard: (fun s => s ≠ .off) action: (fun _ _ => .off)
  event: ???      guard: … action: … safety: (by …)   -- optional PO slot
```

generates (names namespaced under the machine, the table stack
concatenated per 12 §5's convention):

- `lamp.State` — the state inductive (`Repr`, `BEq`, `DecidableEq`),
- `lamp.Label` — one ctor per `event:`, `lamp.spec : lamp.Label →
  EventSpec lamp.State Inv` — each event carries its safety PO
  (constructor-argument discipline, `Events.lean`; omitted POs default
  to `machine_safety` below),
- `lamp : MachineWithInv lamp.State lamp.Label` (reducible — the
  projections must elaborate in instance search),
- `lamp.labels` + `lamp.labels_complete` — the label enumeration and
  its PROOF (the battery's totality premise, discharged here),
- `lampStates` — the state enumeration (the battery's sweep space),
- `lampTrans` — the transition table, COMPUTED from `step?` over
  labels × states (label-major) so table and guards cannot drift,
- `lampTableStep?` — the table as a lookup (the emitter-facing
  structural reading), keys compared by DECIDABLE equality,
- `lampTableStep?_eq_step?` — THE TIE: over the generated state enum
  the lookup IS `step?` (the state type IS the enumeration, so the
  `cases` exhausts — a stronger tie than the legacy's membership-
  premise form; the proof is `cases <;> rfl`, zero axioms),
- `instance : DecidablePred lamp.inv` — via `inferInstanceAs` (the
  invariant must be instance-synthesizable: equalities, comparisons,
  ∧/→ over decidables — NOT a match on the state),
- `lamp.battery init fuel` — the conformance-battery registration:
  `Machines.Testing.battery` over the generated enumerations with the
  generated completeness proof — the battery's first-class consumer.

## The curated failures (15-patterns #16)

The clause list is a CLOSED WORLD. An unknown clause (`evnt:`) reaches
the ELABORATOR via the low-priority catch-all and is rejected with the
legal-clause enumeration + the ONE did-you-mean engine
(`TextKit.suggestSuffix`). Duplicates and absences are rejected with
the cardinality errors. THE LIMIT (do not re-pay): `Inv:` is TERM-LED —
a typo'd clause AFTER it can be swallowed by term juxtaposition (the
legacy's documented limit); the catch-all is exact for typos before the
first term-led clause.

## Macro traps respected (the audit's list)

- COLON-SUFFIXED keyword atoms (`"states:"`, `"guard:"`, …) — the bare
  spellings would pollute the global token table and break
  struct-instance syntax package-wide.
- `mkIdentFrom` anchors every generated name to the USE site (hygiene).
- Match arms bind DOTTED (`.ctor`) — a bare ident binds a variable and
  every later arm becomes a redundant alternative.
- Positional `(⟨…⟩ : T)` construction, never struct-instance quotations
  inside command-elab bodies.

## Named exclusions (the leftover rule — each lands with its consumer)

- NO payload-carrying events (`send (v : α)`) — the Label enumeration
  has no finite form; lands with the first payload consumer (the
  legacy's sampled battery).
- NO parameterized machines (`machine! m (n : Nat) where …`) — the
  current consumers are parameter-free.
- NO entourage unexpanders — pp-only display sugar; lands when a
  consumer reads generated names in goals/errors (the legacy's
  motivation was error display at scale).
- NO `rank:`/rewind acyclicity clause — no in-tree consumer yet.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Testing
import Lean
import TextKit.Suggest

namespace Machines.Dsl

open Lean Lean.Parser.Command
open Lean.Elab.Command (elabCommand CommandElabM)

/-- The safety-PO DEFAULT (the Events.lean named exclusion's discharge:
    an omitted `safety:` becomes this block). intros the event's goal
    shape `∀ s h, Inv s → Inv (action s h)`, normalizes with
    `simp_all`, then closes the arithmetic/decidable residue with
    `omega`/`decide`/`trivial`. When none close the goal, the error
    surfaces AT THE EVENT SITE — supply `safety: (by …)` with the real
    proof. The author-facing vocabulary is: guard, action, invariant,
    and (when needed) one named tactic block. -/
macro "machine_safety" : tactic =>
  `(tactic| (intro s h hs; simp_all <;> (first | omega | decide | trivial)))

/-! ## The clause kit -/

declare_syntax_cat machineClause

/-- The machine's state enumeration — a non-empty list LITERAL of
    state names; the state inductive is GENERATED from it. -/
syntax (name := machineStatesClause) "states:" "[" ident,* "]" : machineClause

/-- The machine's invariant (mandatory). -/
syntax (name := machineInvClause) "Inv:" term : machineClause

/-- One event clause: name, decidable guard, action, optional safety
    PO (defaulting to `machine_safety`). -/
syntax (name := machineEventClause) "event:" ident
  "guard:" term "action:" term ("safety:" term)? : machineClause

/-- The unknown-clause catch-all (the clause-kit discipline): low
    priority, so the named clauses win; any other well-formed
    `<typo>: <term>` parses and is rejected at ELABORATION with the
    legal-clause enumeration + did-you-mean (the curated error, not a
    bare parse error). See the module header for the term-led limit. -/
syntax (name := machineUnknownClause) (priority := low) ident " : " term : machineClause

/-- The unknown-clause rejection: the error ENUMERATES the legal
    clauses (the closed-world discipline — the valid space, not a
    heuristic) and appends the ONE did-you-mean suffix
    (`TextKit.suggestSuffix` — one engine, one format tree-wide). -/
def clauseError (got : String) (legal : List String) : CommandElabM Unit :=
  let valid := legal.map (fun l => s!"`{l}:`")
  throwError
    s!"machine!: unknown clause `{got}:` — legal clauses: " ++
    s!"{String.intercalate ", " valid}{TextKit.suggestSuffix got legal}"

/-- Generate a `MachineWithInv` + its entourage from the clause data.
    See the module header for the full generated surface. -/
syntax (name := machineCmd) "machine!" ident "where" machineClause* : command

open Lean.Parser.Term in
def elabMachineImpl (stx : Syntax) : Lean.Elab.Command.CommandElabM Unit := do
  -- stx = [machine!, name, where, clausesNode] — the clauses arrive in
  -- SOURCE ORDER (the events' order is the Label-ctor order). The sweep
  -- dispatches on the clause KIND, enforcing the cardinalities.
  let name : TSyntax `ident := ⟨stx[1]!⟩
  let mut states : Option (Array Syntax) := none
  let mut invStx? : Option Syntax := none
  let mut evs : Array Syntax := #[]
  for c in stx[3]!.getArgs do
    match c.getKind with
    | ``machineStatesClause =>
        if states.isSome then
          Lean.throwErrorAt c "machine!: duplicate `states:` clause — at most one"
        states := some c[2]!.getSepArgs
    | ``machineInvClause =>
        if invStx?.isSome then
          Lean.throwErrorAt c "machine!: duplicate `Inv:` clause — at most one"
        invStx? := some c[1]!
    | ``machineEventClause => evs := evs.push c
    | ``machineUnknownClause =>
        clauseError c[0]!.getId.toString ["states", "Inv", "event"]
    | _ => Lean.Elab.throwUnsupportedSyntax
  let some stateCtors := states
    | throwError "machine!: missing `states:` clause — the state \
        enumeration, a non-empty `[ident, …]` list"
  if stateCtors.isEmpty then
    throwError "machine!: `states:` needs at least one state"
  let invT : Term ← match invStx? with
    | some t => pure ⟨t⟩
    | none => throwError "machine!: missing `Inv:` clause — the machine's invariant"
  if evs.isEmpty then
    throwError "machine!: missing `event:` clause — at least one event is required"
  let stateId := mkIdentFrom stx (name.getId ++ `State)
  let labelId := mkIdentFrom stx (name.getId ++ `Label)
  let specId := mkIdentFrom stx (name.getId ++ `spec)
  -- THE STATE ENUM: one ctor per listed state.
  let ctorStx : Array (TSyntax `Lean.Parser.Command.ctor) :=
    ← stateCtors.mapM fun s => do
      let si : TSyntax `ident := ⟨s⟩
      `(ctor| | $si:ident)
  elabCommand (← `(command|
    /-- The state space, machine!-generated from the `states:` clause
        (the enumerated finite machine the conformance battery sweeps). -/
    inductive $stateId:ident where $[$ctorStx:ctor]*
      deriving Repr, BEq, DecidableEq))
  -- THE EVENT FAMILY: one Label ctor per event; each EventSpec carries
  -- its safety PO (the defaulting lands here — `machine_safety` above).
  let mut labelCtors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
  let mut arms : Array (TSyntax `Lean.Parser.Term.matchAlt) := #[]
  for ev in evs do
    let evName : TSyntax `ident := ⟨ev[1]!⟩
    let g : Term := ⟨ev[3]!⟩
    let a : Term := ⟨ev[5]!⟩
    labelCtors := labelCtors.push (← `(ctor| | $evName:ident))
    -- ev[6] is the optional (safety: s) group: empty, or [safety:, term].
    let optSaf : Syntax := ev[6]!
    let saf : Term ←
      if optSaf.getNumArgs > 0 then pure ⟨optSaf[1]!⟩ else `(by machine_safety)
    -- DOTTED arm binding (the trap): the pattern is the ctor, not a var.
    arms := arms.push (← `(matchAltExpr| | .$evName:ident =>
      (⟨$g, $a, $saf⟩ : EventSpec $stateId $invT)))
  elabCommand (← `(command|
    /-- The event labels, machine!-generated (one ctor per `event:`
        clause, source order). -/
    inductive $labelId:ident where $[$labelCtors:ctor]*
      deriving Repr, BEq, DecidableEq))
  elabCommand (← `(command|
    /-- The EventSpec family, machine!-generated: each label's guard,
        action, and safety PO, discharged at construction
        (Events.lean's discipline). -/
    def $specId:ident : $labelId:ident → EventSpec $stateId $invT
      $[$arms:matchAlt]*))
  -- THE ASSEMBLY (positional construction — the struct-instance trap).
  -- @[reducible]: the projections must elaborate in instance search
  -- (the generated DecidablePred instance + the battery's instances).
  elabCommand (← `(command|
    /-- The machine!-assembled `MachineWithInv` (Events.lean's
        carrier): the invariant slot + the EventSpec family; `step?` is
        derived from the guards. -/
    @[reducible] def $name:ident : MachineWithInv $stateId $labelId :=
      (⟨$invT, $specId⟩ : MachineWithInv $stateId $labelId)))
  -- THE LABEL ENUMERATION + its completeness PROOF (the battery's
  -- totality premise — discharged here, not assumed).
  let labelsId := mkIdentFrom stx (name.getId ++ `labels)
  let labelTerms : Array Term ← evs.mapM fun ev => do
    let evName : TSyntax `ident := ⟨ev[1]!⟩
    `($(mkIdentFrom ev (name.getId ++ `Label ++ evName.getId)))
  elabCommand (← `(command|
    /-- The label enumeration, machine!-generated (the conformance
        battery's label argument). -/
    def $labelsId:ident : List ($labelId) := [$labelTerms,*]))
  let completeId := mkIdentFrom stx (name.getId ++ `labels_complete)
  elabCommand (← `(command|
    /-- The enumeration's totality, PROVED (the battery's premise —
        a partial enumeration fails the build here, not silently). -/
    theorem $completeId : ∀ l : $labelId, l ∈ $labelsId := by
      intro l; cases l <;> simp [$labelsId:ident]))
  -- THE TABLE STACK (12 §5's convention names, concatenated).
  let base : String := name.getId.getString!
  let statesId := mkIdentFrom stx (Name.mkSimple (base ++ "States"))
  let transId := mkIdentFrom stx (Name.mkSimple (base ++ "Trans"))
  let tstepId := mkIdentFrom stx (Name.mkSimple (base ++ "TableStep?"))
  let tieId := mkIdentFrom stx (Name.mkSimple (base ++ "TableStep?_eq_step?"))
  let stateTerms : Array Term ← stateCtors.mapM fun s => do
    let si : TSyntax `ident := ⟨s⟩
    `($(mkIdentFrom si (name.getId ++ `State ++ si.getId)))
  elabCommand (← `(command|
    /-- The state enumeration, machine!-generated (the conformance
        battery's state argument). -/
    def $statesId:ident : List $stateId := [$stateTerms,*]))
  elabCommand (← `(command|
    /-- The transition table, COMPUTED from the machine: for each event
        (label-major, states in enumeration order), the enabled
        (event, from, to) triples — it cannot drift from the guards. -/
    def $transId:ident : List ($labelId × $stateId × $stateId) :=
      _root_.List.flatMap
        (fun l => _root_.List.filterMap
          (fun s => _root_.Option.map (fun s' => (l, s, s'))
            (_root_.Machines.MachineWithInv.step? $name s l))
          $statesId)
        $labelsId))
  elabCommand (← `(command|
    /-- The machine as a table lookup (the emitter-facing structural
        reading; the tie theorem pins it to `step?`). Keys compare by
        DECIDABLE equality, not `==`. -/
    def $tstepId:ident : $labelId → $stateId → _root_.Option $stateId :=
      fun e s => _root_.Option.map (fun r => r.2.2)
        (_root_.List.find? (fun r => decide (r.1 = e) && decide (r.2.1 = s))
          $transId)))
  elabCommand (← `(command|
    /-- THE TIE: the generated table IS the machine — for every event
        and EVERY state (the state type IS the enumeration, so the
        cases exhaust; the proof is `cases <;> rfl`, zero axioms). -/
    theorem $tieId:ident (e : $labelId) (s : $stateId) :
        $tstepId e s = _root_.Machines.MachineWithInv.step? $name s e := by
      cases e <;> cases s <;> rfl))
  elabCommand (← `(command|
    /-- The invariant is decidable (machine!-generated; requires the
        `Inv:` clause to be instance-synthesizable). -/
    instance : _root_.DecidablePred ($name).inv :=
      fun s => inferInstanceAs (_root_.Decidable (($name).inv s))))
  -- THE BATTERY REGISTRATION: the generated enumerations + the
  -- generated completeness proof feed `Machines.Testing.battery`.
  let battId := mkIdentFrom stx (name.getId ++ `battery)
  elabCommand (← `(command|
    /-- The conformance battery, machine!-registered: deadlock-freedom,
        guard coverage, invariant non-vacuity over the generated
        enumerations (Testing.lean; the completeness premise is the
        generated `labels_complete`). -/
    def $battId:ident (init : $stateId) (fuel : Nat) :
        List (String × _root_.Machines.Testing.BatteryVerdict $stateId $labelId) :=
      _root_.Machines.Testing.battery $name $labelsId $statesId init fuel
        $completeId))

/-- The registration form: the type must be the literal `CommandElab`
    synonym, so the impl is a separate def. -/
@[command_elab machineCmd] def elabMachine : Lean.Elab.Command.CommandElab :=
  elabMachineImpl

end Machines.Dsl
