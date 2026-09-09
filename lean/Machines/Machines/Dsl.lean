/-
# Machines.Dsl — the instance-fronted authoring layer

lean-v3 §5.3: raw framework events are 60–70% proof boilerplate. `machine!`
generates the skeleton and leaves the author writing State + Inv +
guard/action per event only.

```lean
machine! counter where
  State: CounterS
  Inv: fun s => s.n ≤ 10
  event: incr guard: (fun s => s.n < 10) action: (fun s _ => ⟨s.n + 1⟩)
  event: decr guard: (fun s => s.n > 0)  action: (fun s _ => ⟨s.n - 1⟩)
    safety: (by intro s _ h; exact h)   -- optional; default is `machine_safety`
```

generates:
- `counter.Label` — an inductive with one constructor per event name (the
  veil Assemble pattern: proofs case-split and execution enumerates the
  SAME generated set; they cannot drift),
- `counter.spec : counter.Label → EventSpec State Inv` — the event family,
- `counter : Machine` — the assembly.

## The PO default

An event's `safety` field is the proof-obligation slot. Omitted, it becomes
`by machine_safety`, which tries `simp_all`/`omega`/`grind`/`trivial` in
order (`grind` covers conjunction-shaped invariants that defeat
`simp_all; omega` — verified against a `x ≤ 10 ∧ y ≤ x` machine).
When none close the goal, the error surfaces at the event site — supply
`safety: (by ...)` with the real proof. The author-facing vocabulary is:
guard, action, invariant, and (when needed) one named tactic block.

## Macro traps encoded here (lean/AGENTS.md fuel)

- **Keyword pollution**: bare syntax atoms (`"State"`, `"guard"`, …) enter the
  global token table and then FAIL to parse as identifiers — structure
  instances like `def m : Machine where State := …` break package-wide.
  Colon-suffixed atoms (`"State:"`) are distinct tokens and do not pollute.
- **Hygiene**: an ident literal inside a quotation (`def foo := …`) is bound
  to the macro-definition site; use sites can't see it. `mkIdentFrom stx`
  anchors generated names to the use site.
- Repetition over a custom syntax category binds as `$evs:machineEvent*`;
  individual events are destructured by raw position (nested pattern
  quotations over a custom category inside a command elab choke on the
  struct-literal parser — and positional ⟨⟩ output sidesteps that too).
- Struct-instance quotations `{ f := $x }` fail inside command-elab bodies;
  the positional form `(⟨…⟩ : T)` does not.
- `matchAltExpr` quotations build arms; the `def … | …` splice wants
  ``TSyntax `Lean.Parser.Term.matchAlt`` — core ships the Coe.
- Match arms must bind `.ctor` (dotted) — a bare ident binds a variable and
  every subsequent arm becomes a redundant alternative.
-/

import Machines.Core
import Lean

namespace Machines.Dsl

open Machines
open Lean Lean.Parser.Command
open Lean.Elab.Command (elabCommand CommandElabM)

/-- The default safety discharge: cheap closers in order. Named once here
    because tactic blocks containing `|` cannot be spliced into term
    quotations (the pipe collides with matchAlt's separator). The `done`
    guard matters: bare `simp_all` SUCCEEDS without closing the goal
    (partial progress), which would swallow the `first` chain and leave
    unsolved goals. omega/grind/trivial fail cleanly when stuck; simp_all
    needs the guard. -/
macro "machine_safety" : tactic => `(tactic| (intros; first | (simp_all; done) | omega | grind | trivial))

/-- One event clause of `machine!`. Colon-suffixed keywords so the global
    token table is untouched. -/
syntax machineEvent := "event:" ident "guard:" term "action:" term ("safety:" term)?

/-- Generate a `Machines.Machine` from State/Inv and a list of events.
    Optional binders between the name and `where` make a parameterized
    machine: `machine! counter (max : Nat) where …` generates
    `counter.spec (max : Nat) : …` and `counter (max : Nat) : Machine`
    (the Label inductive and the labels list stay parameter-free — event
    names don't depend on parameters). -/
syntax (name := machineCmd) "machine!" ident bracketedBinder* "where"
  "State:" term "Inv:" term machineEvent* : command

open Lean.Parser.Term in
def elabMachineImpl (stx : Syntax) : Lean.Elab.Command.CommandElabM Unit := do
  -- stx = [machine!, name, bindersNode, where, State:, StateTerm, Inv:, InvTerm, eventsNode]
  let name : TSyntax `ident := ⟨stx[1]!⟩
  let binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) :=
    (stx[2]!.getArgs).map (⟨·⟩)
  let sty : Term := ⟨stx[5]!⟩
  let invty : Term := ⟨stx[7]!⟩
  let evs : Array Syntax := stx[8]!.getArgs
  let labelId := mkIdentFrom stx (name.getId ++ `Label)
  let specId := mkIdentFrom stx (name.getId ++ `spec)
  let mut ctors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
  let mut arms : Array (TSyntax `Lean.Parser.Term.matchAlt) := #[]
  for (ev : Syntax) in evs do
    -- machineEvent = [event:, name, guard:, g, action:, a, (safety:, s)?]
    let evName : TSyntax `ident := ⟨ev[1]!⟩
    let g : Term := ⟨ev[3]!⟩
    let a : Term := ⟨ev[5]!⟩
    ctors := ctors.push (← `(ctor| | $evName:ident))
    -- ev[6] is the optional (safety: s) group: a null node, empty or
    -- [safety:, term]. The term inside is at [1].
    let optSaf : Syntax := ev[6]!
    let saf : Term ←
      if optSaf.getNumArgs > 0 then pure ⟨optSaf[1]!⟩
      else `(by machine_safety)
    let arm ← `(matchAltExpr| | .$evName:ident => (⟨$g, $a, $saf⟩ : EventSpec $sty $invty))
    arms := arms.push (arm : TSyntax `Lean.Parser.Term.matchAlt)
  -- binder NAMES for application sites (spec is applied to them in the
  -- machine assembly). `(x : ty)` → the idents at child 1 (a null node of
  -- one or more idents; we take them all).
  let binderNames : Array (TSyntax `ident) := binders.flatMap fun b =>
    (b.raw[1]!.getArgs).map (⟨·⟩)
  elabCommand (← `(command|
    inductive $labelId:ident where $[$ctors:ctor]* deriving Repr, DecidableEq))
  elabCommand (← `(command|
    def $specId:ident $[$binders]* : $labelId:ident → EventSpec $sty $invty $[$arms:matchAlt]*))
  -- @[reducible]: tests/uses write `door.run ⟨0⟩ …` with concrete states;
  -- without it, `door.State` doesn't unfold and instance search fails.
  elabCommand (← `(command|
    @[reducible] def $name:ident $[$binders]* : Machine :=
      ⟨$sty, $labelId:ident, $invty, ($specId:ident $binderNames*)⟩))
  -- the full label enumeration, free with the machine (the conformance
  -- battery in Machines.Testing consumes it)
  let labelsId := mkIdentFrom stx (name.getId ++ `labels)
  let labelTerms : Array Term ← evs.mapM fun ev => do
    let evName : TSyntax `ident := ⟨ev[1]!⟩
    `($(mkIdentFrom ev (name.getId ++ `Label ++ evName.getId)))
  elabCommand (← `(command|
    def $labelsId:ident : List ($labelId:ident) := [$labelTerms,*]))
  -- the completeness proof: every constructor is in `labels`. The
  -- conformance battery consumes this as a PROOF PARAMETER (not a
  -- convention) — the enumeration's totality is now checked, not assumed.
  let completeId := mkIdentFrom stx (name.getId ++ `labels_complete)
  elabCommand (← `(command|
    theorem $completeId : ∀ l : $labelId, l ∈ $labelsId := by
      intro l; cases l <;> decide))

/-- The registration form the attribute accepts: the type must be the
    literal `CommandElab` synonym, so the impl is a separate def. -/
@[command_elab machineCmd] def elabMachine : Lean.Elab.Command.CommandElab := elabMachineImpl

end Machines.Dsl
