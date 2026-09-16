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

Acyclicity clause (optional): `rank: <stateRankFn> rewind: <labelCtor>` —
when present, `machine!` additionally generates `counter.rank_advances`
(every non-rewind event strictly increases the rank) and
`counter.rank_advances_tr` (the same, over `counter.tr`) — the acyclicity
pair three machines (schema-lang's pipeline/tick/orderMachine) used to
carry by hand, byte-identical modulo names.

Finite-state entourage clause (optional): `states: [<s1>, <s2>, …]` — for
machines whose state space is a finite enumeration (a list LITERAL, so the
generated proof can case it). When present, `machine!` additionally
generates (W2.3 — the four in-tree hand-written copies this replaces):
- `<m>States : List State` — the enumeration itself (the conformance
  battery's state argument, no longer hand-written),
- `<m>Trans : List (<m>.Label × State × State)` — the transition table,
  COMPUTED from the machine (`step?` over labels × states, label-major —
  the hand-written row order), so it cannot drift from the guards,
- `<m>TableStep? : <m>.Label → State → Option State` — the table as a
  lookup (the emitter-facing structural reading),
- `<m>TableStep?_eq_step?` — the agreement theorem: over enumerated
  states the table lookup IS `step?` (proved by `fin_cases` + `decide`;
  an enumeration that misses a guard-satisfying state fails THIS proof
  at build time — the check is the compile),
- `instance : DecidablePred <m>.Inv` — via `inferInstanceAs` (the
  invariant must be instance-synthesizable: equalities, comparisons,
  Boolean coercions, ∧/→ over decidables — NOT a `match` on the state,
  which is why the clause is opt-in: schema-lang's pipeline keeps its
  hand-written instance).
Requirements on the state type: `BEq` (the lookup key) and `DecidableEq`
(the tie proof's `decide`). Payload-CARRYING state constructors (e.g.
`failed (stage : String)`) defeat the lookup reading — a table row keys on
the exact state; keep those machines hand-written (the hand `tableStep?`
wildcard arms are the mechanism the lookup cannot express).

Payload-carrying events (the W2.3(d) follow-up): `event: send (v : α)
guard: … action: …` — bracketed binders after the event name become
Label-ctor arguments and PATTERN-BIND in the guard/action/safety bodies
(`v` is in scope in all three slots). No `Machines.Core` change: the event
family is already label-VALUE-indexed (`Machine.event : Label → EventSpec
State Inv`), so guard/action read the payload off the label. Two
consequences, both mechanical:

- the Label inductive takes the machine's binders (a payload type may
  mention them — mpsc's `send (v : α)`); payload-free machines keep the
  parameter-free Label (backward compat),
- `labels`/`labels_complete` are NOT generated (an infinite payload type
  has no finite enumeration) — the conformance battery's sampled variant
  (`Machines.Testing.conformanceOver`) takes a user-supplied label list
  instead. The `states:` clause is REJECTED on payload machines (the
  transition table is computed from `labels`).

Explicit payload binders only — the generated ctor pattern is positional.

generates:
- `counter.Label` — an inductive with one constructor per event name (see [machineAssemblePattern]).
- `counter.spec : counter.Label → EventSpec State Inv` — the event family,
- `counter : Machine` — the assembly,
- `counter.labels` + `counter.labels_complete` (payload-free machines only).

## The PO default

An event's `safety` field is the proof-obligation slot. Omitted, it becomes
`by machine_safety` — an alias of the OPEN `guestlang_solver`
(Machines.Tactics): `simp_all`/`omega`/`grind`/`trivial` in order, plus any
rung a downstream package registers via `macro_rules` (`grind` covers
conjunction-shaped invariants that defeat `simp_all; omega` — verified
against a `x ≤ 10 ∧ y ≤ x` machine).
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

module

public import Machines.Core
public import Machines.Tactics
public import Lean
public import Mathlib.Tactic.FinCases

-- W5.4 module discipline: the entire DSL layer is elaboration-time
-- (syntax + the machine! command elaborator) → `public meta section`.
public meta section

namespace Machines.Dsl

open Machines
open Lean Lean.Parser.Command
open Lean.Elab.Command (elabCommand CommandElabM)

/-- The default safety discharge: the machine-obligation alias of
    `guestlang_solver` (W6.8 — the ladder itself, and the extension
    point, live in Machines.Tactics). Named because tactic blocks
    containing `|` cannot be spliced into term quotations (the pipe
    collides with matchAlt's separator) — and because `machine!` authors
    read obligations as SAFETY goals. -/
macro "machine_safety" : tactic => `(tactic| guestlang_solver)

/-- One event clause of `machine!`. Colon-suffixed keywords so the global
    token table is untouched. Bracketed binders after the event name are
    the PAYLOAD: Label-ctor arguments, pattern-bound in the guard/action/
    safety bodies (explicit binders only — the pattern is positional). -/
syntax machineEvent := "event:" ident bracketedBinder* "guard:" term "action:" term ("safety:" term)?

-- The optional acyclicity clause: `rank:` names the STATE's rank function
-- (a def on the state type — the theorem statements unfold it), `rewind:`
-- names the Label ctor whose edges may go backward (the recovery edge).
-- When present, `machine!` generates `X_rank_advances` (every non-rewind
-- event strictly increases the rank) + `X_rank_advances_tr` (the same over
-- `X.tr`) — the hand-written pair this replaces lived in three machines
-- byte-identical modulo names.
syntax machineRank := "rank:" term "rewind:" ident

-- The optional finite-state entourage clause: `states:` names the state's
-- finite enumeration (a list literal — the generated tie theorem case-
-- splits it with `fin_cases`). When present, `machine!` generates the
-- `<m>States`/`<m>Trans`/`<m>TableStep?`/`<m>TableStep?_eq_step?` table
-- stack + the `DecidablePred <m>.Inv` instance (see the module header).
syntax machineStates := "states:" term

/-- Generate a `Machines.Machine` from State/Inv and a list of events.
    Optional binders between the name and `where` make a parameterized
    machine: `machine! counter (max : Nat) where …` generates
    `counter.spec (max : Nat) : …` and `counter (max : Nat) : Machine`
    (the Label inductive and the labels list stay parameter-free — event
    names don't depend on parameters). A PAYLOAD machine (an event with
    ctor binders) flips both: the Label takes the machine's binders (a
    payload type may mention them) and no labels list is generated. -/
syntax (name := machineCmd) "machine!" ident bracketedBinder* "where"
  "State:" term "Inv:" term (machineRank)? (machineStates)? machineEvent* : command

open Lean.Parser.Term in
def elabMachineImpl (stx : Syntax) : Lean.Elab.Command.CommandElabM Unit := do
  -- stx = [machine!, name, bindersNode, where, State:, StateTerm, Inv:, InvTerm,
  --        optRank, optStates, eventsNode]
  let name : TSyntax `ident := ⟨stx[1]!⟩
  let binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) :=
    (stx[2]!.getArgs).map (⟨·⟩)
  let sty : Term := ⟨stx[5]!⟩
  let invty : Term := ⟨stx[7]!⟩
  -- stx[8] = the optional rank/rewind group (a null node when absent:
  -- [rank:, term, rewind:, ident] when present); stx[9] = the optional
  -- states group (likewise); stx[10] = the events.
  -- the optional groups wrap the NAMED nodes (arity 1):
  -- optRank[0] = machineRank = [rank:, term, rewind:, ident]
  -- optStates[0] = machineStates = [states:, term]
  let optRank : Syntax := stx[8]!
  let optStates : Syntax := stx[9]!
  let evs : Array Syntax := stx[10]!.getArgs
  let labelId := mkIdentFrom stx (name.getId ++ `Label)
  let specId := mkIdentFrom stx (name.getId ++ `spec)
  -- binder NAMES for application sites (spec is applied to them in the
  -- machine assembly). `(x : ty)` → the idents at child 1 (a null node of
  -- one or more idents; we take them all).
  let binderNames : Array (TSyntax `ident) := binders.flatMap fun b =>
    (b.raw[1]!.getArgs).map (⟨·⟩)
  -- payload detection: any event clause carrying ctor binders.
  -- machineEvent = [event:, name, binderGroup, guard:, g, action:, a, (safety:, s)?]
  let hasPayload : Bool := evs.any fun ev => (ev[2]!.getArgs).size > 0
  -- the `states:` table is computed from the generated `labels`
  -- enumeration, which a payload machine cannot have — reject the mix.
  if optStates.getNumArgs > 0 && hasPayload then
    throwErrorAt stx
      "machine!: payload-carrying events defeat the `labels` enumeration \
       the `states:` table is computed from — drop the `states:` clause \
       (hand-write the table stack) or keep the events payload-free"
  let mut ctors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
  let mut arms : Array (TSyntax `Lean.Parser.Term.matchAlt) := #[]
  for (ev : Syntax) in evs do
    let evName : TSyntax `ident := ⟨ev[1]!⟩
    let evBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) :=
      (ev[2]!.getArgs).map (⟨·⟩)
    let g : Term := ⟨ev[4]!⟩
    let a : Term := ⟨ev[6]!⟩
    ctors := ctors.push (← `(ctor| | $evName:ident $[$evBinders]*))
    -- ev[7] is the optional (safety: s) group: a null node, empty or
    -- [safety:, term]. The term inside is at [1].
    let optSaf : Syntax := ev[7]!
    let saf : Term ←
      if optSaf.getNumArgs > 0 then pure ⟨optSaf[1]!⟩
      else `(by machine_safety)
    -- the payload pattern: every binder's idents, positional — the bound
    -- names are in scope in the guard/action/safety bodies (user syntax
    -- throughout, so hygiene carries the binding).
    let patIds : Array (TSyntax `ident) := evBinders.flatMap fun b =>
      (b.raw[1]!.getArgs).map (⟨·⟩)
    let arm ← `(matchAltExpr| | .$evName:ident $patIds* =>
      (⟨$g, $a, $saf⟩ : EventSpec $sty $invty))
    arms := arms.push (arm : TSyntax `Lean.Parser.Term.matchAlt)
  -- the Label type at use sites: a payload machine's Label takes the
  -- machine's binders (a payload type may mention them — mpsc's
  -- `send (v : α)`); a payload-free machine's stays parameter-free
  -- (backward compat: `counterMachine.Label.increment`, no application).
  let labelTy : Term ←
    if hasPayload then `($labelId:ident $binderNames*) else `($labelId:ident)
  if hasPayload then
    elabCommand (← `(command|
      inductive $labelId:ident $[$binders]* where $[$ctors:ctor]* deriving Repr, DecidableEq))
  else
    elabCommand (← `(command|
      inductive $labelId:ident where $[$ctors:ctor]* deriving Repr, DecidableEq))
  elabCommand (← `(command|
    def $specId:ident $[$binders]* : $labelTy → EventSpec $sty $invty $[$arms:matchAlt]*))
  -- @[reducible]: tests/uses write `door.run ⟨0⟩ …` with concrete states;
  -- without it, `door.State` doesn't unfold and instance search fails.
  elabCommand (← `(command|
    @[reducible] def $name:ident $[$binders]* : Machine :=
      ⟨$sty, $labelTy, $invty, ($specId:ident $binderNames*)⟩))
  -- the full label enumeration, free with the machine (the conformance
  -- battery in Machines.Testing consumes it). Payload machines SKIP the
  -- generation: an infinite payload type has no finite enumeration — the
  -- sampled battery (`Machines.Testing.conformanceOver`) takes the user's
  -- list. (The NAME is needed unconditionally: the `states:` table below
  -- is computed from it, and `states:` + payload is rejected above.)
  let labelsId := mkIdentFrom stx (name.getId ++ `labels)
  if !hasPayload then
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
  -- The finite-state entourage, generated when the states clause is
  -- present (W2.3 — replaces the hand-written `flagTrans`/
  -- `flagTableStep?`/`flagTableStep?_eq_step?`/`DecidablePred` copies).
  -- The table is COMPUTED from the machine (step? over labels × states,
  -- label-major — the hand-written row order), so table and guards cannot
  -- drift; the tie theorem's `fin_cases`+`decide` proof is the check that
  -- the enumeration covers every guard-satisfying state (an under-
  -- enumeration fails the BUILD, loudly). Names are CONCATENATED
  -- (`doorTrans`, not `door.Trans`) — the hand-written convention.
  if optStates.getNumArgs > 0 then
    let statesT : Term := ⟨optStates[0]![1]!⟩
    let base : String := name.getId.getString!
    let statesId := mkIdentFrom stx (Name.mkSimple (base ++ "States"))
    let transId := mkIdentFrom stx (Name.mkSimple (base ++ "Trans"))
    let tstepId := mkIdentFrom stx (Name.mkSimple (base ++ "TableStep?"))
    let tieId := mkIdentFrom stx (Name.mkSimple (base ++ "TableStep?_eq_step?"))
    elabCommand (← `(command|
      /-- The finite state space, machine!-generated from the `states:`
          clause (the conformance battery's state argument). -/
      def $statesId:ident $[$binders]* : List $sty := $statesT))
    elabCommand (← `(command|
      /-- The transition table, computed from the machine itself: for each
          event (label-major, states in enumeration order — the hand-
          written row order), the enabled (event, from, to) triples. -/
      def $transId:ident $[$binders]* : List ($labelId × $sty × $sty) :=
        _root_.List.flatMap
          (fun l => _root_.List.filterMap
            (fun s => _root_.Option.map (fun s' => (l, s, s'))
              (_root_.Machines.Machine.step? ($name $binderNames*) s l))
            ($statesId $binderNames*))
          $labelsId))
    elabCommand (← `(command|
      /-- The machine as a table lookup (the emitter-facing structural
          reading; the tie theorem pins it to `step?`). -/
      def $tstepId:ident $[$binders]* : $labelId → $sty → _root_.Option $sty :=
        fun e s => _root_.Option.map (fun r => r.2.2)
          (_root_.List.find? (fun r => r.1 == e && r.2.1 == s)
            ($transId $binderNames*))))
    elabCommand (← `(command|
      /-- The generated table IS the machine, over the enumerated state
          space. -/
      theorem $tieId:ident $[$binders]* (e : $labelId) (s : $sty)
          (hs : s ∈ ($statesId $binderNames*)) :
          ($tstepId:ident $binderNames*) e s =
            _root_.Machines.Machine.step? ($name $binderNames*) s e := by
        simp only [$statesId:ident] at hs
        fin_cases hs <;> cases e <;> decide))
    elabCommand (← `(command|
      /-- The invariant is decidable (machine!-generated; the `states:`
          clause opts the machine into the finite-space entourage). -/
      instance $[$binders]* : _root_.DecidablePred ($name $binderNames*).Inv :=
        fun s => inferInstanceAs (_root_.Decidable (($name $binderNames*).Inv s))))
  -- The acyclicity pair, generated when the rank clause is present. The
  -- proof mirrors the hand-written originals verbatim (cases over the
  -- enumerated state/label space, then omega over the rank arithmetic).
  if optRank.getNumArgs > 0 then
    let mr : Syntax := optRank[0]!
    let rankT : Term := ⟨mr[1]!⟩
    let rewindId : TSyntax `ident := ⟨mr[3]!⟩
    let advId := mkIdentFrom stx (name.getId ++ `rank_advances)
    let advTrId := mkIdentFrom stx (name.getId ++ `rank_advances_tr)
    let rewindFull : Term :=
      ⟨mkIdentFrom stx (name.getId ++ `Label ++ rewindId.getId)⟩
    let specLem : Term := ⟨mkIdentFrom stx (name.getId ++ `spec)⟩
    -- elemsAndSeps = the lemmas INTERLEAVED with the separator atoms
    let sep := Syntax.atom .none ","
    -- simpLemma = [prePost-group, ← -group, term] — the first two slots
    -- null (a plain forward lemma); the TERM at index 2 (elabSimpArg reads
    -- arg[2] — a node without the null slots silently drops the lemma)
    let lem (t : Term) : Syntax :=
      Syntax.node .none ``Lean.Parser.Tactic.simpLemma
        #[mkNullNode, mkNullNode, t.raw]
    let simpLemmas : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," :=
      ⟨#[lem name, sep, lem specLem, sep, lem rankT]⟩
    let cmd1 ← `(command|
      theorem $advId (s : $sty) (l : $labelId)
          (hnr : l ≠ $rewindFull)
          (w : (_root_.Machines.Machine.event $name l).guard s = true) :
          $rankT s < $rankT ((_root_.Machines.Machine.event $name l).action s w) := by
        cases s <;> cases l <;>
          simp [$simpLemmas,*] at hnr w ⊢ <;> omega)
    elabCommand cmd1
    elabCommand (← `(command|
      theorem $advTrId (s s' : $sty) (l : $labelId)
          (htr : _root_.Machines.Machine.tr $name s l s') (hnr : l ≠ $rewindFull) :
          $rankT s < $rankT s' := by
        obtain ⟨w, hact⟩ := htr
        have h := $advId s l hnr w
        rw [hact] at h
        exact h))

/-- The registration form the attribute accepts: the type must be the
    literal `CommandElab` synonym, so the impl is a separate def. -/
@[command_elab machineCmd] def elabMachine : Lean.Elab.Command.CommandElab := elabMachineImpl

end Machines.Dsl

end -- public meta section
