/-
# Machines — the umbrella module

One import point for the library. Submodules (import what you name —
root-module imports are NOT re-exported into scope, but this module
re-exports by importing):

- `Machines.Basic` — the machine: the executable `step?` + the derived
  authoritative relation + the `step_iff` bridge (15-patterns #1),
  the tape-fold `run` + its compositional laws, the `Reachable` view
  and its run-ties (01-core §3).
- `Machines.Trace` — the witness-carrying `Exec` inductive, the
  tape/record projections tied to `run`, the observer composition
  riding `Kit.Observer.equiv` (04 §4), the `Kit.Execution` bridge.
- `Machines.Explore` — the bounded exploration with the honest
  trichotomy (proved / refuted-with-witness / unknown-with-reason;
  01-core §3) + the soundness theorems.
- `Machines.Events` — the EventSpec/guard layer: events carry their
  guard proof and safety obligation at CONSTRUCTION; the invariant
  slot rides `MachineWithInv` (the honest shape over the landed
  `Machine` — the judgment recorded in its header), bridged down by
  `toMachine`; the preservation theorems (`step?_preserves`,
  `run_preserves`, `reachable_preserves`) + the step inversions.
  SEAM: the `machine!` MACRO (15-patterns #9) is the NEXT order —
  this is the hand-built layer it will generate.
- `Machines.Dsl` — the `machine!` authoring surface (15-patterns #9):
  one declaration generates the state enum + the Label inductive + the
  EventSpec family + the `MachineWithInv` assembly + the transition
  table computed from `step?` + the table↔step tie theorem + the
  `DecidablePred` instance + the conformance-battery registration;
  curated clause failures ride `TextKit.suggestSuffix`.
- `Machines.Testing` — the conformance battery over the enumerated
  finite machine: deadlock-freedom over the REACHABLE fragment,
  guard coverage (a never-enabled event is dead code the compiler
  accepts — the battery refutes it with the dead label), invariant
  non-vacuity. Riding Explore's verdict discipline: proved /
  refuted-with-witness / unknown-with-reason, never a bare bool.
- `Machines.Stream` — the streams (the shared currency of machines and
  deltas): the `D`/`I` pair over the landed `Kit.Additive` (the
  first-entry convention: `(D s) 0 = s 0` — the journal carries the
  init snapshot), and **the dI Iso VALUE** (Kit.Correspondence — both
  round trips, the ONE carrier's isomorphism grade).
- `Machines.Fusion` — the machines ↔ deltas bridges: `Machine.tick`
  (the totalized step — blocked = hold), the state stream, **the
  journal bridge** (`journal = D ∘ stateStream`) and **the replay
  bridge** (`replay = I ∘ journal = run`), and **bisimulation as
  stream equality** (the legacy's cluster, observer-parameterized per
  04 §4: `bisim_iff_respStreams` at the stream level + the trace face
  `respTrace_tick_agree` tied to the landed `Exec.record`).
- `Machines.Coalg` — the coalgebraic half (16-surface §4.2): the
  machine AS an observation coalgebra (`observe : S → I → Option (O × S)`,
  machine + `Kit.Observer`), the UNFOLD (corecursion — `states`/`beh`),
  `Bisim` + the coinduction principle's sound direction
  (`bisim_sound`), **FINALITY** (`behEq_bisim` + `behEq_iff_bisim`:
  behavioral equality IS bisimilarity — the dual of initiality), and
  `Refines` (impl ≤ spec: the observer-parameterized simulation, with
  the behavior-inclusion law `beh_le` and the composition tower
  `Refines.comp` over `Kit.Rel.comp`).
- `Machines.Closure` — THE CLOSURE BRIDGE (02 §9's dissolution): the
  machine-as-rules encoding (each enabled transition `(s, i, s')` = the
  ground rule `state(s') :- state(s), in(i)`) + `deriv_iff_reachable`
  (the Datalog LFP reading IS reachability) + `bridge` (the frontier
  fold's stabilized result = the Datalog closure, both sides CITED:
  `reachableAux_run`/`_complete` + `deriv_iff_eval`) + `inv_of_eval`
  (check_proved's content re-expressed with the closure evaluation as
  the engine — the alternative path; no Explore refactor).
- `Machines.Session` — session types (08 §9): the closed session
  grammar over the payload universe (`done`/`send`/`recv`/`choice`) +
  THE DUALITY as one total function with its laws (the involution
  `dual_dual`, the wire laws `msgs_dual`/`dirs_dual`) + the
  projections (each peer derived from the global protocol;
  `proj_dual` — the projected peers are dual-compatible by
  construction, the choreography cannot drift from the wire) + peer
  agreement as a TYPE (`IsDualOf`) + the session-as-machine (the
  continuation engine over the landed `Machine`) with conformance
  (`follow_runs`, the refusal lemmas, the `offender` named diagnostic)
  + the refinement (a delaying impl refines its protocol, riding
  `Coalg.Refines`).

Named exclusions (per module header): fairness, POR, vector clocks
(08 §10's guard), nondeterministic-relation-primary machines,
nondeterministic bisimulation; and, in Dsl: payload events,
parameterized machines, entourage unexpanders, the rank/rewind
acyclicity clause — each lands with its first consumer.
-/

import Machines.Basic
import Machines.Trace
import Machines.Explore
import Machines.Events
import Machines.Dsl
import Machines.Testing
import Machines.Stream
import Machines.Fusion
import Machines.Coalg
import Machines.Closure
import Machines.Session
