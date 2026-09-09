/-
# Machines.Testing — the conformance battery every machine inherits

The framework theorems (Core's `run_preserves`, Live's liveness vocabulary)
say what is true of EVERY machine. What they do NOT say about a PARTICULAR
authored machine:

1. **Deadlock-freedom over reachable states** — from every state satisfying
   the invariant, at least one event is enabled (the guard-disjunction
   property; lean-v3 §5's Trace reason-to-exist). A machine that can wedge
   in a legal state is a bug the safety POs cannot see.
2. **Guard coverage** — every event is enabled from at least one enumerated
   state. A never-enabled event is dead code the compiler accepts.
3. **Invariant non-vacuity** — the invariant excludes at least one
   enumerated state (a `True` invariant discharges every safety PO and
   proves nothing; with it, guard coverage is the only signal).

These are SWEEPS, not theorems: the framework proves the laws, the battery
checks the instance. One line per machine:

```lean
def doorConformance := Machines.Testing.conformance door
  doorLabelList doorStateList
```

Deliberately NOT here: trace correctness (that's the oracle, engine-side)
and safety (that's the EventSpec PO, discharged at construction).
-/

import Machines.Core
import TestKit

namespace Machines.Testing

open Machines

/-- Deadlock-freedom over an enumerated state space: every invariant-
    satisfying state has at least one enabled event. The completeness
    proof (`∀ l, l ∈ labels`) is a phantom parameter — unused in the
    body, but REQUIRED so the caller PROVES the label enumeration is
    total (a partial enumeration would let a never-swept event wedge
    the machine undetected). -/
def deadlockSweep (m : Machine) (labels : List m.Label) (states : List m.State)
    [DecidablePred m.Inv] (_ : ∀ l, l ∈ labels) : TestKit.CheckResult :=
  let wedged := states.filter (fun s => decide (m.Inv s) && !labels.any (m.enabled s))
  if wedged.isEmpty then .ok ()
  else .error s!"deadlock: {wedged.length} invariant-satisfying state(s) have no enabled event"

/-- Guard coverage: every event fires from at least one enumerated state.
    The completeness proof is REQUIRED — without it, a missing label would
    skip a dead event entirely (the check would pass vacuously). -/
def guardCoverage (m : Machine) (labels : List m.Label) (states : List m.State)
    (_ : ∀ l, l ∈ labels) : TestKit.CheckResult :=
  let dead := labels.filter (fun l => !states.any (m.enabled · l))
  if dead.isEmpty then .ok ()
  else .error s!"dead events: {dead.length} event(s) never enabled over the enumerated states"

/-- Invariant non-vacuity: the invariant excludes at least one enumerated
    state. (If your invariant is genuinely `True`, skip this check — call
    the two above directly.) -/
def invariantNonVacuous (m : Machine) (states : List m.State) [DecidablePred m.Inv] :
    TestKit.CheckResult :=
  if states.any (fun s => !decide (m.Inv s)) then .ok ()
  else .error "invariant holds on every enumerated state — is it vacuous?"

/-- The battery, as named checks for the TestKit driver. The completeness
    proof (`hcomplete`) is threaded into both sweeps — the caller must
    discharge it (the `machine!` macro generates `<name>.labels_complete`). -/
def conformance (m : Machine) (labels : List m.Label) (states : List m.State)
    [DecidablePred m.Inv] (hcomplete : ∀ l, l ∈ labels) : List (String × TestKit.CheckResult) :=
  [ ("deadlock-freedom", deadlockSweep m labels states hcomplete)
  , ("guard-coverage", guardCoverage m labels states hcomplete)
  , ("invariant-non-vacuous", invariantNonVacuous m states) ]

end Machines.Testing
