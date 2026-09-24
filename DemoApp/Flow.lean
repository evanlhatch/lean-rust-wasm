/-
# DemoApp.Flow — the consumer's hand-owned extension module (Scaffold seed)

Seeded ONCE by scaffold; NEVER regenerated (`scaffoldgen` skips an
existing Flow — one writer: the consumer). NO GENERATED header, no
byte-tie: this module is where the fill obligations land (12 §3) —
the emitter row's real fold (its `run` is app logic, not spec
data), the widened properties and the REAL must-fail controls
(one per coverage family, 15-patterns #5). The generated modules
stay byte-tie-clean; the app's real content lives HERE.

Five questions (notes/v3/01-core.md), filled from the AppSpec:
- root: crossing
- carrier grade: the lane item over the registry's nodup-in-type substrate
- spine reading: registration = append; the emitters fold the replay
- ladder rung: generated
- gate row: axioms, docs-check
Consumes (the schema registry refs): Order
Capabilities generated: registry-lane, emitter, diagnostics, tests
-/

import Kit.Emit

import TestingKit.Harness
import DemoApp.App

open DemoApp TestingKit

namespace DemoApp

/-! ## The emitter row (capability: emitter — R1 step 4 / 12 §3) -/

/-- The emitter row: pure and total over the item list, the
    declared outputs nodup IN THE TYPE. FILL OBLIGATIONS (12 §3):
    the real fold replaces `run`'s empty body; the law is cited
    when the fold's correspondence exists (`law := some ...` —
    until then this header note IS the why-not); the outputs join
    the cross-emitter one-writer audit. -/
def demoAppItemEmitter : Kit.Emit.Emitter (List DemoAppItem) where
  name := "demoAppItem-emitter"
  style := .lean
  specSource := "AppSpec DemoApp"
  outputs := []
  run := fun _ => []

/-! ## The consumer's real content (defs land below this line) -/

/-! ## The flow suite (the consumer widens the property and the
    controls — one real must-fail control per coverage family) -/

/-- The seed suite: born-green (the property holds, both control
    shapes are caught); every assert here is the consumer's to
    widen. -/
def demoAppItemFlowSpec : Spec :=
  Spec.ofList "DemoApp flow invariants" (fun _ => do
    assert (true) "the seed property — the consumer widens it")
    [ ("sabotage: the naming fn drops the name", fun _ =>
        assert (false) "control fired: the seed control must fail")
    , ("sabotage: the entry drifts", fun _ =>
        assert (false) "control fired: the seed control must fail")
    ]
    8 42

end DemoApp
