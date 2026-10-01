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
  outputs := ["demo.txt"]
  run := fun items =>
    -- the real fold: one demo line per item (`name weight`),
    -- LF-terminated — the inventory's flat file
    [{ path := "demo.txt"
       contents := String.intercalate "\n"
         (items.map (fun it => s!"{it.name} {it.weight}")) ++ "\n" }]

/-! ## The consumer's real content (defs land below this line) -/

/-- One more item — the attribute appends at elaboration; the
    replay reads it in the consumers of this module. -/
@[demoAppItem]
def gizmoEntry : DemoAppItem := { name := "gizmo", weight := 2 }

/-- The items in elaboration order (the replay's expected face). -/
def items : List DemoAppItem := [sampleEntry, gizmoEntry]

/-- THE app's one real invariant: the units moved is the FOLD over
    the items — never a hand-kept total. -/
def unitsMoved : Nat :=
  items.foldl (fun acc it => acc + it.weight) 0

-- The replay pin for ALL entries (the generated Tests pin carries
-- the FIRST entry + the ≥1 shape; the full names ride here). A
-- drift FAILS the build.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  match ← demoAppItemRegistry env with
  | .error e => Lean.throwError s!"lane fold drifted: {e}"
  | .ok reg =>
    let names := reg.items.map (·.name)
    if names == ["sample", "gizmo"] then
      pure ()
    else
      Lean.throwError s!"lane replay drifted: {names}"

/-! ## The flow suite (the consumer widens the property and the
    controls — one real must-fail control per coverage family) -/

/-- The widened suite: the app's REAL invariants + the REAL
    must-fail controls (one per coverage family: the fold, the
    naming). -/
def demoAppItemFlowSpec : Spec :=
  Spec.ofList "DemoApp flow invariants" (fun _ => do
    assert (unitsMoved == 3) "the units fold (1 + 2)"
    assert (demoAppItemEmitter.outputs == ["demo.txt"])
      "the emitter declares its output path"
    match demoAppItemEmitter.run items with
    | [f] => do
      assert (f.path == "demo.txt") "the fold writes the declared path"
      assert (f.contents.contains "sample 1")
        "the fold renders each item"
      assert (f.contents.endsWith "\n") "the demo file is LF-terminated"
    | _ => assert false "the fold emits exactly one file"
    assert ((demoAppItemObligation sampleEntry).tier
        == .decidableNow) "the tier is computed from the evidence kind"
    assert ((demoAppItemUsageDiag "SCF0001" "probe").code.code == "SCF0001")
      "the diag helper constructs the ONE envelope")
    [ ("sabotage: the demo fold drops an item", fun _ =>
        assert (unitsMoved == 2)
          "control fired: the fold dropped an item")
    , ("sabotage: the naming fn drops the name", fun _ =>
        assert (demoAppItemNameOf sampleEntry == "")
          "control fired: the naming dropped the name")
    ]
    8 42

end DemoApp
