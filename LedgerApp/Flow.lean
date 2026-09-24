/-
# LedgerApp.Flow — the consumer's hand-owned extension module (Scaffold seed)

Seeded ONCE by scaffold; NEVER regenerated (`scaffoldgen` skips an
existing Flow — one writer: the consumer). NO GENERATED header, no
byte-tie: this module is where the fill obligations land (12 §3) —
the emitter row's real fold (its `run` is app logic, not spec
data), the widened properties and the REAL must-fail controls
(one per coverage family, 15-patterns #5). The generated modules
stay byte-tie-clean; the app's real content lives HERE.

Five questions (notes/v3/01-core.md), filled from the AppSpec:
- root: crossing
- carrier grade: the posting over the registry's nodup-in-type substrate
- spine reading: registration = append; the ledger folds the replay
- ladder rung: generated
- gate row: axioms, docs-check
Consumes (the schema registry refs): Order
Capabilities generated: registry-lane, emitter, checks, diagnostics, tests
-/

import Lean
import Kit.Emit

import TestingKit.Harness
import LedgerApp.App

open LedgerApp TestingKit

namespace LedgerApp

/-! ## The emitter row (capability: emitter — R1 step 4 / 12 §3) -/

/-- The emitter row: pure and total over the item list, the
    declared outputs nodup IN THE TYPE. FILL OBLIGATIONS (12 §3):
    the real fold replaces `run`'s empty body; the law is cited
    when the fold's correspondence exists (`law := some ...` —
    until then this header note IS the why-not); the outputs join
    the cross-emitter one-writer audit. -/
def ledgerAppItemEmitter : Kit.Emit.Emitter (List LedgerAppItem) where
  name := "ledgerAppItem-emitter"
  style := .lean
  specSource := "AppSpec LedgerApp"
  outputs := ["ledger.txt"]
  run := fun items =>
    -- the real fold: one ledger line per posting (`name weight`),
    -- LF-terminated — the inventory's flat file
    [{ path := "ledger.txt"
       contents := String.intercalate "\n"
         (items.map (fun it => s!"{it.name} {it.weight}")) ++ "\n" }]

/-! ## The consumer's real content (defs land below this line) -/

/-- Two more postings — the attribute appends at elaboration; the
    replay reads them in the consumers of this module. `weight` is
    the counted units per posting (the template's seed field — the
    fields-are-template-fixed gap is named in the fitness report). -/
@[ledgerAppItem]
def nailsPosting : LedgerAppItem := { name := "nails", weight := 2 }

@[ledgerAppItem]
def boltsPosting : LedgerAppItem := { name := "bolts", weight := 4 }

/-- The postings in elaboration order (the replay's expected face). -/
def postings : List LedgerAppItem :=
  [sampleEntry, nailsPosting, boltsPosting]

/-- THE app's one real invariant: the units moved is the FOLD over
    the postings — never a hand-kept total. -/
def unitsMoved : Nat :=
  postings.foldl (fun acc p => acc + p.weight) 0

-- The replay pin for ALL entries (the generated Tests pin carries
-- the FIRST entry + the ≥1 shape; the full names ride here). A
-- drift FAILS the build.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  match ledgerAppItemRegistry env with
  | .error e => Lean.throwError s!"lane fold drifted: {e}"
  | .ok reg =>
    let names := reg.items.map (·.name)
    if names == ["sample", "nails", "bolts"] then
      pure ()
    else
      Lean.throwError s!"lane replay drifted: {names}"

/-! ## The flow suite (the consumer widens the property and the
    controls — one real must-fail control per coverage family) -/

/-- The widened suite: the ledger's REAL invariants + the REAL
    must-fail controls (one per coverage family: the fold, the
    check). -/
def ledgerAppItemFlowSpec : Spec :=
  Spec.ofList "LedgerApp flow invariants" (fun _ => do
    assert (unitsMoved == 7) "the units fold (1 + 2 + 4)"
    assert (ledgerAppItemEmitter.outputs == ["ledger.txt"])
      "the emitter declares its output path"
    match ledgerAppItemEmitter.run postings with
    | [f] => do
      assert (f.path == "ledger.txt") "the fold writes the declared path"
      assert (f.contents.contains "nails 2")
        "the fold renders each posting"
      assert (f.contents.endsWith "\n") "the ledger file is LF-terminated"
    | _ => assert false "the fold emits exactly one file"
    assert (ledgerAppItemCheck nailsPosting) "a named posting passes the check"
    assert ((ledgerAppItemCheckDiag sampleEntry).code.code == "SCF0013")
      "the refusal rides the ALLOCATED registry row (the coverage tooth's discipline)"
    assert ((ledgerAppItemUsageDiag "SCF0001" "probe").code.code == "SCF0001")
      "the diag helper constructs the ONE envelope")
    [ ("sabotage: the ledger fold drops a posting", fun _ =>
        assert (unitsMoved == 6)
          "control fired: the fold dropped a posting")
    , ("sabotage: the check waves an empty name through", fun _ =>
        assert (ledgerAppItemCheck { name := "", weight := 0 })
          "control fired: the check accepted an empty name")
    ]
    8 42

end LedgerApp
