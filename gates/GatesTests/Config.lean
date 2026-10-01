/-
# GatesTests.Config — the dogfood's teeth (C4/N8: the tree's own knobs
as the FIRST config schema)

The module under test is `Gates.Common`'s config face (the
SchemaCore.Config discipline at the gates' knobs). Pure pins over the
pure cores (`knobOf`/`typedNat`/`knobsOfText`); the IO drivers' file
reads are the exe's business (`just gates` runs them).

1. THE PRECEDENCE IS THE DATA — env wins over the file; the file is
   the base layer; the envNat semantics (absent/unparsable/zero →
   default) preserved BYTE-FOR-BYTE on the env layer.
2. THE FILE LAYER'S TEETH — the mis-typed value refuses with the
   curated CF Diag; the violated check row refuses; the malformed
   text refuses; the ABSENT file is no layer.
3. THE NEGATIVE CONTROLS — the sabotages assert the misbehavior and
   must FAIL (15-patterns #5).
-/

import TestingKit.Harness
import Gates.Common

namespace GatesTests.Config

open SchemaCore TestingKit

/-- The knobs' file-layer record from raw pairs (the pure fixture
    helper — the load's lowering, skipped parse). -/
def knobsOfPairs (pairs : List (String × String)) :
    Except Kit.Diag (RowVals Gates.gatesItem.fields) :=
  match lowerPairs Gates.gatesItem.fields pairs with
  | .error d => .error d
  | .ok clauses =>
      match initialRow Gates.gatesItem.fields with
      | none => .error (configDiag SchemaCore.eCF0002 "no default row")
      | some base =>
          let r := applySources base
            [{ src := ConfigSource.file, overrides := clauses }]
          let keys := pairs.map (·.1)
          let fileChecks : List (Pred Gates.gatesItem.fields) :=
            Gates.gatesChecks.filter fun p => p.reads.any (· ∈ keys)
          if fileChecks.all (fun p => p.check r) then .ok r
          else .error (configDiag SchemaCore.eCF0003 "check row violated")

/-- The knobs' value under env (the precedence's pin helper; a
    REFUSED record never reads as a knob — the default speaks). -/
def knobUnder (pairs : List (String × String)) (env : Option String)
    (name : String) (dflt : Nat) : Nat :=
  match knobsOfPairs pairs with
  | .ok kr => Gates.knobOf (Gates.typedNat kr name dflt) env dflt
  | .error _ => dflt

def configFaceSpec : Spec :=
  Spec.ofList "the gates' knobs ride the config face: precedence, the envNat semantics, the file layer's teeth"
    (fun _ =>
      assert ((
      -- THE ENV OVERRIDE WINS (the same env vars win — the behavior
      -- is the legacy envNat's, byte-for-byte)
        (Gates.knobOf 4 (some "8") 6 == 8)
        && (Gates.knobOf 0 (some "8") 6 == 8)
      -- the envNat semantics on the env layer: absent/unparsable/zero
      -- → the DEFAULT (never the file layer — the strict identity)
        && (Gates.knobOf 4 none 6 == 4)
        && (Gates.knobOf 4 (some "bogus") 6 == 6)
        && (Gates.knobOf 4 (some "0") 6 == 6)
        && (Gates.knobOf 4 none 6 == 4)
      -- the file layer is the BASE (the env absent → the record's value)
        && (match knobsOfPairs [("all_jobs", "4")] with
              | .ok kr => Gates.typedNat kr "all_jobs" 6 == 4
              | .error _ => false)
        && (match knobsOfPairs [] with
              | .ok kr => Gates.typedNat kr "all_jobs" 6 == 6
              | .error _ => false)
      -- the FILE LAYER'S TEETH: the mis-typed value refuses (CF0002)
        && (match knobsOfPairs [("all_jobs", "eight")] with
              | .error d => d.code == SchemaCore.eCF0002
              | .ok _ => false)
      -- the violated check row refuses (CF0003 — jobs = 0)
        && (match knobsOfPairs [("all_jobs", "0")] with
              | .error d => d.code == SchemaCore.eCF0003
              | .ok _ => false)
      -- the malformed text refuses (the parse's curated Diag)
        && (match Gates.knobsOfText "all jobs=8\n" with
              | .error d => d.code == SchemaCore.eCF0002
              | .ok _ => false)
      -- the ABSENT file is no layer (the empty text = the defaults row)
        && (match Gates.knobsOfText "" with
              | .ok kr => Gates.typedNat kr "all_jobs" 6 == 6
              | .error _ => false)
      -- the rss_budget_mb face: 0 means DERIVE (no check row on it)
        && (match knobsOfPairs [("rss_budget_mb", "0")] with
              | .ok _ => true | .error _ => false)
      ))
      "the gates' config face drifted")
    [ ("the env source LOSES to the file layer",
        fun _ =>
          assert (knobUnder [("all_jobs", "4")] (some "8") "all_jobs" 6 == 4)
          "control fired: the env var must override the file layer — \
            the precedence is file < env")
    , ("the mis-typed file value is tolerated",
        fun _ =>
          assert (match knobsOfPairs [("all_jobs", "eight")] with
            | .ok _ => true | .error _ => false)
          "control fired: a mis-typed knob must refuse with the curated \
            CF Diag — the config face has teeth")
    , ("the violated check row is tolerated",
        fun _ =>
          assert (match knobsOfPairs [("all_jobs", "0")] with
            | .ok _ => true | .error _ => false)
          "control fired: jobs = 0 violates the declared >0 row — the \
            check lane's verdict is the load's refusal")
    , ("an env-parsable zero reads through to the record",
        fun _ =>
          assert (Gates.knobOf 4 (some "0") 6 == 4)
          "control fired: a zero env value is NEVER a knob value — the \
            envNat semantics (0 → default), preserved")
    ]
    4 42

/-! ## the axiom pins -/

#print axioms configFaceSpec

end GatesTests.Config
