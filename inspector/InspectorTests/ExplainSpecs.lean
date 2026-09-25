/-
# InspectorTests.ExplainSpecs — the explain command's pins

Positive pins + the MANDATORY negative controls (15-patterns #5) over
`Inspector.Explain`'s composite report (the explanations lane's command
face — 02 §11: why present / why absent / which change repairs):

- the WHY-PRESENT section renders the derivation (the base fact + the
  filter's rule);
- the WHY-ABSENT section renders the blocking condition + the NAMED
  completeness assumption, and the REFUSED face answers without
  claiming (the honesty tooth: the refusal must NOT claim absence);
- the MISSING-PARTNER section names the key-join's miss;
- the REPAIR section renders each candidate followed by the
  SPECIFICATION'S OWN VERDICT (residual violations as data) and the
  duplicate's honest NONE;
- the closing honesty line names the proved verdict face
  (`WhyAbsent.verdict_sound`).

The negative controls are the lying renders (a refusal claiming
absence; the honest-none rendered as a fabricated candidate; the
report omitting the declared scope; a generic invariant-failure line).
-/

import Inspector.Explain
import TestingKit.Spec
import TestingKit.Harness

open Inspector TestingKit

def explainReportSpec : Spec :=
  Spec.ofList "the explain command's report: the three questions rendered honestly"
    (fun _ => do
      let rep := Inspector.Explain.explainReport
      -- WHY PRESENT: the derivation's fact + rule
      assert (rep.contains "why present — the supporting derivation")
        "the why-present section is missing"
      assert (rep.contains "present: [tid=10; src=1; dst=2; amount=30]")
        "the present answer's top line drifted"
      assert (rep.contains "fact: the base row [tid=10; src=1; dst=2; amount=30]")
        "the base fact is missing"
      assert (rep.contains "rule: the filter `amount > 20` accepts it")
        "the filter's rule is missing"
      -- WHY ABSENT: the blocker + the NAMED completeness
      assert (rep.contains "why absent: the row is not in the result")
        "the why-absent claim is missing"
      assert (rep.contains "the filter's predicate rejects it: amount > 20")
        "the blocking condition is missing"
      assert (rep.contains
          "under the declared completeness assumption: the explain fixture's tables as committed")
        "the declared completeness scope is missing"
      -- THE REFUSAL TOOTH: the refusal section never claims absence
      assert (rep.contains "why absent: REFUSED")
        "the refused face is missing"
      assert (rep.contains "absence claim would be a guess")
        "the guess discipline is missing"
      -- THE JOIN'S MISSING PARTNER
      assert (rep.contains "the join's missing partner")
        "the missing-partner section is missing"
      assert (rep.contains "no account row carries the key")
        "the miss's target table is missing"
      -- THE REPAIR SEED: the candidates + the specification's verdicts
      assert (rep.contains "candidate repair: account ← update [id=2; owner=\"bob\"; balance=0]")
        "the credit candidate drifted"
      assert (rep.contains "residual violations remain: unresolved dst")
        "the credit's residual verdict drifted"
      assert (rep.contains "candidate repair: transfer ← remove the row keyed 11")
        "the removal candidate drifted"
      assert (rep.contains "residual violations remain: negative balance")
        "the removal's residual verdict drifted"
      assert (rep.contains "candidate repair: NONE")
        "the honest none is missing"
      -- the closing honesty line
      assert (rep.contains "WhyAbsent.verdict_sound")
        "the proved-verdict line is missing")
    [ ("the refusal claims absence anyway",
        fun _ => assert
          ((Inspector.Explain.explainReport.splitOn "\n\n").filter
              (fun s => s.startsWith "-- why absent, REFUSED")
            |>.any (fun s => s.contains "the row is not in the result"))
          "the refusal was honest")
    , ("the honest none renders as a fabricated candidate",
        fun _ => assert
          (!(Inspector.Explain.explainReport.contains "candidate repair: NONE"))
          "the honest none was rendered")
    , ("the report omits the declared scope",
        fun _ => assert
          (!(Inspector.Explain.explainReport.contains
            "the explain fixture's tables as committed"))
          "the scope was rendered")
    , ("a violation renders as a generic invariant failure",
        fun _ => assert
          (Inspector.Explain.explainReport.contains
            "generic invariant failure: the state is invalid")
          "the report named the failing fact instead")
    ] 1 42

def inspectorExplainSpecs : List Spec := [explainReportSpec]
