/-
# DatalogTests — the closures, the refusal teeth, the negative controls

Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5). Suites:

1. `closures` — the classic closures pinned as values: reachability
   (edge/Path), the ancestor chain, the recursive eligibility rule; the
   monotonicity + fixpoint pins (the theorems exercised as data).
2. `correctness` — `deriv_iff_eval` exercised in BOTH directions: a
   hand-built `Deriv` derivation lands in `eval`, and `eval`'s facts
   have derivations; the LFP's leastness exercised.
3. `safety-teeth` — the safety checker's LOUD refusals: the negated
   literal (the named refusal), the unbound head variable; `Program.run`
   refuses with a rendered message naming the rule.
4. `sweep` — the LCG-seeded property sweep (the fixpoint + EDB-subset
   properties over generated instances) with the mandatory negative
   controls: the one-step-suffices sabotage (caught on chains needing
   two steps) and the unsafe-check-passes sabotage.

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the monotonicity/stabilization/correctness theorems.
-/

import Datalog
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import DatalogTests.Axioms

set_option maxRecDepth 40000

open Datalog TestingKit

/-! ## Fixtures -/

def edge : Pred := ⟨"edge", 2⟩
def path : Pred := ⟨"path", 2⟩
def parent : Pred := ⟨"parent", 2⟩
def anc : Pred := ⟨"ancestor", 2⟩
def basic : Pred := ⟨"basic", 1⟩
def elig : Pred := ⟨"eligible", 1⟩
def req : Pred := ⟨"req", 2⟩

def atom2 (p : Pred) (x y : Nat) : Atom Nat := ⟨p, [x, y]⟩
def atom1 (p : Pred) (x : Nat) : Atom Nat := ⟨p, [x]⟩

/-- `path(X,Y) :- edge(X,Y).` -/
def rPathBase : Rule Nat :=
  ⟨path, [Term.var "X", Term.var "Y"],
    [⟨true, edge, [Term.var "X", Term.var "Y"]⟩]⟩

/-- `path(X,Z) :- path(X,Y), edge(Y,Z).` -/
def rPathRec : Rule Nat :=
  ⟨path, [Term.var "X", Term.var "Z"],
    [⟨true, path, [Term.var "X", Term.var "Y"]⟩,
     ⟨true, edge, [Term.var "Y", Term.var "Z"]⟩]⟩

def pathProg : Program Nat := [rPathBase, rPathRec]

/-- `ancestor(X,Y) :- parent(X,Y).` -/
def rAncBase : Rule Nat :=
  ⟨anc, [Term.var "X", Term.var "Y"],
    [⟨true, parent, [Term.var "X", Term.var "Y"]⟩]⟩

/-- `ancestor(X,Z) :- parent(X,Y), ancestor(Y,Z).` -/
def rAncRec : Rule Nat :=
  ⟨anc, [Term.var "X", Term.var "Z"],
    [⟨true, parent, [Term.var "X", Term.var "Y"]⟩,
     ⟨true, anc, [Term.var "Y", Term.var "Z"]⟩]⟩

def ancProg : Program Nat := [rAncBase, rAncRec]
def parentFacts : List (Atom Nat) :=
  [atom2 parent 1 2, atom2 parent 2 3, atom2 parent 3 4]

/-- `eligible(X) :- basic(X).` -/
def rEligBase : Rule Nat :=
  ⟨elig, [Term.var "X"], [⟨true, basic, [Term.var "X"]⟩]⟩

/-- `eligible(X) :- req(X,Y), eligible(Y).` — the recursive eligibility. -/
def rEligRec : Rule Nat :=
  ⟨elig, [Term.var "X"],
    [⟨true, req, [Term.var "X", Term.var "Y"]⟩,
     ⟨true, elig, [Term.var "Y"]⟩]⟩

def eligProg : Program Nat := [rEligBase, rEligRec]
def eligFacts : List (Atom Nat) :=
  [atom1 basic 1, atom1 basic 2, atom2 req 3 1, atom2 req 4 3]

/-- The chain fixture: 1 → 2 → 3 → 4 needs THREE path-derivations after
    the EDB — the height the one-step-sabotage control must miss. -/
def chainFacts : List (Atom Nat) :=
  [atom2 edge 1 2, atom2 edge 2 3, atom2 edge 3 4]

/-! ## Suite 1: the closures (value pins) -/

-- the programs are safe and well-formed (the checker agrees)
theorem pathProg_ok : pathProg.all (fun r => r.safe && decide (r.wf)) = true := by decide
theorem ancProg_ok : ancProg.all (fun r => r.safe && decide (r.wf)) = true := by decide
theorem eligProg_ok : eligProg.all (fun r => r.safe && decide (r.wf)) = true := by decide

-- reachability: the transitive closure, and ONLY it

theorem path_1_4 : atom2 path 1 4 ∈ eval pathProg chainFacts := by decide
theorem path_1_2 : atom2 path 1 2 ∈ eval pathProg chainFacts := by decide
theorem not_path_2_1 : ¬ (atom2 path 2 1 ∈ eval pathProg chainFacts) := by decide
theorem not_path_1_5 : ¬ (atom2 path 1 5 ∈ eval pathProg chainFacts) := by decide

-- the ancestor chain
theorem anc_1_4 : atom2 anc 1 4 ∈ eval ancProg parentFacts := by decide
theorem not_anc_2_1 : ¬ (atom2 anc 2 1 ∈ eval ancProg parentFacts) := by decide

-- the recursive eligibility: 4 is eligible THROUGH 3's requirement on 1
theorem elig_4 : atom1 elig 4 ∈ eval eligProg eligFacts := by decide
theorem elig_1 : atom1 elig 1 ∈ eval eligProg eligFacts := by decide
theorem req_not_derived : ¬ (atom2 req 2 9 ∈ eval eligProg eligFacts) := by decide

/-! ## Suite 2: the theorems exercised (monotone operator, LFP, correctness) -/

-- THE MONOTONICITY (02-data-plane §9): more facts, at least the same consequences
theorem mono_pin :
    step pathProg chainFacts ⊆ step pathProg (chainFacts ++ [atom2 edge 9 9]) :=
  step_mono pathProg (fun _ ha => List.mem_append.2 (Or.inl ha))

-- THE STABILIZATION: the evaluator's output IS a fixpoint
theorem fixpoint_pin : step pathProg (eval pathProg chainFacts) = eval pathProg chainFacts :=
  eval_fix pathProg chainFacts (by decide) (by decide)

theorem fixpoint_pin_anc :
    step ancProg (eval ancProg parentFacts) = eval ancProg parentFacts :=
  eval_fix ancProg parentFacts (by decide) (by decide)

-- THE CORRECTNESS THEOREM, ← direction: eval's facts have DERIVATIONS
theorem path_1_4_derivable : Deriv pathProg chainFacts (atom2 path 1 4) :=
  (deriv_iff_eval pathProg chainFacts (by decide) (by decide) (by decide)
    (atom2 path 1 4)).2 (by decide)

-- THE CORRECTNESS THEOREM, → direction: a hand-built derivation lands in eval
def sigmaXY (u v : Nat) : String → Nat :=
  fun x => match x with | "X" => u | "Y" => v | _ => 0

theorem deriv_base_12 : Deriv pathProg chainFacts (atom2 path 1 2) :=
  Deriv.fire (r := rPathBase) (σ := sigmaXY 1 2)
    (show rPathBase ∈ pathProg from by decide)
    (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact rfl
      · exact absurd hl (by simp))
    (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact Deriv.base (by decide)
      · exact absurd hl (by simp))
    rfl

theorem base_deriv_lands : atom2 path 1 2 ∈ eval pathProg chainFacts :=
  deriv_base_12.eval_mem (by decide) (by decide) (by decide)

-- THE LFP's LEASTNESS: eval is below every pre-fixpoint above the EDB
-- (exercised with G := eval itself, closed by eval_fix)
theorem leastness_applies :
    eval pathProg chainFacts ⊆ eval pathProg chainFacts :=
  lfp_least pathProg chainFacts
    (fun a ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact by decide
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact by decide
        · rcases List.mem_cons.1 ha with rfl | ha
          · exact by decide
          · exact absurd ha (by simp))
    (fun a ha => by
      rw [eval_fix pathProg chainFacts (by decide) (by decide)] at ha
      exact ha)

/-! ## Suite 3: the safety refusal's teeth -/

/-- `path(X,Y) :- edge(X,0).` — Y is bound by NO body literal. -/
def rUnbound : Rule Nat :=
  ⟨path, [Term.var "X", Term.var "Y"],
    [⟨true, edge, [Term.var "X", Term.cst 0]⟩]⟩

/-- `path(X,Y) :- !edge(X,Y).` — NEGATION: outside the fragment. -/
def rNegated : Rule Nat :=
  ⟨path, [Term.var "X", Term.var "Y"],
    [⟨false, edge, [Term.var "X", Term.var "Y"]⟩]⟩

-- the negated literal: the NAMED refusal (stratified negation is not here)
theorem negated_refused : rNegated.check = some (.negation 0) := by decide

-- the unbound head variable: named, with the variable's name in the report
theorem unbound_refused : rUnbound.check = some (.unboundHead "Y") := by decide

-- the SAFE rules pass the same checker
theorem safe_accepted : rPathBase.check = none ∧ rPathRec.check = none := by decide

-- `Program.run` refuses (the shape is decidable) ...
theorem run_refuses : (match Program.run [rUnbound] chainFacts with
  | .error _ => true | .ok _ => false) = true := by decide
theorem run_refuses_negation_shape : (match Program.run [rNegated] chainFacts with
  | .error _ => true | .ok _ => false) = true := by decide

-- ... and LOUDLY: the rendered message names the rule index + the variable
-- (checked at runtime — string ops are not kernel-reducible)
def checkRunMessage : IO CheckResult := do
  match Program.run [rUnbound] chainFacts with
  | .error m =>
    pure (assert ("unsafe rule #0".isPrefixOf m && m.contains 'Y')
      "the refusal message does not name the rule and the variable")
  | .ok _ => pure (.error "run did not refuse an unsafe program")

def checkRunMessageNegation : IO CheckResult := do
  match Program.run [rNegated] chainFacts with
  | .error m =>
    pure (assert (m.contains "NEGATED")
      "the negation refusal does not name the exclusion")
  | .ok _ => pure (.error "run did not refuse a negation-laden program")

/-! ## Suite 4: the LCG-seeded sweep + the mandatory negative controls -/

/-- The generated EDB: the chain 0→1→2 ALWAYS present, the shortcut
    0→2 decided by the tape. -/
def mkEdbs (t : Tape) : List (Atom Nat) :=
  let (shortcut, _) := t.below 2
  [atom2 edge 0 1, atom2 edge 1 2] ++
    (if shortcut = 1 then [atom2 edge 0 2] else [])

def propFixpoint (t : Tape) : CheckResult := do
  let edb := mkEdbs t
  assert (step pathProg (eval pathProg edb) = eval pathProg edb)
    "eval is not a fixpoint"
  assert (edb.all (fun a => decide (a ∈ eval pathProg edb)))
    "an EDB fact is missing from eval"

def propOneStepSuffices (t : Tape) : CheckResult := do
  let edb := mkEdbs t
  -- SABOTAGE: claims ONE step of firing reaches the fixpoint. Caught on
  -- every instance where the shortcut is absent (a second step is needed).
  assert (iter pathProg edb 1 = eval pathProg edb)
    "one-step sabotage not caught"

def propUnsafePasses (_ : Tape) : CheckResult := do
  -- SABOTAGE: claims the unsafe rule passes the safety check.
  assert (rUnbound.check = none) "unsafe rule passed the check"

def specClosures : Spec := Spec.ofList "datalog-closures"
  propFixpoint
  [ ("one-step-suffices", propOneStepSuffices),
    ("unsafe-check-passes", propUnsafePasses) ]
  12 20250714

-- the refusal MESSAGES run at runtime (string ops are not kernel-decidable);
-- their verdicts ride main's exit code, next to the pure sweep.

def main : IO UInt32 := do
  let rc ← checkRunMessage
  let rcN ← checkRunMessageNegation
  match rc, rcN with
  | .ok (), .ok () => pure ()
  | _, _ =>
    IO.println "run-refusal-message checks FAILED"
    match rc with
    | .ok () => pure ()
    | .error e => IO.println s!"  {e}"
    match rcN with
    | .ok () => pure ()
    | .error e => IO.println s!"  {e}"
  let code ← mainOfSuites [("Datalog", [specClosures])]
  let extra := (match rc with | .ok () => 0 | .error _ => 1) +
    (match rcN with | .ok () => 0 | .error _ => 1)
  return if extra == 0 then code else 1
