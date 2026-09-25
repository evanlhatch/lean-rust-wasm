/-
# ReprTests — the representation discipline's test battery

Positive pins + the MANDATORY negative controls (15-patterns #5); the
sweep discipline is TestingKit's LCG tape (15-patterns #14): same seed,
byte-identical replay. The runner is TestingKit's (`mainOfSuites`).

1. `agreement` — the client theorem's runtime exercise: generated token
   programs run on BOTH representations (sorted assoc list /
   unsorted-with-duplicates log) give the SAME observation, and both
   agree with the spec run over `Abs` (same operations, related
   states, same abstract results). The negative controls: the
   drop-history sabotage (insert REPLACES the log — caught: the lost
   bindings change the lookups) and the iso-collapse (claims the two
   representations' CONCRETE states agree as lists — caught: the
   canonicalizations differ, that is the point).
2. `grades` — the non-iso honesty at runtime: the sorted rep's
   canonicity (a program and its REVERSED program leave the SAME
   sorted list — canonicity observed) against the raw rep's
   non-canonicity (order is meaningful in the log) with the SAME
   observations (order is meaningless in the map — the Abstraction
   grade observed). The negative controls: the canonicity sabotage
   (claims the raw states survive the reversal — caught) and the
   sorted-collapse (claims the sorted states differ — caught).
3. `teeth` — the construction gate: the unbundlability theorems
   (`sorted_ignore_step` / `raw_ignore_step`) pinned at compile time
   (an implementation whose operations don't preserve the relation
   doesn't construct); the duplicate-log pin (the raw rep cannot
   distinguish two states representing the same map — the abstraction
   collapses them). The negative controls: the two sabotage claims
   the teeth forbid (the ignore-step implementation agrees with the
   spec — caught; the duplicate states' observations differ — caught).

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the laws — the core-triple-only surface or the build fails.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Repr
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import ReprTests.Axioms

open Repr TestingKit

/-! ## Fixtures — Nat keys, Bool values, generated token programs -/

/-- Draw one operation token (keys 0-5, both values, insert/delete). -/
def drawOp (t : Tape) : Op Nat Bool × Tape :=
  let (k, t1) := t.below 6
  let (b, t2) := t1.below 2
  let (d, t3) := t2.below 2
  (if d = 0 then Op.insert k (b == 0) else Op.delete k, t3)

/-- Draw `n` operation tokens. -/
def drawOps (t : Tape) : Nat → List (Op Nat Bool) × Tape
  | 0 => ([], t)
  | n + 1 =>
      let (op, t1) := drawOp t
      let (rest, t2) := drawOps t1 n
      (op :: rest, t2)

/-- Draw a token program of length ≤ 6. -/
def drawProg (t : Tape) : List (Op Nat Bool) × Tape :=
  let (n, t1) := t.below 7
  drawOps t1 n

/-- The spec run: the abstract steps folded over the program (the
    simple mathematical spec, executed). -/
def specRun (prog : List (Op Nat Bool)) : Abs Nat Bool :=
  prog.foldl (fun a t => stepAbs t a) (Abs.empty Nat Bool)

/-- A raw-rep run with a SUPPLIED step (the sabotages use it). -/
def runRaw (step : Op Nat Bool → RawAssoc Nat Bool → RawAssoc Nat Bool)
    (prog : List (Op Nat Bool)) : RawAssoc Nat Bool :=
  prog.foldl (fun c t => step t c) rawRep.initC

/-- Render an observation for the failure message. -/
def renderOpt (o : Option Bool) : String :=
  match o with
  | some b => toString b
  | none => "none"

/-! ## Suite 1: the two representations' agreements -/

/-- The agreements: for every key, the sorted rep's observation, the
    raw rep's observation, and the spec run's value coincide —
    `Repr.client_obs` / `Repr.client_cross` observed at runtime. -/
def propAgree (t : Tape) : CheckResult := do
  let (prog, _) := drawProg t
  let sortedRun := runC sortedRep prog sortedRep.initC
  let rawRun := runC rawRep prog rawRep.initC
  let spec := specRun prog
  for k in [0:6] do
    let obsS := lookupS sortedRun.list k
    let obsR := lookupR rawRun k
    assert (obsS == obsR)
      s!"sorted vs raw disagree at key {k}: {renderOpt obsS} vs {renderOpt obsR}"
    assert (obsR == spec k)
      s!"raw vs spec disagree at key {k}: {renderOpt obsR} vs {renderOpt (spec k)}"
    assert (obsS == spec k)
      s!"sorted vs spec disagree at key {k}: {renderOpt obsS} vs {renderOpt (spec k)}"

/-- The DROP-HISTORY sabotage: the insert that REPLACES the log
    instead of appending. The discipline forbids the bundle (the
    `no_ignore_step` family); at runtime the lost bindings change the
    lookups. -/
def rawStepDrop : Op Nat Bool → RawAssoc Nat Bool → RawAssoc Nat Bool
  | .insert k v, _ => [(k, v)]
  | .delete k, l => deleteR k l

def negDropHistory (_ : Tape) : CheckResult :=
  -- fixed distinguishing program: two inserts; the sabotage loses the first
  let prog : List (Op Nat Bool) := [Op.insert 1 true, Op.insert 2 false]
  let real := runRaw rawStep prog
  let sab := runRaw rawStepDrop prog
  assert (lookupR real 1 == lookupR sab 1)
    "the drop-history sabotage was not caught"

/-- The ISO-COLLAPSE sabotage: claims the two representations'
    CONCRETE states agree as lists. Caught: the canonicalizations
    differ (insort vs append) — that is the point of two
    representations. -/
def negIsoCollapse (_ : Tape) : CheckResult :=
  let prog : List (Op Nat Bool) := [Op.insert 1 true, Op.insert 0 false]
  let sortedRun := runC sortedRep prog sortedRep.initC
  let rawRun := runC rawRep prog rawRep.initC
  assert (sortedRun.list == rawRun)
    "the iso-collapse sabotage was not caught: the concrete states agree"

def specAgreement : Spec := Spec.ofList "repr-agreement"
  propAgree
  [ ("drop-history", negDropHistory),
    ("iso-collapse", negIsoCollapse) ]
  12 20250731

/-! ## Suite 2: the non-iso honesty at runtime -/

/-- Canonicity observed: the sorted rep's state after a program equals
    the state after the REVERSED program (both ascending, same
    abstract map — `canonicity` at runtime); the raw rep's OBSERVATION
    also agrees (order is meaningless in the map — the Abstraction
    grade) while its state carries the order (order is meaningful in
    the log). -/
def propGrades (t : Tape) : CheckResult := do
  let (prog0, _) := drawProg t
  -- the reversal argument needs COMMUTING operations: inserts commute,
  -- deletes do not (delete-then-insert ≠ insert-then-delete) — so the
  -- canonicity exercise runs on the program's INSERTS only
  let prog := prog0.filter (fun op =>
    match op with
    | .insert _ _ => true
    | .delete _ => false)
  let sortedRun := runC sortedRep prog sortedRep.initC
  let sortedRev := runC sortedRep prog.reverse sortedRep.initC
  let rawRun := runC rawRep prog rawRep.initC
  let rawRev := runC rawRep prog.reverse rawRep.initC
  -- the sorted states AGREE (canonicity, the retraction-grade face)
  assert (sortedRun.list == sortedRev.list)
    "canonicity broke: the sorted rep's state depends on the insert order"
  -- the raw OBSERVATIONS agree (the Abstraction grade: order carries
  -- no meaning in the MAP)
  for k in [0:6] do
    assert (lookupR rawRun k == lookupR rawRev k)
      s!"the raw rep's observation depends on the insert order at key {k}"

/-- The CANONICITY SABOTAGE: claims the raw rep's STATE also survives
    the reversal (canonicity for the raw rep). Caught: the write log's
    order is meaningful — the raw rep has NO canonicity. -/
def negCanonicitySabotage (_ : Tape) : CheckResult :=
  let prog : List (Op Nat Bool) := [Op.insert 1 true, Op.insert 2 false]
  let rawRun := runC rawRep prog rawRep.initC
  let rawRev := runC rawRep prog.reverse rawRep.initC
  assert (rawRun == rawRev)
    "the canonicity sabotage was not caught: the raw states agree"

/-- The SORTED-COLLAPSE sabotage: claims the sorted rep's state
    depends on the insert order. Caught: it does not (canonicity). -/
def negSortedCollapse (_ : Tape) : CheckResult :=
  let prog : List (Op Nat Bool) := [Op.insert 1 true, Op.insert 2 false]
  let sortedRun := runC sortedRep prog sortedRep.initC
  let sortedRev := runC sortedRep prog.reverse sortedRep.initC
  assert (!(sortedRun.list == sortedRev.list))
    "the sorted-collapse sabotage was not caught: the sorted states differ"

def specGrades : Spec := Spec.ofList "repr-grades"
  propGrades
  [ ("canonicity-sabotage", negCanonicitySabotage),
    ("sorted-collapse", negSortedCollapse) ]
  12 20250732

/-! ## Suite 3: the construction gate's teeth -/

/-- The teeth, pinned at compile time: an implementation whose step
    ignores an operation cannot bundle (`Repr.no_ignore_step`
    instantiated at BOTH representations). -/
example (k : Nat) (v : Bool) :
    ¬ ∃ r : Represents (Op Nat Bool) (Abs Nat Bool) (SortedAssoc Nat Bool)
        (Abs Nat Bool),
      r.R = RSorted ∧ r.stepC = (fun _ c => c) ∧ r.stepA = stepAbs :=
  sorted_ignore_step k v

example (k : Nat) (v : Bool) :
    ¬ ∃ r : Represents (Op Nat Bool) (Abs Nat Bool) (RawAssoc Nat Bool)
        (Abs Nat Bool),
      r.R = RRaw ∧ r.stepC = (fun _ c => c) ∧ r.stepA = stepAbs :=
  raw_ignore_step k v

/-- The duplicate-log pin: the raw rep cannot distinguish the two
    states `[(k,v),(k,v)]` and `[(k,v)]` — the abstraction collapses
    them (`raw_not_injective`'s witness observed). -/
def propTeeth (t : Tape) : CheckResult := do
  let (k, t1) := t.below 6
  let (b, _) := t1.below 2
  let v := b == 0
  let l1 : RawAssoc Nat Bool := [(k, v), (k, v)]
  let l2 : RawAssoc Nat Bool := [(k, v)]
  -- the abstraction collapses the duplicate states (observation equal)
  assert (lookupR l1 k == lookupR l2 k)
    "the duplicate-log states' observations differ"
  -- the states themselves are distinct (the non-iso witness)
  assert (!(l1 == l2))
    "the raw non-injectivity witness failed: the states agree"
  -- the client theorem's instance, computed
  let prog : List (Op Nat Bool) := [Op.insert k v, Op.delete (k + 6)]
  assert (toAbsR (runC rawRep prog rawRep.initC) k == some v)
    "the client theorem's instance broke on the out-of-range delete"

def negIgnoreBundled (_ : Tape) : CheckResult :=
  -- SABOTAGE: claims an ignore-step implementation still agrees with
  -- the spec. Caught: the sabotaged run's observation diverges (the
  -- runtime face of the unbundlability teeth above).
  let k := 3; let v := true
  let prog : List (Op Nat Bool) := [Op.insert k v]
  let sab := runRaw (fun _ c => c) prog
  let spec := specRun prog
  assert (lookupR sab k == spec k)
    "the ignore-step sabotage was not caught"

def negDupObsDiffer (_ : Tape) : CheckResult :=
  -- SABOTAGE: claims the duplicate-log states are observationally
  -- DISTINCT. Caught: the abstraction collapses them (last-wins).
  let k := 2
  assert (!(lookupR [(k, true), (k, true)] k == lookupR [(k, true)] k))
    "the duplicate-observation sabotage was not caught"

def specTeeth : Spec := Spec.ofList "repr-teeth"
  propTeeth
  [ ("ignore-bundled", negIgnoreBundled),
    ("dup-obs-differ", negDupObsDiffer) ]
  12 20250733

def main : IO UInt32 :=
  mainOfSuites [("Repr", [specAgreement, specGrades, specTeeth])]
