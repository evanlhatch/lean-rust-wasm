/-
# SchemaTests.Inc — the incremental violation maintenance's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The fixture is SchemaCore.Commit's worked example
(the duel's proposals); the module under test is SchemaCore.IncViolate.

The three faces of the increment:

1. AGREEMENT — the delta-driven check path (`checkDeltaInc`) and the
   post-state check path (`Commit.checkDelta`) produce the SAME verdicts
   AND the same payloads on the slice's fixture — kernel-pinned
   list-equality per duel proposal, both paths exercised.
2. THE CROSS TERM (03 §9's named trap) — the join's delta carries the
   cross term ΔA⋈ΔB: for the cross delta (an account INSERT + a transfer
   INSERT referencing it), the naive delta evaluation — the transfer
   insert judged against the OLD ids — dangles the transfer (a false
   refusal); the checker accepts (the fragment's boundary routes the
   join's ΔA face to the fallback checker, which joins against the
   post-state). Both sides pinned: the cross term is load-bearing.
3. THE REVIVED BLOCK — the negative face's update maintenance reads the
   ROW TABLE (the maintained state carries it): a previously-clean row's
   update can go negative. The naive violations-only maintenance misses
   exactly that revival — pinned: the naive delta would ACCEPT bob's
   overdraft.

Evidence, not architecture — the five-question block lives in the
module under test (SchemaCore.IncViolate).
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.IncViolate
import SchemaTests.Commit

open SchemaCore TestingKit

/-- The violations' equality (Violation carries no BEq — the render is
    NOT byte-tied; the equality is the CTORS', over the rows' `rowBeq`). -/
def violEq : Violation → Violation → Bool
  | .dupId a, .dupId b => a == b
  | .negative a, .negative b => rowBeq accountFields a b
  | .danglingSrc a, .danglingSrc b => rowBeq transferFields a b
  | .danglingDst a, .danglingDst b => rowBeq transferFields a b
  | _, _ => false

instance : BEq Violation := ⟨violEq⟩

/-- The rows' equality (the lane's `rowBeq` — Update's bridge). The
    specs' `==` on the faces' lists rides these. -/
instance : BEq (RowVals accountFields) := ⟨rowBeq accountFields⟩
instance : BEq (RowVals transferFields) := ⟨rowBeq transferFields⟩

/-! ## The agreement face (kernel pins: both paths, same verdicts) -/

/-- THE AGREEMENT (kernel-checked, per duel proposal): the delta-driven
    check's payload IS the post-state check's — exact list equality on
    the slice's fixture (the maintained path handles every face: the
    pointwise negative face, the join faces through the transfer
    insert/remove steps, the dup face over the stable ids). -/
example : checkDeltaInc fixtureSnap.db okP = checkDelta fixtureSnap.db okP := rfl
example : checkDeltaInc fixtureSnap.db overdraftP
    = checkDelta fixtureSnap.db overdraftP := rfl
example : checkDeltaInc fixtureSnap.db danglingP
    = checkDelta fixtureSnap.db danglingP := rfl
example : checkDeltaInc fixtureSnap.db staleP
    = checkDelta fixtureSnap.db staleP := rfl

/-- The verdicts agree (the theorem) and the incremental verdict is the
    query's decision — live on the fixture. -/
example : checkVerdictInc fixtureSnap.db okP = .accept := rfl
example : checkVerdictInc fixtureSnap.db overdraftP
    = .refuse (checkDeltaInc fixtureSnap.db overdraftP) := rfl

/-! ## The cross-term face (03 §9's named trap) -/

/-- Carol's row (id 3, balance 0) — the cross delta's account INSERT. -/
def carolRow : RowVals accountFields :=
  .cons (.u64 3) (.cons (.string "carol") (.cons (.i64 0) .nil))

/-- The cross delta's transfer INSERT: src 3 — carol, INSERTED BY THE
    SAME DELTA (the cross term ΔA⋈ΔB's face). -/
def crossT : RowVals transferFields :=
  transferRow { base := 1, tid := 8, src := 3, dst := 1, amount := 5 }

/-- THE CROSS DELTA: an account insert + a transfer insert referencing
    it. The account insert moves the id list — the join faces' ΔA —
    OUTSIDE the maintained fragment. -/
def crossDelta : Deltas where
  accounts := [RowDelta.insert carolRow]
  transfers := [RowDelta.insert crossT]

/-- THE BOUNDARY IS MECHANICAL: the account insert's step is `none` —
    the maintained path CANNOT take it (the named boundary, as data). -/
example : accStep? (RowDelta.insert carolRow)
      ⟨fixtureAccounts, negativeAccounts fixtureAccounts⟩ = none := rfl

/-- THE NAIVE DELTA MISSES THE CROSS TERM: the transfer insert judged
    against the OLD ids dangles — a false refusal. -/
example : danglingSrc [crossT] (accIds fixtureAccounts) = [crossT] := rfl

/-- THE CHECKER CARRIES THE CROSS TERM (through the named fallback):
    the post-state joins fresh — carol resolves the transfer — CLEAN. -/
example : violations (applyDeltas fixtureSnap.db crossDelta) = [] := rfl

/-- The incremental checker AGREES (the agreement theorem's live face
    over the fallback route). -/
example : incViolations fixtureSnap.db crossDelta = [] := rfl

/-! ## The maintained path's own teeth -/

/-- The maintained join face CARRIES the transfer insert's dangle (the
    fragment's path is not vacuous): the dangling proposal's delta is
    in-fragment, and the maintained relation names the row. -/
example : dangStep1? (accIds fixtureAccounts) trSrc
      (RowDelta.insert (transferRow danglingP)) [] = some [transferRow danglingP] :=
  rfl

/-- THE REVIVED BLOCK (the negative face's tooth): the naive
    violations-only maintenance of an account update — no row table —
    MISSES a previously-clean row's overdraft. -/
def negUpdNaive (negs : List (RowVals accountFields)) (r : RowVals accountFields) :
    List (RowVals accountFields) :=
  negs.filter (fun o => !FieldVal.beq (accKey o) (accKey r))
    ++ (if decide (accBal r < 0) then
          (negs.filter (fun o => FieldVal.beq (accKey o) (accKey r)))
            |>.map (fun _ => r)
        else [])

/-- Bob's row (id 2, balance 50) and his overdraft (the duel's p9's
    amount against his balance). -/
def bobRow : RowVals accountFields :=
  .cons (.u64 2) (.cons (.string "bob") (.cons (.i64 50) .nil))

def bobOverdrawn : RowVals accountFields :=
  withBal bobRow (accBal bobRow - Proposal.amt overdraftP)

/-- THE NAIVE MAINTENANCE IS EMPTY — it never sees bob's overdraft. -/
example : negUpdNaive (negativeAccounts fixtureAccounts) bobOverdrawn = [] := rfl

/-- THE TRUE MAINTENANCE (`negUpd`, with the row table) NAMES IT — the
    revived block is load-bearing. -/
example : negativeAccounts (applyRowDelta "id" (RowDelta.update bobOverdrawn)
    fixtureAccounts) = [bobOverdrawn] := rfl
example : negUpd fixtureAccounts (negativeAccounts fixtureAccounts) bobOverdrawn
    = [bobOverdrawn] := rfl

/-! ## The suite -/

/-- THE INCREMENTAL SUITE: the two faces' agreement (both paths, same
    verdicts), the cross term's teeth, the revived block's teeth. -/
def incSpec : Spec :=
  Spec.ofList "the incremental check agrees with the post-state check (both paths, same verdicts)"
    (fun _ => assert ((
      -- the maintained path's verdicts on the duel's proposals
      (match checkVerdictInc fixtureSnap.db okP with
        | .accept => true | .refuse _ => false)
      && (match checkVerdictInc fixtureSnap.db overdraftP with
        | .accept => false | .refuse _ => true)
      && (match checkVerdictInc fixtureSnap.db danglingP with
        | .accept => false | .refuse _ => true)
      -- the two faces' payloads agree exactly (the kernel pins' live echo)
      && (checkDeltaInc fixtureSnap.db okP == checkDelta fixtureSnap.db okP)
      && (checkDeltaInc fixtureSnap.db overdraftP
            == checkDelta fixtureSnap.db overdraftP)
      -- the cross delta: the checker accepts (the cross term carried)
      && (incViolations fixtureSnap.db crossDelta == [])
      && (violations (applyDeltas fixtureSnap.db crossDelta) == [])
      -- the revived block: the true maintenance names bob's overdraft
      && (negUpd fixtureAccounts (negativeAccounts fixtureAccounts) bobOverdrawn
            == [bobOverdrawn])))
      "the incremental face drifted")
    [ ("the incremental path accepts the overdraft",
        fun _ =>
          assert ((match checkVerdictInc fixtureSnap.db overdraftP with
                  | .accept => true | .refuse _ => false))
            "control fired: the incremental path must REFUSE the overdraft — \
              the maintained negative face carries the revived block")
    , ("the naive transfer-delta agrees with the checker on the cross delta",
        fun _ =>
          assert ((danglingSrc [crossT] (accIds fixtureAccounts) == []
            && (incViolations fixtureSnap.db crossDelta == [])))
            "control fired: the naive delta dangles the transfer (the cross \
              term is load-bearing) — the checker must NOT agree with it")
    , ("the maintained negative face survives without the revived block",
        fun _ =>
          assert ((negUpdNaive (negativeAccounts fixtureAccounts) bobOverdrawn
            == [bobOverdrawn]))
            "control fired: the violations-only maintenance MISSES the \
              revival — the row table in the maintained state is \
              load-bearing")
    , ("the maintained path drops the transfer insert's dangle",
        fun _ =>
          assert ((incViolations fixtureSnap.db
              { accounts := [], transfers := [RowDelta.insert
                  (transferRow danglingP)] } == []))
            "control fired: the maintained join face must CARRY the \
              dangling row — the fragment's path is not vacuous") ]
    4 42

/-! ## The boundary's negative control -/

/-- THE FALLBACK'S AGREEMENT (the boundary's other side): for the
    out-of-fragment cross delta, the incremental checker's route IS the
    fallback — and the fallback IS the post-state checker. A mutant that
    routes the fragment's steps wrong shows up here. -/
def incFallbackSpec : Spec :=
  Spec.ofList "the fallback checker agrees with the maintained faces it replaces"
    (fun _ => assert ((
      -- the cross delta's route: the fallback = the post-state check
      (incViolations fixtureSnap.db crossDelta
        == violations (applyDeltas fixtureSnap.db crossDelta))
      -- the fragment's route: the maintained faces = the recomputed
      -- (danglingP is a PROPOSAL — the check paths take it directly)
      && (checkDeltaInc fixtureSnap.db danglingP
            == checkDelta fixtureSnap.db danglingP)))
      "the fallback's agreement drifted")
    [ ("the fallback disagrees with the checker",
        fun _ =>
          assert ((incViolations fixtureSnap.db crossDelta
            != violations (applyDeltas fixtureSnap.db crossDelta)))
            "control fired: the fallback IS the post-state checker — the \
              agreement is the theorem's content, never a divergence")
    , ("the account insert stays in the maintained fragment",
        fun _ =>
          assert (((accStep? (RowDelta.insert carolRow)
              ⟨fixtureAccounts, negativeAccounts fixtureAccounts⟩).isSome))
            "control fired: the account insert moves the id list — the \
              join faces' ΔA is outside the fragment (the boundary is \
              named, never silent)") ]
    4 42
