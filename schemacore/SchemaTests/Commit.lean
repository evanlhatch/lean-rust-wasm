/- # SchemaTests.Commit — the bidirectional slice's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The fixture is SchemaCore.Violate/Commit's worked
example (03 §9): two keyed tables + the non-negative-balance invariant
+ the transfer→account foreign keys. The slice's THREE FACES:

1. COMMIT — a legal transfer's proposal checks clean and commits: the
   version bumps, the balances move, the ledger records the row.
2. REFUSE-WITH-ROWS — an overdraft's proposal REFUSES and the
   refusal's payload CARRIES THE VIOLATING ROW (02 §1's discipline —
   the render names the row's data, never a bare false).
3. STALE-REFUSE — a proposal computed against a stale snapshot
   version refuses on STALENESS, whatever its content (03 §3's
   race-honesty, `commit_stale` live).

Plus the duel's Lean side: the vector set's expectations are COMPUTED
by the checker (the golden IS the commit), the wire bytes are
`encVal`'s (the ONE encoding — the known-answer pin), and the Rust
consumer (tests/commit_slice.rs, generated) re-proposes each delta
byte-identically and agrees verdict-for-verdict — the DIFFERENTIAL
level (03 §3's table), named, never masqueraded as a theorem.

Evidence, not architecture — the five-question block lives in the
modules under test (SchemaCore.Violate / SchemaCore.Commit).
-/

import TestingKit.Harness
import SchemaCore

open SchemaCore TestingKit

/-! ## The fixture (SchemaCore.Commit's — ONE copy, cited) -/

/-- The fixture's snapshot version (the named snapshot the proposals
    check against). -/
example : fixtureSnap.version = 1 := rfl

/-- The duel carries four proposals — one per face of the slice. -/
example : duelProposals.length = 4 := rfl

/-- The legal transfer (the duel's p8). -/
def okP : Proposal := { base := 1, tid := 8, src := 1, dst := 2, amount := 30 }

/-- The overdraft (the duel's p9: bob's 50 cannot cover 500). -/
def overdraftP : Proposal := { base := 1, tid := 9, src := 2, dst := 1, amount := 500 }

/-- The dangling endpoint (the duel's p10: account 9 does not exist). -/
def danglingP : Proposal := { base := 1, tid := 10, src := 9, dst := 1, amount := 5 }

/-- The stale snapshot (the duel's p11: base 0 ≠ the fixture's 1). -/
def staleP : Proposal := { base := 0, tid := 11, src := 1, dst := 2, amount := 5 }

/-- THE WIRE's known-answer pin: p8's proposal bytes are five
    single-byte varints (the vectors are `encVal`'s — the ONE
    encoding; the Rust consumer re-proposes THESE bytes). -/
example : proposalBytes okP = [1, 8, 1, 2, 30] := rfl

/-- The overdraft's amount rides the wire as a two-group varint. -/
example : proposalBytes overdraftP = [1, 9, 2, 1, 244, 3] := rfl

/-- THE STATE-INVARIANT THEOREM's live face: the ACCEPTED transfer's
    post-state is VALID — the checker soundness ridden through the
    violation lane's bridge (kernel-checked, both citations live). -/
example : Valid (postDb fixtureSnap.db okP) :=
  check_sound fixtureSnap.db okP rfl

/-! ## The three faces -/

/-- THE COMMIT FACE: the legal transfer checks clean, commits, bumps
    the version, moves BOTH balances, and records the ledger row. -/
def commitFaceSpec : Spec :=
  Spec.ofList "a legal transfer commits (the version bumps, the state moves)"
    (fun _ => assert ((
      -- the check accepts (the post-state's violations are [], the
      -- verdict is the query's decision)
      (match checkVerdict fixtureSnap.db okP with
        | .accept => true | .refuse _ => false)
      -- THE SOUNDNESS's live face (the kernel pin below): the
      -- post-state's violation query is EMPTY — the executable echo
      && (match violations (postDb fixtureSnap.db okP) with
          | [] => true | _ => false)
      -- the commit applies
      && (match okP.commit fixtureSnap with
          | .ok s' =>
              match s'.db.accounts, s'.db.transfers with
              | a1 :: a2 :: _, [t] =>
                  (s'.version == 2)
                    && (accBal a1 == 70)
                    && (accBal a2 == 80)
                    && (trAmount t == 30)
                    && (trId t == 8)
              | _, _ => false
          | .error _ => false)))
      "the commit face drifted")
    [ ("the overdraft commits",
        fun _ =>
          assert ((match checkVerdict fixtureSnap.db overdraftP with
                  | .accept => true | .refuse _ => false))
            "control fired: the overdraft must REFUSE — bob's 50 cannot \
              cover 500 (the violation query's negative-balance face)")
    , ("the commit applies to a stale base",
        fun _ =>
          assert (match staleP.commit fixtureSnap with
                  | .ok _ => true | .error _ => false)
            "control fired: a stale-snapshot commit must REFUSE \
              (commit_stale — the race-honesty face)") ]
    4 42

/-- THE REFUSE-WITH-ROWS FACE: the overdraft refuses and the payload
    CARRIES the violating row (bob's, rendered as data). -/
def refuseFaceSpec : Spec :=
  Spec.ofList "an overdraft refuses with the violating rows as data"
    (fun _ =>
      match checkVerdict fixtureSnap.db overdraftP with
      | .refuse vs =>
          match vs with
          | [v] =>
              assert ((v.render.startsWith "negative balance:")
                && (v.render.contains "bob")
                && (v.render.contains "balance=-450"))
                "the refusal's payload lost the violating row"
          | _ => .error "the refusal's payload is not the single row"
      | .accept => .error "the overdraft was accepted")
    [ ("the refusal's payload is empty",
        fun _ =>
          match checkVerdict fixtureSnap.db overdraftP with
          | .refuse vs => assert (vs.isEmpty)
            "control fired: the refusal must CARRY the violating row \
              (02 §1's discipline — never a bare false)"
          | .accept => .error "control: the overdraft was accepted")
    , ("the commit succeeds on the invalid proposal",
        fun _ =>
          assert (match overdraftP.commit fixtureSnap with
                  | .ok _ => true | .error _ => false)
            "control fired: the adapter must refuse the invalid proposal \
              (the violations ride the error, never a silent apply)") ]
    4 42

/-- THE STALE-REFUSE FACE: the stale base refuses on STALENESS — even
    a VALID delta never commits against a stale snapshot. -/
def staleFaceSpec : Spec :=
  Spec.ofList "a stale-snapshot commit refuses on staleness"
    (fun _ =>
      assert ((match staleP.commit fixtureSnap with
               | .error (.stale 0 1) => true | _ => false)
      -- the CONTENT is irrelevant: the same delta at the CURRENT base
      -- would commit (the refusal is the version's, not the delta's)
        && (match checkVerdict fixtureSnap.db
              { staleP with base := 1 } with
            | .accept => true | .refuse _ => false))
        "the stale-refuse face drifted")
    [ ("a current-base proposal refuses as stale",
        fun _ =>
          assert (match ({ staleP with base := 1 }).commit fixtureSnap with
                  | .error (.stale _ _) => true | _ => false)
            "control fired: the staleness refusal must track the VERSION, \
              not the delta's content")
    , ("the stale refusal rides the violations",
        fun _ =>
          assert (match staleP.commit fixtureSnap with
                  | .error (.invalid _) => true | _ => false)
            "control fired: the stale refusal is the VERSION's (.stale), \
              never an invalid-content refusal") ]
    4 42

/-! ## The duel (the differential's Lean side) -/

/-- The duel's wiring: four vectors, the expectations cover them, and
    every expectation agrees with the CHECKER's own verdict (the
    golden IS the commit — a hand-flipped expectation fails here). -/
def duelSpec : Spec :=
  Spec.ofList "the commit duel's vectors + checker-computed expectations"
    (fun _ => assert ((
      (commitDuel.vectors.length == 4)
      && (Kit.Duel.expectsCovered commitDuel)
      && (commitDuel.expects.all fun (path, expect) =>
            match duelProposals.find? (fun np => commitDuelPath np.1 == path),
                  expect with
            | some np, .decode _ =>
                match np.2.commit fixtureSnap with
                | .ok _ => true | .error _ => false
            | some np, .refuse =>
                match np.2.commit fixtureSnap with
                | .error _ => true | .ok _ => false
            -- the commit duel's vocabulary is decode/refuse only: the
            -- wasm execution duel's `run`/`trap` rows name NO checker
            -- agreement here (false = the disagreement verdict)
            | some _, .run _ => false
            | some _, .trap => false
            | none, _ => false)
      -- the manifest's rows name the checker's verdicts verbatim
      && (match expectOf okP with
          | .decode "accept" => true | _ => false)
      && (match expectOf overdraftP with
          | .refuse => true | _ => false)
      -- the dangling face is IN the set (the foreign key's live face)
      && (match checkVerdict fixtureSnap.db danglingP with
          | .refuse vs =>
              match vs with
              | v :: _ => v.render.startsWith "unresolved src:"
              | [] => false
          | .accept => false)))
      "the duel's wiring drifted")
    [ ("an expect row is uncovered",
        fun _ =>
          assert (Kit.Duel.expectsCovered { commitDuel with
            expects := commitDuel.expects ++ [(commitDuelPath "p99", .refuse)]
            expects_nodup := by decide })
          "control fired: a manifest row over an ABSENT vector is a \
            generator bug — the shape check must fire")
    , ("an accept row is expect-refused",
        fun _ =>
          match expectOf okP with
          | .decode _ => .error "control fired: the legal transfer's \
              expectation IS accept — the checker computed it"
          | .refuse => .ok ()
          | .run _ | .trap => .error "control fired: the commit duel \
              speaks decode/refuse, never the wasm duel's vocabulary")
    , ("the vector bytes are a second encoding",
        fun _ =>
          assert (proposalBytes overdraftP != [1, 9, 2, 1, 244, 3])
            "control fired: the vectors ARE encVal's bytes — the \
              known-answer pin is live, never a second encoding") ]
    4 42 (by decide)
