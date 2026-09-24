/-
# ZSetTests — the delta substrate's test battery

Positive pins + the MANDATORY negative controls (15-patterns #5); the
sweep discipline is TestingKit's LCG tape (15-patterns #14): same seed,
byte-identical replay. The runner is TestingKit's (`mainOfSuites`).

1. The group laws' pins: signed merge over LCG-drawn (key, weight)
   pairs — commutes, canonicalizes through the merge; the negative
   controls are the sabotaged merge (drops a summand) and the
   weight-swapping merge.
2. The canonicalization's teeth: two differently-built equal ZSets are
   BEq-equal; the canonical FORM is pinned (sorted, coalesced, zero-
   free); the negative controls are the un-coalesced and the
   order-leaking forms.
3. The trichotomy's discipline (03 §7): two distinct zero-net events —
   the log has TWO entries while the delta projection is zero
   (net-zero ≠ nothing happened, at the data level); occurrence
   identity survives the delta projection. The negative controls are
   the two collapses the doctrine forbids (empty-log-from-net-zero,
   identity-collapse-into-the-delta).
4. The weighted-relation homomorphism seeds (02 §4): projection and
   join commute with union-adds; the negative controls are the two
   WRONG arithmetics (join-adds, projection-multiplies).

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the laws — the core-triple-only surface or the build fails.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import ZSet
import ZSet.Graph
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import ZSetTests.Axioms

open ZSet TestingKit

/-! ## Fixtures — drawn keys and nonzero weights -/

/-- Draw a key from the low half (0..24). -/
def drawKeyLo (t : Tape) : Nat × Tape :=
  let (k, t1) := t.below 25
  (k, t1)

/-- Draw a key from the high half (25..49) — never collides with the
    low half, so sabotages can't pass on a coincidence. -/
def drawKeyHi (t : Tape) : Nat × Tape :=
  let (k, t1) := t.below 25
  (k + 25, t1)

/-- Draw a nonzero weight in {-3, -2, -1, 1, 2, 3} (the sweep's
    negatives must fail on EVERY instance, so zero is excluded). -/
def drawW (t : Tape) : Int × Tape :=
  let (v, t1) := t.below 3
  let (s, t2) := t1.below 2
  (if s == 0 then ((v + 1 : Nat) : Int) else -((v + 1 : Nat) : Int), t2)

/-! ## 1. The group laws' pins -/

/-- Sabotage: the merge drops the second summand. -/
def negAddDropsSecond : Tape → CheckResult := fun t => do
  let (k1, t1) := drawKeyLo t
  let (k2, t2) := drawKeyHi t1
  let (w1, t3) := drawW t2
  let (w2, _) := drawW t3
  let z1 : ZSet Nat := fromList [(k1, w1)]
  let z2 : ZSet Nat := fromList [(k2, w2)]
  assert (add z1 z2 == z1) s!"control fired: {k1} + {k2} dropped {k2}"

/-- Sabotage: the merge swaps the weights between the keys. -/
def negAddSwapsWeights : Tape → CheckResult := fun t => do
  let (k1, t1) := drawKeyLo t
  let (k2, t2) := drawKeyHi t1
  let (w1, t3) := drawW t2
  let (w2, _) := drawW t3
  let z1 : ZSet Nat := fromList [(k1, w1)]
  let z2 : ZSet Nat := fromList [(k2, w2)]
  assert (add z1 z2 == fromList [(k1, w2), (k2, w1)])
    s!"control fired: {k1}+{k2} swapped weights"

/-- The group-law sweep: commutativity + the canonical merge, over
    drawn pairs; plus the non-idempotence pin (03 §7). -/
def groupSpec : Spec :=
  Spec.ofList "group laws (drawn pairs)" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, t2) := drawKeyHi t1
    let (w1, t3) := drawW t2
    let (w2, _) := drawW t3
    let z1 : ZSet Nat := fromList [(k1, w1)]
    let z2 : ZSet Nat := fromList [(k2, w2)]
    assert (add z1 z2 == add z2 z1) s!"{k1}+{k2} broke comm"
    assert (toList (add z1 z2) == toList (fromList [(k1, w1), (k2, w2)]))
      s!"{k1}+{k2} broke the canonical merge"
    assert (!(add z2 z2 == z2)) "signed addition is idempotent (the forbidden collapse)")
    [ ("add drops the second summand", negAddDropsSecond)
    , ("add swaps the weights", negAddSwapsWeights) ]
    64 42

/-! ## 2. The canonicalization's teeth -/

/-- Sabotage: coalescing keeps the FIRST weight instead of the sum. -/
def negCoalesceKeepsFirst : Tape → CheckResult := fun t => do
  let (k, _) := drawKeyLo t
  assert (fromList [(k, (1 : Int)), (k, 1)] == (fromList [(k, 1)] : ZSet Nat))
    s!"control fired: {k} coalesced to the first weight"

/-- Sabotage: the raw build order leaks into the canonical rep. -/
def negOrderLeaks : Tape → CheckResult := fun t => do
  let (k1, t1) := drawKeyLo t
  let (k2, _) := drawKeyHi t1
  let c : ZSet Nat := fromList [(k1, (1 : Int)), (k2, 2)]
  assert (toList c == [(k2, 2), (k1, 1)])
    s!"control fired: {k1},{k2} kept the raw order"

/-- The canonicalization sweep: two differently-built equal ZSets are
    BEq-equal, and the canonical form is PINNED (sorted, coalesced,
    zero-free). -/
def canonSpec : Spec :=
  Spec.ofList "canonicalization teeth" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, _) := drawKeyHi t1
    let a : ZSet Nat := fromList [(k1, (1 : Int)), (k1, 1)]
    let b : ZSet Nat := fromList [(k1, 2)]
    assert (a == b) s!"{k1}: coalesced build ≠ direct build"
    assert (toList a == [(k1, 2)]) s!"{k1}: canonical form wrong"
    let c : ZSet Nat := fromList [(k1, (1 : Int)), (k2, 2)]
    let d : ZSet Nat := fromList [(k2, 2), (k1, 1)]
    assert (c == d) s!"{k1},{k2}: build order broke BEq"
    assert (toList c == [(k1, 1), (k2, 2)]) s!"{k1},{k2}: rep not sorted")
    [ ("coalescing keeps the first weight", negCoalesceKeepsFirst)
    , ("the raw order leaks into the rep", negOrderLeaks) ]
    64 42

/-! ## 3. The trichotomy's discipline (03 §7) -/

/-- Two events with the SAME intent, DIFFERENT occurrence identity,
    whose net is zero — the trichotomy's whole point in three lines. -/
def e1 : Event Nat := { occId := 1, intent := [(3, (1 : Int)), (3, -1)] }
def e2 : Event Nat := { occId := 2, intent := [(3, (1 : Int)), (3, -1)] }

/-- The event log: TWO occurrences. -/
def eventLog : List (Event Nat) := [e1, e2]

/-- Sabotage: net-zero implies nothing happened (the log is empty). -/
def negNetZeroIsEmpty : Tape → CheckResult := fun _ => do
  assert (eventLog.isEmpty) "control fired: the log vanished because the net is zero"

/-- Sabotage: the delta projection carries the occurrence identity. -/
def negIdentityInDelta : Tape → CheckResult := fun _ => do
  assert (e1.occId == e2.occId) "control fired: the delta distinguished the occurrences"

/-- The trichotomy sweep: the two events are DISTINCT (occurrence
    identity), project to the SAME zero net, and the LOG stays
    two-entry while the delta is zero. -/
def trichotomySpec : Spec :=
  Spec.ofList "net-zero ≠ nothing happened" (fun _ => do
    assert (!(e1.occId == e2.occId)) "occurrence identity collapsed"
    assert (e1.net == e2.net) "same intent, different nets (impossible)"
    assert (toList e1.net == []) "the net of [(3,1),(3,-1)] is not zero"
    assert (eventLog.length == 2) "the log lost an occurrence")
    [ ("net-zero means the log is empty", negNetZeroIsEmpty)
    , ("the delta carries the occurrence identity", negIdentityInDelta) ]
    16 42

/-! ## 4. The weighted-relation homomorphism seeds (02 §4) -/

/-- The projection's key map: rows mod 3 (three preimage classes). -/
def mod3 : Nat → Nat := fun k => k % 3

/-- Sabotage: join ADDS weights (the union-arithmetic). -/
def negJoinAdds : Tape → CheckResult := fun t => do
  let (k, t1) := drawKeyLo t
  let (w1, t2) := drawW t1
  let (w2, _) := drawW t2
  let m : ZSet Nat := fromList [(k, w1)]
  let p : ZSet Nat := fromList [(k, w2)]
  assert (weight (join m p) k == weight m k + weight p k)
    s!"control fired: {k}'s join weight added"

/-- Sabotage: projection MULTIPLIES weights (the join-arithmetic). -/
def negProjectMultiplies : Tape → CheckResult := fun t => do
  let (k, t1) := drawKeyLo t
  let (w1, _) := drawW t1
  let m : ZSet Nat := fromList [(k, w1)]
  assert (weight (project mod3 m) (mod3 k) == weight m k * 3)
    s!"control fired: {k}'s projection weight multiplied"

/-- The homomorphism sweep: projection and join commute with
    union-adds (the ONE theorem's per-operation pins, 02 §4). -/
def homomorphismSpec : Spec :=
  Spec.ofList "weight-map homomorphism seeds" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, t2) := drawKeyHi t1
    let (w1, t3) := drawW t2
    let (w2, t4) := drawW t3
    let (wp, _) := drawW t4
    let m1 : ZSet Nat := fromList [(k1, w1)]
    let m2 : ZSet Nat := fromList [(k2, w2)]
    let p : ZSet Nat := fromList [(k1, wp), (k2, 1)]
    assert (project mod3 (add m1 m2) == add (project mod3 m1) (project mod3 m2))
      "projection broke over union"
    assert (join (add m1 m2) p == add (join m1 p) (join m2 p))
      "join broke over union"
    assert (weight (join m1 p) k1 == weight m1 k1 * weight p k1)
      "join's weight didn't multiply")
    [ ("join adds weights", negJoinAdds)
    , ("projection multiplies weights", negProjectMultiplies) ]
    64 42

/-! ## 5. The abstract weighted-relation layer (ZSet.Relation) -/

/-- Draw a nonzero Nat weight in {1..5} (the abstract suite's bags). -/
def drawWN (t : Tape) : Nat × Tape :=
  let (v, t1) := t.below 5
  (v + 1, t1)

/-- Sabotage: the ABSTRACT join adds weights. -/
def negJoinAddsW : Tape → CheckResult := fun t => do
  let (k, t1) := drawKeyLo t
  let (w1, t2) := drawWN t1
  let (wp, _) := drawWN t2
  let m : Weighted Nat Nat := fromListW [(k, w1)]
  let p : Weighted Nat Nat := fromListW [(k, wp)]
  assert (weightW (joinW m p) k == w1 + wp)
    s!"control fired: {k}'s abstract join weight added"

/-- Sabotage: the ABSTRACT projection multiplies weights. -/
def negProjectMultipliesW : Tape → CheckResult := fun t => do
  let (k, _) := drawKeyLo t
  let (w1, _) := drawWN t
  let m : Weighted Nat Nat := fromListW [(k, w1)]
  assert (weightW (projectW (fun x => x) m) k == w1 * 3)
    s!"control fired: {k}'s abstract projection weight multiplied"

/-- The abstract layer's operators over drawn Nat rows: union adds
    (comm + assoc), join multiplies, projection sums over preimages,
    filter restricts (02 §4's arithmetic, at the generic layer). -/
def abstractSpec : Spec :=
  Spec.ofList "abstract operators (Weighted Nat)" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, t2) := drawKeyHi t1
    let (w1, t3) := drawWN t2
    let (w2, t4) := drawWN t3
    let (wp, _) := drawWN t4
    let m : Weighted Nat Nat := fromListW [(k1, w1)]
    let n : Weighted Nat Nat := fromListW [(k2, w2)]
    let p : Weighted Nat Nat := fromListW [(k1, wp), (k2, 1)]
    -- union adds
    assert (weightW (addW m n) k1 == w1) s!"{k1}: union didn't keep m's weight"
    assert (weightW (addW m n) k2 == w2) s!"{k2}: union didn't keep n's weight"
    assert (weightW (addW m p) k1 == w1 + wp) s!"{k1}: union didn't add at the shared key"
    assert (weightW (addW m n) (k1 + k2 + 50) == 0) "off-support weight leaked"
    assert (weightW (addW n m) k1 == weightW (addW m n) k1) "union broke comm"
    assert (weightW (addW (addW m n) p) k1
      == weightW (addW m (addW n p)) k1) "union broke assoc"
    -- join multiplies
    assert (weightW (joinW m p) k1 == w1 * wp) s!"{k1}: join didn't multiply"
    assert (weightW (joinW m n) k1 == 0) "join invented weight off the shared support"
    -- projection sums over preimages (mod-3 classes; a collision sums)
    let g : Nat → Nat := fun k => k % 3
    let wExp : Nat := w1 + (if g k2 == g k1 then w2 else 0)
    assert (weightW (projectW g m) (g k1) == w1) s!"{k1}: projection lost the preimage"
    assert (weightW (projectW g (addW m n)) (g k1) == wExp) "projection broke over union"
    -- filter restricts
    let ev : Nat → Bool := fun k => k % 2 == 0
    let want : Nat := if k1 % 2 == 0 then w1 else 0
    assert (weightW (filterW ev m) k1 == want) s!"{k1}: filter kept/dropped wrong")
    [ ("join adds weights (Weighted)", negJoinAddsW)
    , ("projection multiplies (Weighted)", negProjectMultipliesW) ]
    64 42

/-! ## 6. THE ONE THEOREM (evaluate_wmap) -/

/-- A concrete fragment query: project the union of (filter evens) and
    (the self-join) — every operator row exercised. -/
def theQuery : Query Nat :=
  Query.project (fun k => k % 3)
    (Query.union (Query.filter (fun k => k % 2 == 0) Query.idQ)
      (Query.join Query.idQ Query.idQ))

/-- A raw weightwise map — NOT a `WeightMap` (it breaks `map_add`):
    the homomorphism premise's load-bearing-ness control. -/
def badWmap (f : Int → Int) (m : Weighted Int Nat) : Weighted Int Nat :=
  fromListW (m.rep.map (fun p => (p.1, f p.2)))

/-- Sabotage: THE ONE THEOREM for a non-homomorphism map (w ↦ w+1
    breaks `map_add` — the union's arithmetic diverges by one). -/
def negBrokenMap : Tape → CheckResult := fun t => do
  let (k, _) := drawKeyLo t
  let (w, _) := drawW t
  let m : Weighted Int Nat := fromListW [(k, w)]
  assert (weightW (badWmap (fun x => x + 1)
                     (evaluate (Query.union Query.idQ Query.idQ) m)) k
    == weightW (evaluate (Query.union Query.idQ Query.idQ)
                 (badWmap (fun x => x + 1) m)) k)
    s!"control fired: the theorem held for a non-homomorphism at {k}"

/-- Sabotage: the collapse treated as a TOTAL map — on signed deltas it
    is not additive (w + (-w) = 0: a delta and its negation collapse). -/
def negCollapseSigned : Tape → CheckResult := fun t => do
  let (k, _) := drawKeyLo t
  let (w, _) := drawW t
  let i : Weighted Int Nat := fromListW [(k, w)]
  let d : Weighted Int Nat := fromListW [(k, -w)]
  assert (weightW (supportCollapseW (addW i d)) k
    == wkindBool.add (weightW (supportCollapseW i) k) (weightW (supportCollapseW d) k))
    s!"control fired: the collapse was additive on signed deltas at {k}"

/-- THE ONE THEOREM with the identity map: evaluating through the
    identity weight-map changes nothing, pointwise over the drawn keys
    and their projection classes. -/
def oneTheoremIdSpec : Spec :=
  Spec.ofList "THE ONE THEOREM (identity map)" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, t2) := drawKeyHi t1
    let (w1, t3) := drawW t2
    let (w2, _) := drawW t3
    let m : Weighted Int Nat := fromListW [(k1, w1), (k2, w2)]
    let lhs := wmap idWeightMap (evaluate theQuery m)
    let rhs := evaluate theQuery (wmap idWeightMap m)
    assert (weightW lhs k1 == weightW rhs k1) s!"{k1}: the theorem broke (id)"
    assert (weightW lhs k2 == weightW rhs k2) s!"{k2}: the theorem broke (id)"
    assert (weightW lhs (k1 % 3) == weightW rhs (k1 % 3))
      s!"{k1}%3: the theorem broke (id)")
    [ ("the theorem holds for a non-homomorphism", negBrokenMap)
    , ("the collapse is additive on signed deltas", negCollapseSigned) ]
    64 42

/-- THE ONE THEOREM's ℤ→Bool instance over drawn BAGS: the support of
    the query result is the query over the supports, pointwise. -/
def oneTheoremCollapseSpec : Spec :=
  Spec.ofList "THE ONE THEOREM (ℤ→Bool collapse, bags)" (fun t => do
    let (k1, t1) := drawKeyLo t
    let (k2, t2) := drawKeyHi t1
    let (v1, t3) := t2.below 5
    let (v2, _) := t3.below 5
    let w1 : Int := (v1 + 1 : Nat)
    let w2 : Int := (v2 + 1 : Nat)
    let m : Weighted Int Nat := fromListW [(k1, w1), (k2, w2)]
    let col : Weighted Bool Nat := supportCollapseW m
    assert (weightW (supportCollapseW (evaluate theQuery m)) k1
      == weightW (evaluate theQuery col) k1) s!"{k1}: the collapse broke the theorem"
    assert (weightW (supportCollapseW (evaluate theQuery m)) k2
      == weightW (evaluate theQuery col) k2) s!"{k2}: the collapse broke the theorem"
    assert (weightW (supportCollapseW (evaluate theQuery m)) (k1 % 3)
      == weightW (evaluate theQuery col) (k1 % 3))
      s!"{k1}%3: the collapse broke the theorem")
    [ ("the theorem holds for a non-homomorphism", negBrokenMap)
    , ("the collapse is additive on signed deltas", negCollapseSigned) ]
    64 42

/-! ## 7. The old-values rule (the non-linear operators) -/

/-- Sabotage: the LINEAR distinct law (distinct of a union is the union
    of the distincts) — false, and the sweep must catch it. -/
def negLinearDistinct : Tape → CheckResult := fun t => do
  let (k, _) := drawKeyLo t
  let (w, _) := drawW t
  let i : Weighted Int Nat := fromListW [(k, w)]
  let d : Weighted Int Nat := fromListW [(k, -w)]
  assert (weightW (distinctW (addW i d)) k == weightW (addW (distinctW i) (distinctW d)) k)
    s!"control fired: the linear distinct law held at {k}"

/-- Sabotage: the old state irrelevant — two DIFFERENT old states with
    the SAME delta give the SAME distinct-delta. False: the old state
    is the load-bearing parameter. -/
def negOldIrrelevant : Tape → CheckResult := fun _ => do
  let k := 4
  let i1 : Weighted Int Nat := fromListW [(k, 1)]
  let i2 : Weighted Int Nat := fromListW [(k, 2)]
  let d : Weighted Int Nat := fromListW [(k, -1)]
  assert (weightW (distinctW (addW i1 d)) k == weightW (distinctW (addW i2 d)) k)
    "control fired: the old state didn't matter"

/-- The old-values discipline: distinct/threshold's incremental forms
    carry the OLD STATE as a parameter (`distinctHAt`/`thresholdHAt`),
    the laws hold with it, and the would-be-linear laws fail (the
    doctrine's honesty rule, pinned). -/
def oldValuesSpec : Spec :=
  Spec.ofList "old-values: distinct/threshold need history" (fun t => do
    let (k, t1) := drawKeyLo t
    let (w, _) := drawW t1
    let i : Weighted Int Nat := fromListW [(k, w)]
    let d : Weighted Int Nat := fromListW [(k, -w)]
    assert (weightW (distinctW (addW i d)) k
      == weightW (distinctW i) k + distinctHAt i d k) "distinct's old-values law broke"
    assert (weightW (thresholdW 1 (addW i d)) k
      == weightW (thresholdW 1 i) k + thresholdHAt 1 i d k)
      "threshold's old-values law broke"
    -- the TEETH: the would-be-linear law FAILS (the delta alone is not enough)
    assert (!(weightW (distinctW (addW i d)) k
      == weightW (addW (distinctW i) (distinctW d)) k))
      "distinct turned linear (impossible)")
    [ ("the linear distinct law holds", negLinearDistinct)
    , ("the old state is irrelevant", negOldIrrelevant) ]
    64 42

/-! ## The ZSet-as-instance bridge -/

/-- Sabotage: the bridge loses a weight. -/
def negBridgeDrops : Tape → CheckResult := fun _ => do
  let z : ZSet Nat := fromList [(3, (2 : Int)), (7, -1)]
  assert (weightW (ofZSet z) 3 == 999) "control fired: the bridge kept the weight"

/-- Sabotage: the bridge breaks the merge. -/
def negBridgeMerge : Tape → CheckResult := fun _ => do
  let z : ZSet Nat := fromList [(3, (2 : Int)), (7, -1)]
  assert (weightW (ofZSet (add z z)) 3 == 3) "control fired: the bridge kept the merge"

/-- The landed ZSet IS the ℤ instance: the bridge is weight- and
    operation-preserving (union/join/projection). -/
def bridgeSpec : Spec :=
  Spec.ofList "the ZSet bridge (ofZSet)" (fun _ => do
    let z : ZSet Nat := fromList [(3, (2 : Int)), (7, -1)]
    assert (weightW (ofZSet z) 3 == 2) "bridge lost a weight"
    assert (weightW (ofZSet z) 7 == -1) "bridge lost a weight"
    assert (weightW (ofZSet (add z z)) 3 == 4) "bridge broke the merge"
    assert (weightW (ofZSet (join z z)) 3 == 4) "bridge broke the join"
    assert (weightW (ofZSet (project (fun x => x % 2) z)) 1 == 1)
      "bridge broke the projection")
    [ ("the bridge drops a weight", negBridgeDrops)
    , ("the bridge breaks the merge", negBridgeMerge) ]
    16 42

/-! ## 8. The graph-reading layer (ZSet.Graph) -/

/-- The diamond fixture: 0→1, 0→2, 1→3, 2→3 (Bool weights = membership,
    the graph reading's canonical instance). -/
def diamond : Graph Bool Nat :=
  fromListW [((0, 1), true), ((0, 2), true), ((1, 3), true), ((2, 3), true)]

/-- The cycle fixture: the 3-cycle 0→1→2→0 + the self-loop 3→3. -/
def cycleGraph : Graph Bool Nat :=
  fromListW [((0, 1), true), ((1, 2), true), ((2, 0), true), ((3, 3), true)]

/-- The self-loop-only fixture (the acyclicity check's minimal refusal). -/
def loopGraph : Graph Bool Nat :=
  fromListW [((7, 7), true)]

/-- Sabotage: the reachability sweep misses two-step paths (one
    frontier step only). -/
def negReachOneStep : Tape → CheckResult := fun _ => do
  assert ((reachFrom diamond 1 0).contains 3)
    "control fired: the one-step sweep found the two-step vertex"

/-- Sabotage: the acyclicity check ignores the self-loop. -/
def negAcyclicSelfLoop : Tape → CheckResult := fun _ => do
  assert ((cycle? loopGraph 1).isNone)
    "control fired: the self-loop passed the acyclicity check"

/-- Sabotage: the cycle graph stratified (the wrong layer data). -/
def negStratifyCycle : Tape → CheckResult := fun _ => do
  let badLayer : Nat → Nat := fun v => if v = 0 then 0 else if v = 1 then 1 else 0
  assert (edges cycleGraph |>.all fun e => badLayer e.1 < badLayer e.2.1)
    "control fired: the cycle accepted a layer function"

/-- The graph sweep: the edge/adjacency reading, the reachability
    closure pinned on the diamond, the acyclicity check's both faces
    (the DAG passes; the cycle REFUSES with the cycle as data), the
    strata peel (02 §4's discipline over 01 §1's graph reading). -/
def graphSpec : Spec :=
  Spec.ofList "graph reading (diamond + cycle)" (fun _ => do
    -- the edge/adjacency reading (thin)
    assert (isEdge diamond 0 1) "diamond lost 0→1"
    assert (!isEdge diamond 1 0) "diamond invented 1→0"
    assert (succs diamond 0 == [1, 2]) "diamond's adjacency wrong"
    assert (edgeWeight diamond 0 1 == true) "edge weight lost"
    -- the reachability closure pinned
    assert (reachFrom diamond 2 0 == [3, 2, 1, 0]) "diamond's closure wrong"
    assert (reachFrom diamond 5 0 == [3, 2, 1, 0]) "the sweep didn't stabilize"
    assert (reachFrom diamond 2 1 == [3, 1]) "wrong source closure"
    -- the acyclicity check's both faces
    assert (cycle? diamond 4 == none) "the DAG refused"
    assert (!(cycle? cycleGraph 4 == none)) "the cycle passed"
    assert (cycle? cycleGraph 4 == some [1, 2, 0]) "the witness isn't the 3-cycle"
    assert ((walks cycleGraph 2).contains [0, 1, 2]) "the 3-cycle walk is missing"
    assert (isClosedWalk cycleGraph [0, 1, 2]) "the 3-cycle walk isn't closed"
    -- the strata peel
    assert (peel diamond 4 (verts diamond) == some [[0], [1, 2], [3]])
      "the DAG's strata wrong"
    assert (peel cycleGraph 4 (verts cycleGraph) == none)
      "the cycle graph layered"
    -- the topological discipline's data face
    let goodLayer : Nat → Nat := fun v => if v = 0 then 0 else if v = 3 then 2 else 1
    assert (edges diamond |>.all fun e => goodLayer e.1 < goodLayer e.2.1)
      "the diamond's strata law broke")
    [ ("the reach sweep misses two-step paths", negReachOneStep)
    , ("the acyclicity check ignores the self-loop", negAcyclicSelfLoop)
    , ("the cycle graph stratified", negStratifyCycle) ]
    8 42

/-! ## THE GRADUATION (16-surface §5.1): the canonical rep ≅ the weight
    function -/

/-- THE ISO'S RECONSTRUCTION, pinned in values: the canonical rep's
    weight function reassembles THE rep — the round trips as data. -/
def wz1 : Weighted Int Nat := fromList [(3, 5), (7, -2)]
def wfx1 : FinSupFn Int Nat := (ZSet.weightFnIso (K := Int) (Row := Nat)).to wz1

theorem weightFnIso_to_wz1 :
    (ZSet.weightFnIso (K := Int) (Row := Nat)).to wz1
      = ⟨(weightW wz1, wz1.rep), wz1.sorted, wz1.nonzero, fun _ => rfl⟩ := by
  rfl

/-- THE ISO'S round trips (the carrier discipline — the laws are the
    ISO's FIELDS, cited, never re-proved). -/
theorem weightFnIso_round_trips :
    (ZSet.weightFnIso (K := Int) (Row := Nat)).to
        ((ZSet.weightFnIso (K := Int) (Row := Nat)).inv wfx1) = wfx1
      ∧ (ZSet.weightFnIso (K := Int) (Row := Nat)).inv
          ((ZSet.weightFnIso (K := Int) (Row := Nat)).to wz1) = wz1 :=
  ⟨(ZSet.weightFnIso (K := Int) (Row := Nat)).to_inv _,
   (ZSet.weightFnIso (K := Int) (Row := Nat)).inv_to _⟩

/-- THE CANONICITY TEETH (the lossless claim's content): the weight
    function DETERMINES the canonical rep — two reps with the same
    weight function are THE SAME rep (`extW`, riding `weightOfW_inj`).
    The iso's reconstruction is well-defined BECAUSE of this. -/
theorem weightDetermlesRep :
    ∀ (m n : Weighted Int Nat), (∀ a, weightW m a = weightW n a) → m = n :=
  fun m n h => extW h

/-- THE TEETH (the unrepresentability): a NON-canonical list cannot
    survive as the carrier's rep — the carrier's property demands
    sortedness + zero-freeness + the weight law; a doubled entry's
    weight reads back DOUBLED, so the pure constant function has no
    such rep (the coalescing is load-bearing). -/
theorem nonCanonicalRepRefused :
    ¬ (weightOfW ([(3, (5 : Int)), (3, 5)]) 3 = (5 : Int)) := by
  intro h
  have h3 : weightOfW ([(3, (5 : Int)), (3, 5)]) 3 = 10 := by rfl
  rw [h] at h3
  omega

/-! ## The driver -/

def gradSpec : Spec := Spec.ofList "the rep ≅ weight-function graduation"
  (fun _ => do
    -- the reconstruction's weight function reads back exactly
    assert (weightW wz1 3 == 5 && weightW wz1 7 == -2 && weightW wz1 4 == 0)
      "reconstructed weight function wrong"
    -- the carried rep IS the canonical rep (the wire form survives the round trip)
    assert (((ZSet.weightFnIso (K := Int) (Row := Nat)).inv wfx1).rep
        == [(3, 5), (7, -2)]) "carried rep drifted")
  [ ("sabotage-rep-drops-an-entry", fun _ =>
      assert (weightW wz1 7 == 0) "control"),
    ("sabotage-canonicity-loosened", fun _ =>
      -- a second rep with the same weight function must NOT differ
      assert (fromList [(3, 5), (7, -2)] != fromList [(3, 5), (7, -2)]) "control") ]
  9 42

def main : IO UInt32 :=
  mainOfSuites [("ZSet", [groupSpec, canonSpec, trichotomySpec, homomorphismSpec,
    abstractSpec, oneTheoremIdSpec, oneTheoremCollapseSpec, oldValuesSpec, bridgeSpec,
    graphSpec, gradSpec])]
