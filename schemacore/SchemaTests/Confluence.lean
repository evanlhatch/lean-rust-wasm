/- # SchemaTests.Confluence — the coordination classifier's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The classifier is SchemaCore.Confluence (02 §8's
invariant confluence). Suites:

1. `confluenceSpec` — the four verdict rows, live:
   - SAFE: the monotone append under the growth invariant — classified
     `safeUnderMerge` (the proved sufficient condition: the pair
     commutes + write-invisibility + insert-legality; the GENERAL
     `MergeSafe` claim is pinned at the kernel level below, not just
     the provided-table verdict);
   - OVERDRAW: the counterexample shape on the row fragment — each
     update individually valid, the merged application violates; the
     violating rows come back AS DATA and the verdict is
     `requiresCoordination` with the remedy named; the carrier's own
     overdraw witness (`theOverdraw`: balance 50, withdraw 40,
     withdraw 30) lands on `requiresCoordination` too — the TEETH: the
     classifier refuses to call the doctrine's withdrawal safe;
   - PARTITION: disjoint write surfaces + the provided merge checks →
     `safeUnderPartition` (the provided-table row);
   - UNKNOWN: overlapping writes, no witness, no proved condition —
     the honest open.
2. The obligation integration: the safe pair's merge obligation
   DISCHARGES at `decidableNow`; the overdraw pair's obligation
   REFUSES (the false claim never fabricates evidence — the loud gap).

The kernel-level pins (the `example`s below the fixtures) tie the
general claims: `MergeSafe.ofSufficient` earns the ∀-tables
preservation for the append; the witness's faces + the teeth are
kernel-pinned in SchemaCore.Confluence itself.

Negative controls: the sabotaged verdicts must FAIL — the violating
pair is not safe, the witness is individually valid, the safe pair's
discharge fires, the open row's tier is not decidableNow.

Evidence, not architecture — the five-question block lives in
SchemaCore.Confluence.
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.Confluence

open SchemaCore TestingKit

/-! ## The growth fixture — the SAFE case (the monotone append) -/

/-- The ledger: one u64 column. -/
def cgFields : List Field := [{ name := "count", ty := .u64 }]

/-- The row `[count = n]`. -/
def cgRow (n : UInt64) : RowVals cgFields := .cons (.u64 n) .nil

/-- THE GROWTH INVARIANT: every row's count exceeds zero (row-local
    `Pred` — adding rows can only preserve or grow the claim). -/
def cgInv : CheckItem :=
  { name := "growth", schemaRef := "Ledger", fields := cgFields,
    pred := .u64GtLit "count" 0 }

/-- The MONOTONE APPEND: INSERT count = 1, guard always. -/
def cgInsert : UpdateItem cgFields where
  record := "Ledger"
  name := "appendOne"
  guard := .lit true
  sets := []
  insert? := some (cgRow 1)

/-- The inert second instance: the guard fires nowhere. -/
def cgInert : UpdateItem cgFields where
  record := "Ledger"
  name := "noop"
  guard := .lit false
  sets := []

/-- The provided table. -/
def cgRows0 : List (RowVals cgFields) := [cgRow 1, cgRow 2]

/-! ## The credit fixture — the OVERDRAW case (the row fragment) -/

/-- The account: one u64 balance column. -/
def cbFields : List Field := [{ name := "bal", ty := .u64 }]

/-- The row `[bal = n]`. -/
def cbRow (n : UInt64) : RowVals cbFields := .cons (.u64 n) .nil

/-- THE CREDIT CEILING: bal ≤ 100 (`not (bal > 100)` — the fragment's
    ≤ shape). The overdraw-shaped counterexample lives HERE: the
    guards READ the balance the writes MOVE. -/
def cbInv : CheckItem :=
  { name := "credit", schemaRef := "Acct", fields := cbFields,
    pred := .not (.u64GtLit "bal" 100) }

/-- u₁: the seed write (bal = 1 ⊢ bal := 5) — individually valid. -/
def cbUpd₁ : UpdateItem cbFields where
  record := "Acct"
  name := "seed"
  guard := .u64EqLit "bal" 1
  sets := [{ field := { name := "bal", ty := .u64 }
             path := ColPath.here
             value := .u64 5 }]

/-- u₂: the overdraw write (bal = 5 ⊢ bal := 150) — individually valid
    (its guard refuses the seed table), JOINTLY violating. -/
def cbUpd₂ : UpdateItem cbFields where
  record := "Acct"
  name := "overdraw"
  guard := .u64EqLit "bal" 5
  sets := [{ field := { name := "bal", ty := .u64 }
             path := ColPath.here
             value := .u64 150 }]

/-- The provided table: the seed row. -/
def cbRows0 : List (RowVals cbFields) := [cbRow 1]

/-! ## The partition + unknown fixtures -/

/-- The pair: two u64 columns. -/
def cpFields : List Field :=
  [{ name := "a", ty := .u64 }, { name := "b", ty := .u64 }]

/-- The row `[a = x, b = y]`. -/
def cpRow (x y : UInt64) : RowVals cpFields :=
  .cons (.u64 x) (.cons (.u64 y) .nil)

/-- THE BOUNDS INVARIANT: a ≤ 10 ∧ b ≤ 10. -/
def cpInv : CheckItem :=
  { name := "bounds", schemaRef := "Pair", fields := cpFields,
    pred := .and (.not (.u64GtLit "a" 10)) (.not (.u64GtLit "b" 10)) }

/-- u₁ owns column a. -/
def cpUpd₁ : UpdateItem cpFields where
  record := "Pair"
  name := "setA"
  guard := .lit true
  sets := [{ field := { name := "a", ty := .u64 }
             path := ColPath.here
             value := .u64 5 }]

/-- u₂ owns column b. -/
def cpUpd₂ : UpdateItem cpFields where
  record := "Pair"
  name := "setB"
  guard := .lit true
  sets := [{ field := { name := "b", ty := .u64 }
             path := .there ColPath.here
             value := .u64 7 }]

/-- The provided table. -/
def cpRows0 : List (RowVals cpFields) := [cpRow 0 0]

/-- u₁ of the UNKNOWN pair: overlapping writes, later-wins. -/
def cuUpd₁ : UpdateItem cbFields where
  record := "Acct"
  name := "raiseTo50"
  guard := .lit true
  sets := [{ field := { name := "bal", ty := .u64 }
             path := ColPath.here
             value := .u64 50 }]

/-- u₂ of the UNKNOWN pair: the other later-winner. -/
def cuUpd₂ : UpdateItem cbFields where
  record := "Acct"
  name := "raiseTo80"
  guard := .lit true
  sets := [{ field := { name := "bal", ty := .u64 }
             path := ColPath.here
             value := .u64 80 }]

/-! ## The kernel-level pins (the general claims, not just the table) -/

/-- THE GENERAL SAFE CLAIM: the monotone append preserves the growth
    invariant for EVERY table — the sufficient condition's bridge,
    pinned at the kernel. -/
example : MergeSafe cgInv cgInsert :=
  MergeSafe.ofSufficient (by decide) (by decide)

/-- THE CLASSIFICATION's safe row, kernel-pinned. -/
example : Confluence.classify cgInv cgInsert cgInert cgRows0
    = MergeVerdict.safeUnderMerge := by decide

/-- The carrier's TEETH, kernel-pinned: the classifier refuses to call
    the doctrine's withdrawal safe. -/
example : classifyWithdrawals OverdrawWitness.theOverdraw
    = MergeVerdict.requiresCoordination
        "escrow the balance (reserve the amount), or serialize the withdrawals" :=
  rfl

/-- The overdraw pair's counterexample comes back AS DATA: the merged
    table's violating row, in table order. -/
example : Confluence.mergeCounterexample cbInv cbUpd₁ cbUpd₂ cbRows0
    = [cbRow 150] := rfl

/-- The overdraw pair's verdict, kernel-pinned. -/
example : Confluence.classify cbInv cbUpd₁ cbUpd₂ cbRows0
    = MergeVerdict.requiresCoordination
        "serialize the pair, escrow the shared column, or strengthen the \
          precondition — the guards read what the other writes" := by
  decide

/-- The partition row, kernel-pinned (disjoint write surfaces). -/
example : Confluence.classify cpInv cpUpd₁ cpUpd₂ cpRows0
    = MergeVerdict.safeUnderPartition := by decide

/-- The unknown row, kernel-pinned: overlapping writes, no witness on
    the provided table, no proved condition — the honest open. (The
    pair IS order-dependent — the conflict-policy question is exactly
    what stays open.) -/
example : Confluence.classify cbInv cuUpd₁ cuUpd₂ cbRows0
    = MergeVerdict.unknown := by decide

/-- The open row's tier: `provedAtElab` — a cited kernel theorem is its
    ONLY honest discharge, and none is cited for an arbitrary pair
    (the decide backend is untypeable for the ∀-tables claim). -/
example : (Confluence.openObligation cbInv cbUpd₁).tier
    = Kit.Tier.provedAtElab := by decide

/-! ## The runtime suite -/

/-- Render a table (the comparison surface — RowVals carries no BEq). -/
def cfRenderTable {fs : List Field} (rows : List (RowVals fs)) : String :=
  String.intercalate ";" (rows.map (Pred.renderRow fs))

/-- The provided-table check (the spec's access to `ci.holds`'s
    decidable shadow). -/
def ci_check (ci : CheckItem) (rows : List (RowVals ci.fields)) : Bool :=
  ci.checkRows rows

def confluenceSpec : Spec :=
  Spec.ofList "the coordination classifier: the four rows, the witness as data"
    (fun _ => do
      -- SAFE: the monotone append under the growth invariant
      assert (Confluence.classify cgInv cgInsert cgInert cgRows0
          == MergeVerdict.safeUnderMerge)
        "the monotone append is not safe-under-merge"
      -- the sufficient condition's faces, live
      assert (Confluence.sufficient cgInv cgInsert cgInert cgRows0)
        "the safe pair's sufficient condition failed"
      -- the safe pair's merge obligation DISCHARGES (decidableNow)
      assert (Confluence.dischargeMerge cgInv cgInsert cgInert cgRows0
          == some (Kit.Evidence.decided true))
        "the safe pair's merge obligation did not discharge"
      -- OVERDRAW: each side individually valid...
      assert (ci_check cbInv (cbUpd₁.apply cbRows0)
          && ci_check cbInv (cbUpd₂.apply cbRows0))
        "the overdraw pair's sides are not individually valid"
      -- ...the merged application VIOLATES, the rows come back...
      assert (cfRenderTable (Confluence.mergeCounterexample cbInv cbUpd₁ cbUpd₂ cbRows0)
          == cfRenderTable [cbRow 150])
        "the overdraw counterexample drifted"
      -- ...and the verdict is requires-coordination, remedy named
      assert (match Confluence.classify cbInv cbUpd₁ cbUpd₂ cbRows0 with
        | .requiresCoordination _ => true
        | _ => false)
        "the overdraw pair was not refused"
      -- the CARRIER's witness: the doctrine's own example, refused
      assert (match classifyWithdrawals OverdrawWitness.theOverdraw with
        | .requiresCoordination _ => true
        | _ => false)
        "the carrier's overdraw witness was not refused"
      -- the witness's faces (the lesson's two conjuncts, live)
      assert (OverdrawWitness.theOverdraw.valid1
          && OverdrawWitness.theOverdraw.valid2)
        "the overdraw witness's withdrawals are not individually valid"
      assert (!OverdrawWitness.theOverdraw.mergedOK)
        "the overdraw witness's merged state did not overdraw"
      -- the false claim's obligation REFUSES (the loud gap)
      assert (Confluence.dischargeMerge cbInv cbUpd₁ cbUpd₂ cbRows0 == none)
        "the overdraw pair's obligation fabricated a discharge"
      -- PARTITION: disjoint write surfaces + the provided merge checks
      assert (Confluence.classify cpInv cpUpd₁ cpUpd₂ cpRows0
          == MergeVerdict.safeUnderPartition)
        "the partition pair drifted"
      -- UNKNOWN: overlapping writes, no witness, no condition
      assert (Confluence.classify cbInv cuUpd₁ cuUpd₂ cbRows0
          == MergeVerdict.unknown)
        "the unknown pair drifted — the classifier pretended to know"
      -- the open obligation's row shape
      assert ((Confluence.openObligation cbInv cbUpd₂).label
          == "confluence/Acct/overdraw-merge-safe")
        "the open obligation's label drifted")
    [ ("control: the violating pair IS called safe (sabotage)",
        fun _ =>
          assert (Confluence.classify cbInv cbUpd₁ cbUpd₂ cbRows0
              == MergeVerdict.safeUnderMerge)
            "control fired: the overdraw pair is REFUSED — the classifier \
              does not call a witness-backed pair safe")
    , ("control: the overdraw witness is NOT individually valid (sabotage)",
        fun _ =>
          assert (OverdrawWitness.theOverdraw.valid1 == false)
            "control fired: the first withdrawal IS individually valid — \
              that is the counterexample shape's teeth")
    , ("control: the safe pair's discharge does NOT fire (sabotage)",
        fun _ =>
          assert (Confluence.dischargeMerge cgInv cgInsert cgInert cgRows0
              == none)
            "control fired: the safe pair's obligation DISCHARGES at \
              decidableNow — the backend fires on a true claim")
    , ("control: the open row's tier IS decidableNow (sabotage)",
        fun _ =>
          assert ((Confluence.openObligation cbInv cbUpd₁).tier
              == Kit.Tier.decidableNow)
            "control fired: the open row's tier is provedAtElab — the \
              ∀-tables claim has no decide backend") ]
    1 42
