/-
# TestKit Tests — the harness tests itself

1. Harness: assertEq/checkPasses carry failure messages into LSpec output.
2. PropSpec: a true property passes; its sabotaged sibling is caught —
   and a VACUOUS control (one the sampler can't reach) is flagged.
3. Golden: check/update/mismatch paths against a temp file.
4. DetSpec: the deterministic +/− discipline — a good pair passes, a
   vacuous control is flagged LOUDER than a failure.
5. Harness additions: expectErrorContaining / assertPointwiseEq /
   assertContains, each with a negative control that MUST fail.
6. CheckM: the accumulator driver reports failures and exit codes.
7. GateKit: parseGateArgs accepts exactly --check / --update / --help.
8. DiffSpec: the corruption-negative discipline for differential gates —
   a good gate (positive + 2 context-naming corruptions) passes; an
   IDENTITY corruption (gate vacuous), a context-poor rejection, and an
   empty corruption list are each flagged as gate failures.
9. MutSpec: the mutation battery over a Wf-lane-style checker — the base
   is accepted and every mutant of the four families (swap Ty / rename /
   drop case / dangling .ty ref) is refused; the seeded generative lane
   (`MutSpec.runGen` via runGenPure) and the raw-LCG lane prove pinned-
   seed determinism; the runner's own failure modes (refusalsExpected=0,
   zero-mutant grammar, count drift, a surviving mutant, a refused base)
   are each flagged — a passing negative is louder than a failure.
-/
import TestKit
import TestKit.MutSpec
import Plausible

open TestKit Plausible

/-- The harness checks. -/
def harnessChecks : List (String × CheckResult) :=
  [ ("assert-ok", assert (1 + 1 == 2) "arith broke")
  , ("assertEq-ok", assertEq "eq" (1 + 1) 2)
  , ("allOf-ok", allOf [("a", .ok ()), ("b", .ok ())]) ]

/-- A true property: list reverse is an involution. -/
def revProp : TestSeq :=
  checkPlausibleIO "reverse∘reverse = id"
    (∀ (l : List Nat), l.reverse.reverse = l)
    .done { numInst := 200, randomSeed := some 7 }

/-- Its negative control: reverse = id (false for length ≥ 2 lists — the
    sampler generates those quickly). -/
def revControl : TestSeq :=
  checkPlausibleIO "sabotaged: reverse = id (must be caught)"
    (∀ (l : List Nat), l.reverse = l)
    .done { numInst := 200, randomSeed := some 7 }

/-- A VACUOUS control: sabotage the sampler can't reach (lists are short at
    small sizes but `l.reverse == [] ∧ l ≠ []` is simply never true — the
    control must be CATCHABLE-in-principle but unprovable... no: this one is
    unsatisfiable-as-property yet never-falsified-by-sampling: it asserts
    every generated list has length < 1000, which holds vacuously at small
    sizes). A PropSpec with this as its control must be FLAGGED. -/
def vacuousProp : TestSeq :=
  checkPlausibleIO "vacuous property (passes)"
    (∀ (l : List Nat), l.length < 1000)
    .done { numInst := 50, randomSeed := some 7 }

def vacuousControl : TestSeq :=
  checkPlausibleIO "vacuous control (also passes — must be flagged)"
    (∀ (l : List Nat), l.length < 999)
    .done { numInst := 50, randomSeed := some 7 }

/-- DetSpec: a good pair — check passes, sabotaged sibling errors. -/
def detGood : DetSpec :=
  ⟨"pointwise negation",
    assertPointwiseEq "neg" (fun n : Nat => n + 0) (fun n => n) [0, 1, 2],
    assertPointwiseEq "neg (sabotaged)" (fun n : Nat => n + 1) (fun n => n) [0, 1, 2],
    "off-by-one sibling"⟩

/-- DetSpec with a VACUOUS control: the control passes, so the pair must be
    flagged as a failure. -/
def detVacuous : DetSpec :=
  ⟨"vacuous control demo",
    assert (1 + 1 == 2) "arith broke",
    assert (1 + 1 == 2) "arith broke",
    "identical sibling (passes — must be flagged)"⟩

/-- DetSpec with a failing check: must be flagged, differently from vacuous. -/
def detFailing : DetSpec :=
  ⟨"failing check demo",
    assertEq "eq" (1 + 1) 3,
    .error "control errors as required",
    "erroring sibling"⟩

/-- Harness additions, each with its negative control as a DetSpec pair. -/
def harnessAdditionSpecs : List DetSpec :=
  [ ⟨"expectErrorContaining catches all substrings",
      expectErrorContaining ["universe", "unknown ref"]
        (.error "universeCheck: unknown ref 'Foo'" : Except String Unit),
      expectErrorContaining ["universe", "MISSING"]
        (.error "universeCheck: unknown ref 'Foo'" : Except String Unit),
      "substring absent from message"⟩
  , ⟨"expectErrorContaining rejects .ok",
      expectErrorContaining ["boom"] (.error "boom" : Except String Unit),
      expectErrorContaining ["boom"] (.ok () : Except String Unit),
      ".ok sibling (expectError errors on it — must be caught)"⟩
  , ⟨"assertPointwiseEq catches a known index",
      -- g diverges from f exactly at domain index 2; the error must name it
      assertContains "idx witness"
        (match assertPointwiseEq "pw" (fun n : Nat => n) (fun n => if n == 2 then 99 else n)
            [0, 1, 2, 3] with
          | .error e => e | .ok () => "") "domain index 2",
      assertPointwiseEq "pw" (fun n : Nat => n) (fun n => if n == 2 then 99 else n) [0, 1, 2, 3],
      "raw mismatch result (must error)"⟩
  , ⟨"assertContains finds the needle",
      assertContains "haystack" "the quick brown fox" "quick",
      assertContains "haystack" "the quick brown fox" "MISSING",
      "absent needle (must error)"⟩ ]

-- ── DiffSpec: a miniature differential gate ──────────────────────────

/-- A tiny "replay fold" oracle: sums a column of cells; a cell over the
    bound is a divergence error naming the row, the value, and the bound
    (flatland ReplayGate's tick/column lesson, miniaturized). -/
def foldColumn (cells : List Nat) : CheckResult :=
  match cells.zipIdx.find? (fun (v, _) => v > 100) with
  | some (v, i) => .error s!"replay divergence at row {i}: cell value {v} exceeds bound 100"
  | none => .ok ()

/-- The clean input every spec below shares. -/
def cleanColumn : List Nat := [3, 10, 17, 24, 42]

/-- The good gate: positive passes, both corruptions are rejected WITH
    context. -/
def diffGood : DiffSpec := ⟨"replay fold rejects sabotaged cells",
  foldColumn cleanColumn,
  [ corrupt "oversized first cell" (fun c => 999 :: c.drop 1) cleanColumn foldColumn
      ["row 0", "exceeds bound"]
  , corrupt "oversized last cell" (fun c => c.take 4 ++ [999]) cleanColumn foldColumn
      ["row 4", "exceeds bound"] ]⟩

/-- GATE FAILURE demo 1: the identity "corruption" — the sabotage changes
    nothing, the check passes, the gate is vacuous. Must be flagged. -/
def diffVacuous : DiffSpec := ⟨"identity-corruption demo (must fail)",
  foldColumn cleanColumn,
  [ corrupt "identity sabotage" id cleanColumn foldColumn ]⟩

/-- GATE FAILURE demo 2: the corruption IS caught but the error lacks the
    required context (no row named). Must be flagged. -/
def diffNoContext : DiffSpec := ⟨"context-poor rejection demo (must fail)",
  foldColumn cleanColumn,
  [ corrupt "oversized first cell" (fun c => 999 :: c.drop 1) cleanColumn foldColumn
      ["tick 0", "old-assert"] ]⟩

/-- GATE FAILURE demo 3: no corruptions at all. Must be flagged. -/
def diffEmpty : DiffSpec := ⟨"corruption-free demo (must fail)",
  foldColumn cleanColumn, []⟩

-- ── MutSpec: the mutation battery over a Wf-lane-style checker ──────
--
-- F1 (the shift-left endpoint): the mutation battery proves the CHECKER
-- bites — a known-good base must be accepted, and EVERY mutant of a
-- whole family must be refused. The lane is the schema-lang Wf gate
-- (`universeCheck`, SchemaLang/Item.lean + Wf.lean). TestKit's own cone
-- is import-banned from SchemaLang (LintKit importBan row for
-- `lean/TestKit/`), so this demo runs the discipline against a faithful
-- SELF-CONTAINED miniature of that lane: the same gates (refs resolve,
-- name + mangled-name uniqueness, no empty variants, no inline ref-
-- cycles, legal identifiers) over the same item shape (type items with
-- fields/cases and `.ty` references). The real checker is a ONE-LINE
-- drop-in at the schema-lang site:
--
--   check := fun items => (SchemaLang.universeCheck items).isEmpty
--
-- with `base`/`mutate` reassigned to `List SchemaLang.Item`; MutSpec is
-- parameterized over α, so nothing in the discipline changes.

/- The miniature schema type: a scalar, the boxed position (`list`), or a
   NAME reference into the universe. -/
inductive MiniTy where
  | u64 | string
  | list (a : MiniTy)
  | ty (n : String)
deriving Repr, BEq, Inhabited

/-- One record field: name + type. -/
structure MiniField where
  name : String
  ty : MiniTy
deriving Repr, BEq, Inhabited

/-- A variant case: name + optional payload type (the Wf lane's
    `String × Option Ty` shape). -/
abbrev MiniCase := String × Option MiniTy

/-- The miniature item universe (records + variants — the shapes the four
    mutant families splice). -/
inductive MiniItem where
  | record (name : String) (fields : List MiniField)
  | variant (name : String) (cases : List MiniCase)
deriving Repr, BEq, Inhabited

/-- The identifying name of an item. -/
def MiniItem.name : MiniItem → String
  | .record n _ => n
  | .variant n _ => n

/-- Type-position names only (what `.ty` references may resolve to — the
    `Item.typeNames` mirror). -/
def MiniItem.typeNames : List MiniItem → List String :=
  fun items => items.filterMap fun it =>
    match it with
    | .record n _ => some n
    | .variant n _ => some n

/-! ## The miniature of the Wf lane's gates -/

/-- `.ty` references resolve against the universe's type names (the
    `Ty.check` unknownRef mirror; `list` recurses, `ty` resolves). -/
def miniTyGood (known : List String) : MiniTy → Bool
  | .u64 | .string => true
  | .list a => miniTyGood known a
  | .ty n => known.contains n

/-- Every field ty / case payload ty resolves. -/
def miniRefsResolve (items : List MiniItem) : Bool :=
  let known := MiniItem.typeNames items
  items.all fun it =>
    match it with
    | .record _ fields => fields.all fun f => miniTyGood known f.ty
    | .variant _ cases => cases.all fun (_, p) =>
        match p with | none => true | some t => miniTyGood known t

/-- Item names are unique (the dup-scan mirror). -/
def miniNamesUnique (items : List MiniItem) : Bool :=
  (items.map MiniItem.name).Nodup

/-- A NON-INJECTIVE mangling, like the Wf lane's kebab ("a_b" and "a-b"
    collide) — the post-mangle uniqueness gate needs it. -/
def miniMangle (s : String) : String :=
  s.replace "_" "-"

/-- The MANGLED names are unique too (the `mangleCollDiags` mirror). -/
def miniMangleUnique (items : List MiniItem) : Bool :=
  (items.map (miniMangle ∘ MiniItem.name)).Nodup

/-- A variant must have at least one case (the emptyVariant mirror). -/
def miniVariantsNonempty (items : List MiniItem) : Bool :=
  items.all fun it =>
    match it with
    | .record _ _ => true
    | .variant _ cases => cases ≠ []

/-- A few WIT/Rust reserved words, miniaturized (the `checkSchemaIdent`
    mirror — a field/case named `type` would emit invalid WIT). -/
def miniReserved : List String :=
  ["type", "list", "u64", "record", "variant"]

/-- Field and case identifiers avoid the reserved set. -/
def miniIdentsLegal (items : List MiniItem) : Bool :=
  items.all fun it =>
    match it with
    | .record _ fields => fields.all fun f => !miniReserved.contains f.name
    | .variant _ cases => cases.all fun (c, _) => !miniReserved.contains c

/-- The inline (non-boxed) ref edges (the `Ty.inlineRefs` mirror: `list`
    is THE boxed position — cycles behind it are finite-size; a direct
    `.ty` embed is inline). -/
def miniInlineSucc (items : List MiniItem) (n : String) : List String :=
  match items.find? (fun it => it.name == n) with
  | some (.record _ fields) => fields.filterMap fun f =>
      match f.ty with | .ty m => some m | _ => none
  | some (.variant _ cases) => (cases.filterMap (·.2)).filterMap fun t =>
      match t with | .ty m => some m | _ => none
  | none => []

/-- Reachability in ≤ `fuel` inline steps (the `inlineReaches?` mirror). -/
def miniReaches (items : List MiniItem) (root : String) : Nat → String → Bool
  | 0, m => m == root
  | k + 1, m =>
      m == root || (miniInlineSucc items m).any (miniReaches items root k)

/-- No type item sits on an inline ref-cycle (the W8.13 `InlineAcyclic`
    mirror, at the same `items.length + 1` fuel bound). -/
def miniInlineAcyclic (items : List MiniItem) : Bool :=
  (MiniItem.typeNames items).all fun n =>
    !(miniInlineSucc items n).any (miniReaches items n (items.length + 1))

/-- THE MINIATURE `universeCheck`: `.isEmpty`-equivalent conjunction of
    all five gates. -/
def miniUniverseCheck (items : List MiniItem) : Bool :=
  miniRefsResolve items && miniNamesUnique items && miniMangleUnique items
    && miniVariantsNonempty items && miniIdentsLegal items
    && miniInlineAcyclic items

/-- The known-good base universe: two records + one variant; `order.owner`
    references `user` (resolves), everything unique, no cycles. -/
def baseUniverse : List MiniItem :=
  [ .record "user"  [ { name := "id", ty := .u64 }
                     , { name := "email", ty := .string } ]
  , .record "order" [ { name := "owner", ty := .ty "user" }
                     , { name := "tag", ty := .list .string } ]
  , .variant "status" [ ("open", none), ("closed", some .string) ] ]

/-! ## The four mutant families (each splice hits exactly one gate) -/

/-- Set record `rec`'s field `fld`'s ty to `t`. -/
def setMiniFieldTy (rec fld : String) (t : MiniTy) (items : List MiniItem) :
    List MiniItem :=
  items.map fun it =>
    match it with
    | .record n fs =>
        if n == rec then .record n (fs.map fun f =>
          if f.name == fld then { f with ty := t } else f) else it
    | it => it

/-- Rename record `rec`'s field `fld` to `to`. -/
def renameMiniField (rec fld to : String) (items : List MiniItem) :
    List MiniItem :=
  items.map fun it =>
    match it with
    | .record n fs =>
        if n == rec then .record n (fs.map fun f =>
          if f.name == fld then { f with name := to } else f) else it
    | it => it

/-- Empty variant `v` (drop ALL its cases — a zero-case variant). -/
def emptyMiniVariant (v : String) (items : List MiniItem) : List MiniItem :=
  items.map fun it =>
    match it with
    | .variant n _ => if n == v then .variant v [] else it
    | it => it

/-- The four splices: 1 swap a field's Ty → an inline self-cycle (the
    W8.13 gate); 2 rename a field → a reserved word (the ident gate);
    3 drop a case → a zero-case variant (the empty-variant gate); 4 point
    a `.ty` ref at nothing → unresolvable (the refs gate). Each refuses by
    exactly ONE rule — a surviving splice would mean that rule is dead. -/
def defaultSplices : List (List MiniItem → List MiniItem) :=
  [ setMiniFieldTy "order" "owner" (.ty "order")
  , renameMiniField "user" "email" "type"
  , emptyMiniVariant "status"
  , setMiniFieldTy "order" "owner" (.ty "ghost") ]

/-- The deterministic mutant grammar: one mutant (a whole universe) per
    family — `mutate : α → List α` with `α = List MiniItem`. -/
def mutateItem (items : List MiniItem) : List (List MiniItem) :=
  defaultSplices.map (· items)

/-- The positive battery: base accepted, all four mutants refused. -/
def wfBattery : MutSpec (List MiniItem) :=
  { name := "universeCheck-bites: the four mutant families"
  , base := baseUniverse
  , mutate := mutateItem
  , check := miniUniverseCheck
  , refusalsExpected := 4 }

/-- Map a seeded plan of family indices onto concrete mutants (the
    generative lane's materializer). -/
def planMutants (plan : List Nat) (items : List MiniItem) :
    List (List MiniItem) :=
  plan.map fun i => (defaultSplices.getD i (fun x => x)) items

/-- The generative battery: the mutant SET is a `Plausible.Gen` — a
    permutation of the four families, drawn by the seeded runner
    (`MutSpec.runGen` → `TestKit.runGenPure`: pinned seed AND size). The
    grammar itself is seeded — same seed, same battery. -/
def generativeBattery : MutSpec (List MiniItem) :=
  { name := "universeCheck-bites: seeded generative draw (4 plans)"
  , base := baseUniverse
  , mutate := fun _ => []   -- replaced by the drawn set (runGen)
  , check := miniUniverseCheck
  , refusalsExpected := 4 }

/-- One draw: a seeded permutation of the four splice families. -/
def genMutantSet : Plausible.Gen (List (List MiniItem)) := do
  let ⟨plan, _⟩ ← Plausible.Gen.permutationOf [0, 1, 2, 3]
  pure (planMutants plan baseUniverse)

/-- The pinned-seed law, verified: two draws with the same seed/size are
    the same battery (the snapshot-fixture byte-tie habit). -/
def genDrawDeterminism : CheckResult :=
  match TestKit.runGenPure genMutantSet 7 20, TestKit.runGenPure genMutantSet 7 20 with
  | .error e1, .error e2 =>
      if e1 == e2 then .ok () else .error "pinned seed drifted: the two failures differ"
  | .ok a, .ok b =>
      if a == b then .ok () else .error "pinned seed drifted: the two draws differ"
  | _, _ => .error "pinned seed drifted: draw outcomes differ"

/-- The grammar ITSELF seeded by the raw `TestKit.lcg` stream (no
    Plausible — the pure lane): family i = the i-th LCG iterate mod 4. -/
def lcgPlan (seed : UInt64) : Nat → List Nat
  | 0 => []
  | k + 1 =>
      let s := lcg seed
      (s.toNat % 4) :: lcgPlan s k

/-- The raw-LCG battery: the same four families, the plan seeded directly
    by `TestKit.lcg` with a pinned seed. -/
def lcgBattery (seed : UInt64) : MutSpec (List MiniItem) :=
  { name := s!"universeCheck-bites: raw-LCG plan (seed {seed})"
  , base := baseUniverse
  , mutate := fun items => planMutants (lcgPlan seed 4) items
  , check := miniUniverseCheck
  , refusalsExpected := 4 }

/-! ## The discipline's own failure modes (the negative demos — each of
    these MUST be flagged; a passing negative is louder than a failure) -/

/-- refusalsExpected = 0: no declared teeth. -/
def vacuityZeroSpec : MutSpec (List MiniItem) :=
  { name := "demo: refusalsExpected = 0"
  , base := baseUniverse, mutate := mutateItem
  , check := miniUniverseCheck, refusalsExpected := 0 }

/-- A grammar that produces zero mutants: proves nothing. -/
def vacuityEmptySpec : MutSpec (List MiniItem) :=
  { name := "demo: zero-mutant grammar"
  , base := baseUniverse, mutate := fun _ => []
  , check := miniUniverseCheck, refusalsExpected := 2 }

/-- The grammar silently shrank (3 of 4 mutants): drift. -/
def driftSpec : MutSpec (List MiniItem) :=
  { name := "demo: mutant-count drift"
  , base := baseUniverse
  , mutate := fun _ => mutateItem baseUniverse |>.take 3
  , check := miniUniverseCheck, refusalsExpected := 4 }

/-- Drop ONE case of `status` (not all): still legal — a survivor proves
    the checker doesn't bite, so the battery must FAIL it. -/
def dropOneStatusCase (items : List MiniItem) : List MiniItem :=
  items.map fun it =>
    match it with
    | .variant "status" _ => .variant "status" [("closed", some .string)]
    | it => it

def survivorSpec : MutSpec (List MiniItem) :=
  { name := "demo: a surviving mutant (1-case drop is legal)"
  , base := baseUniverse
  , mutate := fun _ => [dropOneStatusCase baseUniverse]
  , check := miniUniverseCheck, refusalsExpected := 1 }

/-- The base itself is a mutant (dangling ref): the positive guard. -/
def positiveFailSpec : MutSpec (List MiniItem) :=
  { name := "demo: base refused by the checker"
  , base := setMiniFieldTy "order" "owner" (.ty "ghost") baseUniverse
  , mutate := mutateItem
  , check := miniUniverseCheck, refusalsExpected := 4 }

/-- The battery rows: positives must pass, negatives must be REFUSED by
    the runner (a passing negative = vacuity = a loud failure). -/
def mutSpecRows : List (String × CheckResult) :=
  [ ("battery: four families refused"              , wfBattery.run)
  , ("battery: generative draw refused (seed 7)"   , MutSpec.runGen generativeBattery genMutantSet 7 20)
  , ("battery: raw-LCG plan refused (seed 42)"     , (lcgBattery 42).run)
  , ("seed pins the generative battery"            , genDrawDeterminism)
  , ("negative: refusalsExpected=0 must be VACUOUS",
      expectErrorContaining ["VACUOUS"] vacuityZeroSpec.run)
  , ("negative: zero-mutant grammar must be VACUOUS",
      expectErrorContaining ["VACUOUS"] vacuityEmptySpec.run)
  , ("negative: count drift must be flagged"       ,
      expectErrorContaining ["GRAMMAR DRIFT"] driftSpec.run)
  , ("negative: a surviving mutant must be flagged",
      expectErrorContaining ["SURVIVED"] survivorSpec.run)
  , ("negative: a refused base must be a failure"  ,
      expectErrorContaining ["POSITIVE FAILED"] positiveFailSpec.run) ]

def main : IO UInt32 := do
  let mut failures := 0
  -- MutSpec: the mutation battery over the Wf-lane-style checker
  let mutSpecCode ← TestKit.mainOfChecks "MutSpec" mutSpecRows
  if mutSpecCode != 0 then failures := failures + 1
  -- harness suite
  let code ← TestKit.mainOfSuites [("harness", suiteOf harnessChecks)]
  if code != 0 then failures := failures + 1
  -- PropSpec: the good pair passes
  let (ok1, v1) ← (PropSpec.mk "reverse involution" revProp revControl
    "reverse = id").runIO
  IO.println v1
  if !ok1 then failures := failures + 1
  -- PropSpec: the vacuous pair is FLAGGED (property passes, control not caught)
  let (ok2, v2) ← (PropSpec.mk "vacuous demo" vacuousProp vacuousControl
    "nearly-identical threshold").runIO
  IO.println v2
  if ok2 then
    IO.println "FAIL: vacuous pair was not flagged"
    failures := failures + 1
  -- golden: write, match, mismatch
  let tmp : System.FilePath := "/tmp/testkit-golden-demo.txt"
  let r1 ← Golden.checkAgainstGolden "demo" "hello golden\n" tmp true
  let r2 ← Golden.checkAgainstGolden "demo" "hello golden\n" tmp false
  let r3 ← Golden.checkAgainstGolden "demo" "drifted\n" tmp false
  match r1, r2, r3 with
  | .ok (), .ok (), .error _ => IO.println "✓ golden paths"
  | _, _, _ => IO.println "FAIL: golden paths"; failures := failures + 1
  -- DetSpec: the good pair passes via runDets
  let detCode ← runDets [detGood]
  if detCode != 0 then failures := failures + 1
  -- DetSpec negative controls (evaluated via the pure runner):
  -- vacuous control must be flagged; failing check must be flagged.
  let (vacOk, vacVerdict) := detVacuous.run
  IO.println vacVerdict
  if vacOk then
    IO.println "FAIL: vacuous DetSpec control was not flagged"
    failures := failures + 1
  let (failOk, failVerdict) := detFailing.run
  IO.println failVerdict
  if failOk then
    IO.println "FAIL: failing DetSpec check was not flagged"
    failures := failures + 1
  -- Harness additions (positive + negative control per assertion)
  let hCode ← runDets harnessAdditionSpecs
  if hCode != 0 then failures := failures + 1
  -- CheckM: all-pass driver exits 0; a driver with one failure exits 1
  -- and names the failing check.
  let cmOk ← runCheckM do
    check "cm-assert" (assert (2 * 2 == 4) "mul broke")
    check "cm-contains" (assertContains "cm" "abcdef" "cde")
  if cmOk != 0 then failures := failures + 1
  let cmBad ← runCheckM do
    check "cm-pass" (.ok ())
    check "cm-FAIL" (.error "deliberate failure (must exit 1)")
  if cmBad == 0 then
    IO.println "FAIL: CheckM driver swallowed a failure"
    failures := failures + 1
  -- GateKit: parseGateArgs accepts exactly the uniform surface
  let argsOk :=
    GateKit.parseGateArgs [] == some false &&
    GateKit.parseGateArgs ["--check"] == some false &&
    GateKit.parseGateArgs ["--update"] == some true &&
    GateKit.parseGateArgs ["--help"] == none &&
    GateKit.parseGateArgs ["--bogus"] == none
  if !argsOk then
    IO.println "FAIL: parseGateArgs surface"
    failures := failures + 1
  else IO.println "✓ parseGateArgs surface"
  -- GateKit.audit: banned pattern present → finding; required present and
  -- clean text → none. Negative control: the empty rule list is vacuously
  -- clean ONLY here, in the test — a real emitter must never ship `[]`.
  let auditRules : List GateKit.AuditRule :=
    [ { name := "no-todo", pattern := "TODO", why := "unfinished emission" }
    , { name := "hdr", pattern := "package guestlang", required := true
      , why := "the WIT package header is the registry key" } ]
  let auditOk :=
    (GateKit.auditFindings auditRules "package guestlang: demo; x TODO y"
        == ["banned \"TODO\" present — unfinished emission"])
      && (GateKit.auditFindings auditRules "package guestlang: demo;" == [])
      && ((GateKit.auditFindings auditRules "no header here").length == 1)
      && (GateKit.auditFindings ([] : List GateKit.AuditRule) "anything" == [])
  if !auditOk then
    IO.println "FAIL: GateKit.auditFindings controls"
    failures := failures + 1
  else IO.println "✓ GateKit.auditFindings controls"
  -- DiffSpec: the good gate passes via runDiffs
  let diffCode ← runDiffs [diffGood]
  if diffCode != 0 then failures := failures + 1
  -- DiffSpec negative controls (pure runner): each bad gate shape must
  -- be flagged, with the right verdict shape.
  let (vacD, vacDVerdict) := diffVacuous.run
  IO.println vacDVerdict
  if vacD || (vacDVerdict.splitOn "unexpectedly succeeded").length == 1 then
    IO.println "FAIL: identity corruption was not flagged as 'unexpectedly succeeded'"
    failures := failures + 1
  let (noCtx, noCtxVerdict) := diffNoContext.run
  IO.println noCtxVerdict
  if noCtx || (noCtxVerdict.splitOn "lacks context").length == 1 then
    IO.println "FAIL: context-poor rejection was not flagged"
    failures := failures + 1
  let (empD, empDVerdict) := diffEmpty.run
  IO.println empDVerdict
  if empD || (empDVerdict.splitOn "VACUOUS").length == 1 then
    IO.println "FAIL: corruption-free gate was not flagged"
    failures := failures + 1
  if failures == 0 then IO.println "all checks passed" else IO.eprintln s!"{failures} FAILURES"
  return if failures == 0 then 0 else 1
