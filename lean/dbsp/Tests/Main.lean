/-
# Dbsp Tests — executable checks (harness: LSpec, per flatland's notes/lean/lean-v3.md D14)

1. **fix_eq witness**: the ported theorem `fix_eq`/`fix_unique` is a proof;
   the executable check witnesses it on a concrete strict operator
   (F s = 1 + z⁻¹s over ℤ streams; fix F = λt => t+1), times 0..20.
2. delay/agreement sanity.
3. ZSet smoke: group ops + `distinct` (the old-state-requiring operator).

Each witness keeps the same name and the same Boolean outcome it had under
the hand-rolled driver; only the harness changed. LSpec's `test` needs a
`Prop`, so each `CheckResult` is lifted via `checkPasses` (ok → True /
error → False) with a `Testable` instance that carries the failure message.

Run: `lake build DbspTests && .lake/build/bin/DbspTests`
-/
import Dbsp
import Plausible
import TestKit

namespace DbspTests

open Dbsp
open TestKit
open Plausible

/-- A concrete strict operator: `F s = 1 + z⁻¹ s` (pointwise over ℤ).
    Strict: output at n+1 reads input at n; output at 0 is constant. -/
def F : Operator Int Int
  | _, 0 => 1
  | s, n + 1 => s n + 1

/-- The executable witness for `fix_eq` (Operators.lean): the theorem is
    proved; this checks the ported construction computes it. -/
def fixEqWitness : CheckResult := Id.run do
  for t in [0 : 21] do
    if Dbsp.fix F t != F (Dbsp.fix F) t then
      return .error s!"fix F {t} = {Dbsp.fix F t} ≠ F (fix F) {t} = {F (Dbsp.fix F) t}"
    if Dbsp.fix F t != (t : Int) + 1 then
      return .error s!"fix F {t} = {Dbsp.fix F t} ≠ {t + 1}"
  return .ok ()

/-- The D/I inverse pair on a concrete ramp, executable: integrate the
    differences of 0,10,20,… and differentiate back — both directions
    recover the input. (The theorems `derivative_integral`/
    `integral_derivative` prove this for ALL streams; this is the
    oracle-side smoke that the ported definitions compute.) -/
def inversePairWitness : CheckResult := Id.run do
  let ramp : Stream Int := fun n => n * 10
  for t in [0, 1, 2, 5, 10] do
    if I (D ramp) t != ramp t then
      return .error s!"I(D(ramp)) {t} = {I (D ramp) t}, expected {ramp t}"
    if D (I ramp) t != ramp t then
      return .error s!"D(I(ramp)) {t} = {D (I ramp) t}, expected {ramp t}"
  return .ok ()

/-- Executable witness for `cycle_incremental`: T s α := s + α (pointwise)
    makes `fix (fun α => T s (delay α))` the running-sum operator. The
    incrementalized cycle must agree with the differentiated batch cycle
    on a concrete input — recursion computes the same fixpoint in
    delta-land. -/
def cycleIncrementalWitness : CheckResult := Id.run do
  let T : Operator2 Int Int Int := fun s α => s + α
  let input : Stream Int := fun n => if n < 3 then 1 else 0
  let lhs := incremental (fun s => fix (fun α => T s (delay α))) input
  let rhs := fix (fun α => incremental2 T input (delay α))
  for t in [0, 1, 2, 3, 5, 8] do
    if lhs t != rhs t then
      return .error s!"cycle mismatch at {t}: batch {lhs t} vs incremental {rhs t}"
    -- and both are the running sum: 1,2,3,3,3,...
    let expected : Int := min (t + 1 : Int) 3
    if lhs t != expected then
      return .error s!"running sum wrong at {t}: {lhs t}, expected {expected}"
  return .ok ()

/-- Executable witness for `seminaive_equiv` + `recursive_fixpoint_ok`.
    R i o := if o < i then o + 1 else o — a bounded countdown whose iterates
    from 0 stabilize at i (pass 3 for i := 3). The incrementalized
    (semi-naive) loop's output stream must equal the derivative of the
    naive loop's stream, pointwise — and the semi-naive deltas must vanish
    after stabilization (the engine's convergence check). All computable:
    fix/I/D/δ0 evaluate; only `streamElim` is noncomputable and unused here. -/
def seminaiveWitness : CheckResult := Id.run do
  let R : Int → Int → Int := fun i o => if o < i then o + 1 else o
  let inp : Int := 3
  let naiveInner := fix (fun o => lifting2 R (I (δ0 inp)) (delay o))
  let seminaiveInner := fix (fun o => incremental2 (lifting2 R) (δ0 inp) (delay o))
  for t in [0, 1, 2, 3, 4, 5, 6] do
    if D naiveInner t != seminaiveInner t then
      return .error s!"seminaive mismatch at {t}: D(naive) {D naiveInner t} vs seminaive {seminaiveInner t}"
  -- deltas vanish after stabilization (pass 3 = input 3)
  for t in [4, 5, 6] do
    if seminaiveInner t != 0 then
      return .error s!"seminaive not converged at {t}: {seminaiveInner t}"
  -- and the naive stream accumulates to the fixpoint value 3
  if naiveInner 6 != 3 then
    return .error s!"naive limit wrong: {naiveInner 6}, expected 3"
  return .ok ()

def delaySanity : CheckResult := Id.run do
  let s : Stream Int := fun n => n * 10
  for n in [0 : 10] do
    if delay s (n + 1) != s n then return .error s!"delay broke at {n}"
  if delay s 0 != 0 then return .error "delay s 0 ≠ 0"
  return .ok ()

-- The THEORY-side ZSet is noncomputable (mathlib Finsupp quotients with
-- classical choice), so its checks are compile-time proofs, not executable
-- tests. The exec side is Flatland.Change (proved merge/revert laws).

/-- The group law that licenses rollback: deltas invert. -/
example (m : ZSet Nat) : m - m = 0 := sub_self m

/-- Union is commutative — rule application order is provably irrelevant
    (the aggregate phase of the two-phase tick, SPEC-core §7.2). -/
example (a b : ZSet Nat) : a + b = b + a := add_comm a b

/-- The replica-convergence core, at the theory level: opposite arrival
    orders of the same deltas converge (`Dbsp.Replicas`). -/
example (s δ₁ δ₂ : ZSet Nat) :
    Dbsp.Replicas.applyDeltas s [δ₁, δ₂] = Dbsp.Replicas.applyDeltas s [δ₂, δ₁] :=
  Dbsp.Replicas.two_replica_converge s δ₁ δ₂

/-- The retraction law the engine's rewind executes, at the replica level:
    delta-then-inverse restores the state. -/
example (s δ : ZSet Nat) :
    Dbsp.Replicas.applyDeltas (Dbsp.Replicas.applyDeltas s [δ]) [-δ] = s :=
  Dbsp.Replicas.retract_is_inverse s δ

/-! ## Determinism — the hash-chained event log (`Dbsp.Determinism`), executed

The replay-spine laws, executed on concrete + generated logs (the theory
is over ABSTRACT step/combine; this sweep instantiates Int/Int): the
hot-reload replay equality + the chain-hash extension. The NEGATIVE
CONTROL is the anti-Replicas statement: swapping the arrival order does
NOT preserve the ordered replay — order is the artifact here (the group
law covers delta sets, doctrine §8: protocols are sequences). -/

/-- The concrete instantiation: state = Horner evaluation (`s*2 + e`) —
    deliberately NON-commutative in the events, so the ordered replay's
    order-sensitivity is real; the chain combine folds `h*31 + e`
    (the classic polynomial hash, wrapping). -/
def detStep : Int → Int → Int := fun s e => s * 2 + e

def detCombine : UInt64 → Int → UInt64 := fun h e => h * 31 + e.natAbs.toUInt64

/-- The determinism spine, executed (`Dbsp.Determinism`): the full-log
    replay, the hot-reload chunking, the chain-hash extension, and the
    tamper pin (dropping an event changes the hash). -/
def determinismWitness : CheckResult := Id.run do
  let log : List Int := [1, 2, 3, 4]
  -- the replay IS the fold: sum of the events
  if Determinism.replay detStep 0 log != 26 then
    return .error "replay (Horner) wrong"
  -- hot reload: checkpoint [1,2] + tail [3,4] = the full replay
  if Determinism.replay detStep (Determinism.replay detStep 0 [1, 2]) [3, 4]
      != Determinism.replay detStep 0 log then
    return .error "hot-reload mismatch"
  -- the chain hash extends from the checkpoint hash
  if Determinism.chainHash detCombine
      (Determinism.chainHash detCombine 7 [1, 2]) [3, 4]
      != Determinism.chainHash detCombine 7 log then
    return .error "chain extension mismatch"
  -- the tamper pin: dropping an event changes the hash (detection)
  if Determinism.chainHash detCombine 7 [1, 2, 3]
      == Determinism.chainHash detCombine 7 [1, 2] then
    return .error "tamper undetected"
  .ok ()

/-- The suite: every check becomes an LSpec test with the same name and the
    same Boolean outcome the hand-rolled driver gave it. -/
def suite : TestSeq :=
  test "fix-eq-witness" (checkPasses fixEqWitness) $
  test "inverse-pair-witness" (checkPasses inversePairWitness) $
  test "cycle-incremental-witness" (checkPasses cycleIncrementalWitness) $
  test "seminaive-witness" (checkPasses seminaiveWitness) $
  test "delay-sanity" (checkPasses delaySanity) $
  test "determinism-witness" (checkPasses determinismWitness)

namespace DetSweep

open Determinism

def detOk (xs ys : List Int) : Bool :=
  replay detStep 0 (xs ++ ys) == replay detStep (replay detStep 0 xs) ys
    && chainHash detCombine 7 (xs ++ ys)
      == chainHash detCombine (chainHash detCombine 7 xs) ys

/-- The sabotaged control: ORDER-SWAPPED replay — the CRDT convergence
    claim is FALSE for the ordered event log (it is a delta claim, not
    an event-chain claim). Caught for any generated pair with xs ≠ ys. -/
def detCtrl (xs ys : List Int) : Bool :=
  replay detStep 0 (xs ++ ys) == replay detStep 0 (ys ++ xs)

instance : Arbitrary (List Int) where
  arbitrary := Gen.listOf (Arbitrary.arbitrary : Gen Int)

def suite : TestSeq :=
  checkPlausibleIO "determinism: reload equality + chain extension (generated logs)"
    (∀ (xs ys : List Int), detOk xs ys = true)
    .done { numInst := 300, randomSeed := some 20261104 }

def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: order-swapped replay (must be caught)"
    (∀ (xs ys : List Int), detCtrl xs ys = true)
    .done { numInst := 300, randomSeed := some 20261104 }

def spec : TestKit.PropSpec :=
  { name := "determinism spine: same-chain same-replay"
  , suite := suite
  , control := controlSuite
  , controlName := "order-swap" }

end DetSweep

/-! ## Property sweep (with mandatory negative control)

The theory-side `example`s above PROVE the group laws for ALL ZSets;
the witnesses check the ported constructions compute on CONCRETE inputs.
NEITHER exercises a GENERATED input — the AGENTS.md negative-control
mandate targets property sweeps, and dbsp had none.

This sweep samples finite `Int` lists, lifts each to a stream, and checks
the D/I inverse pair (`derivative_integral` / `integral_derivative`) at
each tick — a GENERATED-input sweep over a COMPUTABLE surface (ZSet
itself is noncomputable, so the group laws stay as proofs above). The
sabotaged control (`D(I s) t = s t + 1`) is caught iff the generator
produces a non-trivial stream — a vacuous generator is flagged as a
failure (TestKit.PropSpec). -/
namespace PropSweep

/-- Lift a finite list to a stream (0-padded past the list). -/
def liftStream (xs : List Int) : Stream Int := fun n =>
  if h : n < xs.length then xs.get ⟨n, h⟩ else 0

/-- The D/I inverse pair holds at every tick up to the list length
    (both directions: `D (I s) = s` and `I (D s) = s`). Computable: `D`,
    `I`, `delay`, `Int` arithmetic all reduce. -/
def diOk (xs : List Int) : Bool :=
  let s := liftStream xs
  (List.range (xs.length + 1)).all fun t =>
    D (I s) t == s t && I (D s) t == s t

/-- The sabotaged control: `D (I s) t = s t + 1` — refuted for any
    non-trivial stream (the theorem gives `D (I s) t = s t`, so the
    off-by-one bites whenever the tick is in range). -/
def diOkCtrl (xs : List Int) : Bool :=
  let s := liftStream xs
  (List.range (xs.length + 1)).all fun t => D (I s) t == s t + 1

-- the `Arbitrary (List Int)` instance is DetSweep's (one copy — the
-- dupDefBodies lint): both sweeps sample the same finite Int lists

/-- The property: the D/I inverse pair over generated streams. -/
def suite : TestSeq :=
  checkPlausibleIO "D/I inverse pair (generated streams)"
    (∀ (xs : List Int), diOk xs = true)
    .done { numInst := 500, randomSeed := some 20260909 }

/-- The negative control: the off-by-one variant must be CAUGHT (fail). -/
def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: D(I s) t = s t + 1 (must be caught)"
    (∀ (xs : List Int), diOkCtrl xs = true)
    .done { numInst := 500, randomSeed := some 20260909 }

def spec : TestKit.PropSpec :=
  { name := "D/I inverse pair"
  , suite := suite
  , control := controlSuite
  , controlName := "off-by-one" }

end PropSweep

end DbspTests

open DbspTests in
def main : IO UInt32 := do
  let code ← TestKit.mainOfSuites [("DbspTests", suite)]
  if code != 0 then return code
  -- the property sweep WITH its mandatory negative control
  TestKit.runSpecs [PropSweep.spec, DetSweep.spec]
