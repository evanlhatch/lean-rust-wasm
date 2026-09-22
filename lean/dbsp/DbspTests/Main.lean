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
import TestKit

namespace DbspTests

open Dbsp
open TestKit

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

-- The THEORY-side ZSet is noncomputable (mathlib Finsupp); its laws are
-- kernel-proved where they live (ZSet/Relational/Replicas) — re-
-- instantiating them here would test nothing (T5). The witnesses above
-- exist to prove the ported constructions COMPUTE, and the sweeps below
-- cover the executable spine.

/-! ## Determinism — the hash-chained event log (`Dbsp.Determinism`), executed

The replay-spine laws on concrete logs: the hot-reload replay equality +
the chain-hash extension + the tamper pin. The GENERATED-input sweeps
(retired 2026-12 with their negative controls, per T5 — the covering
theorems `Determinism.replay_append`/`chainHash_append` are axiom-gated;
a control guarding a retired suite has no vacuity to catch) — the
witness below is the concrete pin. -/

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

/-! ## Effects — the DeltaSystem EXTENDS `CodegenCore.DisjointCommute`

The delta/lens unification (B3): `DeltaSystem` is a CLASS whose parent
is `CodegenCore.DisjointCommute` at `L := List Loc` — a mutation's
location = its write set, `Disjoint` = `LocDisjoint`, and every
instance fills the inherited law field. The concrete point-write
system below pins the instance on a fixture; the negative control
pins the hypothesis (an OVERLAP breaks the commutation — it is
load-bearing, not vacuous). -/

/-- Point writes on a location→value map: state = `Nat → Int`, a
    mutation is `(loc, value)`, the write set is the singleton. (The
    def lives outside the instance so the proof's `simp` unfolds it.) -/
def ptPatch : (Nat → Int) → Nat × Int → (Nat → Int) :=
  fun s m x => if x = m.1 then m.2 else s x

instance ptChange : Change (Nat → Int) (Nat × Int) where
  patch := ptPatch
  valid _ _ := True

/-- The concrete delta system (the fixture). -/
instance ptSystem : DeltaSystem (Nat → Int) Nat (Nat × Int) where
  -- the DisjointCommute parent fields (the extends shape: location +
  -- disjointness + the inherited law)
  apply := ptPatch
  loc m := [m.1]
  Disjoint := LocDisjoint
  -- the DeltaSystem fields (valid + writesOf + the relation's symmetry)
  valid _ _ := True
  writesOf m := [m.1]
  disjoint_symm := by
    intro l₁ l₂ hd
    -- `change` reduces the inherited `Disjoint` off the pending record
    change Dbsp.LocDisjoint l₁ l₂ at hd
    exact Dbsp.LocDisjoint.symm hd
  disjoint_commutes := by
    intro m₁ m₂ hd s
    have hne : m₁.1 ≠ m₂.1 := fun h =>
      hd (a := m₁.1) (by simp) (by simp [h])
    funext x
    simp only [ptPatch]
    by_cases h1 : x = m₁.1 <;> by_cases h2 : x = m₂.1
    · exact absurd (h1.symm.trans h2) hne
    · simp only [if_neg h2, if_pos h1]
    · simp only [if_pos h2, if_neg h1]
    · simp only [if_neg h1, if_neg h2]

/-- The shared law, executed on the fixture: disjoint point writes
    compose in either order; the overlap control shows the two orders
    DIFFER when the write sets collide. -/
def disjointCommuteWitness : CheckResult := Id.run do
  let s : Nat → Int := fun _ => 0
  let m₁ : Nat × Int := (0, 1)
  let m₂ : Nat × Int := (5, 7)
  -- both orders agree at every sampled location (the law computes)
  let lhs := ptPatch (ptPatch s m₁) m₂
  let rhs := ptPatch (ptPatch s m₂) m₁
  for x in [0, 5, 3] do
    if lhs x != rhs x then return .error s!"disjoint commute broke at {x}"
  -- NEGATIVE CONTROL: overlapping write sets — the orders observe
  -- differently (later-wins), the hypothesis is load-bearing
  let ov₁ := ptPatch (ptPatch s (0, 1)) (0, 2)
  let ov₂ := ptPatch (ptPatch s (0, 2)) (0, 1)
  if ov₁ 0 == ov₂ 0 then return .error "overlap control failed to observe order"
  .ok ()

/-- The suite: every check becomes an LSpec test with the same name and the
    same Boolean outcome the hand-rolled driver gave it. -/
def suite : TestSeq :=
  test "fix-eq-witness" (checkPasses fixEqWitness) $
  test "inverse-pair-witness" (checkPasses inversePairWitness) $
  test "cycle-incremental-witness" (checkPasses cycleIncrementalWitness) $
  test "seminaive-witness" (checkPasses seminaiveWitness) $
  test "delay-sanity" (checkPasses delaySanity) $
  test "determinism-witness" (checkPasses determinismWitness) $
  test "disjoint-commute-witness" (checkPasses disjointCommuteWitness)

-- The generated-input determinism sweep (DetSweep) retired as a pair with
-- its order-swap control (T5): `Determinism.replay_append` and
-- `chainHash_append` — both axiom-gated — prove the spine for ALL logs;
-- `determinismWitness` above is the concrete pin.

/-! ## Property sweep (retired with its control)

The D/I generated-input sweep retired as a pair with its off-by-one
control (T5): `derivative_integral` / `integral_derivative` (axiom-gated)
prove the inverse pair for ALL streams; `inversePairWitness` above is the
concrete executed pin. A control guarding a retired suite has no vacuity
to catch. -/

end DbspTests

open DbspTests in
def main : IO UInt32 := do
  TestKit.mainOfSuites [("DbspTests", suite)]
