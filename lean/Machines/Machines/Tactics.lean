/-
# Machines.Tactics — local proof idioms

Home for the package's repeated tactic blocks (lean-refactor-guide 4.12),
until a shared ProofKit exists. Currently just `guard_omega`, the
`EventSpec.safety` idiom for decidable-Nat guards (Sync.lean: latch
countDown, semaphore acquire/release).
-/

/-- The `EventSpec.safety` idiom for decidable-`Nat` guards: decode the
    guard hypothesis, unfold the invariant at hypothesis and goal, reduce
    the record-update projections, close by `omega`. -/
macro "guard_omega" Inv:ident : tactic =>
  `(tactic| (intro s h hinv
             simp only [decide_eq_true_eq] at h
             unfold $Inv at hinv ⊢
             simp only at hinv ⊢
             omega))
