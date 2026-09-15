/-
# Machines.Convergent — termination certificates

flatland's notes/lean/TOOLKIT.md §2.4 / lean-v3 Part 5: a convergent machine carries a
variant into a well-founded type that every event strictly decreases — the
cascade-termination certificate (and the CertifiedFixpoint variant's home).
The two idiom shapes (count-down, cap-minus-fill) discharge by `omega`.

Single encoding: `Convergent m` — the engine-side certificate over an EXISTING
`Machine`: a Nat-valued variant, decreasing on every enabled event per the
EventSpec guard-proof (spec §5.1). This is the shape `countDown` /
`capMinusFill` build, and the shape `run_length_bound` consumes.

The theorems: no infinite execution exists (`terminates`, through
`WellFounded.no_infinite_descent`), and any successful `run` has length
bounded by the starting variant (`run_length_bound`). The `omega` discrete
mathlib import (per lean-v3 D1); convergence itself is core-only — the
`WellFounded.no_infinite_descent` argument is pure `Acc` induction.

Consumers: the compiler's runtime-pass budgeting (TOOLKIT §2.4 204–208:
`fix` mode = convergence variant or runtime cap) and the count-down /
cap-minus-fill idiom constructors this file ships.
-/

import Machines.Core
import Mathlib.Order.WellFounded
import Dbsp.Stream

namespace Machines

/-- No infinite strictly-descending chain exists in a well-founded relation.
    (The whole convergence story bottoms out here.) -/
theorem WellFounded.no_infinite_descent {V : Type} {r : V → V → Prop}
    (wf : WellFounded r) (f : Nat → V) (h : ∀ n, r (f (n + 1)) (f n)) : False := by
  suffices ∀ v, Acc r v → ∀ f : Nat → V, f 0 = v → (∀ n, r (f (n + 1)) (f n)) → False from
    this (f 0) (wf.apply (f 0)) f rfl h
  intro v hv
  induction hv with
  | intro x _hx ih =>
    intro f h0 hd
    subst h0
    exact ih (f 1) (hd 0) (fun n => f (n + 1)) rfl (fun n => hd (n + 1))

/-- A stream of states, each a legal step from the previous (the
    divergence witness for a `Machine`, not a certificate). The
    `Dbsp.Stream` type makes the dbsp time-theory available. -/
def Machine.InfiniteRun (m : Machine) (steps : Dbsp.Stream m.State) : Prop :=
  ∀ n, ∃ l, m.tr (steps n) l (steps (n + 1))

/-! ## The Nat-valued certificate over a `Machine` (engine shape, spec §5.1) -/

/-- A convergence certificate for an EXISTING machine: a Nat-valued variant
    that every ENABLED event strictly decreases. The guard proof `h` is
    threaded from the `EventSpec` (an UPDATE…WHERE cannot act without
    discharging its guard), so the decrease obligation never quantifies
    over impossible actions. -/
structure Convergent (m : Machine) where
  variant : m.State → Nat
  decreases : ∀ (s : m.State) (l : m.Label) (h : (m.event l).guard s = true),
    variant ((m.event l).action s h) < variant s

namespace Convergent

/-- The count-down idiom: the variant is (morally) the state itself, and
    every action subtracts some `k l ≥ 1` from it — `variant s' = variant s - k l`
    under the guard's `k l ≤ variant s`. The decrease closes by `omega`.
    For a Nat-state machine the canonical instantiation is
    `variant := id`; the guard supplies both discharge facts. -/
def countDown (m : Machine) (variant : m.State → Nat) (k : m.Label → Nat)
    (hact : ∀ (s : m.State) (l : m.Label) (h : (m.event l).guard s = true),
      variant ((m.event l).action s h) = variant s - k l)
    (hmk : ∀ (s : m.State) (l : m.Label) (_h : (m.event l).guard s = true), k l ≥ 1)
    (hsk : ∀ (s : m.State) (l : m.Label) (_h : (m.event l).guard s = true), k l ≤ variant s)
    : Convergent m where
  variant := variant
  decreases := by
    intro s l h
    have h1 : 1 ≤ k l := hmk s l h
    have h2 : k l ≤ variant s := hsk s l h
    rw [hact s l h]
    omega

/-- The cap-minus-fill idiom: variant = `cap - fill`, where `fill` counts
    how much of a budget has been spent. Each event fills by at least one
    (`fill s + 1 ≤ fill s'`) and the guard keeps the POST-state fill inside
    the cap (`fill s' ≤ cap`) — the machine's `Inv` in action form. The
    decrease closes by `omega`. -/
def capMinusFill (m : Machine) (fill : m.State → Nat) (cap : Nat)
    (hinc : ∀ (s : m.State) (l : m.Label) (h : (m.event l).guard s = true),
      fill s + 1 ≤ fill ((m.event l).action s h))
    (hbnd : ∀ (s : m.State) (l : m.Label) (h : (m.event l).guard s = true),
      fill ((m.event l).action s h) ≤ cap)
    : Convergent m where
  variant := fun s => cap - fill s
  decreases := by
    intro s l h
    have hi := hinc s l h
    have hb := hbnd s l h
    omega

/-- The run-length certificate: each successful step spends exactly one
    unit of the variant, so a run that reaches `fin` in `ls.length` steps
    has `ls.length + variant fin ≤ variant s` — the invariant form of the
    bound below. Induction on `ls`, omega at the step. -/
theorem run_length_le (c : Convergent m) :
    ∀ (s : m.State) (ls : List m.Label) (tr : Machine.Trace m) (fin : m.State),
      m.run s ls = some (tr, fin) → ls.length + c.variant fin ≤ c.variant s := by
  intro s ls
  induction ls generalizing s with
  | nil =>
    intro tr fin h
    simp only [Machine.run] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons l rest ih =>
    intro tr fin h
    obtain ⟨s', tr', fin', hs, hr, htr, hfin⟩ := Machine.run_cons_some m h
    subst htr hfin
    obtain ⟨hg, hact⟩ := Machine.step?_eq_some m hs
    have hdec : c.variant s' < c.variant s := hact ▸ c.decreases s l hg
    have hih := ih s' tr' fin hr
    simp only [List.length_cons]
    omega

/-- THE bound: a convergent machine's successful runs are length-bounded by
    the starting variant. No diverging run exists — every step strictly
    decreases a Nat (see `terminates`); this is the concrete certificate. -/
theorem run_length_bound (c : Convergent m) (s : m.State) (ls : List m.Label)
    (tr : Machine.Trace m) (fin : m.State) (h : m.run s ls = some (tr, fin)) :
    ls.length ≤ c.variant s := by
  have hle := run_length_le c s ls tr fin h
  omega

/-- Convergence soundness: a convergent machine has no infinite run (the
    `Machine.InfiniteRun` witness is impossible) — `wellFounded_lt` on the
    Nat variant is the descending-host. -/
theorem terminates (c : Convergent m) (steps : Dbsp.Stream m.State)
    (h : Machine.InfiniteRun m steps) : False :=
  WellFounded.no_infinite_descent wellFounded_lt
    (fun n => c.variant (steps n))
    (by
      intro n
      obtain ⟨l, hg, hact⟩ := h n
      exact hact ▸ c.decreases (steps n) l hg)

end Convergent

end Machines