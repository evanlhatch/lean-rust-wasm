/-
# Machines.Compose — parallel composition

lean-v3 Part 5 port: independent parallel composition of two machines.
Product state, summed event labels; each side's events act on their OWN
projection and leave the other one untouched. That share-nothing shape is
what makes interleaving SAFE — the diamond theorem below is its certificate.

The theorems, and what each buys:

- `compose_step_inl` / `compose_step_inr` — a composite step on an `inl`
  label IS the left machine's step, definitionally, with the right
  component pinned (`(m1.step? s.1 l1).map (fun s1' => (s1', s.2))`).
- `compose_step_inl_proj` / `compose_step_inr_proj` — the step?/projection
  biconditionals: a composite step lands in `s'` iff the corresponding
  machine stepped its projection and the other projection is untouched.
  These are the workhorses for everything below.
- `compose_commute` — the diamond: e1-then-e2 and e2-then-e1 from the same
  state reach the SAME state. Disjoint projections ⇒ the two interleavings
  coincide, so a scheduler never needs to arbitrate between the two sides.
- `compose_run_inl` / `compose_run_inr` — an all-`inl` run in the composite
  IS the `m1.run` of the first projection (trace labels re-tagged `inl`,
  the other machine pinned to its initial value): pure-side workloads stay
  on their side, nothing leaks into the other projection.

`compose` is `@[reducible]` so its field projections
(`(compose m1 m2).State`, `.step?`, `.run`) unfold for `rw`/`simp`/`change`
at default transparency — otherwise every composite theorem fights
semi-reducible projections.

Deliberately absent here (per lean-v3 D2, same placement): nondeterministic
interleaving/step-relation — the event family is a function, so the
composite is deterministic; a scheduler model lives in its own module later.
-/

import Machines.Core

namespace Machines

namespace Machine

/-- Parallel composition: product state, summed labels, each side's events
    act on their own projection. The invariant is conjunctive — both sides'
    invariants must hold, and each side's safety proof closes over its own
    conjunct. -/
@[reducible]
def compose (m1 m2 : Machine) : Machine where
  State := m1.State × m2.State
  Label := m1.Label ⊕ m2.Label
  Inv := fun s => m1.Inv s.1 ∧ m2.Inv s.2
  event := fun
    | Sum.inl l1 =>
        { guard := fun s => (m1.event l1).guard s.1
          action := fun s h => ((m1.event l1).action s.1 h, s.2)
          safety := fun s h hi => ⟨(m1.event l1).safety s.1 h hi.1, hi.2⟩ }
    | Sum.inr l2 =>
        { guard := fun s => (m2.event l2).guard s.2
          action := fun s h => (s.1, (m2.event l2).action s.2 h)
          safety := fun s h hi => ⟨hi.1, (m2.event l2).safety s.2 h hi.2⟩ }

/-- A composite `inl` step is the left machine's step, with the right
    component pinned. The map-on-Option shape is the statement of "the two
    projections cannot conflict". -/
theorem compose_step_inl (m1 m2 : Machine) (s : m1.State × m2.State) (l1 : m1.Label) :
    (Machine.compose m1 m2).step? s (Sum.inl l1) =
      (m1.step? s.1 l1).map (fun s1' => (s1', s.2)) := by
  unfold Machine.step? Machine.compose
  by_cases hg : (m1.event l1).guard s.1 = true
  · simp [hg]
  · simp [hg]

/-- Symmetric: composite `inr` step = right machine's step, left pinned. -/
theorem compose_step_inr (m1 m2 : Machine) (s : m1.State × m2.State) (l2 : m2.Label) :
    (Machine.compose m1 m2).step? s (Sum.inr l2) =
      (m2.step? s.2 l2).map (fun s2' => (s.1, s2')) := by
  unfold Machine.step? Machine.compose
  by_cases hg : (m2.event l2).guard s.2 = true
  · simp [hg]
  · simp [hg]

/-- The step?/projection biconditional for `inl`: the composite reaches
    `s'` exactly when `m1` reaches `s'.1` and `m2`'s component is untouched. -/
theorem compose_step_inl_proj (m1 m2 : Machine) (s : m1.State × m2.State)
    (l1 : m1.Label) (s' : m1.State × m2.State) :
    (Machine.compose m1 m2).step? s (Sum.inl l1) = some s' ↔
      m1.step? s.1 l1 = some s'.1 ∧ s'.2 = s.2 := by
  rw [compose_step_inl]
  constructor
  · intro h
    cases hms : m1.step? s.1 l1 with
    | none => simp [hms] at h
    | some a1 =>
      simp [hms] at h
      cases s' with
      | mk b1 b2 =>
        have hb1 : a1 = b1 := congrArg Prod.fst h
        have hb2 : s.2 = b2 := congrArg Prod.snd h
        constructor
        · simp [hb1]
        · exact hb2.symm
  · rintro ⟨hm, hs⟩
    rw [hm]
    cases s' with
    | mk a b =>
      change some (a, s.2) = some (a, b)
      have hbs : b = s.2 := by simpa using hs
      rw [hbs]

/-- The step?/projection biconditional for `inr`: the composite reaches
    `s'` exactly when `m2` reaches `s'.2` and `m1`'s component is untouched. -/
theorem compose_step_inr_proj (m1 m2 : Machine) (s : m1.State × m2.State)
    (l2 : m2.Label) (s' : m1.State × m2.State) :
    (Machine.compose m1 m2).step? s (Sum.inr l2) = some s' ↔
      m2.step? s.2 l2 = some s'.2 ∧ s'.1 = s.1 := by
  rw [compose_step_inr]
  constructor
  · intro h
    cases hms : m2.step? s.2 l2 with
    | none => simp [hms] at h
    | some a2 =>
      simp [hms] at h
      cases s' with
      | mk b1 b2 =>
        have hb1 : s.1 = b1 := congrArg Prod.fst h
        have hb2 : a2 = b2 := congrArg Prod.snd h
        constructor
        · simp [hb2]
        · exact hb1.symm
  · rintro ⟨hm, hs⟩
    rw [hm]
    cases s' with
    | mk a b =>
      change some (s.1, b) = some (a, b)
      have has : a = s.1 := by simpa using hs
      rw [has]

/-- The diamond — interleaving is safe. If `e1` (left) and `e2` (right) are
    both enabled at `s`, doing e1-then-e2 and e2-then-e1 reach the SAME
    state. Each event touches only its own projection (`compose_step_*_proj`),
    so the two interleavings coincide pointwise. -/
theorem compose_commute (m1 m2 : Machine) (s : m1.State × m2.State)
    (l1 : m1.Label) (l2 : m2.Label)
    (s' s'' t1 t2 : m1.State × m2.State)
    (h1 : (Machine.compose m1 m2).step? s (Sum.inl l1) = some s')
    (h2 : (Machine.compose m1 m2).step? s' (Sum.inr l2) = some t1)
    (h3 : (Machine.compose m1 m2).step? s (Sum.inr l2) = some s'')
    (h4 : (Machine.compose m1 m2).step? s'' (Sum.inl l1) = some t2) :
    t1 = t2 := by
  obtain ⟨ha1, hs'⟩ := (compose_step_inl_proj m1 m2 s l1 s').mp h1
  obtain ⟨ha3, hs''⟩ := (compose_step_inr_proj m1 m2 s l2 s'').mp h3
  obtain ⟨ha2, hfst1⟩ := (compose_step_inr_proj m1 m2 s' l2 t1).mp h2
  obtain ⟨ha4, hsnd2⟩ := (compose_step_inl_proj m1 m2 s'' l1 t2).mp h4
  have ha2' : m2.step? s.2 l2 = some t1.2 := by simpa [hs'] using ha2
  have ha4' : m1.step? s.1 l1 = some t2.1 := by simpa [hs''] using ha4
  have ht12 : t1.2 = s''.2 := by
    rw [ha2'] at ha3
    exact Option.some.inj ha3
  have ht21 : t2.1 = s'.1 := by
    rw [ha1] at ha4'
    exact (Option.some.inj ha4').symm
  apply Prod.ext
  · exact hfst1.trans ht21.symm
  · exact ht12.trans hsnd2.symm

/-- An all-`inl` run in the composite is exactly the `m1.run` of the first
    projection: labels re-tagged `inl`, every recorded right component
    pinned to its initial value, final state pinned likewise. Pure-left
    workloads never disturb the right projection. -/
theorem compose_run_inl (m1 m2 : Machine) (s : m1.State × m2.State)
    (ls : List m1.Label) :
    (Machine.compose m1 m2).run s (ls.map Sum.inl) =
      (m1.run s.1 ls).map
        (fun p : Machine.Trace m1 × m1.State =>
          (p.1.map (fun q : m1.Label × m1.State => (Sum.inl q.1, (q.2, s.2))), (p.2, s.2))) := by
  induction ls generalizing s with
  | nil =>
    cases s with
    | mk s1 s2 => simp [Machine.run]
  | cons l rest ih =>
    rw [List.map_cons]
    unfold Machine.run
    rw [compose_step_inl]
    cases hms : m1.step? s.1 l with
    | none => simp
    | some s1 =>
      simp
      rw [ih (s1, s.2)]
      cases htail : m1.run s1 rest with
      | none => simp
      | some p => simp

/-- Symmetric: an all-`inr` run is the `m2.run` of the second projection,
    left component pinned. -/
theorem compose_run_inr (m1 m2 : Machine) (s : m1.State × m2.State)
    (ls : List m2.Label) :
    (Machine.compose m1 m2).run s (ls.map Sum.inr) =
      (m2.run s.2 ls).map
        (fun p : Machine.Trace m2 × m2.State =>
          (p.1.map (fun q : m2.Label × m2.State => (Sum.inr q.1, (s.1, q.2))), (s.1, p.2))) := by
  induction ls generalizing s with
  | nil =>
    cases s with
    | mk s1 s2 => simp [Machine.run]
  | cons l rest ih =>
    rw [List.map_cons]
    unfold Machine.run
    rw [compose_step_inr]
    cases hms : m2.step? s.2 l with
    | none => simp
    | some s2 =>
      simp
      rw [ih (s.1, s2)]
      cases htail : m2.run s2 rest with
      | none => simp
      | some p => simp

end Machine

end Machines
