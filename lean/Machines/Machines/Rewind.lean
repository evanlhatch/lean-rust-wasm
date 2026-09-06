/-
# Machines.Rewind — generic undo; rewind-K = undo-K

lean-v3 Part 5: "Rewind.lean — generic undo; flatland's tick-segmented
overlay is one instance."

The shape: a rewindable machine's events carry a Δ witness (what the
journal records) and a `revert` that walks a state back across one event.
`runLogged` records the deltas alongside the trace; the theorems:

- `runLogged_run` — the logged run is the SAME execution as `Machine.run`
  (deltas are observations, not machinery).
- `rewind_runLogged` — reverting the recorded deltas in reverse order
  restores the initial state.
- `runLogged_append` / `runLogged_split` — runs decompose over `++`.
- `rewind_suffix` — **rewind-K = undo-K**: reverting the last K deltas
  restores the state after the first (length − K) events. The engine's
  tick-segmented overlay instantiates this with per-tick segments
  (Flatland.Overlay).

The engine instance: Δ := the per-column ChangeSet batch, revert :=
ChangeSet.revert — `revert_left` discharges from Change.lean's revert law
(the olds-match side condition holds by the journal's construction).
-/

import Machines.Core

namespace Machines

/-- A rewindable machine: a machine whose events record a delta witness
    with a left-inverse revert. -/
structure RewindableMachine extends Machine where
  /-- The delta type (what the journal records per event). -/
  Δ : Type
  /-- The delta an event produces at a state. -/
  deltaOf : (l : Label) → (s : State) → (h : (event l).guard s = true) → Δ
  /-- Reverting a delta walks a state back across the event that
      produced it. -/
  revert : Δ → State → State
  /-- revert is left-inverse to the action that produced the delta. -/
  revert_left : ∀ l s h, revert (deltaOf l s h) ((event l).action s h) = s

namespace RewindableMachine

variable (m : RewindableMachine)

/-- A logged run: the trace plus the per-step deltas (the journal). The
    guard proof is in scope at each step, so the delta is recorded with
    its evidence. -/
def runLogged (s : m.State) (ls : List m.Label) :
    Option (m.Trace × List m.Δ × m.State) :=
  match ls with
  | [] => some ([], [], s)
  | l :: rest =>
    if h : (m.event l).guard s = true then
      match runLogged ((m.event l).action s h) rest with
      | none => none
      | some (tr, ds, fin) => some ((l, (m.event l).action s h) :: tr, m.deltaOf l s h :: ds, fin)
    else none

-- the @[simp] equation set for the logged run (same discipline as Core).

@[simp] theorem runLogged_nil (s : m.State) :
    runLogged m s [] = some ([], [], s) := rfl

@[simp] theorem runLogged_cons (s : m.State) (l : m.Label) (ls : List m.Label) :
    runLogged m s (l :: ls) = if h : (m.event l).guard s = true then
      match runLogged m ((m.event l).action s h) ls with
      | none => none
      | some (tr, ds, fin) =>
        some ((l, (m.event l).action s h) :: tr, m.deltaOf l s h :: ds, fin)
    else none := rfl

/-- Revert a list of deltas onto a state, in list order. Callers pass
    `ds.reverse` for last-first (the overlay's segment rewind). -/
def rewind (m : RewindableMachine) (ds : List m.Δ) (s : m.State) : m.State :=
  ds.foldl (fun st d => m.revert d st) s

/-- The logged run is the same execution as `Machine.run` — deltas are
    observations, not machinery. -/
theorem runLogged_run (m : RewindableMachine) :
    ∀ (ls : List m.Label) (init : m.State) tr ds fin,
      runLogged m init ls = some (tr, ds, fin) →
      m.run init ls = some (tr, fin) := by
  intro ls
  induction ls with
  | nil =>
    intro init tr ds fin h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨h12, h3⟩ := Prod.mk.inj h2
    subst h1 h12 h3
    rfl
  | cons l rest ih =>
    intro init tr ds fin h
    simp only [runLogged] at h
    split at h
    · next hguard =>
      split at h
      · contradiction
      · next tr' ds' fin' hrest =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨h2a, h2b⟩ := Prod.mk.inj h2
        subst h1 h2b
        have hstep : m.step? init l = some ((m.event l).action init hguard) := by
          unfold Machine.step?
          rw [dif_pos hguard]
        have hrun' := ih ((m.event l).action init hguard) tr' ds' fin' hrest
        simp only [Machine.run, hstep, hrun']
    · next => contradiction

/-- **Rewind undoes the run**: reverting the recorded deltas last-first
    restores the initial state. -/
theorem rewind_runLogged (m : RewindableMachine) :
    ∀ (ls : List m.Label) (init : m.State) tr ds fin,
      runLogged m init ls = some (tr, ds, fin) →
      m.rewind ds.reverse fin = init := by
  intro ls
  induction ls with
  | nil =>
    intro init tr ds fin h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨h12, h3⟩ := Prod.mk.inj h2
    subst h1 h12 h3
    rfl
  | cons l rest ih =>
    intro init tr ds fin h
    simp only [runLogged] at h
    split at h
    · next hguard =>
      split at h
      · contradiction
      · next tr' ds' fin' hrest =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨h2a, h2b⟩ := Prod.mk.inj h2
        subst h1 h2a h2b
        show m.rewind ((m.deltaOf l init hguard :: ds').reverse) fin' = init
        rw [List.reverse_cons]
        show m.rewind (ds'.reverse ++ [m.deltaOf l init hguard]) fin' = init
        rw [rewind, List.foldl_append]
        have ihr := ih ((m.event l).action init hguard) tr' ds' fin' hrest
        show m.revert (m.deltaOf l init hguard) (m.rewind ds'.reverse fin') = init
        rw [ihr]
        exact m.revert_left l init hguard
    · next => contradiction

/-- A logged run absorbs an appended label sequence. -/
theorem runLogged_append (m : RewindableMachine) :
    ∀ (ls1 ls2 : List m.Label) (init : m.State) tr1 ds1 mid tr2 ds2 fin,
      runLogged m init ls1 = some (tr1, ds1, mid) →
      runLogged m mid ls2 = some (tr2, ds2, fin) →
      runLogged m init (ls1 ++ ls2) = some (tr1 ++ tr2, ds1 ++ ds2, fin) := by
  intro ls1
  induction ls1 with
  | nil =>
    intro ls2 init tr1 ds1 mid tr2 ds2 fin h1 h2
    obtain ⟨ha, hb⟩ := Prod.mk.inj (Option.some.inj h1)
    obtain ⟨hb1, hb2⟩ := Prod.mk.inj hb
    subst ha hb1 hb2
    simpa [runLogged] using h2
  | cons l rest ih =>
    intro ls2 init tr1 ds1 mid tr2 ds2 fin h1 h2
    simp only [runLogged] at h1
    split at h1
    · next hguard =>
      split at h1
      · contradiction
      · next tr1' ds1' mid' hrest =>
        obtain ⟨h1a, h1b⟩ := Prod.mk.inj (Option.some.inj h1)
        obtain ⟨h1c, h1d⟩ := Prod.mk.inj h1b
        subst h1a h1c h1d
        have hcont := ih ls2 ((m.event l).action init hguard) tr1' ds1' mid' tr2 ds2 fin hrest h2
        simp only [List.cons_append, runLogged]
        rw [dif_pos hguard, hcont]
    · next => contradiction

/-- The converse decomposition: a successful run over an append splits
    into the two prefix runs. -/
theorem runLogged_split (m : RewindableMachine) :
    ∀ (ls1 ls2 : List m.Label) (init : m.State) tr ds fin,
      runLogged m init (ls1 ++ ls2) = some (tr, ds, fin) →
      ∃ mid tr1 ds1 tr2 ds2,
        tr = tr1 ++ tr2 ∧ ds = ds1 ++ ds2 ∧
        runLogged m init ls1 = some (tr1, ds1, mid) ∧
        runLogged m mid ls2 = some (tr2, ds2, fin) := by
  intro ls1
  induction ls1 with
  | nil =>
    intro ls2 init tr ds fin h
    exact ⟨init, [], [], tr, ds, rfl, rfl, rfl, h⟩
  | cons l rest ih =>
    intro ls2 init tr ds fin h
    simp only [List.cons_append, runLogged] at h
    split at h
    · next hguard =>
      split at h
      · contradiction
      · next tr' ds' fin' hrest =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨h2a, h2b⟩ := Prod.mk.inj h2
        subst h1 h2a h2b
        obtain ⟨mid, tr1, ds1, tr2, ds2, htr1, hds1, hr1, hr2⟩ :=
          ih ls2 ((m.event l).action init hguard) tr' ds' fin' hrest
        refine ⟨mid, (l, (m.event l).action init hguard) :: tr1,
          m.deltaOf l init hguard :: ds1, tr2, ds2, ?_, ?_, ?_, hr2⟩
        · rw [htr1]
          rfl
        · rw [hds1]
          rfl
        · simp only [runLogged]
          rw [dif_pos hguard, hr1]
    · next => contradiction

/-- The delta log has one entry per event. -/
theorem runLogged_length (m : RewindableMachine) :
    ∀ (ls : List m.Label) (init : m.State) tr ds fin,
      runLogged m init ls = some (tr, ds, fin) → ds.length = ls.length := by
  intro ls
  induction ls with
  | nil =>
    intro init tr ds fin h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨h12, -⟩ := Prod.mk.inj h2
    subst h12
    rfl
  | cons l rest ih =>
    intro init tr ds fin h
    simp only [runLogged] at h
    split at h
    · next hguard =>
      split at h
      · contradiction
      · next tr' ds' fin' hrest =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hds, -⟩ := Prod.mk.inj h2
        subst hds
        have hlen := ih ((m.event l).action init hguard) tr' ds' fin' hrest
        simp [List.length_cons, hlen]
    · next => contradiction

/-- **rewind-K = undo-K**: reverting the last K recorded deltas restores
    the state after the first (length − K) events. The engine's
    tick-segmented overlay instantiates this with per-tick segments. -/
theorem rewind_suffix (m : RewindableMachine)
    (ls : List m.Label) (init : m.State) (tr : m.Trace) (ds : List m.Δ) (fin : m.State)
    (h : runLogged m init ls = some (tr, ds, fin)) (K : Nat) (hK : K ≤ ls.length) :
    ∃ mid tr1 ds1,
      runLogged m init (ls.take (ls.length - K)) = some (tr1, ds1, mid) ∧
      m.rewind (ds.drop (ls.length - K)).reverse fin = mid := by
  have hsplit : ls.take (ls.length - K) ++ ls.drop (ls.length - K) = ls :=
    List.take_append_drop (ls.length - K) ls
  rw [← hsplit] at h
  obtain ⟨mid, tr1, ds1, tr2, ds2, -, hds, hr1, hr2⟩ := runLogged_split m _ _ _ _ _ _ h
  have hlen1 : ds1.length = ls.length - K := by
    have hL := runLogged_length m _ _ _ _ _ hr1
    rw [hL, List.length_take]
    exact Nat.min_eq_left (Nat.sub_le ls.length K)
  have hdrop : ds.drop (ls.length - K) = ds2 := by
    rw [hds, ← hlen1, List.drop_append]
    simp
  exact ⟨mid, tr1, ds1, hr1, hdrop ▸ rewind_runLogged m _ mid tr2 ds2 fin hr2⟩

end RewindableMachine

end Machines
