/-
# Machines.Coalg — the observation coalgebra: unfold, bisimulation, finality, refinement

Owned by: the coalgebra agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/16-surface.md §4.2 (the coalgebraic half —
the strengthening program's item 2: the TraceModel root has
bisimulation-as-stream-equality — landed in `Machines.Fusion` — but no
FINALITY, the dual of initiality. Land: the unfold/corecursion
discipline + the finality theorem (behavioral equality IS
bisimilarity) + refinement between machines as the morphisms — the
home of impl ≤ spec) + notes/v3/01-core.md §3 (the transition
semantics is AUTHORITATIVE — every derived claim here ties back to the
landed `Machine.step?` by definition, never a parallel encoding) +
notes/v3/04-verification.md §4 (the observer parameter: every
"same behavior" names its observer, as data — here a `Kit.Observer`
field, per 04 §4).

## The coalgebra reading

A machine AS an observation coalgebra: the landed `Machine` (the
authoritative `step?`) paired with a named observer. The coalgebra map
is `observe : S → I → Option (O × S)` — the step + what the observer
sees of the post-state, or the honest refusal (`none`; the refusal is
data, never a silent self-loop — Basic.lean's discipline).

THE UNFOLD (corecursion — the dual of the Universe root's fold): the
behavior of a state IS the stream of observations it yields under an
input stream — `beh : Stream I → S → Stream (Option O)`, `some o` per
fired step, `none` per refusal. Refusal HOLDS the state (Fusion's
`tick` convention — a blocked step is a no-op), so `beh` is total by
construction. This is the STREAM case of the unfold; the landed
machines are step?-functional, so the stream is the honest carrier.

## What lands

- `Coalgebra` — the (machine, observer) bundle; `observe` (the
  coalgebra map), `next` (the post-state, hold-on-refusal), `states`
  (the state stream), `beh` (the behavior stream).
- `Bisim` — the stepwise game over the coalgebra map (observations
  agree per step ∧ successors stay related) — and THE COINDUCTION
  PRINCIPLE's sound direction: `bisim_sound`/`bisim_sound_at` — a
  bisimulation implies behavioral equality, proved honestly over the
  stream shape by the time-shifted induction (no coinductive types —
  Lean core has none; the induction is on time, the input stream
  generalized).
- FINALITY (16 §4.2): `behEq_bisim` — the KERNEL of `beh` is itself a
  bisimulation (the dual of initiality's fold_unique) — packaged as
  `behEq_iff_bisim`: two states have equal behavior on every input iff
  they are related by SOME bisimulation. Behavioral equality IS
  bisimilarity; `beh` is as strong as the final coalgebra's witness.
- `Refines` — impl ≤ spec: the observer-parameterized simulation whose
  field IS the relation (Kit.Relation's `Rel`), with the behavior
  inclusion law `beh_le`; refinements CHAIN through `Rel.comp`
  (`Refines.comp` — the tower).

## The five questions

- **Root**: TraceModel (01-core §3) — the FINALITY half: behavior as
  the derived-but-determining view; bisimulation and refinement as the
  relations between machines. The dual of the Universe root's
  initiality (`foldTy_unique`) is landed HERE, over the stream
  carrier: this makes TraceModel as strong as Universe.
- **Carrier grade**: pattern #1 at the coalgebra level — `observe` is
  data tied to the landed `step?` BY DEFINITION (no parallel
  encoding); every claim rides `Kit.Observer` (04 §4) and
  `Kit.Relation` (the ONE relation family).
- **Spine reading**: none — a substrate module; consumers (the model
  checking lane, refinement lanes) instantiate it.
- **Ladder rung**: hand theorems at the structure (rung 6 —
  relational content over the stream recursion: the time-shift lemmas
  and both finality directions are one induction each; not
  kernel-decidable in general).
- **Gate rows**: axiom pins in MachinesTests.Coalg (the core-triple
  surface over the coinduction principle + the finality iff).

## Named exclusions

- NO execution-TREE behavior (the bounded-branching case of the
  unfold: for bounded input spaces the behavior is a TREE, not a
  stream) — the landed machines are step?-functional; the tree case
  lands with its first branching consumer.
- NO nondeterministic bisimulation (the general LTS story), NO
  stutter/invisible-step quotient — 01-core §3's per-claim choices;
  Fusion's exclusion extended here.
- NO divergence side-conditions: refusal HOLDS (the totalized
  convention), so `beh` is total by construction; a partial-stream
  reading of divergence is not this slice.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic
import Machines.Stream
import Kit.Observer
import Kit.Relation

namespace Machines

/-! ## The observation coalgebra -/

/-- A machine AS an observation coalgebra: the landed `Machine` (the
    authoritative `step?`) paired with the named observer (04 §4)
    whose `see` is what one step exposes. -/
structure Coalgebra (S I O : Type) where
  machine : Machine S I
  observer : Kit.Observer S O

namespace Coalgebra

variable {S I O : Type}

/-! ### The coalgebra map, the post-state, the unfold -/

/-- THE COALGEBRA MAP: `observe : S → I → Option (O × S)` — the step +
    what the observer sees of the post-state, or the honest refusal.
    The dual shape of the fold's algebra: the functor `X ↦ Option (O × X)`.
    Tied to the landed `step?` BY DEFINITION — no parallel encoding. -/
def observe (c : Coalgebra S I O) (s : S) (i : I) : Option (O × S) :=
  (c.machine.step? s i).map fun s' => (c.observer.see s', s')

/-- The post-state of a coalgebra step: the successor if the step
    fired, else HOLD (Fusion's tick convention — a blocked step is a
    no-op, so the unfold below is total). -/
def next (c : Coalgebra S I O) (s : S) (i : I) : S :=
  (c.observe s i).map (fun p => p.2) |>.getD s

theorem next_of_some (c : Coalgebra S I O) {s : S} {i : I} {o : O} {s' : S}
    (h : c.observe s i = some (o, s')) : c.next s i = s' := by
  show ((c.observe s i).map (fun p => p.2)).getD s = s'
  rw [h]; rfl

theorem next_of_none (c : Coalgebra S I O) {s : S} {i : I}
    (h : c.observe s i = none) : c.next s i = s := by
  show ((c.observe s i).map (fun p => p.2)).getD s = s
  rw [h]; rfl

/-- THE UNFOLD, state face (corecursion — fold's dual): the coalgebra's
    state at each time under input stream `ins` from `s`; refusal HOLDS.
    The structural mirror of `Fusion.stateStream`, over the coalgebra map. -/
def states (c : Coalgebra S I O) (ins : Stream I) (s : S) : Stream S :=
  fun t => match t with
    | 0 => s
    | t + 1 => c.next (c.states ins s t) (ins t)

@[simp] theorem states_zero (c : Coalgebra S I O) (ins : Stream I) (s : S) :
    c.states ins s 0 = s := rfl

@[simp] theorem states_succ (c : Coalgebra S I O) (ins : Stream I) (s : S) (t : Nat) :
    c.states ins s (t + 1) = c.next (c.states ins s t) (ins t) := rfl

/-- THE BEHAVIOR (the unfold's observation face): the stream of what
    the observer sees, one entry per step — `some o` when the coalgebra
    fired, `none` when it refused. The behavior of a state IS this
    stream: the coalgebra reading of "what happens". -/
def beh (c : Coalgebra S I O) (ins : Stream I) (s : S) : Stream (Option O) :=
  fun t => (c.observe (c.states ins s t) (ins t)).map fun p => p.1

@[simp] theorem beh_eq (c : Coalgebra S I O) (ins : Stream I) (s : S) (t : Nat) :
    c.beh ins s t = (c.observe (c.states ins s t) (ins t)).map (fun p => p.1) := rfl

/-! ### The time shift (the one lemma the stream discipline needs) -/

/-- The time-shift, state face: one step from `s` then `t` steps under
    the tail of `ins` = `t+1` steps under `ins`. -/
theorem states_shift (c : Coalgebra S I O) (ins : Stream I) (s : S) (t : Nat) :
    c.states ins s (t + 1)
      = c.states (fun u => ins (u + 1)) (c.next s (ins 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show c.next (c.states ins s (t + 1)) (ins (t + 1))
         = c.next (c.states (fun u => ins (u + 1)) (c.next s (ins 0)) t)
             ((fun u => ins (u + 1)) t)
      rw [ih]

/-- The time-shift, behavior face: the behavior from time `t+1` on is
    the behavior of the successor state under the tail of `ins`. -/
theorem beh_shift (c : Coalgebra S I O) (ins : Stream I) (s : S) (t : Nat) :
    c.beh ins s (t + 1)
      = c.beh (fun u => ins (u + 1)) (c.next s (ins 0)) t := by
  show (c.observe (c.states ins s (t + 1)) (ins (t + 1))).map (fun p => p.1)
     = (c.observe (c.states (fun u => ins (u + 1)) (c.next s (ins 0)) t)
         ((fun u => ins (u + 1)) t)).map (fun p => p.1)
  rw [states_shift]

/-! ## Bisimulation + the coinduction principle's sound direction -/

/-- BISIMULATION, the stepwise game over the coalgebra map: `R`-related
    states (i) observe equally at each step — so one side firing forces
    the other (a `none` under `.map (·.1)` cannot equal a `some`) — and
    (ii) step to `R`-related successors (hold-on-refusal included: if
    both refuse, the hypothesis `R s t` carries it). For the landed
    step?-functional machines this IS the classical bisimulation; the
    existential-successor spelling is recovered from (i) + `next`. -/
def Bisim (c : Coalgebra S I O) (R : Kit.Rel S S) : Prop :=
  ∀ s t, R s t → ∀ i,
    (c.observe s i).map (fun p => p.1) = (c.observe t i).map (fun p => p.1)
    ∧ R (c.next s i) (c.next t i)

/-- THE COINDUCTION PRINCIPLE, sound direction (pointwise): a
    bisimulation implies behavioral equality at every time — the
    time-shifted induction, the input stream generalized (16 §4.2). -/
theorem bisim_sound_at (c : Coalgebra S I O) (R : Kit.Rel S S) (hB : c.Bisim R) :
    ∀ (k : Nat) (ins : Stream I) (s t : S), R s t →
      c.beh ins s k = c.beh ins t k := by
  intro k
  induction k with
  | zero =>
      intro ins s t hR
      exact (hB s t hR (ins 0)).1
  | succ k ih =>
      intro ins s t hR
      rw [c.beh_shift ins s k, c.beh_shift ins t k]
      exact ih (fun u => ins (u + 1)) (c.next s (ins 0)) (c.next t (ins 0))
        (hB s t hR (ins 0)).2

/-- THE COINDUCTION PRINCIPLE, sound direction (stream level):
    bisimilar states are behaviorally equal — equal observation streams
    on EVERY input stream. -/
theorem bisim_sound (c : Coalgebra S I O) (R : Kit.Rel S S) (hB : c.Bisim R)
    (s t : S) (hR : R s t) (ins : Stream I) :
    c.beh ins s = c.beh ins t :=
  funext fun k => c.bisim_sound_at R hB k ins s t hR

/-! ## FINALITY: behavioral equality IS bisimilarity -/

/-- Behavioral equality: equal behavior streams on every input. -/
abbrev BehEq (c : Coalgebra S I O) (s t : S) : Prop :=
  ∀ ins : Stream I, c.beh ins s = c.beh ins t

/-- FINALITY, the kernel lemma (16 §4.2): the kernel of `beh` is itself
    a bisimulation — the dual of initiality's `foldTy_unique`. The
    observation conjunct reads the const-input stream at time 0; the
    successor conjunct splices the step's input in front of an
    arbitrary stream and reads the shifted equality at time `k+1`
    (the tail of the splice IS the arbitrary stream, definitionally). -/
theorem behEq_bisim (c : Coalgebra S I O) :
    c.Bisim (fun s t => c.BehEq s t) := by
  intro s t h i
  refine ⟨congrFun (h (fun _ => i)) 0, ?_⟩
  intro ins
  funext k
  have key := congrFun (h (fun u => match u with | 0 => i | u + 1 => ins u)) (k + 1)
  rw [beh_shift, beh_shift] at key
  exact key

/-- **FINALITY** (16 §4.2, the iff): two states have equal behavior on
    every input iff they are related by SOME bisimulation. Forward:
    the kernel of `beh` IS one (`behEq_bisim`). Backward: the
    coinduction principle (`bisim_sound`). Behavioral equality IS
    bisimilarity — the final-coalgebra witness, honestly over streams. -/
theorem behEq_iff_bisim (c : Coalgebra S I O) (s t : S) :
    c.BehEq s t ↔ ∃ R : Kit.Rel S S, c.Bisim R ∧ R s t :=
  ⟨fun hbeq => ⟨fun a b => c.BehEq a b, behEq_bisim c, hbeq⟩,
   fun h => by
      obtain ⟨R, hBis, hst⟩ := h
      exact fun ins => c.bisim_sound R hBis s t hst ins⟩

end Coalgebra

/-! ## Refinement: impl ≤ spec (the morphisms between machines) -/

variable {S I O : Type}

/-- REFINEMENT (16 §4.2): impl (`c₁`) ≤ spec (`c₂`) through the
    simulation `R` — whose field IS the relation (Kit.Relation's `Rel`),
    the observers riding the coalgebras (04 §4). The stepwise
    obligation, at every `R`-related pair and every input:
    either impl REFUSES — then spec may move, but the held impl state
    must stay simulated (`R s₁ s₂'`) — or impl FIRES with observation
    `o` — then spec fires with the SAME observation and a simulated
    successor. Directional by design (Kit's directionality control's
    face); the symmetric claim is a separate, stronger statement. -/
structure Refines {S I O : Type} (c₁ c₂ : Coalgebra S I O) (R : Kit.Rel S S) : Prop where
  step : ∀ {s₁ s₂ : S}, R s₁ s₂ → ∀ i : I,
    (c₁.observe s₁ i = none
      ∧ ∀ (o₂ : O) (s₂' : S), c₂.observe s₂ i = some (o₂, s₂') → R s₁ s₂')
    ∨ ∃ (o : O) (s₁' s₂' : S),
        c₁.observe s₁ i = some (o, s₁')
        ∧ c₂.observe s₂ i = some (o, s₂')
        ∧ R s₁' s₂'

namespace Refines

variable {S I O : Type}

/-- THE REFINEMENT LAW (16 §4.2 — the home of impl ≤ spec): a
    refinement keeps the states related along every input stream, and
    every observation impl makes, spec makes too — the behavior
    inclusion, at every time. One induction over time with the state
    pair and stream generalized (the shift does the rest). -/
theorem beh_le {c₁ c₂ : Coalgebra S I O} {R : Kit.Rel S S}
    (h : Refines c₁ c₂ R) :
    ∀ (t : Nat) (s₁ s₂ : S) (ins : Stream I), R s₁ s₂ →
      R (c₁.states ins s₁ t) (c₂.states ins s₂ t)
      ∧ ∀ o : O, c₁.beh ins s₁ t = some o → c₂.beh ins s₂ t = some o := by
  intro t
  induction t with
  | zero =>
      intro s₁ s₂ ins hs
      refine ⟨hs, ?_⟩
      intro o h₀
      rw [Coalgebra.beh_eq, Coalgebra.states_zero] at h₀
      rcases h.step hs (ins 0) with ⟨hn, _⟩ | ⟨o', a, b, h₁, h₂, _⟩
      · rw [hn] at h₀; exact absurd h₀ (by simp)
      · have ho : o' = o := by
          rw [h₁] at h₀; simpa using h₀
        subst ho
        rw [Coalgebra.beh_eq, Coalgebra.states_zero, h₂]
        rfl
  | succ t ih =>
      intro s₁ s₂ ins hs
      have hrel : R (c₁.next s₁ (ins 0)) (c₂.next s₂ (ins 0)) := by
        rcases h.step hs (ins 0) with ⟨hn, tr⟩ | ⟨o, a, b, h₁, h₂, hR'⟩
        · rw [c₁.next_of_none hn]
          cases hc₂ : c₂.observe s₂ (ins 0) with
          | none => rw [c₂.next_of_none hc₂]; exact hs
          | some q =>
              have hq : c₂.observe s₂ (ins 0) = some q := hc₂
              obtain ⟨o₂, b'⟩ := q
              rw [c₂.next_of_some hq]; exact tr o₂ b' hq
        · rw [c₁.next_of_some h₁, c₂.next_of_some h₂]; exact hR'
      obtain ⟨hRt, hbt⟩ := ih _ _ (fun u => ins (u + 1)) hrel
      rw [c₁.states_shift ins s₁ t, c₂.states_shift ins s₂ t]
      refine ⟨hRt, ?_⟩
      intro o h₀
      rw [c₁.beh_shift ins s₁ t] at h₀
      rw [c₂.beh_shift ins s₂ t]
      exact hbt o h₀

/-- The state-tracking face, at a friendly argument order. -/
theorem states_related {c₁ c₂ : Coalgebra S I O} {R : Kit.Rel S S}
    (h : Refines c₁ c₂ R) (s₁ s₂ : S) (ins : Stream I) (hs : R s₁ s₂) (t : Nat) :
    R (c₁.states ins s₁ t) (c₂.states ins s₂ t) :=
  (h.beh_le t s₁ s₂ ins hs).1

/-- The behavior-inclusion face, at a friendly argument order. -/
theorem beh_le_at {c₁ c₂ : Coalgebra S I O} {R : Kit.Rel S S}
    (h : Refines c₁ c₂ R) (s₁ s₂ : S) (ins : Stream I) (hs : R s₁ s₂) (t : Nat)
    (o : O) (h₀ : c₁.beh ins s₁ t = some o) :
    c₂.beh ins s₂ t = some o :=
  (h.beh_le t s₁ s₂ ins hs).2 o h₀

/-- REFINEMENTS CHAIN (16 §4.2 — the tower; `Kit.Relation.comp`'s
    composition row): impl ≤ mid ≤ spec ⟹ impl ≤ spec through the
    ONE composite relation `Rel.comp R₁ R₂` — its witness the mid
    state, exactly transitivity's shape. -/
theorem comp {S I O : Type} {c₁ c₂ c₃ : Coalgebra S I O} {R₁ R₂ : Kit.Rel S S}
    (h₁ : Refines c₁ c₂ R₁) (h₂ : Refines c₂ c₃ R₂) :
    Refines c₁ c₃ (Kit.Rel.comp R₁ R₂) :=
  ⟨by
    intro s₁ s₃ h i
    obtain ⟨m, hm₁, hm₂⟩ := h
    rcases h₁.step hm₁ i with ⟨hn₁, tr₁⟩ | ⟨o, a, b, h₁a, h₁b, hR₁⟩
    · -- impl refuses
      cases hc₂ : c₂.observe m i with
      | none =>
          rcases h₂.step hm₂ i with ⟨_, tr₂⟩ | ⟨o', a', b', h₂a, h₂b, hR₂⟩
          · -- mid refuses too: spec may fire, tracked by mid's own tracking clause
            refine Or.inl ⟨hn₁, ?_⟩
            intro o₃ s₃' h₃
            exact ⟨m, hm₁, tr₂ o₃ s₃' h₃⟩
          · exact absurd h₂a (by rw [hc₂]; simp)
      | some q =>
          have hq : c₂.observe m i = some q := hc₂
          obtain ⟨o₂, m'⟩ := q
          have hr₁ : R₁ s₁ m' := tr₁ o₂ m' hq
          rcases h₂.step hm₂ i with ⟨hn₂, _⟩ | ⟨o', a', b', h₂a, h₂b, hR₂⟩
          · exact absurd hq (by rw [hn₂]; simp)
          · -- mid fires, spec fires: spec's move is tracked against mid's successor
            have hin : o₂ = o' ∧ m' = a' := by
              rw [hq] at h₂a; simpa using h₂a
            refine Or.inl ⟨hn₁, ?_⟩
            intro o₃ s₃' h₃
            have hcon : o' = o₃ ∧ b' = s₃' := by
              rw [h₂b] at h₃; simpa using h₃
            rw [← hcon.2]
            rw [← hin.2] at hR₂
            exact ⟨m', hr₁, hR₂⟩
    · -- impl fires: mid fires with the same observation
      rcases h₂.step hm₂ i with ⟨hn₂, _⟩ | ⟨o', a', b', h₂a, h₂b, hR₂⟩
      · exact absurd h₁b (by rw [hn₂]; simp)
      · have hin : o' = o ∧ a' = b := by
          rw [h₂a] at h₁b; simpa using h₁b
        refine Or.inr ⟨o, a, b', h₁a, ?_, b, hR₁, ?_⟩
        · rw [hin.1] at h₂b; exact h₂b
        · rw [← hin.2]; exact hR₂⟩

end Refines

end Machines
