/-
# Effects.Footprint — the footprint laws over the minimal state model

The footprint discipline (notes/v3/08-capabilities.md §8): a command
declares its FOOTPRINT (the finite key set it may touch) and carries
the laws IN THE TYPE — construction carries them (the ladder's rung-3
shape at the structure):

- **reads_depend** — the command's RESULT depends only on the footprint
  cells (the reads' law);
- **writes_depend** — the command's WRITES depend only on the footprint
  cells (the write's outcome is a function of the footprint's
  contents — the law the frame rule needs to COMPOSE);
- **writes_preserve** — everything OUTSIDE the footprint is preserved
  (the writes' law).

The frame rule (`Cmd.frame`): two states agreeing outside the footprint
still agree outside it after the command runs — the write's reach is
exactly the footprint. The frame rule COMPOSES (`Cmd.seq` + `seq`'s
laws): sequential composition joins the footprints (the SAME
`Effects.unionMem` set-union discipline as the effect rows — one
mechanism, two instances), and the composite is again a lawful
command. The full wp-composition of contracted lanes is the contracts
wave's (08 §36) — named exclusion, never hinted at here.

The minimal state model, honestly named: `State := Key → Nat` — a
total function, a "missing" key reading zero. The model is honest for
the DISCIPLINE (the laws are about dependence and preservation, not
about storage); a real store's model (bounded keys, the storage
crossing) lands with its first consumer.

Doctrine slots (notes/v3/01-core.md, the five questions):
- **Root**: Universe (finite data: the key sets) over the Change
  reading (the write IS a change — its dependence laws are the
  Change discipline's shape, 01 §2).
- **Carrier grade**: none — the laws are the command's type, not a
  crossing between presentations.
- **Spine reading**: none — the footprint laws are consumed by the
  effect-annotated lanes when they mount.
- **Ladder rung**: rung 3 (the laws as the command's TYPE fields —
  construction discharges them) + rung 6 (the frame rule + the
  composite's laws: small generic hand theorems over the fields).
- **Gate rows**: EffectsTests' axiom self-check + the pins.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Effects.Basic

namespace Effects

/-! ## The minimal state model -/

/-- A state key (finite — the ids name the app's state cells). -/
abbrev Key := Nat

/-- The state: a total function from keys to nat values (a "missing"
    key reads zero — the model's honest note, see the header). -/
def State := Key → Nat

/-- A footprint: the finite set of keys a command may touch. -/
abbrev Fp := List Key

/-- The key-set join — the SAME set-union discipline as the effect rows
    (`Effects.unionMem`, cited; one mechanism, two instances). -/
def Fp.join : Fp → Fp → Fp := unionMem

theorem Fp.mem_join (k : Key) (a b : Fp) :
    k ∈ Fp.join a b ↔ k ∈ a ∨ k ∈ b := mem_unionMem k a b

/-! ## The command: the footprint laws IN THE TYPE -/

/-- A command: a declared footprint + a read + a write, with the three
    footprint laws carried at construction (rung 3 — an unlawful
    command is unconstructible). The footprint is an upper bound on
    BOTH the read's dependence and the write's reach. -/
structure Cmd where
  /-- The declared footprint. -/
  fp : Fp
  /-- The read: the command's result. -/
  run : State → Nat
  /-- The write: the state change. -/
  wr : State → State
  /-- THE reads' law: the result depends only on the footprint cells. -/
  reads_depend : ∀ s s', (∀ k, k ∈ fp → s k = s' k) → run s = run s'
  /-- THE writes' dependence: the write AT a footprint cell depends
      only on the footprint cells (the law the frame rule composes
      through; outside the footprint the write is a copy —
      `writes_preserve`). -/
  writes_depend : ∀ s s' k, k ∈ fp →
      (∀ j, j ∈ fp → s j = s' j) → wr s k = wr s' k
  /-- THE writes' law: everything outside the footprint is preserved. -/
  writes_preserve : ∀ s k, k ∉ fp → wr s k = s k

/-! ## The frame rule -/

/-- THE frame rule: two states agreeing OUTSIDE the footprint still
    agree outside it after the command runs — the write's reach is
    exactly the declared footprint. -/
theorem Cmd.frame (c : Cmd) (s s' : State)
    (h : ∀ k, k ∉ c.fp → s k = s' k) :
    ∀ k, k ∉ c.fp → c.wr s k = c.wr s' k := by
  intro k hk
  rw [c.writes_preserve s k hk, c.writes_preserve s' k hk]
  exact h k hk

/-! ## The composition (the frame rule composes) -/

/-- The agreement carrier: if `s`, `s'` agree on the JOINED footprint,
    then after `c₁` the states agree on the joined footprint — the
    frame rule + the dependence laws, composed (the seq proofs' shared
    lemma). -/
theorem wr_frame_of_join (c₁ c₂ : Cmd) (s s' : State)
    (h : ∀ k, k ∈ Fp.join c₁.fp c₂.fp → s k = s' k) :
    ∀ k, k ∈ Fp.join c₁.fp c₂.fp → c₁.wr s k = c₁.wr s' k := by
  intro k hk
  if hj1 : k ∈ c₁.fp then
    exact c₁.writes_depend s s' k hj1
      (fun j hj => h j ((Fp.mem_join j c₁.fp c₂.fp).mpr (Or.inl hj)))
  else
    rw [c₁.writes_preserve s k hj1, c₁.writes_preserve s' k hj1]
    exact h k hk

/-- Sequential composition: the footprints JOIN (the set-union
    discipline, cited); the runs thread through the writes; the
    composite is again a lawful command — the frame rule composes
    through the join. -/
def Cmd.seq (c₁ c₂ : Cmd) : Cmd where
  fp := Fp.join c₁.fp c₂.fp
  run := fun s => c₂.run (c₁.wr s)
  wr := fun s => c₂.wr (c₁.wr s)
  reads_depend := by
    intro s s' h
    exact c₂.reads_depend (c₁.wr s) (c₁.wr s')
      (fun k hk2 => wr_frame_of_join c₁ c₂ s s' h k
        ((Fp.mem_join k c₁.fp c₂.fp).mpr (Or.inr hk2)))
  writes_depend := by
    intro s s' k hk h
    if hk2 : k ∈ c₂.fp then
      exact c₂.writes_depend (c₁.wr s) (c₁.wr s') k hk2
        (fun j hj => wr_frame_of_join c₁ c₂ s s' h j
          ((Fp.mem_join j c₁.fp c₂.fp).mpr (Or.inr hj)))
    else
      rw [c₂.writes_preserve (c₁.wr s) k hk2, c₂.writes_preserve (c₁.wr s') k hk2]
      exact wr_frame_of_join c₁ c₂ s s' h k hk
  writes_preserve := by
    intro s k hk
    have h1 : k ∉ c₁.fp :=
      fun hm => hk ((Fp.mem_join k c₁.fp c₂.fp).mpr (Or.inl hm))
    have h2 : k ∉ c₂.fp :=
      fun hm => hk ((Fp.mem_join k c₁.fp c₂.fp).mpr (Or.inr hm))
    rw [c₂.writes_preserve (c₁.wr s) k h2, c₁.writes_preserve s k h1]

/-- The composite's reads' law, stated as the frame discipline's
    composition pin: the composite command still reads only its joined
    footprint — THE composition law the effects lane's rows predict
    (the join is the upper bound; the footprint's join is its
    state-side twin). -/
theorem Cmd.seq_reads (c₁ c₂ : Cmd) (s s' : State)
    (h : ∀ k, k ∈ Fp.join c₁.fp c₂.fp → s k = s' k) :
    (c₁.seq c₂).run s = (c₁.seq c₂).run s' :=
  (c₁.seq c₂).reads_depend s s' h

end Effects
