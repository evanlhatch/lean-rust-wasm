/-
# Machines.Live — the liveness vocabulary

Vendored from verse-lab/lentil (Apache-2.0) per notes/lean/lean-v3.md D17:
the TLA operators over executions, restated over our traces. Safety says
"nothing bad happens"; this vocabulary says "something good eventually
happens" — deadlock-freedom (some guard always enabled) and cascade progress
are stated in it.

An execution is an infinite sequence of states (`Exec σ := Nat → σ`);
operators are indexed by the current position. No strong fairness, no
stuttering — ticks don't need them.
-/

namespace Machines

/-- An execution: a state at every instant. -/
abbrev Exec (σ : Type) := Nat → σ

/-- A temporal predicate on executions, evaluated at an instant. -/
abbrev TPred (σ : Type) := Exec σ → Nat → Prop

/-- □p — always. -/
def tlaAlways (p : TPred σ) : TPred σ := fun e i => ∀ k, p e (i + k)

/-- ◇p — eventually. -/
def tlaEventually (p : TPred σ) : TPred σ := fun e i => ∃ k, p e (i + k)

/-- ◯p — next. -/
def tlaNext (p : TPred σ) : TPred σ := fun e i => p e (i + 1)

/-- p ↝ q — leads-to: whenever p, q eventually follows.
    `□(p → ◇q)` definitionally. -/
def leadsTo (p q : TPred σ) : TPred σ := fun e i => ∀ k, p e (i + k) → ∃ k', q e (i + k + k')

/-- leads-to is transitive. -/
theorem leadsTo_trans (p q r : TPred σ) (e : Exec σ) (i : Nat) :
    leadsTo p q e i → leadsTo q r e i → leadsTo p r e i := by
  intro hpq hqr k hp
  obtain ⟨k', hq⟩ := hpq k hp
  obtain ⟨k'', hr⟩ := hqr (k + k') (by simpa [Nat.add_assoc] using hq)
  exact ⟨k' + k'', by simpa [Nat.add_assoc] using hr⟩

/-- Weak fairness for an action: if continuously enabled, it eventually
    fires. (Full TLA proof rules — lentil's `wf1` — land with the Machines
    scheduler model that needs them.) -/
def weaklyFair (enabled fired : TPred σ) : TPred σ :=
  fun e i => ∀ k, (∀ k', enabled e (i + k + k')) → ∃ k', fired e (i + k + k')

end Machines
