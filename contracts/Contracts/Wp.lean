/-
# Contracts.Wp — the wp engine over the honest minimal imperative fragment

notes/v3/08-capabilities.md §36: requires/ensures with wp-composition —
"the contract lanes' composition engine: `wp (p >>= k) Q = wp p (fun x =>
wp (k x) Q)`" — scoped to the contracted lanes; total pure functions keep
direct proofs. The review's §5 shapes the content: for each primitive —
the execution semantics + the precondition transformer + the soundness
theorem; the compound obligations derive STRUCTURALLY; the developer
writes the program + the postcondition; the toolkit computes the
obligations (`Contract.vc`, Contracts/Contract.lean), discharges the
routine fragments, and shows the remaining domain-specific goals.

The fragment: assign / ret / bind / cond over the effects lane's State
model (`Effects.Footprint`'s `Key → Nat` — ONE state model, two lanes;
no parallel table). The value-returning discipline (this wave): `ret`
is the expression/return shape, `bind` composes WITH the value, and the
postcondition ranges over the RESULT + the state — §36's full shape
with the value, `wp_bind`. The state-only reading is the derived face
`wpS` (the result discarded); `skip` and `seq` are its derived
specializations (`ret 0` / the value-ignoring bind), not extra
constructors.

The loops (this wave): the honest loop discipline — the wp over a loop
is NOT a structural transformer arm; it is the weakest-HONEST
precondition: the stated INVARIANT (required data, never inferred) +
the VARIANT (the termination certificate), four verification
conditions (`LoopVCs`: init / preserve / descend / exit), and the
fuel-bounded execution (`While.run`) the variant bounds. `while_sat`
is the soundness: the four VCs give the postcondition at fuel
`var + 1`. The invariant is REQUIRED — a loop with a wrong invariant
produces a VC that refuses to discharge (the teeth in ContractsTests).

Deliberately OUT (named exclusions, 02's trap discipline): nested
loops (the body is loop-free `Prog`; a while-in-while lands with its
first consumer), nondeterminism (a relational wp, not a transformer),
invariant INFERENCE (the invariant is data on `While`, by design — the
wp stays honest, the toolkit computes nothing it cannot).

The five questions (notes/v3/01-core.md):
- root: Universe (the fragment's programs + the while carrier + the wp
  transformer as closed data over the effects lane's State model).
- carrier grade: none — `wp` is a plain transformer; the discipline is
  the SOUNDNESS THEOREM (`wp_sound`, `while_sat`), not a type
  distinction.
- spine reading: none — the lanes' contracts ride it; nothing is
  accumulated here.
- ladder rung: rung 6 — small generic hand theorems (soundness, the
  bind/seq/cond/mono/consequence rules, the exactness iff, the
  while's fuel induction).
- gate row: none yet — Contracts is outside Gates.Packages' gated set;
  ContractsTests.Axioms pins the axiom cones.

Core-only: imports Effects.Footprint + Kit.Obligation only (the cone
rule; no mathlib, no Batteries).
-/

import Effects.Footprint
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Contracts

/-- The state: the EFFECTS LANE's model (`Effects.Footprint`), aliased —
one state model, two lanes. -/
abbrev State := Effects.State

/-- A state key: the effects lane's. -/
abbrev Key := Effects.Key

/-! ## The fragment -/

/-- The in-place update: the fragment's one state primitive (the same
shape the effects lane's `incr1_wr` machinery uses — the honest minimal,
defined once here). -/
def upd (k : Key) (v : State → Nat) (s : State) : State :=
  fun j => if j = k then v s else s j

/-- The program fragment: assign / ret / bind / cond. `ret` returns a
value read from the state; `bind` composes with the value (the
continuation reads the result — §36's `p >>= k`). -/
inductive Prog : Type where
  | assign (k : Key) (e : State → Nat) : Prog
  | ret (v : State → Nat) : Prog
  | bind (p : Prog) (k : Nat → Prog) : Prog
  | cond (b : State → Bool) (p q : Prog) : Prog

/-- The no-op: the value-ignoring return — derived, not a constructor
(the leftover rule at the term level: one carrier, no parallel
shape). -/
def Prog.skip : Prog := .ret (fun _ => 0)

/-- The state-only composition: the bind whose continuation discards
the value — the fragment's original `seq`, derived. -/
def Prog.seq (p q : Prog) : Prog := .bind p (fun _ => q)

/-- The execution semantics (the review's §5: each primitive first).
A program returns its RESULT and the exit state — the pair is the
value-returning discipline's carrier. -/
def Prog.exec : Prog → State → Nat × State
  | .assign k e, s => (0, upd k e s)
  | .ret v, s => (v s, s)
  | .bind p k, s => match p.exec s with | (x, s') => (k x).exec s'
  | .cond b p q, s => match b s with | true => p.exec s | false => q.exec s

/-- The bind's exec reduces through the pair: the continuation runs on
the FIRST projection's value at the SECOND projection's state. (The
one-step shape the exec-side computations use.) -/
@[nolint linter.guestlang.zeroCitation "public API: consumed by the exec-side computations in ContractsTests; the bind exec's one-step reduction shape"]
theorem Prog.exec_bind (p : Prog) (k : Nat → Prog) (s : State) :
    (Prog.bind p k).exec s = (k (p.exec s).1).exec (p.exec s).2 := rfl

/-! ## The precondition transformer -/

/-- `wp : Program → (Nat → State → Prop) → State → Prop` — the weakest
precondition transformer over the fragment, the postcondition over the
RESULT + the exit state (§36's full shape). Each arm is the primitive's
rule, and the compound programs derive STRUCTURALLY (the bind threads
the value through — the doctrine's composition shape). The write
returns no value: its result is `0` by convention, stated once here. -/
def wp : Prog → (Nat → State → Prop) → State → Prop
  | .assign k e, Q => fun s => Q 0 (upd k e s)
  | .ret v, Q => fun s => Q (v s) s
  | .bind p k, Q => fun s => wp p (fun x s' => wp (k x) Q s') s
  | .cond b p q, Q => fun s => (b s = true → wp p Q s) ∧ (b s = false → wp q Q s)

/-- The state-only reading: the postcondition over the exit state alone
(the result discarded) — the fragment's original face, derived from the
result-aware `wp`. -/
def wpS (p : Prog) (Q : State → Prop) (s : State) : Prop :=
  wp p (fun _ s' => Q s') s

/-! ## The soundness theorem -/

/-- THE soundness (08 §36): the wp-computed precondition SUFFICES — an
execution from a wp-satisfying state lands in the postcondition, over
the result + the exit state. One induction over the fragment; each
primitive's arm is its rule. -/
theorem wp_sound : ∀ (p : Prog) (Q : Nat → State → Prop) (s : State),
    wp p Q s → Q (p.exec s).1 (p.exec s).2 := by
  intro p
  induction p with
  | assign k e => intro Q s h; exact h
  | ret v => intro Q s h; exact h
  | bind p k ihp ihk =>
      intro Q s h
      exact ihk (p.exec s).1 Q (p.exec s).2 (ihp (fun x s' => wp (k x) Q s') s h)
  | cond b p q ihp ihq =>
      intro Q s h
      simp only [wp] at h
      simp only [Prog.exec]
      cases hb : b s with
      | true => exact ihp Q s (h.1 hb)
      | false => exact ihq Q s (h.2 hb)

/-! ## The rules -/

/-- THE composition rule (08 §36's exact shape, WITH the value):
`wp (p >>= k) Q = wp p (fun x => wp (k x) Q)` — the postcondition over
the result + the state, the continuation reading the result. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (wp_bind_pin); THE composition rule with the value — 08 §36's exact shape"]
theorem wp_bind (p : Prog) (k : Nat → Prog) (Q : Nat → State → Prop) :
    wp (Prog.bind p k) Q = wp p (fun x => wp (k x) Q) := rfl

/-- THE composition rule at the state-only specialization: `wp (p ;; q)
Q = wp p (wp q Q)` — §36's shape at the value-ignoring bind. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (wp_seq_pin); THE state-only composition rule — 08 §36 at the value-ignoring bind"]
theorem wp_seq (p q : Prog) (Q : State → Prop) :
    wpS (p.seq q) Q = wpS p (wpS q Q) := rfl

/-- THE conditional rule. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (wp_cond_pin); the conditional rule"]
theorem wp_cond (b : State → Bool) (p q : Prog) (Q : Nat → State → Prop) :
    wp (Prog.cond b p q) Q =
      fun s => (b s = true → wp p Q s) ∧ (b s = false → wp q Q s) :=
  rfl

/-- The transformer is monotone in the postcondition — the consequence
rule's engine. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `wp_cons` in this module (the consequence rule's engine)"]
theorem wp_mono : ∀ (p : Prog) (Q Q' : Nat → State → Prop),
    (∀ x s, Q x s → Q' x s) → ∀ s, wp p Q s → wp p Q' s := by
  intro p
  induction p with
  | assign k e => intro Q Q' hQ s hs; exact hQ _ _ hs
  | ret v => intro Q Q' hQ s hs; exact hQ _ _ hs
  | bind p k ihp ihk =>
      intro Q Q' hQ s hs
      exact ihp (fun x s' => wp (k x) Q s') (fun x s' => wp (k x) Q' s')
        (fun x s' h' => ihk x Q Q' hQ s' h') s hs
  | cond b p q ihp ihq =>
      intro Q Q' hQ s hs
      exact ⟨fun hb => ihp Q Q' hQ s (hs.1 hb),
             fun hb => ihq Q Q' hQ s (hs.2 hb)⟩

/-- THE consequence rule: strengthening the precondition / weakening the
postcondition preserves the wp-verified triple (the honest discipline —
the wp computes for ONE postcondition; consumers move between them
through mono + the entry-condition implication). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (cons_pin); THE consequence rule — strengthen the precondition, weaken the postcondition"]
theorem wp_cons (p : Prog) (P P' : Nat → State → Prop) (Q Q' : Nat → State → Prop)
    (hP : ∀ x s, P x s → P' x s) (hQ : ∀ x s, Q x s → Q' x s)
    (hvc : ∀ x s, P' x s → wp p Q s) (s : State) (h : P 0 s) : wp p Q' s :=
  wp_mono p Q Q' hQ s (hvc 0 s (hP 0 s h))

/-- Exactness: over the deterministic fragment the wp is not merely
sufficient but EXACT — `wp p Q s ↔ Q (p.exec s)`. The sampled sweeps
ride this iff (the wp/exec agreement), and its sabotage controls have
teeth: a too-strong wp claim is refuted at a drawn state. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (soundness_pin/exact_pin; the sweep's exec side rides it); exactness over the deterministic fragment — the wp is the strongest precondition"]
theorem wp_iff : ∀ (p : Prog) (Q : Nat → State → Prop) (s : State),
    wp p Q s ↔ Q (p.exec s).1 (p.exec s).2 := by
  intro p
  induction p with
  | assign k e => intro Q s; exact Iff.rfl
  | ret v => intro Q s; exact Iff.rfl
  | bind p k ihp ihk =>
      intro Q s
      constructor
      · intro h
        exact (ihk (p.exec s).1 Q (p.exec s).2).mp
          ((ihp (fun x s' => wp (k x) Q s') s).mp h)
      · intro h
        exact (ihp (fun x s' => wp (k x) Q s') s).mpr
          ((ihk (p.exec s).1 Q (p.exec s).2).mpr h)
  | cond b p q ihp ihq =>
      intro Q s
      constructor
      · rintro ⟨h1, h2⟩
        simp only [Prog.exec]
        cases hb : b s with
        | true => exact (ihp Q s).mp (h1 hb)
        | false => exact (ihq Q s).mp (h2 hb)
      · intro h
        simp only [Prog.exec] at h
        simp only [wp]
        cases hb : b s with
        | true =>
            rw [hb] at h
            exact ⟨fun _ => (ihp Q s).mpr h, by simp⟩
        | false =>
            rw [hb] at h
            exact ⟨by simp, fun _ => (ihq Q s).mpr h⟩

/-! ## The loops — the honest while discipline

The wp over a loop is NOT a transformer arm: the loop is its own
carrier (`While`), and its precondition is the weakest-HONEST one —
the stated INVARIANT (required data on the carrier, never inferred) +
the VARIANT (the termination certificate). The discipline's VCs are
`LoopVCs`: the invariant holds initially / the body preserves it / the
variant strictly descends / the exit establishes the postcondition.
The execution is fuel-bounded (`While.run`) and the variant bounds the
fuel — `while_sound` / `while_sat` are the soundness. -/

/-- The while carrier: the guard + the loop-free body + the REQUIRED
invariant + the variant. The invariant and variant are DATA — the
honesty of the discipline: the toolkit never invents them. -/
structure While where
  guard : State → Bool
  body : Prog
  inv : State → Prop
  var : State → Nat

/-- The fuel-bounded execution: fuel 0 stops (the state unchanged); a
stored step runs the body when the guard holds. The loop discards the
body's RESULT (the while's value discipline is the state's). -/
def While.run (w : While) : Nat → State → State
  | 0, s => s
  | n+1, s => if w.guard s then w.run n (w.body.exec s).2 else s

/-- The stored-step reduction (the guard holds). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `while_sound_fuel` in this module"]
theorem While.run_true (w : While) (n : Nat) (s : State) (h : w.guard s = true) :
    w.run (n+1) s = w.run n ((w.body.exec s).2) := by
  simp only [While.run, h, if_true]

/-- The exit-step reduction (the guard fails). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `while_sound_fuel` in this module"]
theorem While.run_false (w : While) (n : Nat) (s : State) (h : w.guard s = false) :
    w.run (n+1) s = s := by
  simp [While.run, h]

/-- The loop's four verification conditions — the discipline's whole
content, as one structure. Each field names its slot: init / preserve /
descend / exit. A wrong invariant makes `vBody` false, and the
structure cannot be built (the teeth in ContractsTests). -/
structure LoopVCs (P Q : State → Prop) (w : While) where
  /-- The invariant holds initially. -/
  vInit : ∀ s, P s → w.inv s
  /-- The body preserves the invariant (the wp discipline's own shape:
  the wp of the body suffices for the invariant). -/
  vBody : ∀ s, w.guard s = true → w.inv s → wp w.body (fun _ s' => w.inv s') s
  /-- The variant strictly descends, and stays positive while the loop
  continues — the termination certificate. -/
  vVar : ∀ s, w.guard s = true → w.inv s →
      0 < w.var s ∧ w.var ((w.body.exec s).2) < w.var s
  /-- The exit establishes the postcondition. -/
  vExit : ∀ s, w.inv s → w.guard s = false → Q s

/-- THE loop soundness, at the fuel-general strength: from an invariant
state, fuel `n ≥ var s` lands in the postcondition. One induction on
the fuel; the descent case consumes one step of the variant. -/
theorem while_sound_fuel (P Q : State → Prop) (w : While) (v : LoopVCs P Q w) :
    ∀ n s, w.inv s → w.var s ≤ n → Q (w.run n s) := by
  intro n
  induction n with
  | zero =>
      intro s hinv hle
      have h0 : w.var s = 0 := Nat.le_zero.mp hle
      cases hg : w.guard s with
      | false => exact v.vExit s hinv hg
      | true =>
          have hh := (v.vVar s hg hinv).1
          exact absurd h0 (by omega)
  | succ n ih =>
      intro s hinv hle
      cases hg : w.guard s with
      | false =>
          rw [While.run_false w n s hg]
          exact v.vExit s hinv hg
      | true =>
          have hv := v.vVar s hg hinv
          have hbod : w.inv ((w.body.exec s).2) :=
            wp_sound w.body (fun _ s' => w.inv s') s (v.vBody s hg hinv)
          rw [While.run_true w n s hg]
          exact ih ((w.body.exec s).2) hbod (by have := hv.2; omega)

/-- THE loop's satisfaction: the four VCs give the postcondition at
fuel `var + 1` — the weakest-HONEST precondition is exactly the stated
invariant, and the variant is the ENTIRE termination argument. The
invariant is required data (`LoopVCs` cannot be built without it); the
toolkit computes nothing it cannot — the honesty of the discipline. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (sumLoopSat + the teeth); THE loop's soundness — the invariant is REQUIRED, never inferred"]
theorem while_sat (P Q : State → Prop) (w : While) (v : LoopVCs P Q w) (s : State)
    (h : P s) : Q (w.run (w.var s + 1) s) :=
  while_sound_fuel P Q w v (w.var s + 1) s (v.vInit s h) (Nat.le_succ _)

end Contracts
