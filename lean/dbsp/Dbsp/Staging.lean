/-
# Dbsp.Staging — schedule equivalence: staged fixpoints are THE fixpoint

The core theorem of SPEC-core §7.4 (lean-v3 step 12): the generated stage
schedule (topological walk over the SCC condensation, per-SCC fixpoint)
and the monolithic cascade compute the same stream — because both are
fixpoints of one strict operator, and strict operators have unique
fixpoints (`fix_unique`).

Contents:

- `schedule_equiv` — the abstract form: any two fixpoints of a strict
  operator agree. Two schedules that each produce a fixpoint of the same
  strict operator compute THE same stream. (This is `fix_unique` restated
  as the schedule-equivalence contract.)
- `jointOp` / `stagedFix` / `staged_eq_joint` — the triangular
  decomposition (Bekič's lemma for strict stream operators): for a
  two-block system where block B does not read block A (the condensation's
  topological order), computing B's fixpoint first and then A's fixpoint
  with B's value plugged in yields the joint fixpoint. The n-block stage
  schedule is the iterated form of this lemma.

Hypothesis ledger (SPEC §7.4's H1–H5): the strictness hypotheses here ARE
H1 — output at pass k+1 depends only on inputs at passes ≤ k. H2–H5
(row-shape, tick-granular transitions, lifecycle, flow-group backups) are
engine-side obligations: they are why the engine's per-pass operator
satisfies these strictness hypotheses, not part of this theorem.
-/

import Dbsp.Certs
import Dbsp.Linear
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Function.Basic

namespace Dbsp

variable {a A B : Type} [AddCommGroup a] [AddCommGroup A] [AddCommGroup B]

/-- **Schedule equivalence, abstract form.** Any fixpoint of a strict
    operator is THE fixpoint; hence any two schedules that each produce a
    fixpoint of the same strict operator agree on the final stream.
    Frame order may differ; the result may not (SPEC §7.4). -/
theorem schedule_equiv (F : Operator a a) (hstrict : Strict F)
    (s1 s2 : Stream a) (h1 : s1 = F s1) (h2 : s2 = F s2) : s1 = s2 :=
  (fix_unique F hstrict s1 h1).trans (fix_unique F hstrict s2 h2).symm

/-- The monolithic joint operator over two blocks: `(α, β) ↦ (F₁ α β,
    F₂ β)`. Block B does not read block A — the condensation's topological
    order (an upstream SCC's value is final before downstream runs). -/
def jointOp (F₁ : Operator2 A B A) (F₂ : Operator B B) : Operator (A × B) (A × B) :=
  fun γ => sprod (F₁ (lifting Prod.fst γ) (lifting Prod.snd γ), F₂ (lifting Prod.snd γ))

/-- The staged computation: the upstream block's loop to fixpoint first,
    then the downstream block's loop with the upstream fixpoint plugged
    in. -/
def stagedFix (F₁ : Operator2 A B A) (F₂ : Operator B B) : Stream A × Stream B :=
  let bstar := fix F₂
  let astar := fix (fun α => F₁ α bstar)
  (astar, bstar)

/-- **The triangular decomposition**: the staged schedule computes the
    joint fixpoint. The strictness hypotheses are the legality conditions
    (H1): B's loop is strict; A's loop is strict with B's fixpoint plugged
    in; the joint operator is strict. -/
theorem staged_eq_joint (F₁ : Operator2 A B A) (F₂ : Operator B B)
    (hF₂ : Strict F₂)
    (hstaged : Strict (fun α => F₁ α (fix F₂)))
    (hjoint : Strict (jointOp F₁ F₂)) :
    sprod (stagedFix F₁ F₂) = fix (jointOp F₁ F₂) := by
  apply fix_unique (jointOp F₁ F₂) hjoint
  have h2 : F₂ (fix F₂) = fix F₂ := (fix_eq F₂ hF₂).symm
  have h1 : F₁ (fix (fun α => F₁ α (fix F₂))) (fix F₂)
          = fix (fun α => F₁ α (fix F₂)) := (fix_eq _ hstaged).symm
  show sprod (fix (fun α => F₁ α (fix F₂)), fix F₂)
     = sprod (F₁ (fix (fun α => F₁ α (fix F₂))) (fix F₂), F₂ (fix F₂))
  congr 1
  exact Prod.ext h1.symm h2.symm

end Dbsp

namespace Dbsp

/-! ## The N-block stage schedule (the engine's condensation walk) -/

section NBlock

variable {A : Type} [AddCommGroup A] {n : Nat}

/-- The N-block joint operator over pi-streams: the queue cascade's
    monolithic operator. `(fun j u => s u j)` is the pi-stream unbundling. -/
def jointOpN (F : Fin n → (Fin n → Stream A) → Stream A) :
    Operator (Fin n → A) (Fin n → A) :=
  fun s t i => F i (fun j u => s u j) t

/-- The N-block staged computation — the stage walker's walk as data:
    block 0's loop to fixpoint first (triangularity makes the
    not-yet-computed tail irrelevant), then the tail staged with block 0's
    fixpoint plugged in. -/
def stagedN : (n : Nat) → (F : Fin n → (Fin n → Stream A) → Stream A) → Fin n → Stream A
  | 0, _ => fun i => i.elim0
  | _ + 1, F =>
      Fin.cons (fix (fun α => F 0 (Fin.cons α 0)))
        (stagedN _ (fun j γ' => F j.succ
          (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ')))

/-- The strictness ledger for the staged walk (SPEC §7.4's H1, per stage):
    every successive tail's joint operator — the loops the walk actually
    runs — is strict. A two-layer def: the flag is the Prop-recursion; the
    soundness theorem is `stagedN_eq_jointN` below. -/
def stagedStrict : (n : Nat) → (F : Fin n → (Fin n → Stream A) → Stream A) → Prop
  | 0, _ => True
  | n + 1, F =>
      Strict (jointOpN (fun j γ' => F j.succ
        (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ'))) ∧
      stagedStrict n (fun j γ' => F j.succ
        (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ'))

/-- **The N-block triangular decomposition** (iterated Bekič for strict
    stream operators): the staged walk computes the joint fixpoint.

    Hypothesis ledger (SPEC §7.4): `htri` is the condensation's topological
    order — stage `i` reads only stages `≤ i`; `hloops` is H1 per stage —
    every block's loop is strict whatever the other blocks hold; `hstaged`
    is H1 for the walk's actual loops (each remaining tail with the
    computed prefix plugged in); `hjoint` is H1 for the queue cascade's
    monolithic operator. H2–H5 are engine-side: they are WHY the engine's
    per-pass operator satisfies these strictness hypotheses. -/
@[cert] theorem stagedN_eq_jointN : ∀ (n : Nat) (F : Fin n → (Fin n → Stream A) → Stream A)
    (htri : ∀ (i : Fin n) (γ₁ γ₂ : Fin n → Stream A),
      (∀ j : Fin n, j ≤ i → γ₁ j = γ₂ j) → F i γ₁ = F i γ₂)
    (hloops : ∀ (i : Fin n) (fixed : Fin n → Stream A),
      Strict (fun α => F i (Function.update fixed i α)))
    (hstaged : stagedStrict n F)
    (hjoint : Strict (jointOpN F)),
    fix (jointOpN F) = fun t i => stagedN n F i t := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ _
    funext t i
    exact i.elim0
  | succ n ih =>
    intro F htri hloops hstaged hjoint
    obtain ⟨hstaged1, hstaged2⟩ := hstaged
    -- the head loop's strictness, from the per-stage hypothesis
    have hG₀eq : (fun α => F 0 (Fin.cons α (0 : Fin n → Stream A))) =
        (fun α => F 0 (Function.update (0 : Fin (n + 1) → Stream A) 0 α)) := by
      funext α
      congr 1
      funext j
      cases j using Fin.cases with
      | zero => rw [Fin.cons_zero, Function.update_self]
      | succ j =>
        rw [Fin.cons_succ,
          Function.update_of_ne (a := j.succ) (a' := 0) (Fin.succ_ne_zero j)]
        rfl
    have hG₀strict : Strict (fun α => F 0 (Fin.cons α (0 : Fin n → Stream A))) := by
      rw [hG₀eq]
      exact hloops 0 0
    -- the head fixpoint absorbs any tail (triangularity at 0)
    have hhead : ∀ rest : Fin n → Stream A,
        F 0 (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) rest) =
          fix (fun α => F 0 (Fin.cons α (0 : Fin n → Stream A))) := by
      intro rest
      have htri0 := htri 0 (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) rest)
        (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) 0) (fun j hj => by
          have h0 : j = 0 := by
            apply Fin.ext
            rw [Fin.le_def] at hj
            rw [Fin.val_zero] at hj ⊢
            omega
          subst h0
          rw [Fin.cons_zero, Fin.cons_zero])
      rw [htri0]
      exact (fix_eq _ hG₀strict).symm
    -- the tail inherits triangularity and per-stage strictness
    have htri' : ∀ (j : Fin n) (γ₁ γ₂ : Fin n → Stream A),
        (∀ j' : Fin n, j' ≤ j → γ₁ j' = γ₂ j') →
        F j.succ (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ₁) =
          F j.succ (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ₂) := by
      intro j γ₁ γ₂ h
      apply htri j.succ
      intro j' hj'
      cases j' using Fin.cases with
      | zero => rw [Fin.cons_zero, Fin.cons_zero]
      | succ j'' =>
        rw [Fin.cons_succ, Fin.cons_succ]
        apply h j''
        rw [Fin.le_def] at hj' ⊢
        rw [Fin.val_succ, Fin.val_succ] at hj'
        omega
    have hloops' : ∀ (j : Fin n) (fixed : Fin n → Stream A),
        Strict (fun α => F j.succ (Fin.cons (fix (fun α => F 0 (Fin.cons α 0)))
          (Function.update fixed j α))) := by
      intro j fixed
      have heq : (fun α => F j.succ (Fin.cons (fix (fun α => F 0 (Fin.cons α 0)))
            (Function.update fixed j α))) =
          (fun α => F j.succ (Function.update
            (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) fixed) j.succ α)) := by
        funext α
        congr 1
        funext j'
        cases j' using Fin.cases with
        | zero =>
          rw [Fin.cons_zero,
            Function.update_of_ne (a := 0) (a' := j.succ) (Fin.succ_ne_zero j).symm,
            Fin.cons_zero]
        | succ j'' =>
          rw [Fin.cons_succ]
          by_cases he : j'' = j
          · subst he
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (a := j''.succ) (a' := j.succ)
                (fun h => he (Fin.succ_inj.mp h)),
              Function.update_of_ne he, Fin.cons_succ]
      rw [heq]
      exact hloops j.succ _
    have ih' := ih _ htri' hloops' hstaged2 hstaged1
    -- the staged bundle is a fixpoint of the joint operator
    have hfix : jointOpN F (fun t i => stagedN (n + 1) F i t) =
        (fun t i => stagedN (n + 1) F i t) := by
      funext t i
      have hunfold : stagedN (n + 1) F =
          Fin.cons (fix (fun α => F 0 (Fin.cons α (0 : Fin n → Stream A))))
            (stagedN n (fun j γ' => F j.succ
              (Fin.cons (fix (fun α => F 0 (Fin.cons α (0 : Fin n → Stream A)))) γ'))) := rfl
      rw [hunfold]
      cases i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        show (F 0 (Fin.cons (fix (fun α => F 0 (Fin.cons α 0)))
            (stagedN n (fun j γ' => F j.succ
              (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ')))) t) = _
        rw [hhead]
      | succ j =>
        rw [Fin.cons_succ]
        show (F j.succ (Fin.cons (fix (fun α => F 0 (Fin.cons α 0)))
            (stagedN n (fun j' γ' => F j'.succ
              (Fin.cons (fix (fun α => F 0 (Fin.cons α 0))) γ')))) t) = _
        have hfe := fix_eq _ hstaged1
        have hpoint := congrFun (congrFun hfe t) j
        rw [ih'] at hpoint
        exact hpoint.symm
    exact (fix_unique _ hjoint _ hfix.symm).symm

end NBlock

end Dbsp
