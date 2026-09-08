/-
# Dbsp.Circuit — the circuit DSL and the proven optimizer

Ports tchajed/database-stream-processing-theory `src/circuits.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3). This is the
flatlandc-certification TEMPLATE: a compiler knows a fixed set of
operator templates (`Func`), wires them into circuits, and
`incrementalize_ok` certifies that the incrementalization of a circuit
is the circuit of incrementalized operators; `recursive_opt_ok` certifies
bottom-up local rewrite passes.

The parameterization honors the Lean 3 source: `Func` is the closed set
of external function templates, `denoteF` fixes their meaning. Lean 4's
`^Δ`-notation is dropped throughout: write `incremental Q`.

Adaptations vs the source: the `intro`/`elim` (stream-elim) constructors
and the alternate `incrementalize` definition are commented out in the
source — skipped. `is_strict` restated with the Lean 4 idiom
`{ b : Bool // b = true → Strict … }`; `denote` by plain structural
match (no unfreezing tricks needed). Inside `namespace Dbsp` the Ckt
constructor names shadow the stream-operator names (`delay`,
`incremental`, `lifting`, `fix`), so the operators are written fully
qualified. `denoteF` is an explicit parameter of `equiv` (Lean 4 drops
section variables used only in definition bodies).
-/

import Dbsp.Certs
import Dbsp.Incremental
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Bool.Basic

namespace Dbsp

variable {Func : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type}

/-- A circuit is a structural description of a stream operator over a
    parameterized set `Func` of external (compiled) function templates. -/
inductive Ckt (Func : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type) :
    (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type 1 where
  | delay {a : Type} [AddCommGroup a] : Ckt Func a a
  | derivative {a : Type} [AddCommGroup a] : Ckt Func a a
  | integral {a : Type} [AddCommGroup a] : Ckt Func a a
  | incremental {a b : Type} [AddCommGroup a] [AddCommGroup b] : Ckt Func a b → Ckt Func a b
  | lifting {a b : Type} [AddCommGroup a] [AddCommGroup b] : Func a b → Ckt Func a b
  | seq {a b c : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] :
      Ckt Func a b → Ckt Func b c → Ckt Func a c
  | par {a1 b1 a2 b2 : Type} [AddCommGroup a1] [AddCommGroup a2] [AddCommGroup b1] [AddCommGroup b2] :
      Ckt Func a1 b1 → Ckt Func a2 b2 → Ckt Func (a1 × a2) (b1 × b2)
  | feedback {a b : Type} [AddCommGroup a] [AddCommGroup b] :
      Ckt Func (a × b) b → Ckt Func a b

/-- The denotation of a circuit: how it reads and writes streams. -/
def Ckt.denote (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b) :
    {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Stream a → Stream b
  | a, b, _, _, c =>
      match c with
      | Ckt.delay => Dbsp.delay
      | Ckt.derivative => D
      | Ckt.integral => I
      | Ckt.incremental g => Dbsp.incremental (Ckt.denote denoteF g)
      | Ckt.lifting cf => Dbsp.lifting (denoteF _ _ cf)
      | Ckt.seq f1 f2 => fun s => Ckt.denote denoteF f2 (Ckt.denote denoteF f1 s)
      | Ckt.par f1 f2 => uncurryOp (fun x1 x2 => sprod (Ckt.denote denoteF f1 x1, Ckt.denote denoteF f2 x2))
      | Ckt.feedback F => fun s => Dbsp.fix (fun α => Ckt.denote denoteF F (sprod (s, Dbsp.delay α)))

/-- The feedback body of a circuit: on input `s` and loop value `α`,
    `⟦F⟧ (s ⊗ α)`. Named so the causality/incrementalization arguments
    stay first-order (no higher-order unification against anonymous
    lambdas). -/
def Ckt.feedbackBody (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    {a b : Type} [AddCommGroup a] [AddCommGroup b] (F : Ckt Func (a × b) b) :
    Operator2 a b b :=
  fun s α => Ckt.denote denoteF F (sprod (s, α))

variable {a b c d : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c] [AddCommGroup d]
variable {denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b}

/-- Circuit equivalence: equal denotations. -/
def equiv (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (f1 f2 : Ckt Func a b) : Prop := Ckt.denote denoteF f1 = Ckt.denote denoteF f2

@[refl]
theorem equiv_refl (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (f : Ckt Func a b) : equiv denoteF f f := by
  unfold equiv
  rfl

@[symm]
theorem equiv_symm (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (f1 f2 : Ckt Func a b) : equiv denoteF f1 f2 → equiv denoteF f2 f1 := by
  intro h
  exact h.symm

@[trans]
theorem equiv_trans (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (f1 f2 f3 : Ckt Func a b) : equiv denoteF f1 f2 → equiv denoteF f2 f3 → equiv denoteF f1 f3 := by
  intro h12 h23
  exact h12.trans h23

@[simp]
theorem denote_seq (f1 : Ckt Func a b) (f2 : Ckt Func b c) :
    Ckt.denote denoteF (Ckt.seq f1 f2) =
      fun x => Ckt.denote denoteF f2 (Ckt.denote denoteF f1 x) := rfl

@[simp]
theorem denote_par (f1 : Ckt Func a b) (f2 : Ckt Func c d) :
    Ckt.denote denoteF (Ckt.par f1 f2) =
      uncurryOp (fun x1 x2 => sprod (Ckt.denote denoteF f1 x1, Ckt.denote denoteF f2 x2)) := rfl

@[simp]
theorem denote_delay : Ckt.denote denoteF (Ckt.delay : Ckt Func a a) = Dbsp.delay := rfl

@[simp]
theorem denote_derivative : Ckt.denote denoteF (Ckt.derivative : Ckt Func a a) = D := rfl

@[simp]
theorem denote_incremental (g : Ckt Func a b) :
    Ckt.denote denoteF (Ckt.incremental g) = Dbsp.incremental (Ckt.denote denoteF g) := rfl

@[simp]
theorem denote_integral : Ckt.denote denoteF (Ckt.integral : Ckt Func a a) = I := rfl

@[simp]
theorem denote_lifting (cf : Func a b) :
    Ckt.denote denoteF (Ckt.lifting cf) = Dbsp.lifting (denoteF _ _ cf) := rfl

@[simp]
theorem denote_feedback (F : Ckt Func (a × b) b) :
    Ckt.denote denoteF (Ckt.feedback F) =
      fun s => Dbsp.fix (fun α => Ckt.denote denoteF F (sprod (s, Dbsp.delay α))) := rfl

/-- Sequential composition is associative up to equivalence. -/
theorem seq_assoc (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (f1 : Ckt Func a b) (f2 : Ckt Func b c) (f3 : Ckt Func c d) :
    equiv denoteF (Ckt.seq (Ckt.seq f1 f2) f3) (Ckt.seq f1 (Ckt.seq f2 f3)) := by
  simp [equiv]

/-- Every circuit denotes a causal operator. -/
theorem ckt_causal (f : Ckt Func a b) : Causal (Ckt.denote denoteF f) := by
  induction f with
  | delay =>
      exact strict_causal_to_causal Dbsp.delay delay_strict
  | derivative =>
      exact derivative_causal
  | integral =>
      exact integral_causal
  | incremental g ih =>
      exact causal_incremental (Ckt.denote denoteF g) ih
  | lifting cf =>
      exact lifting_causal (denoteF _ _ cf)
  | seq f1 f2 ih1 ih2 =>
      exact causal_comp_causal (Ckt.denote denoteF f1) ih1 (Ckt.denote denoteF f2) ih2
  | par f1 f2 ih1 ih2 =>
      rw [denote_par, causal2]
      intro s1 s1' s2 s2' n heq1 heq2
      show (Ckt.denote denoteF f1 s1 n, Ckt.denote denoteF f2 s2 n) =
           (Ckt.denote denoteF f1 s1' n, Ckt.denote denoteF f2 s2' n)
      exact Prod.ext (ih1 s1 s1' n heq1) (ih2 s2 s2' n heq2)
  | feedback F ih =>
      rw [denote_feedback]
      refine feedback_ckt_causal Dbsp.delay delay_strict (Ckt.feedbackBody denoteF F) ?_
      rw [causal2]
      intro s1 s1' s2 s2' n heq1 heq2
      exact ih _ _ _ (fun i hi => by
        show (s1 i, s2 i) = (s1' i, s2' i)
        rw [heq1 i hi, heq2 i hi])

/-- The decidable strictness analysis: the flag is true exactly when the
    circuit's denotation is (known to be) strict. False flags carry a
    proof obligation `false = true → _` — vacuously true. -/
def isStrictFlag : {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Bool
  | _, _, _, _, Ckt.delay => true
  | _, _, _, _, Ckt.derivative => false
  | _, _, _, _, Ckt.integral => false
  | _, _, _, _, Ckt.incremental g => isStrictFlag g
  | _, _, _, _, Ckt.lifting _ => false
  | _, _, _, _, Ckt.seq f1 f2 => isStrictFlag f1 || isStrictFlag f2
  | _, _, _, _, Ckt.par f1 f2 => isStrictFlag f1 && isStrictFlag f2
  | _, _, _, _, Ckt.feedback _ => false

/-- Soundness of the strictness flag (induction, reusing the composition
    facts: strict∘causal and causal∘strict are strict). -/
theorem isStrict_sound (f : Ckt Func a b) :
    isStrictFlag f = true → Strict (Ckt.denote denoteF f) := by
  induction f with
  | delay => intro _; exact delay_strict
  | derivative => intro h; simp [isStrictFlag] at h
  | integral => intro h; simp [isStrictFlag] at h
  | lifting _ => intro h; simp [isStrictFlag] at h
  | feedback _ _ => intro h; simp [isStrictFlag] at h
  | incremental g ih =>
      intro h
      show Strict (Dbsp.incremental (Ckt.denote denoteF g))
      unfold Dbsp.incremental
      apply causal_strict_strict
      · apply strict_causal_strict
        · exact integral_causal
        · exact ih h
      · exact derivative_causal
  | seq f1 f2 ih1 ih2 =>
      intro h
      simp only [isStrictFlag, Bool.or_eq_true] at h
      cases h with
      | inl hb1 =>
          exact causal_strict_strict (Ckt.denote denoteF f1) (ih1 hb1)
            (Ckt.denote denoteF f2) (ckt_causal f2)
      | inr hb2 =>
          exact strict_causal_strict (Ckt.denote denoteF f1) (ckt_causal f1)
            (Ckt.denote denoteF f2) (ih2 hb2)
  | par f1 f2 ih1 ih2 =>
      intro h
      simp only [isStrictFlag, Bool.and_eq_true] at h
      obtain ⟨hb1, hb2⟩ := h
      intro s1 s2 n heq
      show (Ckt.denote denoteF f1 (lifting Prod.fst s1) n,
            Ckt.denote denoteF f2 (lifting Prod.snd s1) n) =
           (Ckt.denote denoteF f1 (lifting Prod.fst s2) n,
            Ckt.denote denoteF f2 (lifting Prod.snd s2) n)
      exact Prod.ext
        (ih1 hb1 _ _ n (fun i hi => congrArg Prod.fst (heq i hi)))
        (ih2 hb2 _ _ n (fun i hi => congrArg Prod.snd (heq i hi)))

def isStrict (f : Ckt Func a b) : { b : Bool // b = true → Strict (Ckt.denote denoteF f) } :=
  ⟨isStrictFlag f, fun h => isStrict_sound f h⟩

/-! ## The proven rewrite pass: `recursiveOpt` -/

/-- Bottom-up optimization: apply `opt` at each node; where `opt` returns
    `none`, keep the recursively-optimized children. -/
def recursiveOpt (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b)) :
    {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Ckt Func a b
  | a, b, _, _, c =>
      match c with
      | Ckt.delay => (opt _ _ Ckt.delay).getD Ckt.delay
      | Ckt.derivative => (opt _ _ Ckt.derivative).getD Ckt.derivative
      | Ckt.integral => (opt _ _ Ckt.integral).getD Ckt.integral
      | Ckt.incremental g => (opt _ _ (Ckt.incremental g)).getD (Ckt.incremental (recursiveOpt opt g))
      | Ckt.lifting cf => (opt _ _ (Ckt.lifting cf)).getD (Ckt.lifting cf)
      | Ckt.seq f1 f2 =>
          (opt _ _ (Ckt.seq f1 f2)).getD (Ckt.seq (recursiveOpt opt f1) (recursiveOpt opt f2))
      | Ckt.par f1 f2 =>
          (opt _ _ (Ckt.par f1 f2)).getD (Ckt.par (recursiveOpt opt f1) (recursiveOpt opt f2))
      | Ckt.feedback F => (opt _ _ (Ckt.feedback F)).getD (Ckt.feedback (recursiveOpt opt F))

@[simp]
theorem recursive_opt_seq (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (f1 : Ckt Func a b) (f2 : Ckt Func b c) :
    recursiveOpt opt (Ckt.seq f1 f2) =
      (opt _ _ (Ckt.seq f1 f2)).getD (Ckt.seq (recursiveOpt opt f1) (recursiveOpt opt f2)) := rfl

@[simp]
theorem recursive_opt_par (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (f1 : Ckt Func a b) (f2 : Ckt Func c d) :
    recursiveOpt opt (Ckt.par f1 f2) =
      (opt _ _ (Ckt.par f1 f2)).getD (Ckt.par (recursiveOpt opt f1) (recursiveOpt opt f2)) := rfl

@[simp]
theorem recursive_opt_feedback (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (F : Ckt Func (a × b) b) :
    recursiveOpt opt (Ckt.feedback F) =
      (opt _ _ (Ckt.feedback F)).getD (Ckt.feedback (recursiveOpt opt F)) := rfl

@[simp]
theorem recursive_opt_incremental (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (g : Ckt Func a b) :
    recursiveOpt opt (Ckt.incremental g) =
      (opt _ _ (Ckt.incremental g)).getD (Ckt.incremental (recursiveOpt opt g)) := rfl

/-- If the optimizer only returns equivalent circuits when it returns, then
    `opt` at a node preserves equivalence whether it fires or not. -/
theorem opt_or_else_ok (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (h_opt : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f1 f2 : Ckt Func a b),
      opt _ _ f1 = some f2 → equiv denoteF f1 f2)
    (f1 f2 : Ckt Func a b) :
    equiv denoteF f2 f1 → equiv denoteF ((opt _ _ f1).getD f2) f1 := by
  intro heq
  cases hopt : opt _ _ f1 with
  | none =>
      simp only [Option.getD_none]
      exact heq
  | some f2x =>
      simp only [Option.getD_some]
      exact (h_opt f1 f2x hopt).symm

/-- The rewrite pass is sound: `recursiveOpt opt` is equivalent to the
    identity on every circuit (induction on the circuit shape). -/
theorem recursive_opt_ok (denoteF : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → a → b)
    (opt : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Option (Ckt Func a b))
    (h_opt : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f1 f2 : Ckt Func a b),
      opt _ _ f1 = some f2 → equiv denoteF f1 f2) :
    ∀ (f : Ckt Func a b), equiv denoteF (recursiveOpt opt f) f := by
  intro f
  induction f with
  | delay =>
      exact opt_or_else_ok denoteF opt h_opt Ckt.delay Ckt.delay (equiv_refl denoteF Ckt.delay)
  | derivative =>
      exact opt_or_else_ok denoteF opt h_opt Ckt.derivative Ckt.derivative (equiv_refl denoteF Ckt.derivative)
  | integral =>
      exact opt_or_else_ok denoteF opt h_opt Ckt.integral Ckt.integral (equiv_refl denoteF Ckt.integral)
  | incremental g ih =>
      apply opt_or_else_ok denoteF opt h_opt (Ckt.incremental g)
      unfold equiv at ih ⊢
      rw [denote_incremental, denote_incremental, ih]
  | lifting cf =>
      exact opt_or_else_ok denoteF opt h_opt (Ckt.lifting cf) (Ckt.lifting cf) (equiv_refl denoteF (Ckt.lifting cf))
  | seq f1 f2 ih1 ih2 =>
      apply opt_or_else_ok denoteF opt h_opt (Ckt.seq f1 f2)
      unfold equiv at ih1 ih2 ⊢
      rw [denote_seq, denote_seq, ih1, ih2]
  | par f1 f2 ih1 ih2 =>
      apply opt_or_else_ok denoteF opt h_opt (Ckt.par f1 f2)
      unfold equiv at ih1 ih2 ⊢
      rw [denote_par, denote_par, ih1, ih2]
  | feedback F ih =>
      apply opt_or_else_ok denoteF opt h_opt (Ckt.feedback F)
      unfold equiv at ih ⊢
      rw [denote_feedback, denote_feedback]
      funext s
      congr 1
      funext α
      rw [ih]

/-! ## The compiler: `incrementalize` -/

/-- Incrementalize a circuit: linear `lifting` leafs are their own
    incremental form; everything else wraps in `incremental`. The
    `isLinear`/`isLinearOk` pair is the compiler's linearity oracle. -/
def incrementalize (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool) :
    {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → Ckt Func a b → Ckt Func a b
  | a, b, _, _, c =>
      match c with
      | Ckt.delay => Ckt.delay
      | Ckt.derivative => Ckt.derivative
      | Ckt.integral => Ckt.integral
      | Ckt.incremental g => Ckt.incremental (incrementalize isLinear g)
      | Ckt.lifting cf => if isLinear _ _ cf = true then Ckt.lifting cf else Ckt.incremental (Ckt.lifting cf)
      | Ckt.seq f1 f2 => Ckt.seq (incrementalize isLinear f1) (incrementalize isLinear f2)
      | Ckt.par f1 f2 => Ckt.par (incrementalize isLinear f1) (incrementalize isLinear f2)
      | Ckt.feedback F => Ckt.feedback (incrementalize isLinear F)

@[simp]
theorem incrementalize_incremental (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (g : Ckt Func a b) :
    incrementalize isLinear (Ckt.incremental g) = Ckt.incremental (incrementalize isLinear g) := rfl

@[simp]
theorem incrementalize_lifting (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (cf : Func a b) :
    incrementalize isLinear (Ckt.lifting cf) =
      if isLinear _ _ cf = true then Ckt.lifting cf else Ckt.incremental (Ckt.lifting cf) := rfl

@[simp]
theorem incrementalize_seq (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (f1 : Ckt Func a b) (f2 : Ckt Func b c) :
    incrementalize isLinear (Ckt.seq f1 f2) =
      Ckt.seq (incrementalize isLinear f1) (incrementalize isLinear f2) := rfl

@[simp]
theorem incrementalize_par (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (f1 : Ckt Func a b) (f2 : Ckt Func c d) :
    incrementalize isLinear (Ckt.par f1 f2) =
      Ckt.par (incrementalize isLinear f1) (incrementalize isLinear f2) := rfl

@[simp]
theorem incrementalize_feedback (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (F : Ckt Func (a × b) b) :
    incrementalize isLinear (Ckt.feedback F) = Ckt.feedback (incrementalize isLinear F) := rfl

/-- **The compiler certificate**: incrementalizing a circuit (by the
    linearity oracle) then denoting it is EXACTLY the incremental form of
    the original denotation: `⟦incrementalize isLinear c⟧ = ⟦c⟧^Δ`. A
    template-certified compiler, per circuit. -/
@[cert] theorem incrementalize_ok (isLinear : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Func a b → Bool)
    (isLinearOk : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : Func a b),
      isLinear _ _ f = true → ∀ x y : a, denoteF _ _ f (x + y) = denoteF _ _ f x + denoteF _ _ f y)
    (f : Ckt Func a b) :
    Ckt.denote denoteF (incrementalize isLinear f) = Dbsp.incremental (Ckt.denote denoteF f) := by
  induction f with
  | delay =>
      simp [incrementalize]
  | derivative =>
      simp [incrementalize]
  | integral =>
      simp [incrementalize]
  | incremental g ih =>
      simp [incrementalize, ih]
  | lifting cf =>
      by_cases hif : isLinear _ _ cf = true
      · have hlin := isLinearOk cf hif
        rw [incrementalize_lifting, if_pos hif, denote_lifting]
        exact (lti_incremental (Dbsp.lifting (denoteF _ _ cf)) (lifting_lti (denoteF _ _ cf) hlin)).symm
      · rw [incrementalize_lifting, if_neg hif, denote_incremental]
  | seq f1 f2 ih1 ih2 =>
      simp only [incrementalize_seq, denote_seq]
      rw [ih1, ih2]
      funext s
      rw [incremental_comp (Ckt.denote denoteF f2) (Ckt.denote denoteF f1) s]
  | par f1 f2 ih1 ih2 =>
      simp only [incrementalize_par, denote_par]
      rw [ih1, ih2]
      funext s
      simp only [uncurryOp, incremental]
      rw [derivative_sprod, integral_fst_comm, integral_snd_comm]
  | feedback F ih =>
      have hc : Causal (uncurryOp (Ckt.feedbackBody denoteF F)) := by
        rw [causal2]
        intro s1 s1' s2 s2' n heq1 heq2
        exact ckt_causal F _ _ _ (fun i hi => by
          show (s1 i, s2 i) = (s1' i, s2' i)
          rw [heq1 i hi, heq2 i hi])
      show Ckt.denote denoteF (Ckt.feedback (incrementalize isLinear F)) =
           Dbsp.incremental (fun s => Dbsp.fix (fun α => Ckt.feedbackBody denoteF F s (Dbsp.delay α)))
      rw [cycle_incremental _ hc, denote_feedback]
      funext s
      congr 1
      funext α
      show Ckt.denote denoteF (incrementalize isLinear F) (sprod (s, Dbsp.delay α)) =
           incremental2 (Ckt.feedbackBody denoteF F) s (Dbsp.delay α)
      rw [ih, incremental_sprod]
      rfl

end Dbsp
