/-
# Kit.Hyper — the hyperproperty substrate (the power jump)

notes/v3/16-surface.md §4.3: `Rel` lifted to PAIRS of executions (the
product program) — the power jump that makes noninterference
("secret changes can't alter public outputs") STATABLE — the property
class other toolkits can't express. The discipline: hyperproperties are
RELATIONS OVER PAIRS — statable, checkable, never vibes.

What lands here:

- the power-jump type (`Rel2`: relations between EXECUTION PAIRS) + the
  lifting discipline (`Rel.lift2`: a 1-relation lifts to a 2-relation
  by pairing, POINTWISE) + the law that the lift respects THE ONE
  composition (`Rel.lift2_comp` — the power tower merges with the
  engine's, no parallel story);
- the pair-map (`pairMap`: the product program runs `f` on BOTH
  executions) and the power-jump preservation box (`Preserves2` —
  01-core §6's box one power up: the quantified object is the pair);
- THE flagship hyperproperty (`Noninterfering`) as a TYPE over a
  two-run relation, with the observation-derived two-run relation
  (`agreeOn` — two runs related iff they agree on the observation; the
  secret is outside the relation's vocabulary) and the composition
  that makes the claim a CITATION (`noninterfering_of_factor`: the
  public output factors through the public input — the extract is
  data);
- the observer composition (Kit.Observer cited, never rebuilt): the
  output-coarsening row (`Noninterfering.below` — one-way, honestly:
  coarsening the INPUT observer weakens the hypothesis and is NOT
  sound) + the security row (`noninterfering_securityOf`: the output
  determined by what principal p sees);
- the worked instances (16 §4.3: ONE positive, ONE negative, each with
  the counterexample pair as DATA): the secret-dropping machine
  (proved), the leaky machine (refuted — numeric AND execution-shaped
  under `securityObs`).

Boundary (16 §4.3, kept): schedule-independence and the other named
hyperproperties land with their first consumer — the substrate makes
them STATABLE, it does not preempt their shapes.

The five questions (notes/v3/01-core.md):
- root: TraceModel — the behavior side: the quantified object is the
  PAIR of executions (01 §3's transition semantics is authoritative;
  the two runs are two of its points).
- carrier grade: none of the inverting grades — noninterference is a
  hyperproperty, stated over `Kit.Relation`'s engine at the power; the
  observer nuance rides `Kit.Observer`'s Below rows (cited).
- spine reading: none — the consumers are the security/lanes claims.
- ladder rung: hand theorems of the small generic kind (01 §7) — the
  factor row IS the shape every future noninterference claim cites.
- gate row: the axiom pins in `KitTests.Axioms` + the KitTests pins —
  positive, negative, and the mandatory controls (the self-pair-only
  audit and the loose relation are the producers).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Relation
import Kit.Observer

namespace Kit

/-! ## The power jump: relations between execution pairs -/

/-- A relation between EXECUTION PAIRS: `Rel2 A B` relates the pair
    `(a₁, a₂)` to the pair `(b₁, b₂)` — the two-run carrier (16 §4.3).
    (`abbrev`: the instances and the decide-level checks reach
    through.) -/
abbrev Rel2 (A B : Type) := Rel (A × A) (B × B)

/-- The lifting discipline (16 §4.3): a 1-relation lifts to a
    2-relation by pairing, POINTWISE — the pair is related exactly when
    both components are. -/
abbrev Rel.lift2 (R : Rel A B) : Rel2 A B :=
  fun p q => R p.1 q.1 ∧ R p.2 q.2

/-- The lift respects THE ONE composition: lifting the composite is the
    composite of the lifts (pointwise `Iff`, the honest shape) — the
    power tower merges with the engine's, no parallel story. -/
theorem Rel.lift2_comp {A B C : Type} (R : Rel A B) (S : Rel B C)
    (p : A × A) (q : C × C) :
    Rel.comp (Rel.lift2 R) (Rel.lift2 S) p q
      ↔ Rel.lift2 (Rel.comp R S) p q := by
  constructor
  · intro h
    obtain ⟨m, h1, h2⟩ := h
    exact ⟨⟨m.1, h1.1, h2.1⟩, ⟨m.2, h1.2, h2.2⟩⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨b, hb1, hb2⟩ := h1
    obtain ⟨b', hb1', hb2'⟩ := h2
    exact ⟨(b, b'), ⟨hb1, hb1'⟩, ⟨hb2, hb2'⟩⟩

/-! ## The product program: the pair-map + the power preservation box -/

/-- The pair-map of `f` — the product program runs `f` on BOTH
    executions. -/
def pairMap (f : A → B) : A × A → B × B := fun p => (f p.1, f p.2)

/-- THE power-jump preservation box (16 §4.3; 01-core §6's box one
    power up): `f` — run on both executions by `pairMap` — carries the
    two-run relation `R` into `S`. The quantified object is the
    EXECUTION PAIR; nothing about a single run is claimed. -/
def Preserves2 {A B : Type} (f : A → B) (R : Rel2 A A) (S : Rel2 B B) :
    Prop :=
  ∀ p q, R p q → S (pairMap f p) (pairMap f q)

/-! ## THE flagship hyperproperty: noninterference -/

/-- THE flagship hyperproperty (16 §4.3): noninterference — "secret
    changes can't alter public outputs" — as a TYPE over a two-run
    relation. `R` says which input-run pairs are admissible (public
    agreement; the secret is free to differ — the relation never
    mentions it); `R'` the output side. `f` is noninterfering when
    every admissible pair maps to an `R'`-related output pair. -/
def Noninterfering {In Out : Type} (f : In → Out) (R : Rel In In)
    (R' : Rel Out Out) : Prop :=
  ∀ u v, R u v → R' (f u) (f v)

/-- The observation-derived two-run relation: two runs related iff they
    AGREE on the observation. The canonical `R` for noninterference —
    the public input's agreement; the secret is outside the relation's
    vocabulary. (`abbrev`: the decide-level checks reach through.) -/
abbrev agreeOn {A O : Type} (obs : A → O) : Rel A A :=
  fun u v => obs u = obs v

/-- Observation agreement is symmetric (the price `ofPreserves2`
    quotes below is always on offer for it). -/
theorem agreeOn_symm {A O : Type} (obs : A → O) (u v : A)
    (h : agreeOn obs u v) : agreeOn obs v u := h.symm

/-- The composition that makes noninterference a CITATION (16 §4.3 +
    15 §5.4's extract-as-data discipline): if `f`'s observed output
    FACTORS through the observed input (the extract `g` is DATA), `f`
    is noninterfering — the secret never reaches the output. Every
    worked instance below is one application. -/
theorem noninterfering_of_factor {In Out OIn OOut : Type} {f : In → Out}
    {obs : In → OIn} {obs' : Out → OOut}
    (g : OIn → OOut) (h : ∀ u, obs' (f u) = g (obs u)) :
    Noninterfering f (agreeOn obs) (agreeOn obs') :=
  fun u v hu => by
    show obs' (f u) = obs' (f v)
    rw [h u, h v, hu]

/-- The lifting discipline's read: noninterference IS the preservation
    box at the power — the pair-map of `f` carries the LIFTED two-run
    relation into the lifted `R'` (one application per component; no
    new content). -/
theorem Noninterfering.toPreserves2 {In Out : Type} {f : In → Out}
    {R : Rel In In} {R' : Rel Out Out} (h : Noninterfering f R R') :
    Preserves2 f (Rel.lift2 R) (Rel.lift2 R') :=
  fun _p _q hpq => ⟨h _ _ hpq.1, h _ _ hpq.2⟩

/-- The converse, at the honest price: a SYMMETRIC `R` (observation
    agreement is — `agreeOn_symm`) reads the power box back down to
    noninterference. -/
theorem Noninterfering.ofPreserves2 {In Out : Type} {f : In → Out}
    {R : Rel In In} {R' : Rel Out Out} (hsym : ∀ u v, R u v → R v u)
    (h : Preserves2 f (Rel.lift2 R) (Rel.lift2 R')) :
    Noninterfering f R R' :=
  fun u v huv => (h (u, v) (v, u) ⟨huv, hsym u v huv⟩).1

/-! ## The observer composition (cites Kit.Observer, never rebuilds) -/

/-- The coarsening row (15 §5.4's Below discipline, at the power): a
    noninterference claim survives coarsening the OUTPUT observer —
    the conclusion weakens, the extract is data. ONE-WAY, honestly:
    coarsening the INPUT observer weakens the hypothesis and is NOT
    sound (a coarser input view admits pairs the fine view refused). -/
theorem Noninterfering.below {In Out OIn OOut OOut' : Type}
    {f : In → Out} {oIn : Observer In OIn} {oOut : Observer Out OOut}
    {oOut' : Observer Out OOut'}
    (h : Noninterfering f (agreeOn oIn.see) (agreeOn oOut.see))
    (hout : Observer.Below oOut' oOut) :
    Noninterfering f (agreeOn oIn.see) (agreeOn oOut'.see) :=
  fun u v hu => by
    show oOut'.see (f u) = oOut'.see (f v)
    rw [hout.seen (f u), hout.seen (f v), h u v hu]

/-- THE security row (04 §4's vocabulary, cited): if `f`'s public
    output is determined by what principal `p` SEES (`securityObs`'s
    view — the extract `g` is data), then `f` is noninterfering from
    `p`'s sight line to the public output. The flagship hyperproperty
    at the observer hierarchy — no new proof machinery. -/
theorem noninterfering_securityOf {E P : Type}
    (f : Execution E → Execution E) (canSee : P → E → Bool) (p : P)
    (g : Option E × List E → Option E)
    (h : ∀ x, (apiObs E).see (f x) = g ((securityObs canSee p).see x)) :
    Noninterfering f (agreeOn (securityObs canSee p).see)
      (agreeOn (apiObs E).see) :=
  noninterfering_of_factor g h

/-! ## The worked instances (16 §4.3: statable, checkable, never vibes)

The toy machine's shape: a two-part input — the PUBLIC part (the first
component) and the SECRET part (the second).
-/

/-- THE WORKED POSITIVE: the machine that drops the secret — the
    public output is the public input alone (the factor `g = id`,
    cited). -/
def dropSecret : Nat × Nat → Nat := fun p => p.1

/-- The positive instance's theorem. -/
theorem dropSecret_noninterfering :
    Noninterfering dropSecret (agreeOn Prod.fst) (agreeOn id) :=
  noninterfering_of_factor id (fun _u => rfl)

/-- The positive instance's power face: the pair-map of `dropSecret`
    carries the lifted public agreement into the lifted output
    agreement (`Noninterfering.toPreserves2`, no new proof). -/
theorem dropSecret_preserves2 :
    Preserves2 dropSecret (Rel.lift2 (agreeOn Prod.fst))
      (Rel.lift2 (agreeOn id)) :=
  dropSecret_noninterfering.toPreserves2

/-- THE WORKED NEGATIVE: the leaky sibling — adds the secret into the
    public output. -/
def leakSecret : Nat × Nat → Nat := fun p => p.1 + p.2

/-- THE counterexample pair, as data: same public input (`0 = 0`),
    different public outputs (`0 ≠ 1`). -/
def leakWitness : (Nat × Nat) × (Nat × Nat) := ((0, 0), (0, 1))

/-- The negative instance's theorem: the leak is REFUTED by the
    counterexample pair — the type has teeth. -/
theorem leakSecret_notNoninterfering :
    ¬ Noninterfering leakSecret (agreeOn Prod.fst) (agreeOn id) := by
  intro h
  have h0 := h leakWitness.1 leakWitness.2
    (rfl : Prod.fst leakWitness.1 = Prod.fst leakWitness.2)
  simp [leakSecret, agreeOn, leakWitness] at h0

/-! ## The execution face (Kit.Observer's runs, cited) -/

/-- The run-map that publishes only the result — the trace (the
    secret's carrier) is dropped. -/
def resultOnly {E : Type} (x : Execution E) : Execution E :=
  { trace := [], result := x.result, cost := 0 }

/-- The positive execution instance: the run-map is noninterfering
    under the FULL audit observation — audit agreement pins the
    result, and the published run's trace is empty for every input. -/
theorem resultOnly_audit_noninterfering (E : Type) :
    Noninterfering (resultOnly (E := E)) (agreeOn (auditObs E).see)
      (agreeOn (auditObs E).see) := by
  intro x y h
  have h1 : x.result = y.result := congrArg Prod.fst h
  exact congrArg (fun r : Option E => (r, ([] : List E))) h1

/-- THE coarsening row exercised: the audit-level claim survives
    forgetting the trace — the api face (the Below row CITED:
    `apiBelowAudit`). -/
theorem resultOnly_api_noninterfering (E : Type) :
    Noninterfering (resultOnly (E := E)) (agreeOn (auditObs E).see)
      (agreeOn (apiObs E).see) :=
  (resultOnly_audit_noninterfering E).below (apiBelowAudit E)

/-- The positive execution face under the SECURITY observer: the
    result-only run-map is noninterfering from ANY principal's sight
    line (the extract is `Prod.fst`, data — `noninterfering_securityOf`). -/
theorem resultOnly_security_noninterfering (E P : Type)
    (canSee : P → E → Bool) (p : P) :
    Noninterfering (resultOnly (E := E))
      (agreeOn (securityObs canSee p).see) (agreeOn (apiObs E).see) :=
  noninterfering_securityOf resultOnly canSee p (fun q => q.1)
    (fun _x => rfl)

/-- The leaky run-map: the result is the trace's FIRST event —
    whatever principal `p` cannot see rides the public output. -/
def leakExec {E : Type} (x : Execution E) : Execution E :=
  { trace := [], result := x.trace.head?, cost := 0 }

/-- The leaky runs (the counterexample pair, as data): same api result
    (`some 0`), secrets `7` / `9` in the trace — invisible to the
    principal that sees nothing. -/
def secEx1 : Execution Int := { trace := [7], result := some 0, cost := 1 }

def secEx2 : Execution Int := { trace := [9], result := some 0, cost := 1 }

/-- THE WORKED NEGATIVE, execution face: the leaky run-map is NOT
    noninterfering from the blind principal's sight line — the
    counterexample pair above is the data, `securityObs` is the
    observer. -/
theorem leakExec_notNoninterfering :
    ¬ Noninterfering leakExec
        (agreeOn (securityObs (fun _p (_e : Int) => false) 0).see)
        (agreeOn (apiObs Int).see) := by
  intro h
  have h0 := h secEx1 secEx2 (by simp [securityObs, secEx1, secEx2])
  simp [apiObs, leakExec, secEx1, secEx2, agreeOn] at h0

end Kit
