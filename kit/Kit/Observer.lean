/-
# Kit.Observer — the observer parameter

"Same behavior" is meaningless without naming the observer
(notes/v3/04-verification.md §4). Every equivalence/refinement claim
carries one — as DATA. The five questions:

- **Root**: TraceModel (01-core §3) — the behavior side: this is the
  observation vocabulary over executions, the derived VIEW the
  TraceModel's transition semantics exposes (the sequential trace set,
  refinement = inclusion parameterized by the observation).
- **Carrier grade**: the refinement/observation grade of 01-core §4 —
  `Observer.Below` (o₁'s observation is DETERMINED by o₂'s, with the
  extract as data) and `Observer.equiv` (the kernel of `see`, proved
  an equivalence).
- **Spine reading**: none — the consumers (duel, witness lane, skew
  checks, instrumentation claims) instantiate; nothing is emitted.
- **Ladder rung**: n/a for Change — but the standard hierarchy's
  INCLUSION relations (`apiBelowAudit`, `auditBelowPerf`,
  `securityBelowAudit`) are landed as `Below` DATA, one per 04 §4's
  row.
- **Gate rows**: the axiom report over the law theorems + KitTests
  pins (positive + negative controls: the coarseness witness — api
  does NOT see traces — and the directionality witness — refinement
  is NOT symmetric across observers).

The minimal execution shape the standard observers consume: events are
an OPAQUE type parameter E (occurrence identity stays downstream —
01-core §3: an event is not its label); the trace is a `List E`; the
terminal `result` is `none` when the execution diverged or has no
return. `cost` is the resource counter perfObs reads. This is the
MINIMAL shape — richer executions (conflict, causal order) extend it
deliberately per 01-core §3, never silently.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Correspondence

namespace Kit

/-! ## The observer -/

/-- An observer: what an execution SHOWS. `see : E → O` — the
    observation is the claim's parameter; every later claim of "same
    behavior" names one. -/
structure Observer (E O : Type) where
  see : E → O

/-- Equivalence UNDER an observer: the kernel of `see`. It IS an
    equivalence relation — proved below. (`abbrev`: the Decidable
    instances reach through.) -/
abbrev Observer.equiv (o : Observer E O) (x y : E) : Prop :=
  o.see x = o.see y

theorem Observer.equiv_refl (o : Observer E O) (x : E) :
    o.equiv x x := rfl

theorem Observer.equiv_symm (o : Observer E O) {x y : E}
    (h : o.equiv x y) : o.equiv y x := h.symm

theorem Observer.equiv_trans (o : Observer E O) {x y z : E}
    (h₁ : o.equiv x y) (h₂ : o.equiv y z) : o.equiv x z := h₁.trans h₂

/-! ## Observational inclusion (the hierarchy, as data) -/

/-- o₁ is BELOW o₂ when o₂'s observation DETERMINES o₁'s — the
    extract is DATA, and the law field `seen` pins it (a Below without
    the law is not constructible). This is how the standard hierarchy
    lands: each inclusion is a value, not prose. -/
structure Observer.Below {E O₁ O₂ : Type}
    (o₁ : Observer E O₁) (o₂ : Observer E O₂) where
  extract : O₂ → O₁
  seen : ∀ e, o₁.see e = extract (o₂.see e)

/-- Below is reflexive (extract = id). -/
def Observer.Below.refl (o : Observer E O) : Observer.Below o o where
  extract a := a
  seen _ := rfl

/-- Below composes (the pipeline's extract chain). -/
def Observer.Below.trans {o₁ : Observer E O₁} {o₂ : Observer E O₂}
    {o₃ : Observer E O₃} (h₁₂ : Observer.Below o₁ o₂)
    (h₂₃ : Observer.Below o₂ o₃) : Observer.Below o₁ o₃ where
  extract a := h₁₂.extract (h₂₃.extract a)
  seen e := by rw [h₁₂.seen e, h₂₃.seen e]

/-! ## The minimal execution shape -/

/-- The minimal execution the standard observers consume: a sequential
    trace of events (the event type E is the consumer's parameter —
    opaque here), the terminal result (`none` = diverged / no return),
    and the resource cost. -/
structure Execution (E : Type) where
  trace : List E
  result : Option E
  cost : Nat

/-! ## The standard hierarchy (04-verification §4) -/

/-- apiObs — return values + public errors: the terminal result ONLY.
    The trace is invisible to the API observer. -/
def apiObs (E : Type) : Observer (Execution E) (Option E) :=
  ⟨fun x => x.result⟩

/-- auditObs — apiObs PLUS the committed events: the full trace. -/
def auditObs (E : Type) : Observer (Execution E) (Option E × List E) :=
  ⟨fun x => (x.result, x.trace)⟩

/-- perfObs — auditObs PLUS the resource costs. -/
def perfObs (E : Type) :
    Observer (Execution E) (Option E × List E × Nat) :=
  ⟨fun x => (x.result, x.trace, x.cost)⟩

/-- securityObs p — what principal p can see: the result PLUS the
    VISIBLE trace (the visibility policy as Bool data, per event). -/
def securityObs {E P : Type} (canSee : P → E → Bool) (p : P) :
    Observer (Execution E) (Option E × List E) :=
  ⟨fun x => (x.result, x.trace.filter (canSee p))⟩

/-- THE hierarchy row: api ⊑ audit (the trace determines the result —
    extract = the first projection). -/
def apiBelowAudit (E : Type) :
    Observer.Below (apiObs E) (auditObs E) where
  extract q := q.1
  seen _ := rfl

/-- THE hierarchy row: audit ⊑ perf. -/
def auditBelowPerf (E : Type) :
    Observer.Below (auditObs E) (perfObs E) where
  extract q := (q.1, q.2.1)
  seen _ := rfl

/-- THE hierarchy row: securityObs p ⊑ audit (p's visible trace is a
    filter of the full trace; same result). -/
def securityBelowAudit {E P : Type} (canSee : P → E → Bool) (p : P) :
    Observer.Below (securityObs canSee p) (auditObs E) where
  extract q := (q.1, q.2.filter (canSee p))
  seen _ := rfl

/-! ## Refinement of trace sets, parameterized by the observer -/

/-- Observational refinement between trace SETS (01-core §3:
    refinement = inclusion, parameterized by the observation): every
    impl execution is matched, under `o`, by a spec execution.
    DIRECTIONAL by design — the reverse claim is separate (see the
    KitTests directionality control). -/
def Observer.refines (o : Observer E O) (impl spec : List E) : Prop :=
  ∀ x, x ∈ impl → ∃ y, y ∈ spec ∧ o.see y = o.see x

theorem Observer.refines_refl (o : Observer E O) (xs : List E) :
    o.refines xs xs := fun _ h => ⟨_, h, rfl⟩

theorem Observer.refines_trans (o : Observer E O) (a b c : List E)
    (h₁ : o.refines a b) (h₂ : o.refines b c) : o.refines a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h₁ x hx
  obtain ⟨z, hz, hyz⟩ := h₂ y hy
  exact ⟨z, hz, hyz.trans hxy⟩

/-! ## The Galois connection: coarsen ⊣ refine (04-verification §4 + 16-surface §5.4) -/

/- **THE GALOIS CONNECTION** on the observer lattice. `Below` IS the
    connection's data: with `o₁` the COARSE observer and `o₂` the FINE
    one, the extract is the COARSEN map (a fine observation read as
    the coarse one — the left-adjoint action), and the fine observation
    map `o₂.see` is the REFINE map (the right-adjoint action on the
    execution). The connection's law — the adjunction's closing
    triangle — is the field `seen`: `coarsen (refine e) = o₁.see e`
    (the coarse observation IS the coarsened fine observation). The
    forgetful triangle closes; the reflecting one needs the extract
    invertible — the ISO case (16 §5.1's graduation), not claimed at
    the connection's grade. The carrier-form tie is `toAbstraction`
    (ONE theorem); the coarsening-preserves-claims family
    (`refines_below`, `equiv_below`) hangs off it as corollaries. -/

/-- **THE TIE** (16 §5.4's one theorem): the observer lattice's
    coarsening IS the correspondence kit's `Abstraction` grade — the
    Galois-connection data as a carrier value. The abstraction sends
    the execution to its FINE observation; the concretization fiber of
    `b` names the executions whose COARSE observation the extract
    reproduces; soundness is `seen` itself. Every
    coarsening-preserves-claims statement is now a corollary of the
    `Abstraction` surface (`Kit.Correspondence`), never a fresh
    proof. -/
def Observer.Below.toAbstraction {E O₁ O₂ : Type}
    {o₁ : Observer E O₁} {o₂ : Observer E O₂} (h : Below o₁ o₂) :
    Kit.Abstraction E O₂ where
  abst e := o₂.see e
  conc b e := o₁.see e = h.extract b
  sound e := h.seen e

/-- The Galois law, element form: `e` lies in the concretization fiber
    of `b` iff the refined-then-coarsened observation matches — the
    fiber identity unfolds to `seen`'s law. -/
theorem Observer.Below.conc_iff {E O₁ O₂ : Type} {o₁ : Observer E O₁}
    {o₂ : Observer E O₂} (h : Below o₁ o₂) (b : O₂) (e : E) :
    h.toAbstraction.conc b e ↔ h.extract (o₂.see e) = h.extract b := by
  constructor
  · intro hs
    show h.extract (o₂.see e) = h.extract b
    rw [← h.seen e]
    exact hs
  · intro hs
    show o₁.see e = h.extract b
    rw [h.seen e]
    exact hs

/-- COROLLARY (the coarsening-preserves-claims family, 16 §5.4):
    forgetting observations preserves refinement claims — a claim
    visible under the FINE observer is visible under the COARSE one.
    Instrumentation-preservation instances (`Kit.Hyper`'s output
    row at the power; the machines' observer theorems) ride this,
    never re-prove it. -/
theorem Observer.refines_below {E O₁ O₂ : Type} {o₁ : Observer E O₁}
    {o₂ : Observer E O₂} (h : Below o₁ o₂) {impl spec : List E}
    (hr : o₂.refines impl spec) : o₁.refines impl spec := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hr x hx
  refine ⟨y, hy, ?_⟩
  rw [h.seen y, h.seen x]
  exact congrArg h.extract hxy

/-- COROLLARY: coarser observers distinguish less — fine-observational
    equality implies coarse-observational equality (the `Below`
    discipline's kernel inclusion). -/
theorem Observer.equiv_below {E O₁ O₂ : Type} {o₁ : Observer E O₁}
    {o₂ : Observer E O₂} (h : Below o₁ o₂) {x y : E}
    (hxy : o₂.equiv x y) : o₁.equiv x y := by
  show o₁.see x = o₁.see y
  rw [h.seen x, h.seen y]
  exact congrArg h.extract hxy

end Kit
