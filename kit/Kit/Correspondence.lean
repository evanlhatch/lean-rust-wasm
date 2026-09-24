/-
# Kit.Correspondence — the graded correspondence library

The ONE carrier (notes/v3/01-core.md §4): every crossing between two
presentations declares its strongest honest law from this library —
never pretending lossless. Grades: `Iso` (both round trips) >
`Retraction` (one round trip) > `Codec` (decode∘encode = id + the
accepted-byte policy explicit) plus the non-invertible grades
`Normalization` (sound + idempotent), `Simulation` (directional
behavior preservation), `Abstraction` (sound approximation — over,
never exact).

Provenance: mined from `legacy/lean/codegen-core/CodegenCore/Kit.lean`
(`Iso`, the one-ended `PartialIso` — v3 renames it `Codec` and adds the
policy field, and carries the image-iso upgrade here as
`Retraction.toImageIso`). Ported: the theorem content; the file is FRESH.

Shared surface, owned here once: identity, composition, product/sum
lifting WHERE HONEST (Retraction has NO sum lifting — the inverse
cannot fabricate an element for the uncovered summand; each exclusion
is noted at its section), and transport (pre/post-composition with an
`Iso`, proved once per kind). Core-only: no mathlib, no Batteries
(the cone rule).

The five questions (notes/v3/01-core.md):
- root: none — this library IS §4's carrier vocabulary (the crossings'
  common surface); it names no root of its own.
- carrier grade: defines the grades (Iso > Retraction > Codec;
  Normalization / Simulation / Abstraction) — identity, composition,
  lifting, transport owned here once.
- spine reading: none — the spine's emitters/interpreters cite these
  grades as their law field.
- ladder rung: the laws (composition, lifting, transport) are hand
  theorems of the small generic kind (01 §7: often the best
  foundation).
- gate row: none yet — Kit is outside Gates.Packages' gated set;
  KitTests.Axioms pins the law theorems' cones (core triple only).
-/

import Kit.Relation

namespace Kit

/-! ## Iso — the true bijection -/

/-- True bijection. Rare, precious. (`to`/`inv`, not `to`/`from`:
    `from` is a reserved token in Lean 4.) -/
structure Iso (A B : Type) where
  to : A → B
  inv : B → A
  to_inv : ∀ b, to (inv b) = b
  inv_to : ∀ a, inv (to a) = a

namespace Iso

/-- Identity. -/
def refl (A : Type) : Iso A A where
  to a := a
  inv a := a
  to_inv := fun _ => rfl
  inv_to := fun _ => rfl

/-- Composition (the transitivity of the correspondence). -/
def trans (i : Iso A B) (j : Iso B C) : Iso A C where
  to := j.to ∘ i.to
  inv := i.inv ∘ j.inv
  to_inv c := by show j.to (i.to (i.inv (j.inv c))) = c; rw [i.to_inv, j.to_inv]
  inv_to a := by show i.inv (j.inv (j.to (i.to a))) = a; rw [j.inv_to, i.inv_to]

/-- Product lifting: pointwise, honest on both round trips. -/
def prod (i : Iso A B) (j : Iso C D) : Iso (A × C) (B × D) where
  to p := (i.to p.1, j.to p.2)
  inv p := (i.inv p.1, j.inv p.2)
  to_inv p := by simp [i.to_inv, j.to_inv]
  inv_to p := by simp [i.inv_to, j.inv_to]

/-- Sum lifting: pointwise per summand. -/
def sum (i : Iso A B) (j : Iso C D) : Iso (A ⊕ C) (B ⊕ D) where
  to s := s.map i.to j.to
  inv s := s.map i.inv j.inv
  to_inv s := by cases s <;> simp [i.to_inv, j.to_inv]
  inv_to s := by cases s <;> simp [i.inv_to, j.inv_to]

end Iso

/-! ## Retraction — one round trip (the embedding grade) -/

/-- Embedding with a ONE round-trip law: `inv ∘ emb = id`. The other
    direction holds only on the image (see `toImageIso`). Canonical
    instance: the checked universe inside the raw items. -/
structure Retraction (A B : Type) where
  emb : A → B
  inv : B → A
  inv_emb : ∀ a, inv (emb a) = a

namespace Retraction

/-- Identity is the trivial retraction. -/
def refl (A : Type) : Retraction A A where
  emb a := a
  inv a := a
  inv_emb := fun _ => rfl

/-- Composition: retractions compose (the law routes through both). -/
def trans (i : Retraction A B) (j : Retraction B C) : Retraction A C where
  emb := j.emb ∘ i.emb
  inv := i.inv ∘ j.inv
  inv_emb a := by
    show i.inv (j.inv (j.emb (i.emb a))) = a
    rw [j.inv_emb, i.inv_emb]

/-- Product lifting: pointwise. NO sum lifting — `inv` cannot fabricate
    an `A ⊕ C` element from the `B ⊕ D` summand the retraction does not
    cover (the honest gap is the point of the grade). -/
def prod (i : Retraction A B) (j : Retraction C D) :
    Retraction (A × C) (B × D) where
  emb p := (i.emb p.1, j.emb p.2)
  inv p := (i.inv p.1, j.inv p.2)
  inv_emb p := by simp [i.inv_emb, j.inv_emb]

/-- `emb` is injective (the one round-trip law pins the witness). -/
theorem emb_injective (r : Retraction A B) {a a' : A}
    (h : r.emb a = r.emb a') : a = a' := by
  have h0 := r.inv_emb a
  rw [h] at h0
  exact h0.symm.trans (r.inv_emb a')

/-- The image subtype: exactly the `B`s that are `emb` of something. -/
abbrev image (r : Retraction A B) : Type := {b : B // ∃ a, r.emb a = b}

/-- The retraction restricted to its image is a TRUE `Iso` — the
    image-iso upgrade (15-patterns #11, ported from `PartialIso.toImageIso`).
    `to` inverts through the retraction; `inv` re-embeds. -/
def toImageIso (r : Retraction A B) : Iso r.image A where
  to x := r.inv x.1
  inv a := ⟨r.emb a, a, rfl⟩
  to_inv a := r.inv_emb a
  inv_to x := by
    obtain ⟨a, ha⟩ := x.2
    refine Subtype.ext ?_
    rw [← ha, r.inv_emb]

/-- Transport LEFT across an `Iso`: the retraction travels. -/
def transportLeft (i : Iso A' A) (r : Retraction A B) : Retraction A' B where
  emb a' := r.emb (i.to a')
  inv b := i.inv (r.inv b)
  inv_emb a' := by rw [r.inv_emb, i.inv_to]

/-- Transport RIGHT across an `Iso`: the retraction travels. -/
def transportRight (i : Iso B B') (r : Retraction A B) : Retraction A B' where
  emb a := i.to (r.emb a)
  inv b' := r.inv (i.inv b')
  inv_emb a := by rw [i.inv_to, r.inv_emb]

end Retraction

/-! ## Codec — the wire grade: decode∘encode = id, the accepted-byte
     policy EXPLICIT -/

/-- The one-ended wire law PLUS the explicit accepted-byte policy:
    `decode (encode b) = some b` (everything we emit decodes back), and
    decode succeeds ONLY on accepted bytes (`decode_some_policy`) — the
    wire may carry bytes we do not accept, and the policy says which.
    v3's correction of the legacy `PartialIso`: the policy is a FIELD,
    not folklore. -/
structure Codec (A B : Type) where
  encode : B → A
  decode : A → Option B
  /-- The accepted-byte policy: which `A`s this codec accepts. -/
  policy : A → Prop
  decode_encode : ∀ b, decode (encode b) = some b
  /-- Decode succeeds only on accepted bytes — a `some` verdict
      certifies the input was in policy. -/
  decode_some_policy : ∀ a b, decode a = some b → policy a

namespace Codec

/-- The identity codec (policy: everything). -/
def refl (A : Type) : Codec A A where
  encode a := a
  decode a := some a
  policy _ := True
  decode_encode := fun _ => rfl
  decode_some_policy := fun _ _ _ => trivial

/-- Composition: codecs compose under the one-ended law (the reason the
    law is one-ended — the composition discipline of 15-patterns #2,
    at the carrier level). The composite policy: the left leg accepted
    the bytes AND whatever the left decode names is in the right's
    policy. -/
def trans (c : Codec A B) (d : Codec B C) : Codec A C where
  encode := c.encode ∘ d.encode
  decode a := (c.decode a).bind d.decode
  policy a := c.policy a ∧ ∀ b, c.decode a = some b → d.policy b
  decode_encode := by
    intro b
    show (c.decode (c.encode (d.encode b))).bind d.decode = _
    rw [c.decode_encode]
    exact d.decode_encode b
  decode_some_policy := by
    intro a b h
    obtain ⟨x, hx1, hx2⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨c.decode_some_policy a x hx1, fun b' hb => ?_⟩
    have hxb : x = b' := Option.some.inj (hx1.symm.trans hb)
    rw [← hxb]
    exact d.decode_some_policy x b hx2

/-- Product lifting: pair the codecs; the policy is the conjunction. -/
def prod (c : Codec A B) (d : Codec C D) : Codec (A × C) (B × D) where
  encode p := (c.encode p.1, d.encode p.2)
  decode p := (c.decode p.1).bind fun x => (d.decode p.2).map fun e => (x, e)
  policy p := c.policy p.1 ∧ d.policy p.2
  decode_encode := by
    intro b
    show (c.decode (c.encode b.1)).bind
        (fun x => (d.decode (d.encode b.2)).map fun e => (x, e)) = _
    rw [c.decode_encode, d.decode_encode]
    rfl
  decode_some_policy := by
    intro a b h
    cases hc : c.decode a.1 with
    | none => rw [hc] at h; simp at h
    | some x =>
        rw [hc] at h
        cases hd : d.decode a.2 with
        | none => rw [hd] at h; simp at h
        | some y =>
            rw [hd] at h
            simp only [Option.bind_some, Option.map_some] at h
            obtain ⟨rfl, rfl⟩ := Option.some.inj h
            exact ⟨c.decode_some_policy a.1 x hc,
                   d.decode_some_policy a.2 y hd⟩

/-- Sum lifting: pair the codecs per summand; the policy follows the
    summand. -/
def sum (c : Codec A B) (d : Codec C D) : Codec (A ⊕ C) (B ⊕ D) where
  encode s := s.map c.encode d.encode
  decode s := s.elim (fun a => (c.decode a).map Sum.inl)
                     (fun e => (d.decode e).map Sum.inr)
  policy s := s.elim c.policy d.policy
  decode_encode := by
    intro b
    cases b with
    | inl b' => show (c.decode (c.encode b')).map Sum.inl = _; rw [c.decode_encode]; rfl
    | inr b' => show (d.decode (d.encode b')).map Sum.inr = _; rw [d.decode_encode]; rfl
  decode_some_policy := by
    intro a b h
    cases a with
    | inl a' =>
        show c.policy a'
        have h1 : (c.decode a').map Sum.inl = some b := h
        cases hc : c.decode a' with
        | none => rw [hc] at h1; simp at h1
        | some x =>
            rw [hc] at h1
            exact c.decode_some_policy a' x hc
    | inr a' =>
        show d.policy a'
        have h1 : (d.decode a').map Sum.inr = some b := h
        cases hd : d.decode a' with
        | none => rw [hd] at h1; simp at h1
        | some y =>
            rw [hd] at h1
            exact d.decode_some_policy a' y hd

/-- Transport LEFT across an `Iso`: the codec travels (the policy
    along the iso). -/
def transportLeft (i : Iso A' A) (c : Codec A B) : Codec A' B where
  encode b := i.inv (c.encode b)
  decode a' := c.decode (i.to a')
  policy a' := c.policy (i.to a')
  decode_encode b := by rw [i.to_inv, c.decode_encode]
  decode_some_policy a' b := c.decode_some_policy (i.to a') b

/-- Transport RIGHT across an `Iso`: the codec travels (the policy is
    on the byte side, unchanged). -/
def transportRight (i : Iso B B') (c : Codec A B) : Codec A B' where
  encode b' := c.encode (i.inv b')
  decode a := (c.decode a).map i.to
  policy := c.policy
  decode_encode b' := by rw [c.decode_encode, Option.map_some, i.to_inv]
  decode_some_policy a b' h := by
    cases hc : c.decode a with
    | none => rw [hc] at h; simp at h
    | some x =>
        rw [hc] at h
        simp only [Option.map_some] at h
        exact c.decode_some_policy a x hc

end Codec

/-! ## Normalization — sound + idempotent (canonical forms) -/

/-- A normalization: `norm` maps every value into the canonical form
    along the relation `R` (soundness), and is idempotent. The
    completeness grade (every value HAS a canonical form pre-existing)
    is deliberately absent — it lands with the first consumer that has
    one (01-core §4: "completeness when available"). -/
structure Normalization (A : Type) where
  norm : A → A
  /-- The soundness relation: `R x y` reads "y is the normalized form
      of x" — the lane owns it (equality, subform, refinement …). -/
  R : A → A → Prop
  /-- Soundness: normalizing stays within the relation. -/
  sound : ∀ a, R a (norm a)
  /-- Idempotence: a normalized value is already canonical. -/
  idempotent : ∀ a, norm (norm a) = norm a

namespace Normalization

/-- Identity normalization (relation: equality). -/
def refl (A : Type) : Normalization A where
  norm a := a
  R x y := x = y
  sound := fun _ => rfl
  idempotent := fun _ => rfl

/-- A fixed point of `norm` is related to itself. -/
theorem fixedPoint_sound (n : Normalization A) (a : A)
    (h : n.norm a = a) : n.R a a := by
  have hs := n.sound a
  rw [h] at hs
  exact hs

/-- Product lifting: pointwise norm, product relation. -/
def prod (m : Normalization A) (n : Normalization B) :
    Normalization (A × B) where
  norm p := (m.norm p.1, n.norm p.2)
  R x y := m.R x.1 y.1 ∧ n.R x.2 y.2
  sound p := ⟨m.sound p.1, n.sound p.2⟩
  idempotent p := by simp [m.idempotent, n.idempotent]

/-- Transport LEFT across an `Iso`: the relation travels. -/
def transportLeft (i : Iso A' A) (n : Normalization A) :
    Normalization A' where
  norm a' := i.inv (n.norm (i.to a'))
  R x y := n.R (i.to x) (i.to y)
  sound a' := by rw [i.to_inv]; exact n.sound (i.to a')
  idempotent a' := by
    show i.inv (n.norm (i.to (i.inv (n.norm (i.to a')))))
        = i.inv (n.norm (i.to a'))
    rw [i.to_inv, n.idempotent]

end Normalization

/-! ## Simulation — directional behavior preservation -/

/-- A simulation of `A`-steps by `B`-steps along the relation `R`:
    every `A`-step from an `R`-related state has a matching `B`-step.
    Directional BY DESIGN (01-core §4: "behavior preservation in the
    named direction") — bisimulation is a separate claim, not a hidden
    second field. -/
structure Simulation (A B : Type) where
  stepA : A → A → Prop
  stepB : B → B → Prop
  R : A → B → Prop
  /-- The one-step preservation law. -/
  sim : ∀ a a' b, R a b → stepA a a' → ∃ b', R a' b' ∧ stepB b b'

namespace Simulation

/-- Identity simulation: a transition relation simulates itself along
    equality. -/
def refl (A : Type) (step : A → A → Prop) : Simulation A A where
  stepA := step
  stepB := step
  R a b := a = b
  sim a a' b h hs := by rw [← h]; exact ⟨a', rfl, hs⟩

/-- Composition: simulations compose — HONESTLY only when the
    intermediate's step relation matches (`hcomp`: t's A-steps contain
    s's B-steps; the degenerate honest case is `t.stepA = s.stepB`).
    The multi-stage pipeline's end-to-end preservation — the composite
    relation exists-by-witness. -/
def trans (s : Simulation A B) (t : Simulation B C)
    (hcomp : ∀ x y, s.stepB x y → t.stepA x y) : Simulation A C where
  stepA := s.stepA
  stepB := t.stepB
  R a c := ∃ b, s.R a b ∧ t.R b c
  sim a a' c h hs := by
    obtain ⟨b, hab, hbc⟩ := h
    obtain ⟨b', hab', hbb'⟩ := s.sim a a' b hab hs
    have hb' : t.stepA b b' := hcomp b b' hbb'
    obtain ⟨c', hbc', hcc'⟩ := t.sim b b' c hbc hb'
    exact ⟨c', ⟨b', hab', hbc'⟩, hcc'⟩

/-- Product lifting: parallel steps, pointwise relation. -/
def prod (s : Simulation A B) (t : Simulation C D) :
    Simulation (A × C) (B × D) where
  stepA p q := s.stepA p.1 q.1 ∧ t.stepA p.2 q.2
  stepB p q := s.stepB p.1 q.1 ∧ t.stepB p.2 q.2
  R p q := s.R p.1 q.1 ∧ t.R p.2 q.2
  sim p p' q h hp := by
    obtain ⟨hs1, hs2⟩ := hp
    obtain ⟨ht1, ht2⟩ := h
    obtain ⟨b1, hb1, hb1'⟩ := s.sim p.1 p'.1 q.1 ht1 hs1
    obtain ⟨d1, hd1, hd1'⟩ := t.sim p.2 p'.2 q.2 ht2 hs2
    exact ⟨(b1, d1), ⟨hb1, hd1⟩, ⟨hb1', hd1'⟩⟩

end Simulation

/-! ## Abstraction — sound approximation (over, never exact) -/

/-- A sound approximation: `abst` maps concrete to abstract; `conc b a`
    reads "a is a concrete value OF the abstract b". Soundness: every
    concrete value sits in the concretization of its own abstraction —
    the abstraction is an OVER-approximation (the concretization of
    `abst a` may name more values than `a`; exactness is a separate,
    rare claim and is deliberately not a field). -/
structure Abstraction (A B : Type) where
  abst : A → B
  conc : B → A → Prop
  /-- Soundness: the abstraction covers its own value. -/
  sound : ∀ a, conc (abst a) a

namespace Abstraction

/-- Identity abstraction (exact by construction — the degenerate
    over-approximation). -/
def refl (A : Type) : Abstraction A A where
  abst a := a
  conc b a := b = a
  sound := fun _ => rfl

/-- Composition: over-approximations compose (the pipeline's end-to-end
    soundness — the composite concretization is the witness chain). -/
def trans (p : Abstraction A B) (q : Abstraction B C) : Abstraction A C where
  abst := q.abst ∘ p.abst
  conc c a := ∃ m, p.conc m a ∧ q.conc c m
  sound a := ⟨p.abst a, p.sound a, q.sound (p.abst a)⟩

/-- Product lifting: pointwise. -/
def prod (p : Abstraction A B) (q : Abstraction C D) :
    Abstraction (A × C) (B × D) where
  abst r := (p.abst r.1, q.abst r.2)
  conc r s := p.conc r.1 s.1 ∧ q.conc r.2 s.2
  sound r := ⟨p.sound r.1, q.sound r.2⟩

/-- Transport LEFT across an `Iso`: the abstraction travels. -/
def transportLeft (i : Iso A' A) (p : Abstraction A B) :
    Abstraction A' B where
  abst a' := p.abst (i.to a')
  conc b a' := p.conc b (i.to a')
  sound a' := p.sound (i.to a')

end Abstraction

/-! ## The carrier-as-graph bridge (16-surface §4.1)

Every carrier value INDUCES its graph — the `Rel` its round trip names —
and the carrier's `trans` and the engine's `Rel.comp` AGREE, proved once
per grade: ONE composition tower, the grades riding on top. The engine
runs over graphs; the grades refine. Direction honesty, judged per grade:

- `Iso`: the graph is its `to` — total, functional, both round trips
  under it.
- `Retraction`: the graph is its `emb` — the ONE direction the grade's
  law rides. Total on `A`; the uncovered `B`s have no incoming edge
  (the honest gap is visible in the graph).
- `Codec`: the graph is the DECODE direction, PARTIAL —
  `decode a = some b`. A pair is in the graph exactly when the byte is
  ACCEPTED (`decode_some_policy` makes the policy visible in the graph)
  and names `b`. The encode direction is deliberately NOT the graph: it
  is total on `B`, not on the wire's `A`s.

The agreement shape is POINTWISE `Iff` — `Rel.comp_assoc`'s honest
precedent (`Eq` of relations would buy the same content via funext +
propext, nothing more).
-/

/-- The graph of an `Iso`: `R a b := b = i.to a`. -/
abbrev Iso.toRel (i : Iso A B) : Rel A B := fun a b => b = i.to a

/-- THE tower merge, `Iso` grade: the carrier's `trans` IS the engine's
    `Rel.comp` on the graphs. No round-trip law is spent — the graph
    composition is pure associativity. -/
theorem Iso.toRel_trans (i : Iso A B) (j : Iso B C) (a : A) (c : C) :
    (i.trans j).toRel a c ↔ Rel.comp i.toRel j.toRel a c :=
  ⟨fun h => ⟨i.to a, rfl, h⟩,
   fun h => by
     obtain ⟨b, h1, h2⟩ := h
     rw [h1] at h2
     exact h2⟩

/-- The unit row, `Iso` grade: the identity iso's graph IS the
    diagonal — the engine's unit, cited, not re-proved. -/
theorem Iso.toRel_refl (A : Type) (a b : A) :
    (Iso.refl A).toRel a b ↔ Rel.refl A a b :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- The graph of a `Retraction`: `R a b := b = r.emb a` — the `emb`
    direction, the one the grade's law rides. -/
abbrev Retraction.toRel (r : Retraction A B) : Rel A B :=
  fun a b => b = r.emb a

/-- THE tower merge, `Retraction` grade. -/
theorem Retraction.toRel_trans (r : Retraction A B) (s : Retraction B C)
    (a : A) (c : C) :
    (r.trans s).toRel a c ↔ Rel.comp r.toRel s.toRel a c :=
  ⟨fun h => ⟨r.emb a, rfl, h⟩,
   fun h => by
     obtain ⟨b, h1, h2⟩ := h
     rw [h1] at h2
     exact h2⟩

/-- The unit row, `Retraction` grade. -/
theorem Retraction.toRel_refl (A : Type) (a b : A) :
    (Retraction.refl A).toRel a b ↔ Rel.refl A a b :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- The graph of a `Codec`: the DECODE direction, PARTIAL —
    `R a b := c.decode a = some b`. -/
abbrev Codec.toRel (c : Codec A B) : Rel A B :=
  fun a b => c.decode a = some b

/-- THE tower merge, `Codec` grade: the composite's decode graph is the
    engine's composite of the decode graphs — the `bind`'s existential
    IS the witness chain (the collapse `Option.bind_eq_some_iff` reads). -/
theorem Codec.toRel_trans (c : Codec A B) (d : Codec B C) (a : A) (b : C) :
    (c.trans d).toRel a b ↔ Rel.comp c.toRel d.toRel a b :=
  ⟨fun h => Option.bind_eq_some_iff.mp h,
   fun h => Option.bind_eq_some_iff.mpr h⟩

/-- The unit row, `Codec` grade: the identity codec's graph is the
    diagonal — the partial graph of a total codec. -/
theorem Codec.toRel_refl (A : Type) (a b : A) :
    (Codec.refl A).toRel a b ↔ Rel.refl A a b := by
  show (some a = some b) ↔ a = b
  exact ⟨Option.some.inj, fun h => by rw [h]⟩

end Kit
