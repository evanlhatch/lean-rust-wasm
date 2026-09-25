/-
# Kit.Change — the Change capability ladder

The Change root (notes/v3/01-core.md §2): "what changes" is NOT assumed
reversible. The honest hierarchy — an instance declares how far up it
sits: `Applicable` → `Composable` → `WithIdentity` → `Reversible` →
`Commuting` → `Additive`. Each rung ADDS structure; nothing below is
smuggled in. The five questions:

- **Root**: Change (01-core §2) — the symmetry layer between Universe
  and TraceModel; not data, not behavior.
- **Carrier grade**: the ladder itself — graded structures, the same
  honesty discipline as `Kit.Correspondence` (each grade declares its
  strongest honest law; no pretending lossless).
- **Spine reading**: none — this is the delta substrate the spine's
  lanes ride, not a spine stage.
- **Ladder rung**: this file DEFINES the rungs; instances land at
  their highest honest rung (the worked instances below).
- **Gate rows**: the axiom report (`gates axioms`) over the law
  theorems + KitTests pins (positive + the mandatory negative
  controls: three non-climbable non-instances, PROVED).

THE TRICHOTOMY (notes/v3/03-bidirectional.md §7) is NOT collapsed here:
Δ is the DELTA of the trichotomy — an accepted net state change. A
COMMAND (requested intent, can fail/no-op) and an EVENT (recorded
occurrence with identity + causality) are different objects and get
different types downstream. `apply : S → Δ → Option S` is the delta's
application to a state — the Option is the honest totality (a delta
may not apply to a given state, e.g. a replacement whose −old row is
absent), NOT a command's failure to be accepted.

The two doctrine laws are STATED here at full generality, as
structures with the law as a field:
- the LOCAL MIGRATION equation — `Migration.local`:
  `migrate (applyOld s e) = applyNew (migrate s) (upcast e)`;
- the INCREMENTAL-DERIVATIVE shape — `ChangeFunctor.incremental`:
  `f (apply x dx) = apply (f x) (deriveChange f x dx)` — the derivative
  depends on the OLD INPUT x, not Δ alone.
Honest note (a note, not a stub): replay preservation ("follows ONCE
by induction") is NOT proved here — it needs `upcast` to respect
composition (`upcast (compose a b) = compose (upcast a) (upcast b)`),
extra structure on the delta side. It lands with the first consumer
that has a concrete migration (the leftover rule).

Worked instances, at their highest honest rung:
- `intAdd` — `Additive Int Int` (the full ladder; state and delta are
  the integers — Nat cannot host the group rung, it has no negatives,
  which is exactly the monus control's point).
- `monus` — `WithIdentity Nat Nat` (saturating subtraction: composes,
  has the no-op, NOT reversible — information is lost; proved).
- `fieldSet` — `Applicable Rec FieldDelta` ONLY (the doctrine's
  set-forgets-old-value example; the controls PROVE it can neither
  compose at this Δ nor reverse).

Core-only: no mathlib, no Batteries (the cone rule); the group laws
are discharged by `omega` over the prelude integers.
-/

namespace Kit

/-! ## Rung 1 — Applicable (a patch that applies) -/

/-- The bottom rung: a fallible application. The honest shape —
    `apply : S → Δ → Option S`; a delta may fail to apply to a given
    state (the option is the totality of application, never a
    command's acceptance). -/
structure Applicable (S Δ : Type) where
  apply : S → Δ → Option S

namespace Applicable

/-- The trivial change: Δ = Unit, application is the identity. -/
def unit (S : Type) : Applicable S Unit where
  apply s _ := some s

/-- Product lifting: the left delta applies first, then the right's —
    an ORDERED product, honest on both components' fallibility. -/
def prod (c : Applicable S Δ) (d : Applicable T Δ') :
    Applicable (S × T) (Δ × Δ') where
  apply p q :=
    (c.apply p.1 q.1).bind fun s => (d.apply p.2 q.2).map fun t => (s, t)

/-- Sum lifting: a delta applies only to its own summand. The
    mismatch case (state of one side, delta of the other) is `none` —
    the honest refusal, not a silent pass-through. -/
def sum (c : Applicable S Δ) (d : Applicable T Δ') :
    Applicable (S ⊕ T) (Δ ⊕ Δ') where
  apply st dt :=
    match st, dt with
    | .inl s, .inl e => (c.apply s e).map Sum.inl
    | .inr t, .inr e => (d.apply t e).map Sum.inr
    | _, _ => none

end Applicable

/-! ## Rung 2 — Composable (deltas compose: Δ₁;Δ₂) -/

/-- Adds composition with associativity, and application must respect
    it: applying the composite is applying in sequence. NOTE the
    honest gap: the laws tie `compose` to `apply` — this is
    composition of APPLIED deltas, not a bare monoid on Δ. -/
structure Composable (S Δ : Type) extends Applicable S Δ where
  compose : Δ → Δ → Δ
  assoc : ∀ a b c, compose (compose a b) c = compose a (compose b c)
  applyCompose : ∀ s a b,
    apply s (compose a b) = (apply s a).bind (apply · b)

namespace Composable

/-- Product lifting: pointwise composition; the law routes through
    both components. -/
def prod (c : Composable S Δ) (d : Composable T Δ') :
    Composable (S × T) (Δ × Δ') where
  apply p q :=
    (c.apply p.1 q.1).bind fun s => (d.apply p.2 q.2).map fun t => (s, t)
  compose p q := (c.compose p.1 q.1, d.compose p.2 q.2)
  assoc a b e := by
    show (c.compose (c.compose a.1 b.1) e.1, d.compose (d.compose a.2 b.2) e.2)
       = (c.compose a.1 (c.compose b.1 e.1), d.compose a.2 (d.compose b.2 e.2))
    rw [c.assoc, d.assoc]
  applyCompose p a b := by
    rw [c.applyCompose, d.applyCompose]
    cases hc : c.apply p.1 a.1 with
    | none => rfl
    | some s =>
      cases hd : d.apply p.2 a.2 with
      | none =>
          show (c.apply s b.1).bind (fun _ => none) = none
          cases c.apply s b.1 <;> rfl
      | some t => rfl

end Composable

/-! ## Rung 3 — WithIdentity (the no-op) -/

/-- Adds the no-op delta, with its laws BOTH as composition identity
    and as application behavior (`apply s nop = some s`). -/
structure WithIdentity (S Δ : Type) extends Composable S Δ where
  nop : Δ
  composeNopLeft : ∀ d, compose nop d = d
  composeNopRight : ∀ d, compose d nop = d
  applyNop : ∀ s, apply s nop = some s

/-! ## Rung 4 — Reversible (an inverse exists) -/

/-- Adds the inverse with the round-trip law: whatever the delta
    applied, the inverse undoes — back to the ORIGINAL state. This is
    the UPPER rung of the honest hierarchy (01-core §2): it requires
    the delta to retain old information. Inverses are DERIVED only
    where lawful — see `Additive` (derived from the group `neg`) and
    the negative controls below (monus, field-set: no lawful inverse,
    PROVED). -/
structure Reversible (S Δ : Type) extends WithIdentity S Δ where
  inv : Δ → Δ
  roundTrip : ∀ s d s', apply s d = some s' → apply s' (inv d) = some s

namespace Reversible

/-- The no-op is its own undo — as APPLIED. (`inv nop = nop` is NOT
    derivable here: `apply` need not be injective in Δ — two distinct
    deltas may apply identically.) -/
theorem apply_invNop (r : Reversible S Δ) (s : S) :
    r.apply s (r.inv r.nop) = some s :=
  r.roundTrip s r.nop s (r.applyNop s)

end Reversible

/-! ## Rung 5 — Commuting (disjoint changes commute) -/

/-- Adds a disjointness predicate and the commute law UNDER it.
    Parameterized by the disjointness, never global — the predicate is
    a FIELD, and the law holds only for disjoint pairs. (Global
    commutation is the additive rung's bonus, proved below as
    `Additive.bindComm`.) -/
structure Commuting (S Δ : Type) extends Reversible S Δ where
  Disjoint : Δ → Δ → Prop
  commute : ∀ s a b, Disjoint a b →
    (apply s a).bind (apply · b) = (apply s b).bind (apply · a)

/-! ## Rung 6 — Additive / group (the Z-set rung: dbsp) -/

/-- The additive rung: the INHERITED `compose` is an abelian group
    operation — commutative (`composeComm`), with the inherited `inv`
    as the compose-level inverse (`invLeft`/`invRight`). NO new
    operations: a fresh `add`/`neg` would duplicate `compose`/`inv`
    (the dupDefBodies lesson — the first version of this rung did
    exactly that and the linter caught it), so:
- composition commutes UNCONDITIONALLY (`bindComm` — no disjointness
    premise needed; this is what the group rung buys over `Commuting`);
- the compose-level inverse laws imply the apply-level round trip
    (`invRoundTrip`) — "inverses derived only where lawful".
    NOTE (03 §7): signed addition commutes but is NOT idempotent, and
    net-zero ≠ nothing happened — the trichotomy's event identity
    stays downstream, NOT in Δ. -/
structure Additive (S Δ : Type) extends Commuting S Δ where
  composeComm : ∀ a b, compose a b = compose b a
  invLeft : ∀ d, compose (inv d) d = nop
  invRight : ∀ d, compose d (inv d) = nop

namespace Additive

/-- The group action commutes — UNCONDITIONALLY (no disjointness
    predicate needed; this is what the group rung buys over
    `Commuting`). -/
theorem bindComm (g : Additive S Δ) (s : S) (a b : Δ) :
    (g.apply s a).bind (g.apply · b)
      = (g.apply s b).bind (g.apply · a) := by
  rw [← g.applyCompose, g.composeComm, g.applyCompose]

/-- The compose-level inverse laws imply the apply-level round trip:
    applying `d` then `inv d` returns the original state. (This is
    exactly `Reversible.roundTrip` — the additive rung's inverse laws
    FORCE it, which is what "the inverse is lawful here" means.) -/
theorem invRoundTrip (g : Additive S Δ) (s : S) (d : Δ) (s' : S)
    (h : g.apply s d = some s') :
    g.apply s' (g.inv d) = some s := by
  have h1 := g.applyCompose s d (g.inv d)
  rw [g.invRight, g.applyNop, h] at h1
  rw [Option.bind_some] at h1
  exact h1.symm

end Additive

/-! ## The poison-fold (the fallible composition's fold face) -/

/-- THE POISON-FOLD: fold the fallible steps left-to-right, the FIRST
    `none` poisons the whole fold. This is `apply : S → Δ → Option S`'s
    list face — the compose-with-failure discipline is the ladder's own
    operation (`Composable.applyCompose` binds two; this binds a
    list), so the helper lives HERE, never re-rolled. Three lanes
    instantiate it: the incremental checker's maintained folds
    (`SchemaCore.IncViolate`'s `accFold?`/`dangFold1?`) and the
    witnessed journal's application (`SchemaCore.Delta`'s
    `witnessedApply`). -/
def optionFoldl {α β : Type} (f : β → α → Option β) :
    List α → β → Option β
  | [], b => some b
  | a :: as, b => (f b a).bind (optionFoldl f as ·)

theorem optionFoldl_nil {α β : Type} (f : β → α → Option β) (b : β) :
    optionFoldl f [] b = some b := rfl

theorem optionFoldl_cons {α β : Type} (f : β → α → Option β)
    (a : α) (as : List α) (b : β) :
    optionFoldl f (a :: as) b = (f b a).bind (optionFoldl f as ·) := rfl

/-- THE POISON-FOLD'S COMPOSITION: the fold over a concatenation is
    the bind of the two folds (the `Composable.applyCompose` face, at
    the fold's granularity). -/
theorem optionFoldl_append {α β : Type} (f : β → α → Option β)
    (as bs : List α) (b : β) :
    optionFoldl f (as ++ bs) b
      = (optionFoldl f as b).bind (fun b' => optionFoldl f bs b') := by
  induction as generalizing b with
  | nil => simp [optionFoldl]
  | cons a rest ih =>
      rw [List.cons_append, optionFoldl_cons, optionFoldl_cons,
        Option.bind_assoc]
      simp only [ih]

/-- THE ONE AGREEMENT LEMMA (the lanes' parallel inductions, folded
    once): when each `some` step's image is related by `R` to the
    plain fold's step image, a `some` poison-fold output IS the plain
    fold's output, `R`-related. The lanes instantiate `R` with their
    maintained-vs-recomputed face (the table identity + the negative
    face's perm; the dangle filter's equality) and their step
    agreements discharge `hstep` — the induction happens ONCE here. -/
theorem optionFoldl_agree {α σ τ : Type}
    (f : σ → α → Option σ) (plain : τ → α → τ) (R : σ → τ → Prop)
    (hstep : ∀ a s t s', f s a = some s' → R s t → R s' (plain t a))
    (as : List α) (s : σ) (t : τ) (hR : R s t) :
    ∀ s', optionFoldl f as s = some s' →
      R s' (List.foldl plain t as) := by
  induction as generalizing s t with
  | nil =>
      intro s' h
      simp only [optionFoldl, Option.some.injEq] at h
      subst h
      exact hR
  | cons a rest ih =>
      intro s' h
      simp only [optionFoldl] at h
      cases hs : f s a with
      | none => simp [hs] at h
      | some s₁ =>
          simp only [hs, Option.bind_some] at h
          -- `List.foldl plain t (a :: rest)` whnf-reduces to
          -- `List.foldl plain (plain t a) rest` — the goal IS the
          -- induction's face (defeq, `List.foldl_cons`).
          exact ih s₁ (plain t a) (hstep a s t s₁ hs hR) s' h

/-! ## The two doctrine laws, stated at this generality -/

/-- THE LOCAL MIGRATION EQUATION (01-core §2):
    `migration (applyOld s e) = applyNew (migration s) (upcast e)` —
    Option-lifted for the fallible applies. A migration is a
    correspondence between two change structures; the equation is its
    law FIELD (a migration without the law is not constructible).
    (`localLaw`, not `local` — the latter is a Lean keyword.) -/
structure Migration (c : Applicable S₀ Δ₀) (d : Applicable S₁ Δ₁) where
  migrate : S₀ → S₁
  upcast : Δ₀ → Δ₁
  localLaw : ∀ s e,
    d.apply (migrate s) (upcast e) = (c.apply s e).map migrate

/-- THE INCREMENTAL-DERIVATIVE SHAPE (01-core §2):
    `f (apply x dx) = apply (f x) (deriveChange f x dx)` — the derived
    change depends on the OLD INPUT x, not Δ alone (fallibility
    Option-lifted on the outside). -/
structure ChangeFunctor (c : Applicable S Δ) (d : Applicable T Δ') where
  deriveChange : (S → T) → S → Δ → Δ'
  incremental : ∀ (f : S → T) (x : S) (dx : Δ),
    (c.apply x dx).map f = d.apply (f x) (deriveChange f x dx)

/-! ## Worked instance: the integers under addition (the full ladder) -/

/-- apply on the integers: total, never fails (the degenerate honest
    Option — always `some`). State AND delta are Int: the group rung
    needs negatives, which Nat does not have. -/
def intAddApply : Int → Int → Option Int := fun s d => some (s + d)

def intAddCompose : Int → Int → Int := fun a b => a + b

def intAddNeg : Int → Int := fun d => -d

theorem intAddCompose_assoc (a b c : Int) :
    intAddCompose (intAddCompose a b) c = intAddCompose a (intAddCompose b c) := by
  simp only [intAddCompose]; omega

theorem intAddApply_compose (s a b : Int) :
    intAddApply s (intAddCompose a b)
      = (intAddApply s a).bind (fun x => intAddApply x b) := by
  simp only [intAddApply, intAddCompose, Option.bind_some, Option.some.injEq]
  omega

theorem intAddCompose_nopLeft (d : Int) : intAddCompose 0 d = d := by
  simp only [intAddCompose]; omega

theorem intAddCompose_nopRight (d : Int) : intAddCompose d 0 = d := by
  simp only [intAddCompose]; omega

theorem intAddApply_nop (s : Int) : intAddApply s 0 = some s := by
  simp only [intAddApply, Option.some.injEq]; omega

theorem intAddCompose_comm (a b : Int) : intAddCompose a b = intAddCompose b a := by
  simp only [intAddCompose]; omega

theorem intAdd_invLeft (d : Int) : intAddCompose (intAddNeg d) d = 0 := by
  simp only [intAddCompose, intAddNeg]; omega

theorem intAdd_invRight (d : Int) : intAddCompose d (intAddNeg d) = 0 := by
  simp only [intAddCompose, intAddNeg]; omega

/-- The full-ladder instance: `Additive Int Int`. Every lower rung's
    fields are discharged along the way; the additive rung adds ONLY
    laws (commutativity + the compose-level inverse) over the
    inherited operation — no parallel `add`. -/
def intAdd : Additive Int Int where
  apply := intAddApply
  compose := intAddCompose
  assoc := intAddCompose_assoc
  applyCompose := intAddApply_compose
  nop := 0
  composeNopLeft := intAddCompose_nopLeft
  composeNopRight := intAddCompose_nopRight
  applyNop := intAddApply_nop
  inv := intAddNeg
  -- roundTrip/commute are NOT hand omega scripts here: both are
  -- DERIVED from the sibling fields by exactly the derivation the
  -- generic laws catalog (`Additive.invRoundTrip` / `Additive.bindComm`
  -- — one proof path; the instance cannot cite them, being their
  -- subject, so the derivation is inlined at the fields and the
  -- STANDALONE statements live only in the Additive namespace).
  roundTrip := by
    intro s d s' h
    have h1 := intAddApply_compose s d (intAddNeg d)
    rw [intAdd_invRight, intAddApply_nop, h] at h1
    rw [Option.bind_some] at h1
    exact h1.symm
  Disjoint _ _ := True
  commute s a b _ := by
    rw [← intAddApply_compose, intAddCompose_comm, intAddApply_compose]
  composeComm := intAddCompose_comm
  invLeft := intAdd_invLeft
  invRight := intAdd_invRight

/-! ## Worked instance: saturating subtraction (climbs to
     WithIdentity, NOT reversible) -/

/-- monus: `apply s d = some (s - d)` — truncated Nat subtraction.
    Composes as `a + b` (the monus law `(s - a) - b = s - (a + b)`),
    no-op `0`. NOT reversible: the delta forgets what was subtracted —
    `monus_notReversible` below is the proof obligation. -/
def monusApply : Nat → Nat → Option Nat := fun s d => some (s - d)

/-- (the body is `Nat.add` BY NAME — a lambda copy would be an
    alpha-twin of grind's internal `Lean.Grind.offset`; the named
    reference is both cleaner and dedup-clean) -/
def monusCompose : Nat → Nat → Nat := Nat.add

/-- `Nat.add` is `+` definitionally, but omega/simp only recognize the
    `HAdd` SYNTAX — this `rfl` bridge rewrites the named reference back
    to the recognized form (the `monusCompose := Nat.add` discipline's
    price, paid once here). -/
private theorem natAdd_eq (a b : Nat) : Nat.add a b = a + b := rfl

theorem monusCompose_assoc (a b c : Nat) :
    monusCompose (monusCompose a b) c = monusCompose a (monusCompose b c) := by
  simp only [monusCompose, natAdd_eq]; omega

theorem monusApply_compose (s a b : Nat) :
    monusApply s (monusCompose a b)
      = (monusApply s a).bind (fun x => monusApply x b) := by
  simp only [monusApply, monusCompose, natAdd_eq, Option.bind_some, Option.some.injEq]
  omega

theorem monusCompose_nopLeft (d : Nat) : monusCompose 0 d = d := by
  simp only [monusCompose, natAdd_eq]; omega

theorem monusCompose_nopRight (d : Nat) : monusCompose d 0 = d := by
  simp only [monusCompose, natAdd_eq]; omega

theorem monusApply_nop (s : Nat) : monusApply s 0 = some s := by
  simp only [monusApply, Option.some.injEq]; omega

def monus : WithIdentity Nat Nat where
  apply := monusApply
  compose := monusCompose
  assoc := monusCompose_assoc
  applyCompose := monusApply_compose
  nop := 0
  composeNopLeft := monusCompose_nopLeft
  composeNopRight := monusCompose_nopRight
  applyNop := monusApply_nop

/-- NEGATIVE CONTROL (the rung is real): NO `inv : Nat → Nat` satisfies
    the round-trip law for monus — subtracting 5 from 3 lands on 0,
    and nothing subtracted from 0 returns 3. The inverse is UNLAWFUL,
    so the `Reversible` field is unconstructible at this Δ. -/
theorem monus_notReversible :
    ¬ ∃ inv : Nat → Nat,
      ∀ s d s', monusApply s d = some s' → monusApply s' (inv d) = some s := by
  rintro ⟨inv, h⟩
  have h0 := h 3 5 0 rfl
  obtain ⟨n, hn⟩ : ∃ n, inv 5 = n := ⟨_, rfl⟩
  rw [hn] at h0
  simp only [monusApply, Option.some.injEq] at h0
  omega

/-! ## Worked instance: the record field-set (Applicable ONLY) -/

/-- The doctrine's star example (01-core §2): `set name := "Alice"`
    forgets the old name unless the delta stores it. Minimal honest
    shape: a two-field record, deltas as (field, new-value) pairs —
    the OLD VALUE IS NOT IN THE DELTA. -/
structure Rec where
  name : Nat
  email : Nat
deriving DecidableEq, Repr, BEq

inductive Field where
  | name | email
deriving DecidableEq, Repr, BEq

/-- A field-set delta: `set f := v`. The old value is FORGOTTEN. -/
abbrev FieldDelta := Field × Nat

def fieldSetApply : Rec → FieldDelta → Option Rec
  | r, (.name, v) => some { r with name := v }
  | r, (.email, v) => some { r with email := v }

/-- The bottom-rung instance. WHY it can't climb (proved below):
- NOT composable AT THIS Δ — one field-set cannot be the net of two
    field-sets on DIFFERENT fields; the honest climb needs
    `List FieldDelta` (or old-value retention), a different Δ;
- NOT reversible at any shape — the round-trip law forces the delta
    to retain old information, which a field-set does not. -/
def fieldSet : Applicable Rec FieldDelta where
  apply := fieldSetApply

/-- NEGATIVE CONTROL: no composition of field-sets satisfies
    `applyCompose` — the composite of a name-set and an email-set
    changes BOTH fields, but a single field-set changes exactly one.
    The `Composable` law field is unconstructible at this Δ. -/
theorem fieldSet_notComposable :
    ¬ ∃ compose : FieldDelta → FieldDelta → FieldDelta,
      ∀ s a b, fieldSetApply s (compose a b)
        = (fieldSetApply s a).bind (fieldSetApply · b) := by
  rintro ⟨compose, h⟩
  have hr := h ⟨0, 0⟩ (Field.name, 1) (Field.email, 2)
  revert hr
  cases hw : compose (Field.name, 1) (Field.email, 2) with
  | mk f v =>
      intro hr
      cases f <;> simp [fieldSetApply] at hr

/-- NEGATIVE CONTROL: no inverse satisfies the round-trip law for
    field-sets — the two source states ⟨0,0⟩ and ⟨9,0⟩ both map to the
    SAME image under `set name := 7`, and one fixed `inv (name, 7)`
    cannot restore both. (Even a composable List-Δ would still fail
    this: the old value is not in the delta.) -/
theorem fieldSet_notReversible :
    ¬ ∃ inv : FieldDelta → FieldDelta,
      ∀ s d s', fieldSetApply s d = some s' →
        fieldSetApply s' (inv d) = some s := by
  rintro ⟨inv, h⟩
  have h0 := h ⟨0, 0⟩ (Field.name, 7) ⟨7, 0⟩ rfl
  have h1 := h ⟨9, 0⟩ (Field.name, 7) ⟨7, 0⟩ rfl
  revert h0 h1
  cases hw : inv (Field.name, 7) with
  | mk f v =>
      intro h0 h1
      cases f <;> simp [fieldSetApply] at h0 h1 <;> omega

end Kit
