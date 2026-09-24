/-
# Cost.Basic — the cost model + the grading discipline

The quantitative-semantics foundation (the reviews' fourth verification
dimension: costs, latency, memory, retries, budgets need COMPOSITION
LAWS, not just Nat fields — same program, additional lawful
interpretation, exposed only when requested).

Two pieces, honest-minimal:

- **The cost model** (`CostModel`): the cost type + the zero + the
  composition (associative, zero-united) + the MONOTONICITY discipline:
  composition is monotone in the second argument — more subwork never
  decreases the composed cost. The canonical instance is `natCost` (Nat
  costs, addition); the parameterized shape is kept because the model,
  not the carrier, is what the laws cite.
- **The grading discipline** (`Graded`): a graded evaluation carries
  the cost ALONGSIDE the value — the writer shape, `val` + `cost`, with
  `Graded.bind` composing the two carriers (the value flows through
  `f`; the costs compose through the model). Grading adds annotation,
  never control: no Option, no early exit — the cost is a lawful
  annotation on the SAME program.

Doctrine slots (notes/v3/01-core.md): the five questions —
- **Root**: Universe (data) — costs are monotone-consumption data, NOT
  a root (01 §1: "resources are not a root: fuel/budgets/size =
  monotone consumption, a Change instance (monus)"). The monus tie
  lives in `Cost.Budget`.
- **Carrier grade**: the writer shape over `CostModel` — same program,
  additional lawful interpretation (01 §4's "same result after hiding
  instrumentation" is the Budget/observer's face; here: same VALUE,
  plus the composed cost).
- **Spine reading**: none — this is annotation substrate the lanes'
  interpretation pairs ride.
- **Ladder rung**: hand theorems of the small generic kind (01 §7) —
  the bind laws, proved once at the structure, cited everywhere after.
- **Gate rows**: the axiom report over the law theorems + CostTests
  pins (positive + the mandatory negative controls).

Core-only: no mathlib, no Batteries (the cone rule).
-/

namespace Cost

/-! ## The cost model -/

/-- The cost model: a type of costs + the zero + the composition, with
    the discipline the laws cite — associativity, the zero units, and
    MONOTONICITY in the second argument (more subwork never decreases
    the composed cost). -/
structure CostModel (C : Type) [LE C] where
  /-- The zero cost: the pure step. -/
  zero : C
  /-- The composition: two sequential costs, one cost. -/
  compose : C → C → C
  /-- Composition associates — nested programs' costs add in either
      nesting. -/
  compose_assoc : ∀ a b c, compose (compose a b) c = compose a (compose b c)
  /-- The zero is the left unit. -/
  compose_zeroLeft : ∀ a, compose zero a = a
  /-- The zero is the right unit. -/
  compose_zeroRight : ∀ a, compose a zero = a
  /-- The monotonicity discipline: composition is monotone in the
      second argument (the first argument's work is already spent). -/
  mono : ∀ a b₁ b₂, b₁ ≤ b₂ → compose a b₁ ≤ compose a b₂

namespace NatCost

/-- The body is `Nat.add` BY NAME — a lambda copy would be an
    alpha-twin of `Nat.add` (the dupDefBodies class; the same
    discipline as `Kit.Change.monusCompose`). -/
def compose : Nat → Nat → Nat := Nat.add

theorem compose_assoc (a b c : Nat) :
    compose (compose a b) c = compose a (compose b c) := by
  show a + b + c = a + (b + c)
  omega

theorem compose_zeroLeft (a : Nat) : compose 0 a = a := by
  show 0 + a = a
  omega

theorem compose_zeroRight (a : Nat) : compose a 0 = a := by
  show a + 0 = a
  omega

theorem mono (a b₁ b₂ : Nat) (h : b₁ ≤ b₂) : compose a b₁ ≤ compose a b₂ := by
  show a + b₁ ≤ a + b₂
  omega

end NatCost

/-- The canonical instance: Nat costs, addition. -/
def natCost : CostModel Nat where
  zero := 0
  compose := NatCost.compose
  compose_assoc := NatCost.compose_assoc
  compose_zeroLeft := NatCost.compose_zeroLeft
  compose_zeroRight := NatCost.compose_zeroRight
  mono := NatCost.mono

/-! ## The graded carrier (the writer shape) -/

/-- The graded carrier: the value ALONGSIDE the cost. The cost is a
    lawful annotation — it never replaces, filters, or controls the
    value (grading adds annotation, never control). -/
structure Graded (C : Type) (α : Type) where
  /-- The value: the plain semantics' result, untouched. -/
  val : α
  /-- The cost: the composition of the primitives' costs so far. -/
  cost : C

/-- The pure step: a value at the model's zero cost. -/
def Graded.pure {C : Type} [LE C] (m : CostModel C) (a : α) : Graded C α :=
  ⟨a, m.zero⟩

/-- The graded bind: the value flows through `f`; the costs COMPOSE
    through the model. This is the composition law's carrier — a nested
    program's cost is the model-composition of its parts' costs, never
    a silent undercount. (`f g.val` is computed once per projection;
    grading is pure, the two reads denote one computation.) -/
def Graded.bind {C : Type} [LE C] (m : CostModel C) {α β : Type}
    (g : Graded C α) (f : α → Graded C β) : Graded C β where
  val := (f g.val).val
  cost := m.compose g.cost (f g.val).cost

/-! ## The bind laws (proved once at the structure) -/

/-- The left writer law: sequencing from a pure step is `f` itself —
    the zero cost's unit law, read through the carrier. -/
theorem Graded.pure_bind {C : Type} [LE C] (m : CostModel C)
    {α β : Type} (f : α → Graded C β) (a : α) :
    (Graded.pure m a).bind m f = f a := by
  show (⟨(f a).val, m.compose m.zero (f a).cost⟩ : Graded C β) = f a
  rw [m.compose_zeroLeft]

/-- The right writer law: sequencing a pure step after `g` changes
    nothing — including the cost. -/
theorem Graded.bind_pure {C : Type} [LE C] (m : CostModel C)
    {α : Type} (g : Graded C α) :
    g.bind m (Graded.pure m) = g := by
  obtain ⟨v, c⟩ := g
  show (⟨v, m.compose c m.zero⟩ : Graded C α) = ⟨v, c⟩
  rw [m.compose_zeroRight]

/-- THE composition law (the associativity the reviews demand): a
    nested program's cost is the model-composition of its parts' costs
    in EITHER nesting — the models' `compose_assoc`, cited. -/
theorem Graded.bind_assoc {C : Type} [LE C] (m : CostModel C)
    {α β γ : Type} (g : Graded C α) (f : α → Graded C β)
    (h : β → Graded C γ) :
    (g.bind m f).bind m h = g.bind m (fun x => (f x).bind m h) := by
  obtain ⟨v, c⟩ := g
  show (⟨(h (f v).val).val, m.compose (m.compose c (f v).cost) (h (f v).val).cost⟩ : Graded C γ)
     = ⟨(h (f v).val).val, m.compose c (m.compose (f v).cost (h (f v).val).cost)⟩
  rw [m.compose_assoc]

end Cost
