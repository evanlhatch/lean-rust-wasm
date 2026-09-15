/-
# CodegenCore.Kit — the correspondence kit

The agreement-theorem vocabulary (lean-cohesion-plan §0): laws attach to
SHAPES, not instances. Moved from Machines.Foundations (the Dag STAYS there).
Core-only by design: mathlib's `Function.iterate` becomes the local `iterateN`.
-/

namespace CodegenCore

/-- True bijection. Rare, precious. (`to`/`inv`, not `to`/`from`:
    `from` is a reserved token in Lean 4.) -/
structure Iso (A B : Type) where
  to : A → B
  inv : B → A
  to_inv : ∀ b, to (inv b) = b
  inv_to : ∀ a, inv (to a) = a

namespace Iso

def refl : Iso A A := ⟨_root_.id, _root_.id, fun _ => rfl, fun _ => rfl⟩

def symm (i : Iso A B) : Iso B A where
  to := i.inv; inv := i.to
  to_inv := i.inv_to; inv_to := i.to_inv

/-- Isos compose; the laws compose with them. -/
def trans (i₁ : Iso A B) (i₂ : Iso B C) : Iso A C where
  to := i₂.to ∘ i₁.to
  inv := i₁.inv ∘ i₂.inv
  to_inv := fun c => by
    show i₂.to (i₁.to (i₁.inv (i₂.inv c))) = c
    rw [i₁.to_inv, i₂.to_inv]
  inv_to := fun a => by
    show i₁.inv (i₂.inv (i₂.to (i₁.to a))) = a
    rw [i₂.inv_to, i₁.inv_to]

end Iso

/-- Partial correspondence: decode may fail; encode is a section.
    The law is one-ended (`decode∘encode = id`): the wire may have
    non-canonical encodings, but everything we emit decodes back. -/
structure PartialIso (A B : Type) where
  decode : A → Option B
  encode : B → A
  decode_encode : ∀ b, decode (encode b) = some b

namespace PartialIso

/-- Partial isos compose through `Option.bind`. -/
def trans (p₁ : PartialIso A B) (p₂ : PartialIso B C) : PartialIso A C where
  decode := fun a => (p₁.decode a).bind p₂.decode
  encode := p₁.encode ∘ p₂.encode
  decode_encode := by
    intro c
    show ((p₁.decode (p₁.encode (p₂.encode c))).bind p₂.decode) = some c
    rw [p₁.decode_encode]
    exact p₂.decode_encode c

end PartialIso

/-- Abstraction: the representation determines its semantics (`outParam`).
    No inverse exists; the law lives on operations (`ReprOp`). -/
class Denotes (R : Type) (A : outParam Type) where
  abs : R → A

/-- A representation-respecting operation: the commuting square
    `abs(opR r) = opA (abs r)`. One per operation that moves through
    the representation; each is a theorem shape for primitives and a
    generated differential test for composed paths. -/
structure ReprOp (R A : Type) [Denotes R A] where
  opR : R → R
  opA : A → A
  respects : ∀ r, Denotes.abs (opR r) = opA (Denotes.abs r)

namespace ReprOp

variable [Denotes R A]

/-- Vertical composition of squares: if both commute, the composite commutes. -/
def comp (o₁ o₂ : ReprOp R A) : ReprOp R A where
  opR := o₁.opR ∘ o₂.opR
  opA := o₁.opA ∘ o₂.opA
  respects := fun r => by
    show Denotes.abs (o₁.opR (o₂.opR r)) = o₁.opA (o₂.opA (Denotes.abs r))
    rw [o₁.respects, o₂.respects]

/-- The identity square. -/
def id : ReprOp R A where
  opR := _root_.id; opA := _root_.id
  respects := fun _ => rfl

end ReprOp

/-- The completeness half of a `CheckedProp`, as DATA. `missing` is the
    loud, greppable declaration "this gate is one-directional — the checker
    may reject valid inputs". (The `Option (complete proof)` shape was the
    first design; `Option : Type → Type` cannot carry a Prop without a
    `PLift` wrapper, and that noise at every construction site is worse
    than a two-constructor inductive.) -/
inductive CheckedProp.Completeness {α : Type} (P : α → Prop) (check : α → Bool) : Type where
  | missing : Completeness P check
  | proved : (∀ a, P a → check a = true) → Completeness P check

/-- A proposition with an executable checker. Soundness is mandatory — a
    `true` verdict is a proof. Completeness is a constructor choice with NO
    default: every construction must write `.proved h` or `.missing`, so a
    one-directional gate is declared, never implied. `ofComplete` is the
    both-ways constructor; `isComplete` is the loud flag. -/
structure CheckedProp (α : Type) where
  P : α → Prop
  check : α → Bool
  sound : ∀ a, check a = true → P a
  complete? : CheckedProp.Completeness P check

namespace CheckedProp

/-- Both-ways construction: the common case. -/
def ofComplete (P : α → Prop) (check : α → Bool)
    (sound : ∀ a, check a = true → P a) (complete : ∀ a, P a → check a = true) :
    CheckedProp α :=
  ⟨P, check, sound, .proved complete⟩

/-- The verdict decides the proposition when completeness is present. -/
theorem check_iff (c : CheckedProp α) (h : ∀ a, c.P a → c.check a = true) (a : α) :
    c.check a = true ↔ c.P a :=
  ⟨c.sound a, h a⟩

/-- Loud completeness flag: `false` means soundness-only. -/
def isComplete (c : CheckedProp α) : Bool :=
  match c.complete? with
  | .missing => false
  | .proved _ => true

end CheckedProp

/-- Bounded iteration's witness type. mathlib's `Function.iterate` (`^[n]`)
    is NOT core; the kit is core-only, so the five-line local iterate it is.
    Tail shape (`iterateN f (n+1) x = iterateN f n (f x)` definitionally) —
    the step lemma is `rfl`. -/
def iterateN (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateN f n (f x)

@[simp] theorem iterateN_zero (f : α → α) (x : α) : iterateN f 0 x = x := rfl

@[simp] theorem iterateN_succ (f : α → α) (n : Nat) (x : α) :
    iterateN f (n + 1) x = iterateN f n (f x) := rfl

/-- Iterate `step` from `init`, stopping when `converged` holds; `none`
    when fuel runs out. The cap is a tripwire, not semantics. Soundness
    attaches ONCE here: a returned value is an iterate of the initial value
    AND passes the convergence check; callers discharge `converged`-
    soundness (the check implies fixpoint) at instantiation. -/
def iterateBounded (step : α → α) (converged : α → Bool) : Nat → α → Option α
  | 0, _ => none
  | fuel + 1, x => if converged x then some x else iterateBounded step converged fuel (step x)

-- the @[simp] equation set for the recursive def (the package discipline).
@[simp] theorem iterateBounded_zero (step : α → α) (converged : α → Bool) (init : α) :
    iterateBounded step converged 0 init = none := rfl

@[simp] theorem iterateBounded_succ (step : α → α) (converged : α → Bool) (fuel : Nat) (init : α) :
    iterateBounded step converged (fuel + 1) init =
      if converged init then some init else iterateBounded step converged fuel (step init) := rfl

/-- Soundness: a returned value is an iterate and passes the check. -/
theorem iterateBounded_sound {step : α → α} {converged : α → Bool} :
    ∀ fuel init y, iterateBounded step converged fuel init = some y →
      ∃ n, y = iterateN step n init ∧ converged y = true := by
  intro fuel
  induction fuel with
  | zero => intro init y h; simp [iterateBounded] at h
  | succ fuel ih =>
    intro init y h
    rw [iterateBounded] at h
    by_cases hconv : converged init = true
    · rw [if_pos hconv] at h
      have : init = y := Option.some.inj h
      subst this
      exact ⟨0, rfl, hconv⟩
    · rw [if_neg hconv] at h
      obtain ⟨n, hn, hc⟩ := ih (step init) y h
      refine ⟨n + 1, ?_, hc⟩
      calc y = iterateN step n (step init) := hn
        _ = iterateN step (n + 1) init := rfl

end CodegenCore
