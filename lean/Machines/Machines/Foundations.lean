/-
# Machines.Foundations — the construct kit

The isomorphic primitives everything in the workspace builds on
(notes/lean/TOOLKIT.md Part 2): the three correspondence shapes (laws attach
to the SHAPE, not to each instance) and the Fin-indexed DAG with decidable
acyclicity.

## The correspondence shapes

Every boundary in the system is one of these three:

- `Iso` — true bijection (rare).
- `PartialIso` — decode can fail; `decode∘encode = id` is the one-ended law
  (wire bytes ↔ typed value).
- `Denotes` + `ReprOp` — abstraction: many representations, one semantics.
  THE shape for this engine (delta buffers, overlays, encoded columns).
  The law lives on operations: one commuting square per operation.

Squares compose (`ReprOp.comp`): the composite's proof is the composed
proofs — nobody re-proves (TOOLKIT §4.1).

## The DAG

`Dag n` uses `Fin n` indexing: dangling edges are unrepresentable.
Acyclicity is decidable — `checkAcyclic` — so concrete DAGs discharge with
`decide` at elaboration. Soundness of the fueled check is proved
(`reachesFuel_sound`); completeness (fuel `n` suffices) is the exhaustive
executable check in Tests until the shortest-path proof lands.
-/

import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Tactic.Linter.Style
import Mathlib.Logic.Function.Iterate

namespace Machines

/-! ## Correspondence -/

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

/-! ## The Fin-indexed DAG -/

/-- A directed graph on `n` nodes. `deps v` = the nodes `v` depends on.
    `Fin n` indexing: an edge to a nonexistent node is unrepresentable. -/
structure Dag (n : Nat) where
  deps : Fin n → List (Fin n)

namespace Dag

variable {n : Nat} (d : Dag n)

/-- Reachability along `deps` (the Prop). -/
inductive Reachable : Fin n → Fin n → Prop
  | step {a b : Fin n} (h : b ∈ d.deps a) : Reachable a b
  | trans {a b c : Fin n} : Reachable a b → Reachable b c → Reachable a c

/-- Decidable reachability with fuel (the Bool check). Any path is found
    within `n` steps, so `reachesFuel d n` is exact; soundness is proved
    here, completeness is the executable check in Tests (the package rule:
    an unproved theorem becomes an executable check). -/
def reachesFuel : Nat → Fin n → Fin n → Bool
  | 0, _, _ => false
  | fuel + 1, a, b => (d.deps a).any (fun c => c == b || reachesFuel fuel c b)

theorem reachesFuel_sound {fuel : Nat} {a b : Fin n} :
    d.reachesFuel fuel a b = true → d.Reachable a b := by
  induction fuel generalizing a b with
  | zero => intro h; simp [reachesFuel] at h
  | succ fuel ih =>
    intro h
    simp only [reachesFuel, List.any_eq_true] at h
    obtain ⟨c, hc, hcb⟩ := h
    have hca : d.Reachable a c := .step hc
    cases hceq : c == b with
    | true =>
      have hcb' : c = b := beq_iff_eq.mp hceq
      subst hcb'; exact hca
    | false =>
      have hrec : d.reachesFuel fuel c b = true := by
        have := hcb
        rw [hceq, Bool.false_or] at this
        exact this
      exact .trans hca (ih hrec)

/-- No node reaches itself. -/
def Acyclic : Prop := ∀ v, ¬ d.Reachable v v

/-- The decidable check. Discharge concrete instances with `decide`.
    The bridge theorem (`checkAcyclic = true ↔ Acyclic`) needs completeness
    of the fueled check; until that proof lands, agreement with a reference
    transitive closure is verified exhaustively over small DAGs in Tests. -/
def checkAcyclic : Bool :=
  (List.finRange n).all (fun v => d.reachesFuel n v v == false)

/-- Kahn-flavored topological sort: repeatedly emit every node whose deps
    are already emitted (in `finRange` order — deterministic). `none` on a
    cycle (or on fuel exhaustion, which can't happen on a DAG). -/
def topoSort? (d : Dag n) : Option (List (Fin n)) := go d (n + 1) []
where
  go (d : Dag n) : Nat → List (Fin n) → Option (List (Fin n))
    | 0, _ => none
    | fuel + 1, emitted =>
      let avail := (List.finRange n).filter
        (fun v => v ∉ emitted && (d.deps v).all (· ∈ emitted))
      if avail.isEmpty then
        if emitted.length == n then some emitted else none
      else go d fuel (emitted ++ avail)

/-- What a topological order MEANS (the correctness property; the proof
    and the executable check live with it in Tests). -/
def IsTopoOrder (l : List (Fin n)) : Prop :=
  l.Nodup ∧ (∀ v : Fin n, v ∈ l) ∧
  ∀ (v : Fin n), ∀ d' ∈ d.deps v, ∀ (i j : Nat),
    l[i]? = some d' → l[j]? = some v → i < j

end Dag

/-! ## BoundedFix — fuel-bounded iteration with a convergence witness

The one combinator behind every "iterate until converged, with a cap"
story in the workspace: the cascade exec loop (Flatland.Cascade.fixFuel
is this with `converged := eqb x (step x)`), convergence variants
(Machines.Convergent), Dag reachability fuel, pregel pass budgets.
Soundness attaches ONCE here: a returned value is an iterate of the
initial value AND passes the convergence check; callers discharge
`converged`-soundness (the check implies fixpoint) at instantiation. -/

/-- Iterate `step` from `init`, stopping when `converged` holds; `none`
    when fuel runs out. The cap is a tripwire, not semantics (SPEC §7.5). -/
def iterateBounded (step : α → α) (converged : α → Bool) : Nat → α → Option α
  | 0, _ => none
  | fuel + 1, x => if converged x then some x else iterateBounded step converged fuel (step x)

/-- Soundness: a returned value is an iterate and passes the check. -/
theorem iterateBounded_sound {step : α → α} {converged : α → Bool} :
    ∀ fuel init y, iterateBounded step converged fuel init = some y →
      ∃ n, y = step^[n] init ∧ converged y = true := by
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
      calc y = step^[n] (step init) := hn
        _ = step^[n + 1] init := (Function.iterate_succ_apply step n init).symm

end Machines
