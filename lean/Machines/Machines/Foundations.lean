/-
# Machines.Foundations — the Fin-indexed DAG + kit re-export

The correspondence kit (`Iso`/`PartialIso`/`Denotes`/`ReprOp`/`CheckedProp`/
`iterateBounded`) moved to `CodegenCore.Kit` (W1.1: the kit needs zero
mathlib; this package has it). Re-exported below so the `Machines.` names
keep working for downstream. What STAYS here: the `Dag` with decidable
acyclicity (Machines-owned; `Fin n` indexing makes dangling edges
unrepresentable; `checkAcyclic` discharges concrete DAGs by `decide`).
The two mathlib LINTER imports register the package's lint config — they
serve neither the kit nor the Dag.
-/

import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Tactic.Linter.Style
import CodegenCore.Kit
import Batteries

library_note machineAssemblePattern /--
  The veil Assemble pattern: a generated inductive for `Machine.Label` means
  proofs case-split and execution enumerate the SAME generated set of labels;
  they cannot drift. This is the two-projections core: Projection 1 (executable:
  `step?`, `run`) and Projection 2 (proof: `tr`) both consume the same labels,
  so execution and verification stay aligned.
-/

namespace Machines

/-- W1.1 re-export: the kit's home is CodegenCore (core-only); the
    `Machines.` aliases keep every existing use compiling. `abbrev` (not
    `export` — core Lean 4 has no `export` command): reducible, so instance
    search and anonymous constructors see through them (the AGENTS.md
    abbrev rule). Dotted names do NOT unfold aliases, so the member names
    (`Denotes.abs`, `Iso.trans`, …) get their own one-line aliases. -/
abbrev Iso := CodegenCore.Iso
abbrev Iso.refl := @CodegenCore.Iso.refl
abbrev Iso.symm := @CodegenCore.Iso.symm
abbrev Iso.trans := @CodegenCore.Iso.trans
abbrev PartialIso := CodegenCore.PartialIso
abbrev PartialIso.trans := @CodegenCore.PartialIso.trans
abbrev Denotes := CodegenCore.Denotes
abbrev Denotes.abs := @CodegenCore.Denotes.abs
abbrev ReprOp := @CodegenCore.ReprOp
abbrev ReprOp.comp := @CodegenCore.ReprOp.comp
abbrev ReprOp.id := @CodegenCore.ReprOp.id
abbrev CheckedProp := CodegenCore.CheckedProp
abbrev CheckedProp.ofComplete := @CodegenCore.CheckedProp.ofComplete
abbrev CheckedProp.check_iff := @CodegenCore.CheckedProp.check_iff
abbrev CheckedProp.isComplete := @CodegenCore.CheckedProp.isComplete
abbrev iterateN := @CodegenCore.iterateN
abbrev iterateBounded := @CodegenCore.iterateBounded
abbrev iterateBounded_sound := @CodegenCore.iterateBounded_sound

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

-- the @[simp] equation set for the recursive def (the package discipline).
@[simp] theorem reachesFuel_zero (a b : Fin n) : d.reachesFuel 0 a b = false := rfl

@[simp] theorem reachesFuel_succ (fuel : Nat) (a b : Fin n) :
    d.reachesFuel (fuel + 1) a b =
      (d.deps a).any (fun c => c == b || d.reachesFuel fuel c b) := rfl

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

end Dag

/-! ## BoundedFix — see CodegenCore.Kit

`iterateBounded` + `iterateBounded_sound` moved to the kit; the aliases
above keep `Machines.iterateBounded` working. The design note stands: the
one combinator behind every "iterate until converged, with a cap" story
(the cascade exec loop, Convergent, Dag fuel, pregel pass budgets). -/

end Machines
