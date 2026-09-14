/-
# Proofkit.ImplementedBy — the oracle-eval pattern (TOOLKIT 4)

flatland's rule: model stupid-clear, PROVE slow = fast, RUN fast. The
spec keeps the legible definition; `@[implemented_by]` swaps the runtime
to the optimized one; the equality is a theorem here, so the swap is
checked — not trusted.

The demonstration (the audit's item: zero uses — this is the one site):
`sumToSpec` is the fold (the oracle's eval shape — legible, obviously
correct); `sumTo` is the accumulator version (tail-recursive, the
runtime shape); `sumToFast_spec` is the checked bridge.

Deliberately absent: the pattern is for EVAL paths with an honest
implementation gap (fold vs accumulator, naive vs memoized). A one-line
`rfl` pair doesn't need the attribute.
-/

namespace Proofkit

/-- The REFERENCE (stupid-clear): sum 1..n by the definition. The
    oracle-eval shape — legible, never run in anger once the bridge is
    proved. -/
def sumToRef : Nat → Nat
  | 0 => 0
  | n + 1 => sumToRef n + (n + 1)

/-- The FAST model: tail-recursive accumulator — the runtime shape. -/
def sumTo (n : Nat) : Nat := go 0 n
where go (acc k : Nat) : Nat :=
  match k with
  | 0 => acc
  | k + 1 => go (acc + (k + 1)) k

/-- THE BRIDGE: fast = reference, for every input. The `@[implemented_by]`
    swap below is checked by THIS, not by convention. -/
theorem sumToFast_spec : ∀ n, sumTo n = sumToRef n := by
  intro n
  have hgo : ∀ acc k, sumTo.go acc k = acc + sumToRef k := by
    intro acc k
    induction k generalizing acc with
    | zero => simp [sumTo.go, sumToRef]
    | succ j ih => simp only [sumTo.go, sumToRef, ih]; omega
  simp [sumTo, hgo]

/-- The swap: the spec stays the fold; the runtime takes `sumTo`. -/
@[implemented_by sumTo]
def sumToSpec (n : Nat) : Nat := sumToRef n

end Proofkit
