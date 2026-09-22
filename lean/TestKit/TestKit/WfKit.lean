/-
# TestKit.WfKit — the rung-bridge discharge kit (`wf_split`)

The checker↔relation bridges (`Wf.lean`'s family and its lane
siblings — `Keys`, `TableInvariant`) repeat ONE boilerplate shape on
the "diagnostic-pushed" arms: the LHS is a pushed diagnostic list that
can never equal `[]` (the checker found something), while the RHS's
existential/conjunctive claim refutes against the already-`cases`'d
context (or the Bool-gate's `by_cases` riptide). The hand-written pair
`⟨fun hc => absurd hc (List.cons_ne_nil _ _), fun hok => by obtain
⟨w, h1, _⟩ := hok; cases h1⟩` (and its arity/some-variants) repeated
verbatim across every lane. `wf_split` discharges the pair in one
call:

```lean
theorem keyFieldDiags_eq_nil_iff ... := by
  ...
  | none => wf_split
```

Mechanically: `constructor` splits the `Iff`; the forward direction
`exact absurd hc (List.cons_ne_nil _ _)` needs only the LHS to reduce
to a cons (definitional — the pushed match/`++` forms are
constructor-headed, so no unfold argument is needed); the backward
direction destructs the claim with `contradiction` (constructor-mismatch
equalities — `none = some w`, `.variant … = .record …` — are directly
absurd) and falls back to `simp_all` for the injected variants (`some
a = some b` + a `by_cases` negation, the pushed `++` forms, the
multi-binder spines). Both routes are kernel-checked — this kit
introduces NO new trust base and NO axiom surface.

Deliberate exclusions (do not re-pay): the `wf_split` scope is the
two-arrow `⟨absurd, obtain/cases⟩` rung-bridge. The IF-CONDITION
bridges in `Wf.lean` (`banAsync_ite_nil_iff`'s false arm,
`checkSchemaIdent_eq_nil_iff`'s branches) carry site-specific
backwards (`bool.noConfusion` over a `by_cases`, `rcases` over a
`Bool.or_eq_true`) — a variant of this kit, not the same shape; and
`keysChecked`-style `cons_ne_nil d ds` hips inside larger proofs stay
hand-written. Owner: TestKit.WfKit; consumers: the schema-lang
rung-bridge lanes.

Core only (Lean core, no mathlib): the discipline that lets core-only
packages require TestKit. The proof bodies this kit emits are
`constructor`/`absurd`/`contradiction`/`simp_all` — all core tactics.
-/

module

public import Lean

@[expose] public section

namespace TestKit.WfKit

/-- `wf_split` — the rung-bridge discharge. Goal shape
    `(a pushed diagnostic list) = [] ↔ R`:

    - forward: the LHS is a pushed cons — `absurd` via
      `List.cons_ne_nil` (definitional; no unfold needed);
    - backward: `R` refutes against the cased context — `contradiction`
      first (direct constructor-mismatch equations), `simp_all` for the
      injection, `++`, and multi-binder variants.

    No axiom surface: the emitted proof is `absurd`/`contradiction`/
    `simp_all` over core lemmas. -/
macro "wf_split" : tactic =>
  `(tactic|
    solve
    | (constructor; intro hc; exact absurd hc (List.cons_ne_nil _ _); intro hok; first | contradiction | simp_all))

end TestKit.WfKit
