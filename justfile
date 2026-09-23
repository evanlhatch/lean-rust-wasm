# macht — the thin build spine. Recipes grow when their first consumer
# lands (notes/v3/14-build-map.md); the Lean gates are the first rows
# (notes/v3/09-gates-ops.md §3).

build:
	lake build

test:
	lake build

# The linter driver over the gated roots (LintKit + Gates).
lint:
	lake exe lintkit

# The gates machine: the axiom report + docs-check + the byte-tie
# (the registry's `all`); the byte-tie's writer side is `just gen`.
gates:
	lake exe gates all

# The schema regen (the byte-tie's writer side: regen + commit the
# artifact; a drift with no regen fails `just gates`).
gen:
	lake exe schema

# Single gates (the loud re-baseline: `just gates-axioms-write` refuses a
# non-empty diff without `--accept-drift` — append it by hand).
gates-axioms:
	lake exe gates axioms

gates-docs-check:
	lake exe gates docs-check

# The persisted E-code registry gate (the allocation history; --write is
# the deliberate allocation/canonicalization step, never a launder —
# the content checks run first).
gates-code-registry-check:
	lake exe gates code-registry-check

# The universe-snapshot gate (the breaking gate's substrate; --write is
# the deliberate re-baseline).
gates-snapshot-check:
	lake exe gates snapshot-check
