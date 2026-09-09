/-
# Dbsp.Tactics — project tactic layer

The `zset` simp attribute + tactic: the pointwise Finsupp/ZSet reading
lemmas in one set.

Toolchain trap recorded here (cost an hour): a tactic macro expanding to
`cases ... with | tag => tac` does NOT expose the branch remainders to
trailing `·` bullets at the call site — the `with`-branches swallow them.
The working shape for "split, then let the caller continue per-branch" is
`by_cases ... <;> first | setupA | setupB` — a single tactic, no internal
bullets, goals exposed.
-/

import Lean

/-- The pointwise zset reading lemmas. -/
register_simp_attr zset

/-! ## Toolchain trap (recorded; cost an hour)

A tactic macro expanding to `cases ... with | tag => tac` does NOT expose
the branch remainders to trailing `·` bullets at the call site — the
`with`-branches swallow them. The working shape for "split, then let the
caller continue per-branch" is `by_cases ... <;> first | setupA | setupB`
— a single tactic, no internal bullets, goals exposed.

(The `zset`/`zset?` tactic macros that used to live here were removed:
zero call sites used them as tactics — only the `zset` simp attribute
above is consumed. `@[simp, zset]` tags remain on the pointwise lemmas.) -/
