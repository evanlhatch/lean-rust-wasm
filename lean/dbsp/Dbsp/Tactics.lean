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

/-- `zset`: pointwise zset normalization, then linear arithmetic. -/
macro "zset" : tactic => `(tactic| (simp only [zset]; try omega))

/-- `zset?`: the search variant. -/
macro "zset?" : tactic => `(tactic| simp? only [zset])
