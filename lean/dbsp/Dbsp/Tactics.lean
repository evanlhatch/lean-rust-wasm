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

module

public import Lean

-- Elaboration-time only: syntax/macros/attr registration live in a
-- `public meta section` (W5.4 module discipline).
public meta section

/-- The pointwise zset reading lemmas. -/
register_simp_attr zset

/-- `stream_cases` — expand a function equality on `Nat` by cases.

Expands `f = g` into two goals (`t = 0` and `t = n.succ`) by applying
`funext t; cases t`.  The caller chains the branch tactic, typically
`stream_cases <;> simp` or `stream_cases <;> simp [extra_lemma]`.

Replaces the repeated pattern:
```lean
funext t
cases t <;> simp [lemma1, lemma2]
```
-/
macro "stream_cases" : tactic =>
  `(tactic| funext t <;> cases t)

end -- public meta section