/-
# Dbsp.Tactics — project tactic layer

Two tools, both born from repeated ChangeLaws/Bridge pain (lean/AGENTS.md
traps 9b/9c):

- `beq_cases hb, hp : (a == b)` — case-split on a decidable equality with
  the hypothesis converted (no `rw [beq_iff_eq] at h` dance).
- the `zset` simp attribute + tactic: the pointwise Finsupp/ZSet reading
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

/-- `beq_cases hb, hp : (a == b)` — split on a decidable equality:
    `hp` is the Prop form (`a = b` / `a ≠ b`), `hb` the Bool form, and goal
    occurrences of the scrutinee are rewritten to the literal (the
    `cases h :` behavior, hypothesis-converted). A branch whose goal
    becomes `x = x` under the rewrite auto-closes (rw-rfl) — so trailing
    bullets may number one or two; check the build. -/
syntax "beq_cases " ident ", " ident " : " term : tactic

macro_rules
  | `(tactic| beq_cases $hb:ident, $hp:ident : ($lhs == $rhs)) => `(tactic|
      by_cases $hp:ident : ($lhs = $rhs) <;>
        first
        | (have $hb:ident : (($lhs == $rhs) = true) := beq_iff_eq.mpr $hp:ident
           try rw [$hb:ident])
        | (have $hb:ident : (($lhs == $rhs) = false) :=
             Bool.eq_false_iff.mpr (fun hbeq => ($hp:ident) (beq_iff_eq.mp hbeq))
           try rw [$hb:ident]))
