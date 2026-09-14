/-
# Proofkit.Ladder — the PO discharge ladder (flatland TOOLKIT 4.2)

Bundled proof obligations should name ONE default discharge — cheap
closers in order, failing ONLY with the tactic error at the obligation
site (a missing proof is information; the ladder just removes the
boilerplate for the obligations that are, in fact, routine).

The ladder (cheap → expensive, each rung failing cleanly when stuck):

1. `decide`      — data-decidable slots (registry facts, list membership)
2. `simp_all`    — hypothesis-normalizing conjunctions (`done`-guarded:
                   bare `simp_all` can make partial progress WITHOUT
                   closing, which would swallow the `first` chain)
3. `omega`       — linear arithmetic over Nat/Int
4. `bv_decide`   — fixed-width bitvector facts (the binop contracts)
5. `grind`       — the general closer for conjunction-shaped goals

Consumers: a structure/class PO field takes `:= by po_ladder` as its
autoParam default (the systemic pattern — see `SchemaLang.Update`'s
`UpdatePure.volatileFree` / `NonInterfering.noOverlap`, which sit on the
ladder's `decide` rung); `Machines.Dsl.machine_safety` is the
machine-event specialization of the same idea.

Ownership note: this is a TACTIC MACRO (elaboration-time only) — no
runtime surface, no axioms.
-/

namespace Proofkit

/-- The PO discharge ladder: `decide → simp_all → omega → bv_decide →
    grind`, each rung failing cleanly when stuck. -/
macro "po_ladder" : tactic =>
  `(tactic| first
      | (decide; done)
      | (simp_all; done)
      | omega
      | bv_decide
      | grind)

/-! ## The demonstration: the autoParam default discharges silently -/

/-- A bundled obligation with the ladder as its autoParam default:
    constructing a `Bounded` omits `h` and the ladder closes it. -/
structure Bounded where
  n : Nat
  h : n < 10 := by po_ladder

/-- The positive: no hand proof — the ladder's `decide` rung fired. -/
def boundedSeven : Bounded := { n := 7 }

-- The negative side is NOT demonstrable as a shipped `example` — a slot
-- the ladder cannot close FAILS THE BUILD at the construction site (the
-- error names the goal; the author supplies the real proof). That
-- fail-loud-at-site behavior is the design: the ladder never silently
-- succeeds on partial progress (the `done` guards), and a genuinely
-- unprovable obligation stays an obligation. -/

end Proofkit
