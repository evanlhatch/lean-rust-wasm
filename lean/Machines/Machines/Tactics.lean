/-
# Machines.Tactics — local proof idioms + the open solver

`guestlang_solver` (W6.8): the ONE open discharge tactic — the loom
pattern. Syntax declared once here; rungs are `macro_rules` extensions,
so any downstream package adds its own closer without editing this file.
`machine_safety` (Machines.Dsl) is its machine-obligation alias.
`guard_omega` stays the `EventSpec.safety` idiom for decidable-Nat guards
(Sync.lean: latch countDown, semaphore acquire/release).
-/

module

-- Elaboration-time only: syntax + the open ladder live in a
-- `public meta section` so downstream packages extend the rungs (W5.4).
public meta section

/-- The open discharge solver. The DEFAULT ladder below is today's
    `machine_safety` chain; a package adds a rung with its own
    `macro_rules` against the same syntax, no edit here:

    ```lean
    macro_rules | `(tactic| guestlang_solver) => `(tactic| my_closer)
    ```

    Lean tries every matching rule with backtracking: a rung that fails
    falls through to the next. Rung discipline: fail FAST on foreign
    goals, never succeed partially (partial success swallows the rest of
    the ladder — cf. the `done` guard on `simp_all` below). -/
syntax "guestlang_solver" : tactic

/-- The default ladder. The `done` guard matters: bare `simp_all`
    SUCCEEDS without closing the goal (partial progress), which would
    leave unsolved goals; omega/grind/trivial fail cleanly when stuck. -/
macro_rules
  | `(tactic| guestlang_solver) =>
      `(tactic| (intros; first | (simp_all; done) | omega | grind | trivial))

/-- The `EventSpec.safety` idiom for decidable-`Nat` guards: decode the
    guard hypothesis, unfold the invariant at hypothesis and goal, reduce
    the record-update projections, close by `omega`. -/
macro "guard_omega" Inv:ident : tactic =>
  `(tactic| (intro s h hinv
             simp only [decide_eq_true_eq] at h
             unfold $Inv at hinv ⊢
             simp only at hinv ⊢
             omega))

end -- public meta section
