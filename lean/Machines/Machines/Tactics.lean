/-
# Machines.Tactics — local proof idioms + the open solver

`guestlang_solver` (W6.8): the ONE open discharge tactic — the loom
pattern. Syntax declared once here; rungs are `macro_rules` extensions,
so any downstream package adds its own closer without editing this file.
`machine_safety` (Machines.Dsl) is its machine-obligation alias.
`guard_omega` stays the `EventSpec.safety` idiom for decidable-Nat guards
(Sync.lean: latch countDown, semaphore acquire/release).

Also owns the `declare_eqns` command (plan §4, family 3): the `@[simp]`
equation-restatement generator for recursive defs — the hand-written
`f_nil`/`f_cons` rfl-ladder, generated from the def's own equation
lemmas (`getEqnsFor?`). Consumed by Core/Rewind/Sim.
-/

module

-- The `declare_eqns` elab (plan §4, family 3) needs the Lean meta API —
-- the guestlang_solver/guard_omega macros need only the prelude. Lean-core
-- import: no mathlib leak (constraint 14 does not apply).
public meta import Lean

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

/- `declare_eqns f with n₁ n₂ …` (plan §4, family 3) — the equation-restatement
generator. For recursive def `f`, looks up its equation lemmas
(`getEqnsFor?`) and declares each as a `@[simp]` theorem with the given
name — the hand-written `f_nil`/`f_cons` rfl-ladder, generated. One name
per equation lemma, in order; a count mismatch or a name clash is an
error, never a silent truncation. The generated theorem's STATEMENT is
the equation lemma's own type (identical to the hand restatements it
replaces, up to binder names); the proof is the equation lemma itself
(an opaque theorem, like the `rfl` it replaces — the kernel checks the
equation lemma at the def site either way). -/
open Lean Elab Command Meta in
elab "declare_eqns " f:ident " with " names:ident* : command => do
  let env ← getEnv
  let fName ← liftTermElabM do
    let e ← Elab.Term.elabTerm f none
    pure e.getAppFn.constName!
  match env.find? fName with
  | some (.defnInfo _) => pure ()
  | _ => throwErrorAt f "declare_eqns: {fName} is not a definition"
  let eqns? ← liftTermElabM do
    tryCatch (Meta.getEqnsFor? fName) fun _ => pure none
  let some eqns := eqns?
    | throwErrorAt f "declare_eqns: no equation lemmas for {fName}"
  let names : Array (TSyntax `ident) := names
  if names.size != eqns.size then
    throwError "declare_eqns {fName}: {eqns.size} equation lemmas but\n      {names.size} names given — one name per equation lemma, in order"
  for h : i in [0:eqns.size] do
    let eqn := eqns[i]!
    let name := names[i]!
    if env.contains name.getId then
      throwErrorAt name "declare_eqns: {name.getId} already declared"
    -- force the equation lemma's realization (module mode: the lemmas are
    -- declared lazily, on first name resolution — realizeConst)
    discard <| liftTermElabM do
      tryCatch (do
        let _ ← Elab.Term.elabTerm (mkIdent eqn) none
        pure ()) fun _ => pure ()
    let some info := (← getEnv).find? eqn
      | throwError "declare_eqns: equation lemma {eqn} not found"
    let tyStx ← liftTermElabM <|
      Lean.PrettyPrinter.delab info.type
    elabCommand (← `(command| @[simp] theorem $(mkIdent name.getId) : $tyStx := $(mkIdent eqn)))

end -- public meta section
