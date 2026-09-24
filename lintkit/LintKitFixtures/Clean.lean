/-
LintKitFixtures.Clean — the MANDATORY negative controls: compliant
shapes for every linter, none of which may fire (an uncaught control is
the vacuity tripwire). Runs beside `LintKitFixtures.Violations` in the
LintKitTests driver's fixture closure.

Evidence, not architecture.
-/

import LintKit
import Kit.Correspondence

-- The census linters are ON here too: the negative controls must prove
-- the compliant decls QUIET WHILE ENABLED, not merely unlinted.
set_option linter.guestlang.guestBan true
set_option linter.guestlang.recursiveSimpEqns true
set_option linter.guestlang.decideFirst true
set_option linter.guestlang.graduation true
set_option linter.guestlang.zeroCitation true

namespace LintKitFixtures.Clean

/-- bareChecker NEGATIVE (the NAME bridge): the checker's correspondence
theorem names it in this module. -/
def checkWithBridge (n : Nat) : Bool := n < 10

/-- `checkWithBridge`'s bridge (consumer-side pin shape: the checker is
sound BELOW the domain's bound). -/
theorem checkWithBridge_true_of_lt : ∀ (n : Nat), n < 10 → checkWithBridge n = true :=
  fun n hn => by simp [checkWithBridge, decide_eq_true_iff.mpr hn]

/-- bareChecker NEGATIVE (the REGISTRATION bridge): a same-module def
whose value mentions the checker (the CheckedProp shape,
`check := CodeRegistry.check`). -/
def checkRegistered (n : Nat) : Bool := n % 2 == 0

/-- `checkRegistered`'s spec registration — the value mentions the
checker, which is the module's bridge. -/
def checkRegistered_spec (n : Nat) : Prop := checkRegistered n = true

/-- verdictCtors NEGATIVE: the verdict is an ENUMERATED constructor
carrying its evidence — and its renderer is a legitimate render verb. -/
inductive FixVerdict where
  | pass
  | fail (why : String)

/-- Renders the enumerated verdict (never produces a collapsed one). -/
def FixVerdict.render : FixVerdict → String
  | .pass => "pass"
  | .fail why => s!"fail: {why}"

/-- recursiveSimpEqns NEGATIVE: the recursive def ships `@[simp]`. (Body
deliberately unlike `Violations.recNoSimp`'s — two alpha-equivalent
recursive bodies would be their own dupDefBodies finding.) -/
@[simp] def recSimp : Nat → Nat
  | 0 => 1
  | n + 1 => recSimp n + 1

/-- The guest gate's NEGATIVE control: fixed-width arithmetic over
guest-honest types passes the `@[guest]` gate. -/
@[guest] def guestOk (n : UInt64) : UInt64 := n + 1

/-! ## the proof-hygiene teeth (decideFirst / graduation / zeroCitation) -/

/-- The closed finite space for the decideFirst negative controls.
Deliberately a DIFFERENT inductive from Violations.FixtureColor — two
alpha-equivalent bodies would be their own dupDefBodies finding. -/
inductive FixtureShade where
  | on | off | dim
  deriving DecidableEq

/-- decideFirst NEGATIVE: the same statement shape as
`Violations.colorNeHand`, closed by `by decide` — the proof routes
through `of_decide_eq_true` and stays quiet. -/
theorem colorNeDecide : FixtureShade.on ≠ FixtureShade.off ∧
    FixtureShade.off ≠ FixtureShade.dim := by
  decide

/-- decideFirst NEGATIVE: a rfl-shaped proof over the same space — the
spine is `Eq.refl` (kernel computation modulo presentation) — quiet. -/
theorem shadeRfl : (FixtureShade.on == FixtureShade.on) = true := by
  rfl

/-- graduation NEGATIVE: a codec whose accepted-byte policy is
UNDECIDABLE (`∀ n, …` over Nat — no instance resolvable) — the
honest gap, quiet by the decidability gate. -/
def tautologyCodec : Kit.Codec (Nat → Bool) (Nat → Bool) where
  encode f := f
  decode a := some a
  policy f := ∀ n, f n = f n
  decode_encode := fun _ => rfl
  decode_some_policy := fun _ _ _ _ => rfl

/-- zeroCitation NEGATIVE: cited from `LintKitTests.Main` (the citing
dec `citeCitedFixture` there) — quiet. -/
theorem citedFixture : 1 < 2 := by
  decide

/-- Generic quiet decl (no linter may flag an ordinary def). -/
def plainOk (n : Nat) : Nat := n

end LintKitFixtures.Clean
