/-
LintKitFixtures.Violations — the PLANTED violations (the linters'
positive controls). Every decl here is a deliberate, documented finding:
the LintKitTests driver replays the production path (`importModules` the
fixture oleans, run the runner, assert the finding set) and the negative
controls live in `LintKitFixtures.Clean`.

The fixture root `LintKitFixtures` is deliberately NOT in the lintkit
exe's gated roots — the planted findings never leak into the tree run.
Module name carries no `Tests` component: the linters' test-module
exemptions must NOT swallow the teeth.

Evidence, not architecture.
-/
import LintKit
import Kit.Correspondence

-- The census linters are turned ON for this module at ELABORATION time
-- (the documented per-decl snapshot mechanism): the planted violations
-- are findings of the tests driver, and the build emits the warnings —
-- the fixture is the planted-finding module, that is its job.
set_option linter.guestlang.guestBan true
set_option linter.guestlang.recursiveSimpEqns true
set_option linter.guestlang.decideFirst true
set_option linter.guestlang.graduation true
set_option linter.guestlang.zeroCitation true

namespace LintKitFixtures.Violations

/-- bareChecker POSITIVE: a Bool check* with no bridge theorem and no
value-level registration in this module — fires. -/
def checkNoBridge (n : Nat) : Bool := n % 3 == 0

/-- verdictCtors POSITIVE: a verdict-shaped name returning String — the
collapsed verdict, fires. -/
def badVerdict (n : Nat) : String := toString n

/-- guestBan POSITIVE (census, std level): IO is a host capability. -/
def evilIo : IO Unit := IO.println "fixture evilIo"

/-- guestBan POSITIVE (census, std level): Nat arithmetic is GMP. (The
GMP constant spelled DIRECTLY — the syntactic scan sees pre-LCNF
constants, and `n + 1` hides `Nat.add` behind the HAdd instance.) -/
def evilNatArith (n : Nat) : Nat := Nat.add n 1

/-- The reasoned opt-out (the `@[nolint]` mechanism's own negative
control): same violation shape as `evilIo`, silenced by the attribute —
and the reason string satisfies the nolintReason text lint. -/
@[nolint linter.guestlang.guestBan "fixture: demonstrates the reasoned opt-out"]
def evilNolint : IO Unit := IO.println "fixture evilNolint"

/-- recursiveSimpEqns POSITIVE (census): a recursive def with no `@[simp]`
equation lemmas. -/
def recNoSimp : Nat → Nat
  | 0 => 0
  | n + 1 => recNoSimp n

/-- error: `@guest` function `LintKitFixtures.Violations.guestBad` is not guest-compilable:
- `String` — String runtime lands with guestlang-std — not yet compilable
- `IO` — IO is a host capability — guest functions must be pure over guestlang-std's WASI layer -/
#guard_msgs (error) in
@[guest] def guestBad : IO Unit := IO.println "fixture guestBad"

/-! ## the proof-hygiene teeth (decideFirst / graduation / zeroCitation) -/

/-- The closed finite space for the proof-hygiene teeth. -/
inductive FixtureColor where
  | red | green | blue
  deriving DecidableEq

/-- decideFirst POSITIVE: the statement is decidable over the closed
finite space (Decidable synth + enum ctors), the proof depends on
non-computational lemmas (noConfusion) — a hand script where `decide`
is the honest rung. Fires; zeroCitation fires on it TOO (it is cited
nowhere outside this module — both rows are in fixtureExpected). -/
theorem colorNeHand : FixtureColor.red ≠ FixtureColor.green ∧
    FixtureColor.green ≠ FixtureColor.blue := by
  exact ⟨fun h => FixtureColor.noConfusion h, fun h => FixtureColor.noConfusion h⟩

/-- zeroCitation POSITIVE: a theorem referenced nowhere outside this
module (and no test pin) — the proof-level dead code. Fires. -/
theorem uncitedFixture : 1 = 1 := rfl

/-- zeroCitation NEGATIVE (the test-pin exemption): referenced nowhere
in ANY environment constant, but pinned by `#print axioms` in
`LintKitTests.Main` — the source scan must see it and stay QUIET. -/
theorem pinnedFixture : 2 = 2 := rfl

/-- graduation POSITIVE: a codec whose accepted-byte policy is a decidable
lambda over closed types, with NO toImageIso-style call site anywhere —
the image-iso upgrade is free here (15 #11). Fires. -/
def parityCodec : Kit.Codec Nat Nat where
  encode b := b + b
  decode a := if a % 2 == 0 then some (a / 2) else none
  policy a := a % 2 == 0
  decode_encode := fun b => by
    have h : (b + b) % 2 = 0 := by omega
    rw [if_pos (by simp [h])]
    have h2 : (b + b) / 2 = b := by omega
    exact congrArg some h2
  decode_some_policy := fun a b h => by
    split at h
    · have h2 := Option.some.inj h; omega
    · exact absurd h (by simp)

end LintKitFixtures.Violations
