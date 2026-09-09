/-
# Machines.Session — session types for WIT conversations

The WIT interface defines the TYPES of a component conversation; the
CHOREOGRAPHY (who sends when, what they expect back, when it ends) is a
separate spec — and a wrong choreography (both sides send, or both
wait) deadlocks at runtime where no type check fires.

The choreography as a `Machine`:

- A `Protocol` is a linear script: direction (send/receive) × WIT type
  name (the payload's wire type — the same wire vocabulary the emitters
  own; here we certify the SHAPE of the exchange).
- A `Session` over a protocol is a machine whose state is the POSITION
  in the script; the only enabled event at each position is THAT step
  (both parties follow one script; the Label type IS the script's
  length, so out-of-range steps are unrepresentable).
- Mid-protocol deadlock-freedom is PROVED (`session_mid_deadlockFree`):
  from every position strictly inside the script some event is enabled.
  A COMPLETED position (pos = n) is not a wedge — it is the terminal
  state (`run_preserves` admits it via the `pos ≤ n` invariant; the
  pipeline's `failed` exclusion is the same trick, inverted).
- Termination is PROVED (`session_variant_decreases`): every fired step
  strictly decreases the distance to the end — the Convergent
  certificate; exactly n firings complete the run.
- DUALITY is PROVED (`dual_payload_mirror`): at the same position, dual
  peers see the same payload type in OPPOSITE directions — every send
  on one side is a receive on the other. Two components whose
  choreographies are duals cannot talk past each other.

The instance is the gateway world's real conversation: `gatewayProto`
(the `get-user` call + the `watch-orders` async stream).
-/

import Machines.Core

namespace Machines.Session

/-! ## Protocols -/

/-- Conversation direction: this party SENDS the payload, or RECEIVES it. -/
inductive Dir where
  | snd | rcv
deriving Repr, BEq, DecidableEq

/-- One choreography step: direction + the payload's WIT type name. -/
abbrev Step := Dir × String

/-- Rendering (assertEq failure messages name the actual directions). -/
instance : ToString Dir where
  toString
    | .snd => "snd"
    | .rcv => "rcv"

/-- A linear protocol: the agreed message order. Empty = no conversation. -/
abbrev Protocol := List Step

/-- The other party's direction. -/
def Dir.flip : Dir → Dir
  | .snd => .rcv
  | .rcv => .snd

/-- Directions flip twice back to the same one. -/
theorem Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl

/-- The DUAL protocol: flip every direction, keep the message sequence. -/
def dual : Protocol → Protocol :=
  List.map (fun (d, t) => (d.flip, t))

@[simp] theorem dual_nil : dual [] = [] := rfl
@[simp] theorem dual_cons (s : Step) (rest : Protocol) :
    dual (s :: rest) = (s.1.flip, s.2) :: dual rest := rfl

/-- A double-flipped step is the original step (pointwise). -/
theorem flip_step (s : Step) :
    ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) = s := by
  cases s with
  | mk d t => simp [Dir.flip_flip]

theorem dual_dual (p : Protocol) : dual (dual p) = p := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      -- `dual (dual (s :: rest))` unfolds definitionally to the
      -- double-flipped head over the dual's dual tail
      show ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) :: dual (dual rest) = s :: rest
      rw [flip_step, ih]

/-! ## The session machine (Label = the script's indices) -/

/-- The session invariant: the position is at most the script's length.
    Position n is the COMPLETED protocol — a terminal state inside the
    invariant (the run's `run_preserves` needs it), not a wedge. -/
def SessionInv (n : Nat) (pos : Nat) : Prop := pos ≤ n

/-- The session machine over protocol `p`: at position `i`, the ONLY
    enabled event is step `i`; firing it advances the position. -/
def session (p : Protocol) : Machine where
  State := Nat
  Label := Fin p.length
  Inv := SessionInv p.length
  event := fun l =>
    { guard := fun pos => decide (pos = l.val)
      action := fun pos _ => pos + 1
      safety := by
          intro pos h hinv
          have : pos = l.val := by simpa using h
          unfold SessionInv at hinv ⊢
          omega }

/-- Mid-protocol deadlock-freedom: from every position strictly inside
    the script, the party's own next step is enabled. Between its steps,
    a session cannot wedge; a real conversation deadlock is a DUALITY
    violation (non-dual scripts), which `dual_payload_mirror` rules out
    for dual peers. -/
theorem session_mid_deadlockFree (p : Protocol) (pos : Nat) (hpos : pos < p.length) :
    ∃ l : (session p).Label, ((session p).event l).guard pos = true := by
  exact ⟨Fin.mk pos hpos, by simp [session, decide_eq_true_iff]⟩

/-- Termination: every fired step strictly decreases the distance to the
    end — the Convergent certificate (n firings from 0 reach n; no
    infinite run inside a finite script). -/
theorem session_variant_decreases (p : Protocol) (pos : Nat) (l : Fin p.length)
    (h : pos = l.val) :
    p.length - (pos + 1) < p.length - pos := by
  have := l.isLt
  omega

/-! ## Duality — dual peers mirror payloads -/

/-- A direction differs from its flip (ctor distinctness). -/
theorem Dir.flip_ne (d : Dir) : d ≠ d.flip := by
  cases d <;> intro h <;> cases h

/-- Dualizing preserves the script's length (lockstep precondition). -/
@[simp] theorem dual_length (p : Protocol) : (dual p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s rest ih => simp [dual, ih]

/-- At the same position, dual peers see the same payload TYPE in
    OPPOSITE directions: `p[i] = (d₁, t)` and `(dual p)[i] = (d₂, t)`
    with `d₁ ≠ d₂`. Client's sends are server's receives, of the same
    type, at the same time. -/
theorem dual_payload_mirror (p : Protocol) :
    ∀ (i : Nat) (hi : i < p.length),
      ∃ d₁ d₂ t : _,
        List.get p ⟨i, hi⟩ = (d₁, t) ∧
        (∀ h₂ : i < (dual p).length, List.get (dual p) ⟨i, h₂⟩ = (d₂, t)) ∧
        d₁ ≠ d₂ := by
  induction p with
  | nil => intro i hi; simp at hi
  | cons s rest ih =>
      intro i hi
      have hdual : (dual (s :: rest)) = (s.1.flip, s.2) :: dual rest := rfl
      rw [hdual]
      cases i with
      | zero =>
          exact ⟨s.1, s.1.flip, s.2, rfl, fun _ => rfl, Dir.flip_ne s.1⟩
      | succ i' =>
          have hlt : i' < rest.length := by simpa using hi
          obtain ⟨d₁, d₂, t, h₁, h₂, hne⟩ := ih i' hlt
          refine ⟨d₁, d₂, t, ?_, fun h₃ => ?_, hne⟩
          · simpa [List.get] using h₁
          · have hlen : i' < (dual rest).length := by
              rw [dual_length]
              simpa using h₃
            simpa [List.get] using h₂ hlen

/-! ## The gateway instance — the real WIT world's conversation -/

/-- The gateway world's conversation (Demo.lean's funcs):
    `get-user` — client sends u64, receives option<user>;
    `watch-orders` — client sends order-error, receives the change
    stream (the delta-shaped contract as choreography). -/
def gatewayProto : Protocol :=
  [ (.snd, "u64"), (.rcv, "option<user>")
  , (.snd, "order-error"), (.rcv, "stream<user>") ]

/-- The gateway choreography is self-consistent: dual's length is
    preserved (the lockstep precondition), and dual(dual) is the
    original (a peer dualized twice is the same script). -/
theorem gateway_self_dual : dual (dual gatewayProto) = gatewayProto :=
  dual_dual gatewayProto

end Machines.Session
