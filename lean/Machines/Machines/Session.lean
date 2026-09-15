/-
# Machines.Session — session types for WIT conversations

The WIT interface defines the TYPES of a component conversation; the
CHOREOGRAPHY (who sends when, what they expect back, when it ends) is a
separate spec — and a wrong choreography (both sides send, or both
wait) deadlocks at runtime where no type check fires.

The choreography as a `Machine`, GENERIC over the payload universe `P`:

- A `TProtocol P` is a linear script: direction (send/receive) × payload
  from ANY universe `P` (wire names, schema types, …). Machines owns the
  MECHANISM once; consumers instantiate `P` (schema-lang:
  `P := SchemaLang.Ty`, SchemaLang.Session).
- A `session p` is a machine whose state is the POSITION in the script;
  the only enabled event at each position is THAT step (both parties
  follow one script; the Label type IS the script's length, so
  out-of-range steps are unrepresentable). The payload is never
  inspected — position dynamics are payload-independent BY
  CONSTRUCTION.
- Mid-protocol deadlock-freedom is PROVED (`session_mid_deadlockFree`):
  from every position strictly inside the script some event is enabled.
  A COMPLETED position (pos = n) is not a wedge — it is the terminal
  state (`run_preserves` admits it via the `pos ≤ n` invariant; the
  pipeline's `failed` exclusion is the same trick, inverted).
- Termination is PROVED (`session_variant_decreases`): every fired step
  strictly decreases the distance to the end — the Convergent
  certificate; exactly n firings complete the run.
- DUALITY is PROVED (`tdual_payload_mirror`): at the same position, dual
  peers see the same payload in OPPOSITE directions — every send on one
  side is a receive on the other. Two components whose choreographies
  are duals cannot talk past each other. Peer agreement is a TYPE
  (`IsDualOf`): a hand-written peer whose direction doesn't flip, or
  whose payload differs at any position, fails DEFINITIONAL equality at
  ELABORATION time — a type error, not a runtime check.

The instance is the gateway world's real conversation: `gatewayProto`
(the `get-user` call + the `watch-orders` async stream) at
`P := String` (wire names).

The schema-typed consumer (`P := SchemaLang.Ty`) is
`SchemaLang.Session` — it instantiates THIS generic layer directly
(W4.1c landed; the string-bridge aliases are gone).
-/

import Machines.Core

namespace Machines.Session

/-! ## Protocols -/

/-- Conversation direction: this party SENDS the payload, or RECEIVES it. -/
inductive Dir where
  | snd | rcv
deriving Repr, BEq, DecidableEq

/-- Rendering (assertEq failure messages name the actual directions). -/
instance : ToString Dir where
  toString
    | .snd => "snd"
    | .rcv => "rcv"

/-- The other party's direction. -/
def Dir.flip : Dir → Dir
  | .snd => .rcv
  | .rcv => .snd

/-- Directions flip twice back to the same one. -/
theorem Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl
/-- A direction differs from its flip (ctor distinctness). -/
theorem Dir.flip_ne (d : Dir) : d ≠ d.flip := by
  cases d <;> intro h <;> cases h


/-! ## Payload-TYPED steps — generic over the payload universe (the CORE) -/

/-- A typed step: direction × payload from universe `P`. -/
abbrev TStep (P : Type) := Dir × P

/-- A typed protocol: the agreed message order over payload universe
    `P`. Empty = no conversation. -/
abbrev TProtocol (P : Type) := List (TStep P)

/-- The typed dual: flip every direction, keep every payload. -/
def tdual {P : Type} (p : TProtocol P) : TProtocol P :=
  p.map fun (d, t) => (d.flip, t)

/-- A double-flipped typed step is the original (pointwise; generic in
    the payload). -/
theorem flip_tstep {P : Type} (s : TStep P) :
    ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) = s := by
  cases s with
  | mk d t => simp [Dir.flip_flip]

/-- Dualizing keeps the typed protocol's length (the lockstep
    precondition). -/
@[simp] theorem tdual_length {P : Type} (p : TProtocol P) :
    (tdual p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s rest ih => simp [tdual]

/-- The typed dual is an involution: a peer dualized twice is the same
    script. -/
theorem tdual_dual {P : Type} (p : TProtocol P) : tdual (tdual p) = p := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      show ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) :: tdual (tdual rest)
        = s :: rest
      rw [flip_tstep, ih]

/-- The typed dual keeps the PAYLOAD SEQUENCE: the payloads the peers
    exchange are unchanged — only the directions flip. -/
theorem tdual_types {P : Type} (p : TProtocol P) :
    (tdual p).map (·.2) = p.map (·.2) := by
  induction p with
  | nil => rfl
  | cons s rest ih => simp [tdual]

/-- Directions oppose pairwise: every send on one side is a receive on
    the other (the typed lockstep condition, executed form). -/
theorem tdual_directions_oppose {P : Type} (p : TProtocol P) :
    List.all (List.zip (p.map (·.1)) ((tdual p).map (·.1)))
      (fun x => x.1 != x.2) := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | mk d t =>
          show ((d != d.flip) && List.all
            (List.zip (rest.map (·.1)) ((tdual rest).map (·.1)))
            (fun x => x.1 != x.2)) = true
          have h1 : (d != d.flip) = true := by cases d <;> rfl
          rw [h1]
          simp [ih]

/-- TYPED MIRROR: at the same position, dual peers see the SAME payload
    (any universe) in OPPOSITE directions. Client's sends are server's
    receives, of the same payload, at the same time. -/
theorem tdual_payload_mirror {P : Type} (p : TProtocol P) :
    ∀ (i : Nat) (hi : i < p.length),
      ∃ (d₁ d₂ : Dir) (t : P),
        List.get p ⟨i, hi⟩ = (d₁, t) ∧
        (∀ h₂ : i < (tdual p).length, List.get (tdual p) ⟨i, h₂⟩ = (d₂, t)) ∧
        d₁ ≠ d₂ := by
  induction p with
  | nil => intro i hi; simp at hi
  | cons s rest ih =>
      intro i hi
      have hdual : tdual (s :: rest) = (s.1.flip, s.2) :: tdual rest := rfl
      rw [hdual]
      cases i with
      | zero =>
          exact ⟨s.1, s.1.flip, s.2, rfl, fun _ => rfl, Dir.flip_ne s.1⟩
      | succ i' =>
          have hlt : i' < rest.length := by simpa using hi
          obtain ⟨d₁, d₂, t, h₁, h₂, hne⟩ := ih i' hlt
          refine ⟨d₁, d₂, t, ?_, fun h₃ => ?_, hne⟩
          · simpa [List.get] using h₁
          · have hlen : i' < (tdual rest).length := by
              rw [tdual_length]
              simpa using h₃
            simpa [List.get] using h₂ hlen

/-! ## The session machine (Label = the script's indices) -/

/-- The session invariant: the position is at most the script's length.
    Position n is the COMPLETED protocol — a terminal state inside the
    invariant (the run's `run_preserves` needs it), not a wedge. -/
def SessionInv (n : Nat) (pos : Nat) : Prop := pos ≤ n

/-- The session machine over protocol `p`: at position `i`, the ONLY
    enabled event is step `i`; firing it advances the position. Generic
    in the payload universe — the payload is never inspected. -/
def session {P : Type} (p : TProtocol P) : Machine where
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
    violation (non-dual scripts), which `tdual_payload_mirror` rules out
    for dual peers. -/
theorem session_mid_deadlockFree {P : Type} (p : TProtocol P) (pos : Nat)
    (hpos : pos < p.length) :
    ∃ l : (session p).Label, ((session p).event l).guard pos = true := by
  exact ⟨Fin.mk pos hpos, by simp [session]⟩

/-- THE variant: a fired `Fin n` step with `pos = l.val` strictly
    decreases the distance to the end. -/
theorem pos_variant_decreases (n pos : Nat) (l : Fin n) (h : pos = l.val) :
    n - (pos + 1) < n - pos := by
  have := l.isLt
  omega

/-- Termination: every fired step strictly decreases the distance to the
    end — the Convergent certificate (n firings from 0 reach n; no
    infinite run inside a finite script). -/
theorem session_variant_decreases {P : Type} (p : TProtocol P) (pos : Nat)
    (l : Fin p.length) (h : pos = l.val) :
    p.length - (pos + 1) < p.length - pos :=
  pos_variant_decreases p.length pos l h

/-! ## The gateway instance — the real WIT world's conversation -/

/-- The gateway world's conversation (Demo.lean's funcs), payloads as
    wire names: `get-user` — client sends u64, receives option<user>;
    `watch-orders` — client sends order-error, receives the change
    stream (the delta-shaped contract as choreography). -/
def gatewayProto : TProtocol String :=
  [ (.snd, "u64"), (.rcv, "option<user>")
  , (.snd, "order-error"), (.rcv, "stream<user>") ]

/-- The gateway choreography is self-consistent: dual(dual) is the
    original (a peer dualized twice is the same script). -/
theorem gateway_self_dual : tdual (tdual gatewayProto) = gatewayProto :=
  tdual_dual gatewayProto

/-! ### Peer agreement as a TYPE — the elaboration-error property

`IsDualOf theirs mine` is inhabited EXACTLY when `theirs` is the typed
dual of `mine`. The generic instance is the only witness, so the peer's
script is COMPUTED by the unifier (deriving, not stating): a
hand-written script that disagrees — a direction that doesn't flip, or
a payload that differs at any position — fails definitional equality
at ELABORATION time. This is the type-level check the runtime cannot
skip: the mismatched conversation does not compile. -/

/-- The peer-agreement type. `agrees` is the (unique) witness. -/
class IsDualOf {P : Type} (theirs mine : TProtocol P) : Prop where
  /-- The agreeing peer's script IS the dual's, definitionally. -/
  agrees : theirs = tdual mine

/-- The one witness: the dual always agrees with its original. -/
instance instIsDualOf {P : Type} (p : TProtocol P) : IsDualOf (tdual p) p :=
  ⟨rfl⟩

end Machines.Session
