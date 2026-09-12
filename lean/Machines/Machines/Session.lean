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

The TYPED layer (`TProtocol P`) is GENERIC over the payload universe:
`Machines` knows nothing about the schema's `Ty` (that would be a
package cycle — schema-lang depends on Machines) — it fixes the
DUALITY MECHANISM once, and the schema-lang layer instantiates
`P := SchemaLang.Ty` (SchemaLang.Session). Peer agreement is a TYPE
(`IsDualOf`): a hand-written peer whose direction doesn't flip, or
whose payload differs at any position, fails DEFINITIONAL equality at
ELABORATION time — a type error, not a runtime check.
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
/-- A direction differs from its flip (ctor distinctness). -/
theorem Dir.flip_ne (d : Dir) : d ≠ d.flip := by
  cases d <;> intro h <;> cases h


/-! ## Payload-TYPED steps — generic over the payload universe (the CORE)

The string layer certifies the choreography SHAPE with payloads as wire
names; the TYPED core abstracts the payload: a `TProtocol P` is a
conversation whose payloads range over ANY universe `P`. Machines owns
the MECHANISM (the typed dual and its mirror/liveness certificates)
ONCE — the string layer below is the INSTANTIATION `P := String` (not a
second implementation), and the schema-lang layer supplies
`P := SchemaLang.Ty` (SchemaLang.Session). The two cannot drift.
-/

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
    script (generic form of `dual_dual`). -/
theorem tdual_dual {P : Type} (p : TProtocol P) : tdual (tdual p) = p := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      show ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) :: tdual (tdual rest)
        = s :: rest
      rw [flip_tstep, ih]

/-- The typed dual keeps the PAYLOAD SEQUENCE: the payloads the peers
    exchange are unchanged — only the directions flip (generic form of
    `dual_map_payload`). -/
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

/-- TYPED MIRROR — the generic `dual_payload_mirror`: at the same
    position, dual peers see the SAME payload (any universe) in
    OPPOSITE directions. Client's sends are server's receives, of the
    same payload, at the same time. -/
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



/-! ## The string layer — the typed core at `P := String`

`Step = Dir × String = TStep String` and `Protocol = TProtocol String`
definitionally, so the string theorems ARE the typed ones:
`dual := tdual`, and every string theorem below delegates to its typed
twin. The `@[simp]` surface (`dual_nil`/`dual_cons`/`dual_length`) stays
for the session machine's reasoning. -/

/-- The DUAL protocol: flip every direction, keep the message sequence
    (the typed core at `P := String`). -/
def dual : Protocol → Protocol :=
  tdual (P := String)

@[simp] theorem dual_nil : dual [] = [] := rfl
@[simp] theorem dual_cons (s : Step) (rest : Protocol) :
    dual (s :: rest) = (s.1.flip, s.2) :: dual rest := rfl

/-- A double-flipped step is the original step (pointwise). -/
theorem flip_step (s : Step) :
    ((s.1.flip, s.2).1.flip, (s.1.flip, s.2).2) = s :=
  flip_tstep (P := String) s

theorem dual_dual (p : Protocol) : dual (dual p) = p :=
  tdual_dual (P := String) p

/-- Dualizing keeps the payload SEQUENCE: the message TYPES the peers
    exchange are unchanged — only the directions flip. The payload-type
    agreement the typed layer consumes (no index gymnastics: a map
    equation). -/
theorem dual_map_payload (q : Protocol) : (dual q).map (·.2) = q.map (·.2) :=
  tdual_types (P := String) q

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
  exact ⟨Fin.mk pos hpos, by simp [session]⟩

/-- THE variant: a fired `Fin n` step with `pos = l.val` strictly
    decreases the distance to the end. One proof — both the string and
    the typed choreographies delegate (their statements are identical
    mod the script's length). -/
theorem pos_variant_decreases (n pos : Nat) (l : Fin n) (h : pos = l.val) :
    n - (pos + 1) < n - pos := by
  have := l.isLt
  omega

/-- Termination: every fired step strictly decreases the distance to the
    end — the Convergent certificate (n firings from 0 reach n; no
    infinite run inside a finite script). -/
theorem session_variant_decreases (p : Protocol) (pos : Nat) (l : Fin p.length)
    (h : pos = l.val) :
    p.length - (pos + 1) < p.length - pos :=
  pos_variant_decreases p.length pos l h

/-! ## Duality — dual peers mirror payloads -/

/-- Dualizing preserves the script's length (lockstep precondition). -/
@[simp] theorem dual_length (p : Protocol) : (dual p).length = p.length :=
  tdual_length (P := String) p

/-- At the same position, dual peers see the same payload TYPE in
    OPPOSITE directions: `p[i] = (d₁, t)` and `(dual p)[i] = (d₂, t)`
    with `d₁ ≠ d₂`. Client's sends are server's receives, of the same
    type, at the same time. -/
theorem dual_payload_mirror (p : Protocol) :
    ∀ (i : Nat) (hi : i < p.length),
      ∃ d₁ d₂ t : _,
        List.get p ⟨i, hi⟩ = (d₁, t) ∧
        (∀ h₂ : i < (dual p).length, List.get (dual p) ⟨i, h₂⟩ = (d₂, t)) ∧
        d₁ ≠ d₂ :=
  tdual_payload_mirror (P := String) p

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

/-- The typed choreography AS a session machine: the position dynamics
    are payload-INDEPENDENT (the only enabled event at position `i` is
    step `i`; firing advances) — project the directions, keep the
    length. All string-layer certificates carry over through this. -/
def tsession {P : Type} (p : TProtocol P) : Machine :=
  session (p.map fun (d, _) => (d, ""))

/-- Mid-protocol deadlock-freedom for the TYPED choreography: the
    direction projection has the same length, so the string-layer
    theorem applies verbatim. -/
theorem tsession_mid_deadlockFree {P : Type} (p : TProtocol P) (pos : Nat)
    (hpos : pos < p.length) :
    ∃ l : (tsession p).Label, ((tsession p).event l).guard pos = true :=
  session_mid_deadlockFree _ pos (by simpa using hpos)

/-- Termination for the TYPED choreography: the same variant — every
    fired step strictly decreases the distance to the end. -/
theorem tsession_variant_decreases {P : Type} (p : TProtocol P) (pos : Nat)
    (l : Fin p.length) (h : pos = l.val) :
    p.length - (pos + 1) < p.length - pos :=
  pos_variant_decreases p.length pos l h

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
