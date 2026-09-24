/-
# Machines.Session — session types: the protocol declared once, both peers derived

Owned by: the sessions/boundary lane (the mandate tree, `machines/`).
Driving decisions: notes/v3/08-capabilities.md §9 (protocols as
dual-checked sessions; the guest boundary's contracts as boundary
types with adapters generated from them; boundaries closed per app) +
the duality discipline (a protocol declared once, BOTH peers derived,
drift unrepresentable — the choreography cannot drift from the wire).
Mined from: legacy/lean/Machines/Machines/Session.lean (the
`TProtocol` + the duality check + peer agreement as a TYPE — ported as
content, re-carried over the closed branching grammar).

## What lands (the honest minimal)

- `Session P` — the closed session grammar over the payload universe
  `P`: `done` / `send x k` / `recv x k` / `choice a b`. Machines owns
  the MECHANISM once; consumers instantiate `P` (the legacy
  `TProtocol`'s generic-payload discipline, kept). `choice` is the
  honest minimal branch node: a binary selection resolved by a visible
  synchronized `pick` move (see `Session.Move`); a one-sided choice
  with an OWNER party lands with its first multi-party consumer.
- `Session.dual` — the duality, ONE total function over the closed
  grammar (structural recursion: totality by construction, no
  partiality). Every send becomes a receive of the SAME payload and
  vice versa; choice dualizes under the branches.
- The duality LAWS: `dual_dual` (the involution — `dual ∘ dual = id`
  pointwise) + `dual_inj` (duality is injective) + the wire laws
  (`msgs_dual`: the payload sequence is unchanged; `dirs_dual`: the
  directions flip pointwise). The peers cannot talk past each other.
- The projections: `projClient`/`projServer` — each peer's local
  protocol DERIVED from the global one by one function;
  `proj_dual` (the projected peers are dual-compatible — by
  construction, the drift is unrepresentable) + `projServer_inj` (a
  projected server determines the global protocol — a hand-written
  peer that is not the dual is not a projection of anything).
- `IsDualOf` — peer agreement as a TYPE (mined): the generic instance
  is the only witness, so a peer script that disagrees fails
  definitional equality at ELABORATION time.
- The session-as-machine: `sessionMachine` — the continuation engine
  over the landed `Machine` carrier (state = the remaining protocol,
  `sessionStep?` the authoritative `step?`). `follow` (the canonical
  tape) + `follow_runs` (a protocol-following run COMPLETES);
  `Conforms` (a legal trace = a completing run); the refusal lemmas
  (direction- and payload-mismatched moves are refused — the refusals
  are data) + `taken`/`offender` (the named diagnostic: WHICH move at
  WHICH position violated).
- The refinement: a party that performs the first exchange and then
  delays (`boundedImpl`) refines its protocol (`bounded_refines`),
  riding the landed `Coalg.Refines` — the implementation never leaves
  the protocol's legal behavior; `beh_le` is the behavior inclusion.

## The five questions

- **Root**: TraceModel (01-core §3) — the protocol's execution IS a
  machine over the landed carrier; conformance and refinement are the
  derived views, tied to the authoritative `sessionStep?` by
  definition, never a parallel encoding.
- **Carrier grade**: pattern #1 (relation-as-spec + executable checker
  + proved bridge) at the grammar level: `Conforms` (the spec
  reading) + `sessionMachine.run` (the checker) + `follow_runs`/
  `taken_of_run` (the bridges); the duality laws are hand theorems at
  the structure.
- **Spine reading**: none — Machines is a substrate; the guest
  boundary lane (08 §9's contracts once/stream/async) instantiates the
  payload universe and generates adapters from these types.
- **Ladder rung**: the duality/projection/refinement laws are hand
  theorems at the structure (rung 6 — one structural induction each,
  quantified over the open grammar); the per-fixture faces land as
  rung-3 decides in the tests.
- **Gate rows**: the axiom pins in MachinesTests.Session (the
  core-triple surface over the involution + the refinement).

## Named exclusions (the heavy half waits for consumers)

- NO multi-party (n > 2) protocols, NO recursive/replicated choice
  (μ-quantifiers), NO one-sided (owned) choice nodes — each lands
  with its first consumer (the leftover rule).
- NO channel/deadlock analysis ACROSS peers (the dual-checked two-peer
  lockstep is the landed `proj_dual`; cross-peer interleaving needs a
  product machine that no consumer has asked for yet).
- NO payload inspection in the dynamics: position/branch dynamics are
  payload-independent BY CONSTRUCTION (mined discipline).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic
import Machines.Coalg
import Kit.Observer
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Machines

/-! ## The closed session grammar -/

/-- A session protocol over payload universe `P`: send a payload and
    continue, receive a payload and continue, choose between two
    continuations, or end. Closed grammar — no recursion variable, no
    channel passing (the exclusions above). -/
inductive Session (P : Type) where
  | done : Session P
  | send (x : P) (k : Session P) : Session P
  | recv (x : P) (k : Session P) : Session P
  | choice (a b : Session P) : Session P
deriving DecidableEq, Repr, BEq

/-- Conversation direction: this party SENDS the payload, or RECEIVES
    it (mined from legacy/lean/Machines/Machines/Session.lean). -/
inductive Dir where
  | snd | rcv
deriving DecidableEq, Repr, BEq

def Dir.flip : Dir → Dir
  | .snd => .rcv
  | .rcv => .snd

/-- Directions flip twice back to the same one. -/
theorem Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl

/-- A direction differs from its flip (ctor distinctness). -/
theorem Dir.flip_ne (d : Dir) : d ≠ d.flip := by
  cases d <;> intro h <;> cases h

namespace Session

variable {P : Type}

/-! ### The duality: one function, both peers -/

/-- THE DUALITY: flip every direction, keep every payload, dualize
    under the branches. Total by construction (structural recursion
    over the closed grammar — no partiality, no precondition). -/
def dual : Session P → Session P
  | .done => .done
  | .send x k => .recv x (dual k)
  | .recv x k => .send x (dual k)
  | .choice a b => .choice (dual a) (dual b)

/-- THE INVOLUTION (the duality law): `dual ∘ dual = id`, pointwise.
    Dualizing twice returns the original protocol — the duality loses
    nothing and invents nothing. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem dual_dual (s : Session P) : dual (dual s) = s := by
  induction s with
  | done => rfl
  | send x k ih => simp [dual, ih]
  | recv x k ih => simp [dual, ih]
  | choice a b iha ihb => simp [dual, iha, ihb]

/-- The duality is injective (itsinvolution's face): two protocols with
    the same dual are the same protocol. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem dual_inj {s t : Session P} (h : dual s = dual t) : s = t := by
  have h' : dual (dual s) = dual (dual t) := by rw [h]
  rw [dual_dual, dual_dual] at h'
  exact h'

/-! ### The wire laws: duality flips the directions, keeps the payloads -/

/-- The payload sequence a protocol exchanges, in order. -/
def msgs : Session P → List P
  | .done => []
  | .send x k => x :: msgs k
  | .recv x k => x :: msgs k
  | .choice a b => msgs a ++ msgs b

/-- The direction sequence: which side speaks at each message. -/
def dirs : Session P → List Dir
  | .done => []
  | .send _ k => .snd :: dirs k
  | .recv _ k => .rcv :: dirs k
  | .choice a b => dirs a ++ dirs b

/-- THE WIRE LAW (payloads): dual peers exchange the SAME payloads in
    the same order — only the directions differ. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem msgs_dual (s : Session P) : msgs (dual s) = msgs s := by
  induction s with
  | done => rfl
  | send x k ih => simp [dual, msgs, ih]
  | recv x k ih => simp [dual, msgs, ih]
  | choice a b iha ihb => simp [dual, msgs, iha, ihb]

/-- THE WIRE LAW (directions): dual peers oppose pointwise — every send
    on one side is a receive on the other. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem dirs_dual (s : Session P) : dirs (dual s) = (dirs s).map Dir.flip := by
  induction s with
  | done => rfl
  | send x k ih => simp [dual, dirs, Dir.flip, ih]
  | recv x k ih => simp [dual, dirs, Dir.flip, ih]
  | choice a b iha ihb => simp [dual, dirs, iha, ihb]

/-! ### The projections: each peer derived from the global protocol -/

/-- The CLIENT's local protocol: the global one as written. -/
def projClient (g : Session P) : Session P := g

/-- The SERVER's local protocol: the dual — DERIVED, never hand-written
    (the duality discipline: declare once, both peers derived). -/
def projServer (g : Session P) : Session P := dual g

/-- THE PROJECTION CORRECTNESS (the duality discipline's content): the
    projected peers are dual-compatible BY CONSTRUCTION — `proj_dual`
    holds definitionally, so the choreography cannot drift from the
    wire: there is no room for a server that disagrees with the client
    it was projected from. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem proj_dual (g : Session P) : dual (projClient g) = projServer g := rfl

/-- A projected server determines the global protocol (the involution's
    face at the projection): a hand-written "server" that is not some
    protocol's dual is not a projection of anything. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem projServer_inj {g₁ g₂ : Session P}
    (h : projServer g₁ = projServer g₂) : g₁ = g₂ :=
  dual_inj h

/-! ### Peer agreement as a TYPE (mined from legacy) -/

/-- `IsDualOf theirs mine` is inhabited EXACTLY when `theirs` is the
    dual of `mine`. The generic instance is the only witness, so a
    hand-written peer whose direction doesn't flip — or whose payload
    differs at any position — fails DEFINITIONAL equality at
    ELABORATION time: the mismatched conversation does not compile. -/
class IsDualOf (theirs mine : Session P) : Prop where
  /-- The agreeing peer's script IS the dual's, definitionally. -/
  agrees : theirs = dual mine

/-- The one witness: the dual always agrees with its original. -/
@[nolint linter.guestlang.zeroCitation "public API: the IsDualOf witness (consumed by typeclass resolution, not by name)"]
instance instIsDualOf (p : Session P) : IsDualOf (dual p) p := ⟨rfl⟩

-- The class's field: the projection the Prop-class auto-generates —
-- the agreeing-peer law's API face, read through the class, never
-- cited by name outside.
attribute [nolint linter.guestlang.zeroCitation "public API: the IsDualOf class's field (the agreeing-peer law, read through the class)"]
  IsDualOf.agrees

/-! ### The session-as-machine: the continuation engine -/

/-- One observable move of a session conversation: a branch selection
    at a choice node (visible and synchronized — the honest minimal's
    resolved-by-the-environment choice), or a typed message. -/
inductive Move (P : Type) where
  | pick (b : Bool) : Move P
  | step (d : Dir) (x : P) : Move P
deriving DecidableEq, Repr, BEq

/-- THE AUTHORITATIVE ENGINE (01-core §3): the transition function of
    the session machine. State = the remaining protocol; at a message
    node only the matching `(direction, payload)` move fires (payload
    equality is checked — the wire is typed); at a choice node only the
    `pick` for one branch fires; `done` refuses everything (the
    conversation is over — the refusal is data, never a silent
    self-loop). -/
def sessionStep? [DecidableEq P] : Session P → Move P → Option (Session P)
  | .send x k, .step .snd y => if x = y then some k else none
  | .recv x k, .step .rcv y => if x = y then some k else none
  | .choice a _, .pick true => some a
  | .choice _ b, .pick false => some b
  | _, _ => none

/-- The session machine over the landed carrier (Basic.lean): the state
    is the REMAINING protocol, so the machine is protocol-independent —
    the protocol IS the initial state. -/
def sessionMachine [DecidableEq P] : Machine (Session P) (Move P) :=
  ⟨sessionStep?⟩

/-- The engine tie (pattern #1's face at the machine): the machine's
    `step?` IS the authoritative engine — cited, never re-proved. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem sessionMachine_step [DecidableEq P] (s : Session P) (mv : Move P) :
    sessionMachine.step? s mv = sessionStep? s mv := rfl

/-- The canonical tape: the moves a party that FOLLOWS the protocol
    emits — its own messages in order, the left branch at each choice
    (the canonical resolution). -/
def follow : Session P → List (Move P)
  | .done => []
  | .send x k => .step .snd x :: follow k
  | .recv x k => .step .rcv x :: follow k
  | .choice a _ => .pick true :: follow a

/-- The self-move fires (the payload check passes against itself). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem stepSelf_snd [DecidableEq P] (x : P) (k : Session P) :
    sessionStep? (.send x k) (.step .snd x) = some k := by
  simp [sessionStep?]

@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem stepSelf_rcv [DecidableEq P] (x : P) (k : Session P) :
    sessionStep? (.recv x k) (.step .rcv x) = some k := by
  simp [sessionStep?]

/-- THE CONFORMANCE BRIDGE: a protocol-following run COMPLETES — the
    canonical tape runs the machine from the protocol to `done`. A run
    that follows the protocol is a legal trace. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem follow_runs [DecidableEq P] (s : Session P) :
    sessionMachine.run s (follow s) = some .done := by
  induction s with
  | done => rfl
  | send x k ih =>
      show sessionMachine.run _ (.step .snd x :: follow k) = some .done
      rw [Machine.run_cons, sessionMachine_step, stepSelf_snd, Option.bind_some, ih]
  | recv x k ih =>
      show sessionMachine.run _ (.step .rcv x :: follow k) = some .done
      rw [Machine.run_cons, sessionMachine_step, stepSelf_rcv, Option.bind_some, ih]
  | choice a b iha ihb =>
      show sessionMachine.run _ (.pick true :: follow a) = some .done
      rw [Machine.run_cons, sessionMachine_step,
        show sessionStep? (.choice a b) (.pick true) = some a from rfl,
        Option.bind_some, iha]

/-- CONFORMANCE (the spec reading of the legal trace): a tape conforms
    to a protocol when the session machine, started at the protocol,
    consumes the whole tape and ends `done`. -/
def Conforms [DecidableEq P] (g : Session P) (t : List (Move P)) : Prop :=
  sessionMachine.run g t = some .done

/-! ### The refusals (the conformance teeth at the lemma level) -/

/-- A send-node refuses a RECEIVE move — the direction is wrong; the
    refusal is data, not a silent self-loop. -/
@[nolint linter.guestlang.zeroCitation "public API: the lane's refusal lemmas (Machines.lean's surface index)"]
theorem dirRefused_snd [DecidableEq P] (x y : P) (k : Session P) :
    sessionStep? (.send x k) (.step .rcv y) = none := rfl

@[nolint linter.guestlang.zeroCitation "public API: the lane's refusal lemmas (Machines.lean's surface index)"]
theorem dirRefused_rcv [DecidableEq P] (x y : P) (k : Session P) :
    sessionStep? (.recv x k) (.step .snd y) = none := rfl

/-- A message node refuses a MISMATCHED payload — the wire is typed. -/
@[nolint linter.guestlang.zeroCitation "public API: the lane's refusal lemmas (Machines.lean's surface index)"]
theorem payloadRefused_snd [DecidableEq P] (x y : P) (k : Session P) (h : ¬ x = y) :
    sessionStep? (.send x k) (.step .snd y) = none := by
  simp only [sessionStep?]
  split
  · exact absurd ‹x = y› h
  · rfl

@[nolint linter.guestlang.zeroCitation "public API: the lane's refusal lemmas (Machines.lean's surface index)"]
theorem payloadRefused_rcv [DecidableEq P] (x y : P) (k : Session P) (h : ¬ x = y) :
    sessionStep? (.recv x k) (.step .rcv y) = none := by
  simp only [sessionStep?]
  split
  · exact absurd ‹x = y› h
  · rfl

/-- A completed protocol refuses every move (there is nothing left to
    exchange — `end` is terminal). -/
@[nolint linter.guestlang.zeroCitation "public API: the lane's refusal lemmas (Machines.lean's surface index)"]
theorem doneRefused [DecidableEq P] (mv : Move P) :
    sessionStep? .done mv = none := rfl

/-! ### The named diagnostic: which move violated, where -/

/-- How many moves the engine consumed before refusing (or the tape
    ending): the diagnostic's POSITION. -/
def taken [DecidableEq P] (s : Session P) : List (Move P) → Nat
  | [] => 0
  | mv :: rest =>
      match sessionStep? s mv with
      | none => 0
      | some s' => taken s' rest + 1

/-- THE DIAGNOSTIC BRIDGE: on a CONFORMING tape the engine consumes
    everything — the taken count is the tape's length. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem taken_of_run [DecidableEq P] (s : Session P) :
    ∀ (t : List (Move P)) (s' : Session P),
      sessionMachine.run s t = some s' → taken s t = t.length := by
  intro t
  induction t generalizing s with
  | nil =>
      intro s' h
      rw [Machine.run_nil] at h
      simp [taken]
  | cons mv rest ih =>
      intro s' h
      rw [Machine.run_cons, sessionMachine_step] at h
      obtain ⟨s₀, hstep, hrun⟩ := Option.bind_eq_some_iff.mp h
      have hst := ih s₀ s' hrun
      rw [taken, hstep]
      simp [hst]

/-- THE NAMED DIAGNOSTIC: the first move the protocol refuses — its
    position (the moves consumed before the refusal) and the move
    itself. `none` = no refusal (the tape ran out at or before the
    protocol ended). -/
def offender [DecidableEq P] (s : Session P) (t : List (Move P)) :
    Option (Nat × Move P) :=
  (t[taken s t]?).map fun mv => (taken s t, mv)

/-! ### The refinement: a delaying implementation refines its protocol -/

/-- What one protocol node SHOWS: the message it is waiting to exchange,
    if any (choice/done nodes show nothing — the choice is invisible
    until the picked branch speaks). The observer the refinement speaks
    through. -/
def nodeSee : Session P → Option (Dir × P)
  | .send x _ => some (.snd, x)
  | .recv x _ => some (.rcv, x)
  | _ => none

/-- The node observer over the flag-paired state. -/
def nodeObs : Kit.Observer (Bool × Session P) (Option (Dir × P)) :=
  ⟨fun p => nodeSee p.2⟩

/-- The SPEC engine over the flag-paired state: the flag is refinement
    bookkeeping — the spec ignores it (the tie below is definitional).
    The flag pairing exists because `Coalg.Refines` relates machines
    over ONE state type; the bookkeeping rides along on both sides. -/
def mSpec [DecidableEq P] : Machine (Bool × Session P) (Move P) :=
  ⟨fun p mv => (sessionStep? p.2 mv).map fun k => (p.1, k)⟩

/-- The IMPL: performs the FIRST exchange, then holds forever — a party
    that answers once and delays. -/
def boundedImpl [DecidableEq P] : Machine (Bool × Session P) (Move P) :=
  ⟨fun p mv => match p.1 with
    | false => (sessionStep? p.2 mv).map fun k => (true, k)
    | true => none⟩

/-- The impl's holding face refuses everything. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem impl_holds [DecidableEq P] (s : Session P) (mv : Move P) :
    boundedImpl.step? (true, s) mv = none := rfl

/-- The refinement relation: the impl is FRESH at the spec's node (the
    same continuation, the flag still false), or the impl is HOLDING —
    and a holding party tracks every move the spec makes. -/
def Holds (p q : Bool × Session P) : Prop :=
  p.1 = true ∨ (p.2 = q.2 ∧ q.1 = false)

/-- The IMPL coalgebra's observe at a HOLDING state: none. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem observeHold [DecidableEq P] (s : Session P) (i : Move P) :
    (⟨boundedImpl, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P))).observe
      (true, s) i = none := by
  show ((boundedImpl.step? (true, s) i).map
      fun s' => (nodeObs.see s', s')) = none
  rw [impl_holds]
  rfl

/-- The IMPL coalgebra's observe at a FRESH state that refuses. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem observeFresh_none [DecidableEq P] (k : Session P) (i : Move P)
    (h : sessionStep? k i = none) :
    (⟨boundedImpl, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P))).observe
      (false, k) i = none := by
  show (((sessionStep? k i).map fun k' => (true, k')).map
      fun s' => (nodeObs.see s', s')) = none
  rw [h]
  rfl

/-- The SPEC coalgebra's observe at a FRESH state that refuses. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem observeSpec_none [DecidableEq P] (k : Session P) (i : Move P)
    (h : sessionStep? k i = none) :
    (⟨mSpec, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P))).observe
      (false, k) i = none := by
  show (((sessionStep? k i).map fun k' => (false, k')).map
      fun s' => (nodeObs.see s', s')) = none
  rw [h]
  rfl

/-- Both observes at a FRESH state that fires — the same observation,
    the impl flagged holding, the spec flagged fresh. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem observeFresh_some [DecidableEq P] (k : Session P) (i : Move P)
    (k' : Session P) (h : sessionStep? k i = some k') :
    (⟨boundedImpl, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P))).observe
        (false, k) i
      = some (nodeSee k', (true, k'))
    ∧ (⟨mSpec, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P))).observe
        (false, k) i
      = some (nodeSee k', (false, k')) := by
  refine ⟨?_, ?_⟩
  · show (((sessionStep? k i).map fun j => (true, j)).map
      fun s' => (nodeObs.see s', s')) = some (nodeSee k', (true, k'))
    rw [h]
    rfl
  · show (((sessionStep? k i).map fun j => (false, j)).map
      fun s' => (nodeObs.see s', s')) = some (nodeSee k', (false, k'))
    rw [h]
    rfl

/-- THE REFINEMENT (the honest minimal of impl ≤ spec, riding the
    landed `Coalg.Refines`): an implementation that performs the first
    exchange and then delays refines its protocol — it never produces
    an observation the protocol forbids (`beh_le` is the behavior
    inclusion), and while holding it tracks every move the spec makes.
    The impl may not speak when the protocol does not: the same
    authoritative engine fires on both fresh faces. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem bounded_refines [DecidableEq P] :
    Refines
      (⟨boundedImpl, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P)))
      (⟨mSpec, nodeObs⟩ :
        Coalgebra (Bool × Session P) (Move P) (Option (Dir × P)))
      Holds := by
  refine ⟨?_⟩
  intro s₁ s₂ h i
  obtain ⟨b₁, k₁⟩ := s₁
  obtain ⟨b₂, k₂⟩ := s₂
  rcases h with hhold | ⟨heq, hsf⟩
  · -- the holding face: the impl refuses; whatever the spec does is tracked
    simp only at hhold
    subst hhold
    exact Or.inl ⟨observeHold k₁ i, fun _ _ _ => Or.inl rfl⟩
  · -- the fresh face: same node
    simp only at hsf
    subst hsf
    simp only at heq
    subst heq
    cases b₁ with
    | true => exact Or.inl ⟨observeHold k₁ i, fun _ _ _ => Or.inl rfl⟩
    | false =>
        cases hs : sessionStep? k₁ i with
        | none =>
            refine Or.inl ⟨observeFresh_none k₁ i hs, ?_⟩
            intro o₂ s₂' hsSpec
            rw [observeSpec_none k₁ i hs] at hsSpec
            exact absurd hsSpec (by simp)
        | some k' =>
            exact Or.inr ⟨nodeSee k', (true, k'), (false, k'),
              (observeFresh_some k₁ i k' hs).1, (observeFresh_some k₁ i k' hs).2,
              Or.inl rfl⟩

end Session

end Machines
