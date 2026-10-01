/-
# Wit.Session — the async-lift's WIT face: the world-row ↔ the session bridge

Owner: the sessions/boundary lane's WIT face (the mandate tree,
`wit/` — the module `Wit.Compose`'s header named as its remainder).
Driving decisions: `Machines.AsyncSession` (the WASI async-lift
handshake declared ONCE as a session — the guest's async export and
the host's concurrent call as dual peers) + `Wit.Func`'s async row
(the D2 wave's named remainder, landed) + notes/v3/08-capabilities.md
§9 (protocols as dual-checked sessions).

## The bridge (the honest minimal)

The SESSION machinery — the engine, the step relation, the refusal
teeth — lives in `Machines.Session`/`Machines.AsyncSession` and is NOT
duplicated here (the patterns rule: no parallel table). THIS module is
the WIT face: the reflection that maps a world-row to the tape of the
session its call plays, so the world carrier and the session
discipline can be CHECKED against each other:

- `Wire` — the call's wire ROLES (closed universe): the params (the
  call's ordinary face), the result (the sync row's delivery), the
  task-return + the task handle (the async lift's two moves —
  `Machines.AsyncSession.AsyncWire`'s roles; the VALUE-level pin —
  the 42 — lives there, the roles are what a signature can see).
- `Move` — one directed move (the callee's view: `send`/`recv`).
- `exportTape` — THE DERIVED SHAPE: a world func's export-call
  session, read off the ROW. The sync row: receive the params, send
  the result, done. The async row: receive the params, then the
  lift's two SENDS — task-return, then task handle, done (the
  `guestAsyncExport` shape: deliver the flat result through
  task-return, then return the handle).
- `importTape` — the wired import's session: THE DUAL (every
  direction flipped, the payload sequence equal) — `dual`'s
  definitional face.

## The checks (the teeth at the signature level)

- `import_dual_export` — the duality check: the import row's tape IS
  the export's dual, for EVERY func (definitional — a hand-written
  peer disagreeing on a direction fails it).
- `dual_involutive` — the two peers' agreement is symmetric.
- `sync_async_tapes_ne` — a sync row's session ≠ an async row's
  session: the signature-level face of the join's async conjunct
  (`Wit.Compose.SigEquiv`) — a sync import wired to an async export
  is a duality failure, and the signature relation sees it.

Cone: imports `Wit` + `Wit.World` only (the WIT lane's core face;
no Machines import — the bridge is the REFLECTION, the engine stays
in `machines/`).

The five questions (notes/v3/01-core.md):
- root: Crossing — the world-row read as the session its call plays
  (the async lane's contract face).
- carrier grade: none of its own — the tapes are the closed
  universe's data; the checks are definitional.
- spine reading: the Interpretation stage's session face over the
  world carrier — the duality reading `Wit.Compose` names.
- ladder rung: rung 1 — closed data + definitional checks.
- gate row: the axiom report (the `Wit` root's sweep) + the
  WitTests duality pins.
-/
module


public import Wit
public import Wit.World


@[expose] public section
namespace Wit.Session

/-! ## the wire roles + the moves -/

/-- One wire ROLE of a func's call session. The universe is CLOSED:
    the call's ordinary face (params, result) + the async lift's two
    moves (task-return, task handle). The VALUE-level pin — the flat
    result the host awaits — is `Machines.AsyncSession.AsyncWire`'s;
    a signature sees the roles. -/
inductive Wire where
  /-- The call's named params (one role for the call's argument
      face). -/
  | params
  /-- The sync row's delivery: the result crosses the ordinary
      return. -/
  | result
  /-- The async lift's flat-result move (the callee's
      `[task-return]<fn>` import — the D2 `future<u64>` row's
      runtime face). -/
  | taskReturn
  /-- The async lift's handle move (the lifted body's return; 0 =
      sync-computable, done at the first poll). -/
  | taskHandle
deriving DecidableEq, Repr, BEq

/-- One directed move, in the CALLEE's view: `send` = the callee
    emits the payload, `recv` = the callee consumes it. -/
inductive Move where
  | send : Wire → Move
  | recv : Wire → Move
deriving DecidableEq, Repr, BEq

/-- The dual move: the direction flips, the payload is the same (the
    two peers' one shared wire). -/
def Move.flip : Move → Move
  | .send w => .recv w
  | .recv w => .send w

/-- A session TAPE: the moves in wire order. -/
def Tape := List Move

/-- The tape's dual: every direction flipped (the definitional face
    of `Machines.Session.dual` at the signature level). -/
def dual (t : Tape) : Tape := t.map Move.flip

/-! ## THE DERIVED SHAPE: the world-row's call tape -/

/-- An EXPORT's call session, read off the world func's ROW (the
    callee's view):

- the sync row — receive the params, send the result, done;
- the async row — receive the params, then the lift's two SENDS
  (task-return, then task handle), done — `Machines.AsyncSession`'s
  `guestAsyncExport` shape, derived from the row's `async` flag. -/
def exportTape (f : Func) : Tape :=
  [Move.recv .params]
    ++ (if f.async then [Move.send .taskReturn, Move.send .taskHandle]
        else [Move.send .result])

/-- An IMPORT's call session: the wired consumer's view — THE DUAL of
    the same row's export tape (the recipe's two faces of one
    handshake: the host's concurrent call is the guest's async export
    read from the other side). -/
def importTape (f : Func) : Tape := dual (exportTape f)

/-! ## the checks -/

/-- THE DUALITY CHECK: the import row's tape IS the export's dual —
    for every func, sync or async, definitionally. A hand-written
    peer whose directions do not flip fails this equality at
    elaboration (`Machines.AsyncSession.instHostDualGuest`'s
    discipline at the signature level). -/
theorem import_dual_export (f : Func) : importTape f = dual (exportTape f) := rfl

/-- The duality is symmetric: the dual's dual is the tape (the
    involution's tape face — `Machines.Session.dual_dual`'s
    signature-level reading). -/
theorem dual_involutive (t : Tape) : dual (dual t) = t := by
  show (t.map Move.flip).map Move.flip = t
  induction t with
  | nil => rfl
  | cons m t ih =>
      simp only [List.map_cons]
      cases m <;> simp [ih, Move.flip]

/-- THE SIGNATURE-LEVEL TOOTH: a sync row's call session is not an
    async row's session — the async row appends the lift's two moves.
    The join's async conjunct (`Wit.Compose.SigEquiv`) is this
    inequality lifted to the signature relation: a sync import wired
    to an async export is a duality failure the graph check SURFACES
    (the skew verdict), never a silent pass. -/
theorem sync_async_tapes_ne (f : Func) :
    exportTape { f with async := false }
      ≠ exportTape { f with async := true } := by
  show [Move.recv .params]
        ++ [Move.send .result]
      ≠ [Move.recv .params]
        ++ [Move.send .taskReturn, Move.send .taskHandle]
  simp

end Wit.Session

end -- public section

