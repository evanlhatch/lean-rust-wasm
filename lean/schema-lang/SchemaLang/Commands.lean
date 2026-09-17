/-
# SchemaLang.Commands — the effects/commands surface (W8.6)

The runbook order: `schema_command` items (one sum type per world); guest
fns RETURN commands; host executes; results return as events. The canon
row (Part 2): **the guest↔host effect loop = a session protocol
(commands out, events in)** — with the SESSION ROW's laws (duality,
mid-protocol deadlock-freedom, termination). The vision's kernel rule:
effects cross the boundary ONE way — guest logic returns commands as
DATA; the host executes; results return as events.

This module is the declaration + derivation core, pure data end to end:

- `EffectDecl` — the declaration: one world's command sum-type name and
  event sum-type name (the "one sum type per world" rule; the sum types
  themselves are ordinary `Item.variant`s — the schema declares them,
  nothing new is invented at this layer).
- `EffectDecl.protocol` — THE DERIVED SESSION: the guest sends a member
  of the command sum type, the host answers with an event
  (`[(.snd, commands), (.rcv, events)]`), as a `SchemaLang.Session`
  `TProtocol` at `P := Ty`. The CHOREOGRAPHY MECHANISM is NOT re-proved:
  every law below CITES the generic `Machines.Session` theorem
  (duality `tdual_dual` + the `IsDualOf` peer type; mid-protocol
  deadlock-freedom `session_mid_deadlockFree`; termination
  `session_variant_decreases`) — proved once, instantiated here.
- `toWire` (SchemaLang.Session) — the WIT view: the protocol's payloads
  render through `Ty.witName` = `Emit.Wit.tyWit`, the ONE renderer, so
  the choreography and the interface cannot drift
  (`tdual_toWire` is the bridge).
- `EffectDecl.check` / `EffectWellFormed` / `check_eq_nil_iff` — the
  well-formedness lane (the `Wf`/CheckedProp discipline, the Keys lane's
  shape): both declared names must RESOLVE to variants in the item
  universe. A command type that names a record, or an event type that
  names nothing, is refused by the checker — and at ELABORATION time the
  `IsDualOf` peer type refuses a hand-written non-dual peer (the type
  error the runtime cannot skip).

Deliberate exclusions (no consumer yet; the module grows with the first
one, the Scheduling-lane discipline): the `schema_command` elaboration
surface + registry (the meta lane — the pure lane is the spec of
record); the host EXECUTION semantics and the oracle's host simulation
(W8.10's command-executor generation consumes the same declaration);
guest-side fn-return typing (W8.9's pre/post lane rides the func
surface, not this one); queue/mailbox redelivery (canon Part 3: a
stream + a cursor — the stream rows own it; this lane is the
choreography only).
-/

module

public import Machines.Session
public import SchemaLang.Ty
public import SchemaLang.Item
public import SchemaLang.Session

@[expose] public section

namespace SchemaLang

/-! ## The declaration data -/

/-- One world's effect declaration (data): the world's name, the schema
    name of its COMMAND sum type (the guest's outbound requests), and
    the schema name of its EVENT sum type (the host's answers). One sum
    type per role, per world — the runbook's `schema_command` shape.
    The named types are ordinary schema items (`Item.variant`); the
    checker below refuses names that do not resolve to variants. -/
structure EffectDecl where
  /-- The world the declaration belongs to (diagnostics + provenance). -/
  world : String
  /-- The command sum type: the guest RETURNS these as data. -/
  commands : String
  /-- The event sum type: the host's answers, as data. -/
  events : String
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The well-formedness lane (the Keys shape: checker + relation + bridge) -/

/-- The lane's diagnostic: a declared name did not RESOLVE to a variant
    in the item universe (missing — with a did-you-mean — or resolved to
    a non-variant item, which cannot be a sum type). -/
inductive EffectDiag where
  | missing (world role name : String) (hints : List String)
  | notVariant (world role name : String)
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString EffectDiag where toString := reprStr

/-- One lane (commands or events) of the declaration against the item
    universe: the name must resolve to a VARIANT (a sum type). A record,
    func or resource in the name's slot is a type error at the wire —
    refused here, not misread downstream. -/
def effectLaneCheck (world role : String) (items : List Item)
    (name : String) : List EffectDiag :=
  match items.find? (fun it => it.name == name) with
  | none => [.missing world role name
      (CodegenCore.didYouMean name (Item.typeNames items))]
  | some (.variant _ _) => []
  | some _ => [.notVariant world role name]

/-- The executable checker (the diagnostic authority): BOTH lanes must
    resolve to variants. Empty list = well formed. -/
def EffectDecl.check (items : List Item) (w : EffectDecl) : List EffectDiag :=
  effectLaneCheck w.world "commands" items w.commands
    ++ effectLaneCheck w.world "events" items w.events

/-- One lane as a Prop (the relation side): the name resolves to a
    variant item with that name. -/
def EffectLaneOk (items : List Item) (name : String) : Prop :=
  ∃ cs, items.find? (fun it => it.name == name) = some (.variant name cs)

/-- THE REASONING AUTHORITY: both sum types of the declaration resolve
    to variants in the universe. -/
def EffectWellFormed (items : List Item) (w : EffectDecl) : Prop :=
  EffectLaneOk items w.commands ∧ EffectLaneOk items w.events

/-- The per-lane bridge (the `keyFieldDiags_eq_nil_iff` shape). -/
theorem effectLaneCheck_eq_nil_iff {world role : String} {items : List Item}
    {name : String} :
    effectLaneCheck world role items name = [] ↔ EffectLaneOk items name := by
  unfold effectLaneCheck EffectLaneOk
  cases hx : items.find? (fun it => it.name == name) with
  | none =>
      constructor
      · intro hc; cases hc
      · rintro ⟨cs, h1⟩; cases h1
  | some it =>
      have hsome := List.find?_some hx
      cases it with
      | variant vn cs =>
          have hvn : vn = name := beq_iff_eq.mp hsome
          subst hvn
          constructor
          · intro _; exact ⟨cs, rfl⟩
          · intro _; rfl
      | record _ _ | func _ | resource _ =>
          constructor
          · intro hc; cases hc
          · rintro ⟨cs, h1⟩; cases h1

/-- Master bridge: the executable authority and the relation agree. -/
theorem EffectDecl.check_eq_nil_iff {items : List Item} {w : EffectDecl} :
    w.check items = [] ↔ EffectWellFormed items w := by
  unfold EffectDecl.check EffectWellFormed
  rw [List.append_eq_nil_iff, effectLaneCheck_eq_nil_iff,
    effectLaneCheck_eq_nil_iff]

/-- The bridge, sound direction. -/
theorem EffectDecl.check_sound {items : List Item} {w : EffectDecl} :
    w.check items = [] → EffectWellFormed items w :=
  EffectDecl.check_eq_nil_iff.mp

/-- The bridge, complete direction (the non-vacuity companion: a
    well-formed declaration certifies a clean checker run, so a broken
    one CANNOT be well-formed — the negative controls' warrant). -/
theorem EffectDecl.check_complete {items : List Item} {w : EffectDecl} :
    EffectWellFormed items w → w.check items = [] :=
  EffectDecl.check_eq_nil_iff.mpr

/-! ## The derived session — commands out, events in -/

/-- THE DERIVED PROTOCOL: the guest sends a member of the command sum
    type, the host answers with an event. Two positions — the simplest
    lockstep loop; longer choreographies compose. The payload `.ty`
    references resolve against the schema universe (the universe check)
    and render to WIT through the ONE renderer (`Ty.witName`). -/
def EffectDecl.protocol (w : EffectDecl) : Session.TProtocol :=
  [ (.snd, .ty w.commands), (.rcv, .ty w.events) ]

/-! ### The session row's laws — CITED, not re-proved

Every theorem below is the generic `Machines.Session` fact instantiated
at the derived protocol. The mechanism (duality, mid-protocol
deadlock-freedom, termination) is proved ONCE, generically; a world
declaration INHERITS the laws by composition — the session row's
inheritance rule. -/

/-- DUALITY (cites `Machines.Session.tdual_dual`): the host's script —
    the dual of the guest's — dualized back is the guest's. A peer
    dualized twice is the same script; the loop composes. -/
theorem EffectDecl.protocol_dual (w : EffectDecl) :
    Session.tdual (Session.tdual w.protocol) = w.protocol :=
  Machines.Session.tdual_dual w.protocol

/-- DUALITY, peer-agreement form (cites `Machines.Session.instIsDualOf`):
    the HOST's script is the typed dual, and `IsDualOf` is inhabited
    EXACTLY by the dual — a hand-written host script that disagrees
    (does not flip the guest's directions) fails definitional equality
    at ELABORATION time. Dual-checked, as the canon row requires. -/
instance instEffectIsDualOf (w : EffectDecl) :
    Machines.Session.IsDualOf (Session.tdual w.protocol) w.protocol :=
  Machines.Session.instIsDualOf w.protocol

/-- MID-PROTOCOL DEADLOCK-FREEDOM (cites
    `Machines.Session.session_mid_deadlockFree`): from every position
    strictly inside the derived protocol, a step is enabled — the
    command/event loop cannot wedge between its steps. -/
theorem EffectDecl.protocol_deadlockFree (w : EffectDecl) (pos : Nat)
    (h : pos < w.protocol.length) :
    ∃ l : (Machines.Session.session w.protocol).Label,
      ((Machines.Session.session w.protocol).event l).guard pos = true :=
  Machines.Session.session_mid_deadlockFree w.protocol pos h

/-- TERMINATION (cites `Machines.Session.session_variant_decreases`):
    every fired step strictly decreases the distance to the end — the
    Convergent certificate; exactly `2` firings complete the loop. -/
theorem EffectDecl.protocol_terminates (w : EffectDecl) (pos : Nat)
    (l : Fin w.protocol.length) (h : pos = l.val) :
    w.protocol.length - (pos + 1) < w.protocol.length - pos :=
  Machines.Session.session_variant_decreases w.protocol pos l h

/-! ### The WIT view — the ONE renderer -/

/-- The WIRE SHAPE of the derived protocol: `send <commands>` then
    `receive <events>`, payloads rendered by `Ty.witName` (the same
    text `Emit.Wit.tyWit` puts on the wire — kebab-mangled). -/
theorem EffectDecl.toWire_eq (w : EffectDecl) :
    Session.toWire w.protocol
      = [ (Machines.Session.Dir.snd, Ty.witName (.ty w.commands))
        , (Machines.Session.Dir.rcv, Ty.witName (.ty w.events)) ] := rfl

/-- THE WIT BRIDGE (cites `SchemaLang.Session.tdual_toWire`): the wire
    view of the typed dual IS the wire dual of the wire view — the
    choreography cannot drift from the interface, in either reading. -/
theorem EffectDecl.protocol_wire_bridge (w : EffectDecl) :
    Session.toWire (Session.tdual w.protocol)
      = Machines.Session.tdual (Session.toWire w.protocol) :=
  Session.tdual_toWire w.protocol

/-- The wire PAYLOAD SEQUENCE survives dualing (cites
    `SchemaLang.Session.typed_wire_payloads_agree`, the generic
    `Machines.Session.tdual_types` via the bridge): the guest and host
    exchange the same named types, position for position. -/
theorem EffectDecl.protocol_wire_payloads (w : EffectDecl) :
    (Session.toWire (Session.tdual w.protocol)).map (·.2)
      = (Session.toWire w.protocol).map (·.2) :=
  Session.typed_wire_payloads_agree w.protocol

end SchemaLang
