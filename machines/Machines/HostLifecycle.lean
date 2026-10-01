/-
# Machines.HostLifecycle — the host's lifecycle as a machine

THE MODEL (the honest minimal): the wasm host's lifecycle states —
`unloaded → loaded → instantiated → running` plus the terminal states
`stopped` (clean shutdown) and `failed` (a typed refusal or a trap) —
as ONE `machine!` declaration (`Machines.Dsl`, 15-patterns #9's
entourage). This is the Lean-side spec the host implementation
(`crates/mandate-host`) is tested against; the discipline the doctrine
demands (11: the host lifecycle IS a machine — the conformance battery
applies to it like any other; 03 §4: the escape paths — a refusal is
an EXPLICIT transition into a terminal state, never a silent retry;
04 §4: the observer — the phase enum IS the apiObs face, the journal
the auditObs one).

The states (one per host phase, the implementation's `Phase` mirror):

- `unloaded` — no artifact in hand;
- `loaded` — the artifact set read + hash-tied (the skew check ran);
- `instantiated` — the engine compiled the bytes and the linker
  instantiated the instance;
- `running` — the guest export is callable (the start surface
  verified: the export present, the signature lifted);
- `stopped` — TERMINAL, clean (the host released the engine);
- `failed` — TERMINAL, refused (skew / engine refusal / signature
  refusal / trap);
- `zombie` — enumerated but UNREACHABLE (no event targets it): the
  invariant's exclusion face, the wedge control's reason to exist.

The events — the four driven transitions plus the four
environment-induced refusals, each an EVENT the model names (a
refusal is a first-class transition, 03 §4's expensive-explicit rule):

- `load` (unloaded→loaded), `refuseLoad` (unloaded→failed — the skew
  refusal);
- `instantiate` (loaded→instantiated), `refuseInstantiate`
  (loaded→failed — the engine refused the bytes);
- `start` (instantiated→running), `refuseStart` (instantiated→failed
  — the export missing or misigned);
- `trap` (running→failed — a runtime trap or a golden mismatch);
- `stop` (running→stopped — the clean shutdown).

The invariant: the lifecycle never WEDGES — `zombie` is the enumerated
state that satisfies the invariant NOWHERE (no event's action targets
it; every guard keeps it out), so the invariant `s ≠ .zombie` is TRUE
of every reachable state and NON-VACUOUS (it excludes an enumerated
state — the lamp fixture's pattern). The terminal states stay
invariant-covered and REACHABLE (a refusal is a first-class
transition, 03 §4's expensive-explicit rule), so the deadlock-freedom
check carries real content: every live phase keeps an enabled event,
and the wedge control below shows the battery catching its violation.
A first draft's lesson, kept as the record: excluding the terminal
states (`s ≠ .failed ∧ ...`) is WRONG — it makes every refusal event's
safety PO unprovable (a transition INTO an invariant-violating state
is unconstructible); the discipline lives in the transition TABLE,
not in wishing the refusals away.

The Rust-side discipline (the evidence level, named honestly): the
transition LEGALITY is proved here, kernel-checked, for the MODEL. The
implementation is held to the model by TESTED AGREEMENT (the
differential level, 03 §3 — never a theorem): the Rust test suite
mirrors `hostLifecycleTrans` (the value pin below is the source of
record), drives every legal row through the real host, sweeps every
illegal (event, from) pair for the typed refusal, and pins the
refusal rows' terminal face via sabotage. The mirror's drift risk is
the provenance comment on the Rust constant; a change on either side
without the other fails the differential.

The five questions:
- root: TraceModel (01 §3) — the lifecycle is a transition system;
  legality is the derived `step?`, the table cannot drift from it.
- carrier grade: pattern #1 — `machine!`'s generated `step?` is the
  checker; `hostLifecycleTableStep?` the table reading; the generated
  tie theorem the bridge.
- spine reading: none — a model declaration; the host's test suite is
  its consumer.
- ladder rung: rung 0/3 — the safety POs are constructor arguments
  (the macro's `machine_safety` default discharges each), the pins are
  decided values.
- gate row: the axiom sweep over the Machines roots (this module's
  decls are swept; the generated tie carries propext only — the
  core-triple allowlist, pinned below) + the Rust differential in
  `mandate-host`'s test suite.

Named exclusions (the leftover rule): no payload events (the macro's
named exclusion — the lifecycle carries no data in its states), no
restart-from-terminal transitions (the model declares the terminal
states CLOSED; a host that grows a restart transition extends this
file deliberately), no journal/observer state in the enum (the
journal's honesty is the Live loop's invariant — the reopen tooth —
not a lifecycle state).

Core-only: no mathlib, no Batteries (the cone rule).
-/
module

public import Machines.Dsl
@[expose] public section


namespace Machines

/- The machine (block comment, not a docstring — a docstring does not
   attach to a syntax-declared command; the audit's trap). -/
machine! hostLifecycle where
  states: [unloaded, loaded, instantiated, running, stopped, failed, zombie]
  Inv: fun s => s ≠ .zombie
  event: load guard: (fun s => s = .unloaded) action: (fun _ _ => .loaded)
  event: refuseLoad guard: (fun s => s = .unloaded) action: (fun _ _ => .failed)
  event: instantiate guard: (fun s => s = .loaded) action: (fun _ _ => .instantiated)
  event: refuseInstantiate guard: (fun s => s = .loaded) action: (fun _ _ => .failed)
  event: start guard: (fun s => s = .instantiated) action: (fun _ _ => .running)
  event: refuseStart guard: (fun s => s = .instantiated) action: (fun _ _ => .failed)
  event: trap guard: (fun s => s = .running) action: (fun _ _ => .failed)
  event: stop guard: (fun s => s = .running) action: (fun _ _ => .stopped)

/-! ## The pins — the model's committed face -/

/-- THE TRANSITION TABLE, pinned in values: the differential's source
    of record (the Rust suite's `MODEL_TRANS` mirrors THIS — the
    provenance is the Rust file's header; a drift on either side fails
    the differential). One row per (event, from) — each event is
    enabled in exactly one state; the terminal states enable
    nothing. -/
theorem hostLifecycleTrans_pin :
    hostLifecycleTrans
      = [(hostLifecycle.Label.load, .unloaded, .loaded),
         (hostLifecycle.Label.refuseLoad, .unloaded, .failed),
         (hostLifecycle.Label.instantiate, .loaded, .instantiated),
         (hostLifecycle.Label.refuseInstantiate, .loaded, .failed),
         (hostLifecycle.Label.start, .instantiated, .running),
         (hostLifecycle.Label.refuseStart, .instantiated, .failed),
         (hostLifecycle.Label.trap, .running, .failed),
         (hostLifecycle.Label.stop, .running, .stopped)] := by rfl

/-- THE LEGALITY TEETH (the transition legality the host's typed
    errors mirror): the happy path fires in order; the classic
    violations — start before instantiating, stop before running,
    instantiate before loading, load while running — are `none` (the
    guest's CALLS are not transitions: `running` faces them through
    `trap`, the call itself carries no state change). -/
theorem hostLifecycle_legality_pin :
    hostLifecycleTableStep? .load .unloaded = some .loaded
    ∧ hostLifecycleTableStep? .instantiate .loaded = some .instantiated
    ∧ hostLifecycleTableStep? .start .instantiated = some .running
    ∧ hostLifecycleTableStep? .stop .running = some .stopped
    ∧ hostLifecycleTableStep? .start .loaded = none
    ∧ hostLifecycleTableStep? .stop .unloaded = none
    ∧ hostLifecycleTableStep? .instantiate .unloaded = none
    ∧ hostLifecycleTableStep? .load .running = none := by
  decide

/-- THE BATTERY REGISTRATION, pinned exactly — and honest about the
    deadlock row: the battery counts the TERMINAL states as wedges
    (they satisfy the invariant and enable nothing — that is what
    terminal MEANS), so deadlock-freedom refutes with `.failed` as
    the witness. The model pins the refutation rather than
    laundering it: the witness names the terminal face (`.failed`,
    refused-by-design), and the WEDGE CONTROL below shows the same
    check catching a wedged LIVE phase (`.running`) — the battery
    distinguishes the two, which is the discipline. Guard coverage
    (every event fires somewhere) and invariant non-vacuity (the
    invariant excludes the enumerated `zombie` state — a REAL
    invariant, not `True`) prove. -/
theorem hostLifecycle_battery :
    hostLifecycle.battery .unloaded 8
      = [("deadlock-freedom", .refuted (.wedged .failed)),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .proved)] := by rfl

/-! ## The mandatory negative controls (15-patterns #5) -/

/- The SABOTAGED lifecycle: `stop` and `trap` deleted — `running`
   keeps the invariant but enables NOTHING, the lifecycle wedges in
   the live phase, and the battery REFUTES the deadlock-freedom row
   with the wedged state as the witness. The compiler accepts this
   machine; the battery does not. -/
machine! hostLifecycleWedge where
  states: [unloaded, loaded, instantiated, running, stopped, failed, zombie]
  Inv: fun s => s ≠ .zombie
  event: load guard: (fun s => s = .unloaded) action: (fun _ _ => .loaded)
  event: instantiate guard: (fun s => s = .loaded) action: (fun _ _ => .instantiated)
  event: start guard: (fun s => s = .instantiated) action: (fun _ _ => .running)

/-- THE CONTROL: the wedged lifecycle's deadlock row REFUTES, with
    `.running` — the LIVE phase it wedges in — as the witness. The
    model's own battery refutes with `.failed` (terminal by design);
    the sabotaged one with `.running` (a live phase stuck) — the
    witness DISTINGUISHES the designed terminality from the defect,
    which is the tooth. The other two rows still prove (the sabotage
    is sharp, not blanket). -/
theorem hostLifecycleWedge_battery_refutes :
    hostLifecycleWedge.battery .unloaded 8
      = [("deadlock-freedom", .refuted (.wedged .running)),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .proved)] := by rfl

/- THE GENERATED TIE carries the core triple at most — pinned at its
   actual face (a generated proof that grew a `sorry` or an axiom
   beyond the allowlist fails HERE). -/
/-- info: 'Machines.hostLifecycleTableStep?_eq_step?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hostLifecycleTableStep?_eq_step?

end Machines

end -- public section
