//! THE LIFECYCLE — the host as a state machine, disciplined by the
//! Lean model `Machines.HostLifecycle` (the `machine!` declaration:
//! states `unloaded → loaded → instantiated → running` + the terminal
//! `stopped`/`failed`; doctrine: notes/v3/11 — the host lifecycle IS a
//! machine and the conformance battery applies; notes/v3/03 §4 — the
//! escape paths: a refusal is an EXPLICIT transition into a terminal
//! state, never a silent retry or a bare panic; notes/v3/04 §4 — the
//! observer: the phase enum is the apiObs face).
//!
//! THE EVIDENCE LEVEL (the honest cut, named): the model's transition
//! legality is PROVED in Lean (kernel-checked, the generated table↔step
//! tie); THIS side is held to the model by TESTED AGREEMENT — the
//! differential level (03 §3), never a theorem. The mechanism:
//!
//! - [`MODEL_TRANS`] mirrors the model's `hostLifecycleTrans` (the
//!   Lean value pin `hostLifecycleTrans_pin` is the source of record —
//!   the provenance is THIS comment plus the Lean pin; a change on
//!   either side without the other fails the differential in
//!   `tests/lifecycle.rs`, which drives every legal row through the
//!   real host and sweeps every illegal (event, from) pair);
//! - every phase boundary checks the transition and refuses ILLEGAL
//!   ones with the typed [`crate::HostError::Lifecycle`] — the
//!   phase-guard IS the discipline (a run export before instantiation
//!   refuses; nothing dereferences a half-built engine);
//! - the model's refusal events are the terminal face: a load/instantiate/
//!   start refusal moves the host to [`Phase::Failed`] and surfaces the
//!   typed error — the escape path is a transition, exactly as declared.
//!
//! WHAT THIS ISN'T: no second semantics. The lean module owns the
//! model; this file owns the IMPLEMENTATION's discipline — the state
//! enum, the guards at the boundaries, and the refusal routing. The
//! component machinery itself is `component.rs`'s (the skew-checked
//! load, the typed lift); this module sequences it.

use std::path::Path;

use wasmtime::component::{Component, Instance};
use wasmtime::{Engine, Store};

use crate::component::{load_component, GUEST_EXPORT, GUEST_GOLDEN};
use crate::engine::instantiate_component_module;
use crate::{HostError, HostError::Lifecycle};

/// The lifecycle phases — the mirror of `Machines.hostLifecycle.State`
/// (the model's enumeration; `zombie` is the model's invariant face —
/// an unreachable wedge state — and has no implementation image: an
/// unreachable state needs no code).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// No artifact in hand.
    Unloaded,
    /// The artifact set read + hash-tied (the skew check ran).
    Loaded,
    /// The engine compiled the bytes; the linker instantiated.
    Instantiated,
    /// The guest export is callable (the start surface verified).
    Running,
    /// TERMINAL, clean — the engine resources are released.
    Stopped,
    /// TERMINAL, refused — skew / engine refusal / signature refusal /
    /// trap (the model's `refuseLoad`/`refuseInstantiate`/
    /// `refuseStart`/`trap` targets).
    Failed,
}

impl Phase {
    /// The phase's spelling (the error's + the differential's
    /// vocabulary — mirrors the model's constructor names).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Unloaded => "unloaded",
            Self::Loaded => "loaded",
            Self::Instantiated => "instantiated",
            Self::Running => "running",
            Self::Stopped => "stopped",
            Self::Failed => "failed",
        }
    }

    /// Every phase (the illegal-transition sweep's space — the model's
    /// enumerated states minus `zombie`).
    pub const ALL: [Phase; 6] = [
        Self::Unloaded,
        Self::Loaded,
        Self::Instantiated,
        Self::Running,
        Self::Stopped,
        Self::Failed,
    ];
}

/// The driven events' names (the model's Label ctors; the refusal
/// events are environment-induced and named in [`MODEL_TRANS`] only).
pub const EVENT_LOAD: &str = "load";
pub const EVENT_INSTANTIATE: &str = "instantiate";
pub const EVENT_START: &str = "start";
pub const EVENT_STOP: &str = "stop";
/// The export call is NOT a model transition (the call is activity
/// WITHIN `running`; the model's `trap` is its refusal face) — but the
/// phase guard's refusal names it, so the differential can sweep it.
pub const EVENT_CALL: &str = "call";

/// One row of the model's transition table: (event, from, to).
pub type ModelTransition = (&'static str, Phase, Phase);

/// THE MODEL'S TRANSITION TABLE — the Rust mirror of Lean's
/// `hostLifecycleTrans` (the source of record is
/// `Machines.HostLifecycle.hostLifecycleTrans_pin`; the differential
/// in `tests/lifecycle.rs` fails on drift). One row per (event, from):
/// each event is enabled in exactly one phase; the terminal phases
/// enable nothing.
pub const MODEL_TRANS: &[ModelTransition] = &[
    (EVENT_LOAD, Phase::Unloaded, Phase::Loaded),
    ("refuseLoad", Phase::Unloaded, Phase::Failed),
    (EVENT_INSTANTIATE, Phase::Loaded, Phase::Instantiated),
    ("refuseInstantiate", Phase::Loaded, Phase::Failed),
    (EVENT_START, Phase::Instantiated, Phase::Running),
    ("refuseStart", Phase::Instantiated, Phase::Failed),
    ("trap", Phase::Running, Phase::Failed),
    (EVENT_STOP, Phase::Running, Phase::Stopped),
];

/// THE HOST MACHINE: the component lane's loading/instantiation/call
/// sequenced through the model's lifecycle. The invariants:
///
/// - the phase is total and honest — every constructor-visible field
///   is `Some` exactly when the phase demands it (`Loaded` carries the
///   wasm; `Instantiated`/`Running` carry the engine triple); a
///   mismatched field would be an internal-skew bug, and the accessors
///   refuse it typed rather than unwrap;
/// - every transition checks the model's legality FIRST (the typed
///   [`HostError::Lifecycle`] refusal, phase unchanged);
/// - every REFUSAL the environment induces (skew, engine refusal,
///   signature refusal, trap) lands in [`Phase::Failed`] — the model's
///   terminal face, never a half-state.
///
/// (Debug is hand-rolled: the engine triple's types do not all carry
/// Debug, and the phase is the honest observable anyway — the fields
/// are the phase's private consequence.)
pub struct HostMachine {
    phase: Phase,
    wasm: Option<Vec<u8>>,
    engine: Option<Engine>,
    component: Option<Component>,
    instance: Option<Instance>,
    store: Option<Store<()>>,
}

impl std::fmt::Debug for HostMachine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HostMachine").field("phase", &self.phase.name()).finish()
    }
}

impl Default for HostMachine {
    fn default() -> Self {
        Self::new()
    }
}

impl HostMachine {
    /// A fresh host: [`Phase::Unloaded`] (the model's initial state).
    /// THE INIT DISCIPLINE (wave-30 C1): the composition root's
    /// observability init runs HERE (idempotent upstream — a second init
    /// is ignored), so a machine is never built against an unregistered
    /// fault registry or an uninitialized deployment.
    #[must_use]
    pub fn new() -> Self {
        crate::init_observability();
        Self {
            phase: Phase::Unloaded,
            wasm: None,
            engine: None,
            component: None,
            instance: None,
            store: None,
        }
    }

    /// The current phase (the apiObs face — 04 §4).
    #[must_use]
    pub fn phase(&self) -> Phase {
        self.phase
    }

    /// The illegal-transition guard: `event` is legal only from
    /// `legal`. The refusal is TYPED and leaves the phase unchanged —
    /// the discipline is the check, not a convention.
    fn guard(&self, event: &'static str, legal: Phase) -> Result<(), HostError> {
        if self.phase == legal {
            Ok(())
        } else {
            Err(Lifecycle { from: self.phase.name(), event })
        }
    }

    /// THE LOAD: the artifact set read + skew-checked (the model's
    /// `load`, legal only from `Unloaded`). A refusal (hash mismatch,
    /// malformed sidecar, world skew) is the model's `refuseLoad` —
    /// the host lands in [`Phase::Failed`] and the typed error
    /// surfaces; the host never carries half-read artifacts.
    ///
    /// # Errors
    /// The illegal transition (typed `Lifecycle`), or the load's own
    /// typed refusal (which also moves the host to `Failed`).
    pub fn load(&mut self, gen_dir: &Path) -> Result<(), HostError> {
        // THE OBSERVABILITY FACE (C1): one dotted-static scope per host
        // operation — 'static low-cardinality names ONLY; high-cardinality
        // data rides log kv, never scope tags. Bind the guard: a dropped
        // guard is a zero-length span.
        let _span = fast_observe::scope!("host.load");
        self.guard(EVENT_LOAD, Phase::Unloaded)?;
        match load_component(gen_dir) {
            Ok(wasm) => {
                self.wasm = Some(wasm);
                self.phase = Phase::Loaded;
                Ok(())
            }
            // refuseLoad: unloaded → failed — the escape path is a
            // transition (03 §4).
            Err(e) => {
                self.phase = Phase::Failed;
                Err(e)
            }
        }
    }

    /// THE INSTANTIATE: the engine compiles the checked bytes and the
    /// linker instantiates the instance (the model's `instantiate`,
    /// legal only from `Loaded`). An engine refusal is the model's
    /// `refuseInstantiate` — [`Phase::Failed`].
    ///
    /// # Errors
    /// The illegal transition, an internal-skew absence of the loaded
    /// bytes (typed `Incomplete` — the phase discipline makes this
    /// unreachable), or the engine's compile/instantiate refusal.
    pub fn instantiate(&mut self) -> Result<(), HostError> {
        let _span = fast_observe::scope!("host.instantiate");
        self.guard(EVENT_INSTANTIATE, Phase::Loaded)?;
        let wasm = self
            .wasm
            .clone()
            .ok_or(HostError::Incomplete("instantiate: the Loaded phase lost its wasm"))?;
        match Self::instantiate_impl(&wasm) {
            Ok((engine, component, instance, store)) => {
                self.engine = Some(engine);
                self.component = Some(component);
                self.instance = Some(instance);
                self.store = Some(store);
                self.phase = Phase::Instantiated;
                Ok(())
            }
            Err(e) => {
                self.phase = Phase::Failed;
                Err(e)
            }
        }
    }

    /// The instantiation's engine work (the phase commit happens at
    /// ONE site, above): the shared component skeleton's whole triple.
    fn instantiate_impl(
        wasm: &[u8],
    ) -> Result<(Engine, Component, Instance, Store<()>), HostError> {
        let (engine, component, store, instance) = instantiate_component_module(wasm)?;
        Ok((engine, component, instance, store))
    }

    /// THE START: the export surface verified — the export present,
    /// the typed lift accepting — and the host is [`Phase::Running`]
    /// (the model's `start`, legal only from `Instantiated`). A
    /// missing or misigned export is the model's `refuseStart` —
    /// [`Phase::Failed`]; the world's contract is consumed HERE, not
    /// mid-call.
    ///
    /// # Errors
    /// The illegal transition, the internal-skew absence of the
    /// engine triple (typed `Incomplete`), or the refusal pair
    /// (`MissingExport` / `ComponentSignature`).
    pub fn start(&mut self) -> Result<(), HostError> {
        let _span = fast_observe::scope!("host.start");
        self.guard(EVENT_START, Phase::Instantiated)?;
        let out = (|| {
            let store = self
                .store
                .as_mut()
                .ok_or(HostError::Incomplete("start: the Instantiated phase lost its store"))?;
            let instance = self
                .instance
                .as_ref()
                .ok_or(HostError::Incomplete("start: the Instantiated phase lost its instance"))?;
            let func = instance
                .get_func(&mut *store, GUEST_EXPORT)
                .ok_or_else(|| HostError::MissingExport(GUEST_EXPORT.to_string()))?;
            // The typed lift IS the signature check (the same tooth
            // component.rs pins): a drifted signature refuses at
            // start, never mid-call.
            func.typed::<(u64, u64), (u64,)>(&*store)
                .map_err(|_| HostError::ComponentSignature("add64 : (u64, u64) -> u64"))
        })();
        match out {
            Ok(_typed) => {
                self.phase = Phase::Running;
                Ok(())
            }
            // refuseStart: instantiated → failed.
            Err(e) => {
                self.phase = Phase::Failed;
                Err(e)
            }
        }
    }

    /// THE CALL: the guest export with TYPED values (legal only from
    /// `Running` — the task's named tooth: a run export before
    /// instantiation refuses, TYPED). The call is NOT a model
    /// transition — it is `running`'s activity; the phase stays
    /// `Running` across a successful call. A trap (or any engine
    /// fault) or a golden mismatch is the model's `trap` — the host
    /// lands in [`Phase::Failed`].
    ///
    /// # Errors
    /// The illegal transition, the internal-skew absence of the
    /// engine triple (typed `Incomplete`), the engine fault, or the
    /// golden mismatch (`ComponentAnswerMismatch`).
    pub fn call(&mut self, a: u64, b: u64) -> Result<u64, HostError> {
        let _span = fast_observe::scope!("host.call");
        self.guard(EVENT_CALL, Phase::Running)?;
        let out = (|| {
            let store = self
                .store
                .as_mut()
                .ok_or(HostError::Incomplete("call: the Running phase lost its store"))?;
            let instance = self
                .instance
                .as_ref()
                .ok_or(HostError::Incomplete("call: the Running phase lost its instance"))?;
            let func = instance
                .get_func(&mut *store, GUEST_EXPORT)
                .ok_or_else(|| HostError::MissingExport(GUEST_EXPORT.to_string()))?;
            let typed = func
                .typed::<(u64, u64), (u64,)>(&*store)
                .map_err(|_| HostError::ComponentSignature("add64 : (u64, u64) -> u64"))?;
            let (got,) = typed
                .call(&mut *store, (a, b))
                .map_err(|e| HostError::Engine(format!("call {GUEST_EXPORT}: {e:?}")))?;
            Ok(got)
        })();
        match out {
            Ok(got) if got == GUEST_GOLDEN => Ok(got),
            Ok(got) => {
                // The golden discipline's trap face: the host runs TO
                // the seeded fact; anything else refuses — and the
                // lifecycle treats it as the model's `trap`.
                self.phase = Phase::Failed;
                Err(HostError::ComponentAnswerMismatch { got, expected: GUEST_GOLDEN })
            }
            Err(e) => {
                self.phase = Phase::Failed;
                Err(e)
            }
        }
    }

    /// THE STOP: the clean shutdown (the model's `stop`, legal only
    /// from `Running`) — the engine resources are released and the
    /// host lands in the TERMINAL [`Phase::Stopped`].
    ///
    /// # Errors
    /// The illegal transition.
    pub fn stop(&mut self) -> Result<(), HostError> {
        let _span = fast_observe::scope!("host.stop");
        self.guard(EVENT_STOP, Phase::Running)?;
        self.engine = None;
        self.component = None;
        self.instance = None;
        self.store = None;
        self.phase = Phase::Stopped;
        Ok(())
    }
}
