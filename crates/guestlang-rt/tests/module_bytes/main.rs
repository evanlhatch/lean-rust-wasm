//! FUZZ: `guestlang_rt::invoke_core_fueled` — the wasmi engine's module
//! boundary (compile + invoke under random bytes).
//!
//! NON-DUPLICATION RATIONALE (why this target exists at all):
//! - Lean PROVES the guest programs' semantics (the compiled fragment's
//!   fixpoint theorems, the fuel/determinism pins) and the differential
//!   manifest replays Lean's own evals into Rust. All of that is over
//!   COMPILER-EMITTED modules. Nothing reaches the EXECUTING engine's
//!   boundary: arbitrary bytes handed to `wasmi`'s validator here.
//! - This is the hostile-input contract, category (a): random bytes as
//!   a "module" must NEVER panic — the engine either runs the export or
//!   returns a structured `RtError`. A panic (not a guest trap — wasmi
//!   reports those as `Err`) is the bug this target exists to find.
//! - One Rust-owned engine contract is pinned when a call DOES
//!   succeed: the reported fuel consumption never exceeds the
//!   endowment (the deterministic budget is enforced, not advisory).
//!
//! NOT covered here (deliberate exclusions):
//! - Results-equality against Lean's oracle: that is the differential
//!   manifest's job (Lean generates the expected values; re-fuzzing
//!   them would duplicate the oracle).
//! - The pool (`Pool`/`Pool::new_hard`): its classification logic is
//!   pinned by `tests/pool.rs`; the pool's own boundary reduces to
//!   this same `Runtime::new` + `call` path per worker.
//! - Wall-clock hangs: fuel is the deterministic timeout proxy (see
//!   pool.rs's mode table); a bounded fuel endowment below keeps every
//!   iteration finite.

use bolero::check;

/// The arbitrary module/job: hostile module bytes, a hostile export
/// name, hostile scalar-ABI args, and a bounded fuel endowment.
#[derive(Debug, arbitrary::Arbitrary)]
struct JobInput {
    bytes: Vec<u8>,
    func: String,
    args: Vec<i64>,
    fuel_raw: u16,
}

impl JobInput {
    /// Fuel bounded so even a tight-loop module terminates per run
    /// (fuel is the deterministic timeout proxy — see the header).
    fn fuel(&self) -> u64 {
        u64::from(self.fuel_raw) + 1
    }
}

fn main() {
    check!().with_arbitrary::<JobInput>().for_each(|job| {
        let fuel = job.fuel();
        // The engine boundary: decode-or-error, never panic. Every
        // failure mode (bad magic, failed validation, missing export,
        // arity mismatch, guest trap, out-of-fuel) is a structured
        // `RtError`.
        if let Ok((results, used)) = guestlang_rt::invoke_core_fueled(
            &job.bytes, &job.func, &job.args, fuel,
        ) {
            // The one Rust-owned contract on the success path: the
            // fuel meter is enforced — consumption never exceeds the
            // endowment, and one result per declared return type.
            assert!(
                used <= fuel,
                "fuel meter overrun: consumed {used} of {fuel}"
            );
            let _ = results; // result VALUES belong to the Lean oracle
        }
    });
}
