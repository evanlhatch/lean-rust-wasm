/-
# SchemaLang.Scheduling — time and scheduling as stream operations (W8.5)

The runbook order: rates ("every N ticks"), delays (dbsp `delay` IS
"visible next tick"), deadlines — "modeled on streams from day one".
The canon row (Part 3, W8.5): "a schedule / rate / deadline = stream
operations (sampling, delay, comparison) — NEVER a separate time
system". This module is exactly that row: the operators over
`Dbsp.Stream α = Nat → α`, nothing else.

Implementer choices (the order deferred these; the CONSERVATIVE option
taken each time, recorded per the work-order contract):

- **NO new `Ty` constructor.** A timestamp/duration is a plain `.u64`
  (or `.i64`) scalar in the existing closed universe — the canon row
  forbids a time system in `Ty`, and a ctor would reopen every emitter
  for zero expressiveness. The boundary universe stays CLOSED (W8.1's
  exhaustion pattern untouched; wasm-backend match sites unchanged —
  verified by build).
- **NO wall clock, NO effect.** Time is an INPUT: a tick index (canon
  Part 2, row `tick` — "tick = Mealy machine"; a scheduled machine's
  clock is an input stream of tick counts, not a clock read). The
  vision's scope lock — effects cross one way as command VALUES (W8.6,
  not built) — is untouched: nothing here executes, everything is a
  pure stream function.
- **Rate is a structure with `0 < period` in the type** — a zero-period
  rate is unrepresentable (the `KeyTy` wrong-shape discipline), so the
  firing predicate `due` never divides by zero.
- **Deadlines are tick comparisons over a stream** (`missed`), per the
  canon row's "comparison". No deadline STRATEGY (retry/cancel) is
  built — no consumer exists; this module grows with the first one.

Substrate: `Dbsp.Stream` (the `Nat → α` stream, W4.2 made it
`InfiniteRun`) and `Dbsp.delay` (the unit delay — `delayBy 1 0` is
provably that operator, `delayBy_eq_delay`).
-/

module

public import Dbsp.Stream
public import Dbsp.Operators

@[expose] public section

namespace SchemaLang.Scheduling

/-! ## Time as input -/

/-- A tick index — the model of time. Time is an INPUT (the vision's
    sandbox has no wall clock): every schedule below is a pure function
    of tick indices and streams. -/
abbrev Tick := Nat

/-- THE canonical time input: the identity stream of tick indices. A
    scheduled machine reads this (or a refinement of it) each tick —
    the Mealy-machine tick row (canon Part 2): the clock is an input
    stream, never an effect. -/
def ticks : Dbsp.Stream Tick := fun t => t

theorem ticks_id (t : Tick) : ticks t = t := rfl

/-! ## Rates ("every N ticks") -/

/-- A rate: "every N ticks". The period is NONZERO by construction
    (`hpos` carried in the type — a zero-period rate, and hence a
    division by zero inside `due`, is unrepresentable). -/
structure Rate where
  /-- Fire every `period` ticks (must be positive). -/
  period : Nat
  /-- The positivity witness. -/
  hpos : 0 < period

/-- The firing predicate: tick `t` is DUE iff the period divides it.
    Tick 0 fires (the schedule is live from the origin). -/
def Rate.due (r : Rate) (t : Tick) : Prop := t % r.period = 0

/-- Boolean image of `due` (the executable gate — `due` is the
    proposition, `due?` its decide form). -/
def Rate.due? (r : Rate) (t : Tick) : Bool := t % r.period == 0

/-- The proposition and its Boolean gate AGREE (the `due?` routing is
    faithful — callers may branch on either). -/
theorem Rate.due?_iff (r : Rate) (t : Tick) : r.due t ↔ r.due? t = true := by
  simp [Rate.due, Rate.due?]

/-- Tick 0 is always due (the origin fires). -/
theorem Rate.due_zero (r : Rate) : r.due 0 := Nat.zero_mod _

/-- Periodicity: a due tick's period-shifted successor is due, and
    conversely (the rate's whole behavior is its residues — one period
    of the pattern determines the stream). -/
theorem Rate.due_periodic (r : Rate) (t : Tick) :
    r.due (t + r.period) ↔ r.due t := by
  show (t + r.period) % r.period = 0 ↔ t % r.period = 0
  rw [Nat.add_mod_right]

/-- Every multiple of the period fires. -/
theorem Rate.due_mul (r : Rate) (k : Tick) : r.due (k * r.period) :=
  Nat.mul_mod_left k r.period

/-- The NEGATIVE: a tick inside the first period (past the origin) is
    not due — the rate is not the always-fire rate. -/
theorem Rate.due?_false_of_lt (r : Rate) (t : Tick)
    (ht : 0 < t) (hlt : t < r.period) : r.due? t = false := by
  rw [Rate.due?, Nat.mod_eq_of_lt hlt]
  cases h : (t == 0) with
  | false => rfl
  | true => exact absurd (eq_of_beq h) (Nat.ne_of_gt ht)

/-- The SAMPLING operator (the canon row's "sampling"): at a due tick
    the schedule emits the stream's current value; between firings it
    HOLDS the carried value `d` (a constant between firings — the
    sample-and-hold discipline). -/
def Rate.sample (r : Rate) (d : α) (s : Dbsp.Stream α) : Dbsp.Stream α :=
  fun t => if r.due? t then s t else d

/-- At a due tick, the sampled stream IS the source stream. -/
theorem Rate.sample_due (r : Rate) (d : α) (s : Dbsp.Stream α) (t : Tick)
    (h : r.due? t = true) : r.sample d s t = s t := by
  simp [Rate.sample, h]

/-- Between firings, the sampled stream HOLDS `d`. -/
theorem Rate.sample_hold (r : Rate) (d : α) (s : Dbsp.Stream α) (t : Tick)
    (h : r.due? t = false) : r.sample d s t = d := by
  simp [Rate.sample, h]

/-! ## Delays ("visible next tick") -/

/-- A k-tick delay with a pre-history default: the stream's value at
    tick `t` is what the source produced `k` ticks earlier; before tick
    `k`, the default `d`. `delayBy 1 d s` IS "visible next tick" — and
    `delayBy_eq_delay` shows the `d = 0` unit case IS dbsp's `delay`. -/
def delayBy (k : Tick) (d : α) (s : Dbsp.Stream α) : Dbsp.Stream α :=
  fun t => if _ : k ≤ t then s (t - k) else d

/-- A zero delay is the identity (the stream is visible immediately). -/
theorem delayBy_zero (d : α) (s : Dbsp.Stream α) : delayBy 0 d s = s := by
  funext t; simp [delayBy, Nat.sub_zero]

/-- The delayed stream at the origin shows ONLY the default — nothing
    has "happened" yet (the negative: a delay is not the identity). -/
theorem delayBy_one_zero (d : α) (s : Dbsp.Stream α) :
    delayBy 1 d s 0 = d := rfl

/-- THE LAW the runbook names: a one-tick delay IS "visible next
    tick" — the value produced at `t` is observed at `t + 1`. -/
theorem delayBy_one_succ (d : α) (s : Dbsp.Stream α) (t : Tick) :
    delayBy 1 d s (t + 1) = s t := by
  simp [delayBy]

/-- Delays compose by ADDITION of their horizons: delaying `k + m` is
    delaying `m` then `k` (the delay algebra — a pipeline of delays is
    one delay, no scheduling semantics hides in the composition).
    Stated over `Nat` (`Tick` is an abbrev — the arithmetic must sit at
    `Nat` for `omega`; the abbrev defeats its atom collection). -/
theorem delayBy_add (k m : Nat) (d : α) (s : Dbsp.Stream α) :
    delayBy (k + m) d s = delayBy k d (delayBy m d s) := by
  funext t
  show (if k + m ≤ t then s (t - (k + m)) else d)
     = (if k ≤ t then (if m ≤ t - k then s (t - k - m) else d) else d)
  by_cases hkm : k + m ≤ t
  · rw [if_pos hkm, if_pos (by omega : k ≤ t),
      if_pos (by omega : m ≤ t - k)]
    congr 1
    omega
  · by_cases hk : k ≤ t
    · rw [if_neg hkm, if_pos hk, if_neg (by omega : ¬ (m ≤ t - k))]
    · rw [if_neg hkm, if_neg hk]

/-- The dbsp tie: the unit delay with `0` pre-history IS
    `Dbsp.delay` (the Operators port's `z⁻¹` — no second delay
    operator exists in the tree). -/
theorem delayBy_eq_delay [Zero α] (s : Dbsp.Stream α) :
    delayBy 1 0 s = Dbsp.delay s := by
  funext t
  cases t with
  | zero => rfl
  | succ n => exact delayBy_one_succ 0 s n

/-! ## Deadlines (the comparison) -/

/-- The MISSED predicate (the canon row's "comparison"): at tick `t`,
    the deadline `d` is missed iff `t` is at-or-past `d` AND the done
    stream still reports not-done there. `done` is a stream of claims
    (an INPUT — the task's own progress report), never a clock. -/
def missed (d : Tick) (done : Dbsp.Stream Bool) (t : Tick) : Bool :=
  d ≤ t && !done t

/-- A done task never misses (the deadline's sufficiency direction). -/
theorem missed_false_of_done (d : Tick) (done : Dbsp.Stream Bool) (t : Tick)
    (h : done t = true) : missed d done t = false := by
  simp [missed, h]

/-- Before the deadline, nothing is missed — however far behind. -/
theorem missed_false_of_lt (d : Tick) (done : Dbsp.Stream Bool) (t : Tick)
    (h : t < d) : missed d done t = false := by
  simp [missed, Nat.not_le.mpr h]

/-- AT the deadline, an unfinished task is missed (the deadline bites —
    the negative to `missed_false_of_lt`). -/
theorem missed_at (d : Tick) (done : Dbsp.Stream Bool)
    (h : done d = false) : missed d done d = true := by
  simp [missed, h]

/-- PAST the deadline with the task still unfinished: missed (the
    predicate's completeness direction). -/
theorem missed_true_of_overdue (d : Tick) (done : Dbsp.Stream Bool) (t : Tick)
    (h : d < t) (hd : done t = false) : missed d done t = true := by
  simp [missed, hd, Nat.le_of_lt h]

end SchemaLang.Scheduling

end -- @[expose] public section
