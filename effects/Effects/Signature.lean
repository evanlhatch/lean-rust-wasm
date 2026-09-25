/-
# Effects.Signature — the algebraic presentations: signature + laws + interpreters

The effects discipline's completion (the reviews' §11, the algebraic
presentations): a library defines a SIGNATURE plus LAWS, then the
application chooses INTERPRETERS — the same application runs under the
pure reference interpreter, the cost-graded one, the fault-injection
one. The important part is the LAWFUL interpretation, not the runtime
implementation. Close each application's signature; keep the library's
ecosystem open.

What lands here, honest-minimal:

- **The signature as DATA** (`Signature`): the operation set (the
  key-value / journal / clock-flavored operations the doctrine names —
  get/put/append/now over an abstract carrier state, with the journal
  and clock accessors as fields) + each operation's TYPE (the handler
  shape) + the LAWS as FIELDS — an unlawful signature doesn't
  construct (the rung-3 shape; the tooth is EffectsTests' sabotaged
  `get_put`). The laws: reads see pending writes (`get_put`); writes
  never touch the journal (`put_journal`); the journal records
  (`append_mem`); the clock never rewinds (`now_mono`) and the reading
  never outruns the clock (`now_read_le`).
- **The interpreter lifts** (`Interpreter`): an interpreter is a
  lawful `Signature` instance over ITS carrier — the lift's law fields
  CITE the source signature's fields (the lawful interpretation: the
  lift constructs only because the source is lawful). Three:
  `Interpreter.cost` (the cost-graded reading riding `Cost`'s model —
  the cost annotation threaded through the carrier, composed through
  `Cost.natCost`), `Interpreter.fault` (the failure-injection SEED:
  law-invisible faults only — ghost journal entries and a doubled
  clock tick, both COUNTED in the carrier; the laws pin the journal's
  RECORDING and the clock's DIRECTION, never its step, so a lawful
  injector is exactly the faults the laws are blind to — the D7 story
  again), and the pure reference (`pureSig`) as the base reading.
- **The program + the interpretation discipline**: the SHALLOW
  embedding, judged honestly — a program is a function parameterized
  by the handlers (`Program`); no free monad (the term universe would
  buy the generic per-program lift through `Kit.Expr.preserves`; the
  shallow discipline pays per-program instead, and says so). The
  worked programs (`kvProgram`, `logProgram`) run UNCHANGED under the
  pure and the cost-graded readings; the agreement is the run-level
  relation (`runRel`, a `Kit.Rel`) packaged as a `Kit.Interpretation`
  bundle, proved for the worked program by the lifts' definitional
  value-channel identity; the api-observer face (`Kit.apiObs`) sees
  the SAME result under both readings while `Kit.perfObs` sees the
  cost (the observer hierarchy's instrument-hiding row, 04 §4).

Named exclusions (each lands with its first consumer + its named law):
the free-monad term universe (the generic per-program agreement lift —
lands when programs become DATA), effect-row ENFORCEMENT at the
interpreter level (the rows stay `Effects.Basic`'s upper bounds; the
interpreters here are lawful by construction, not row-checked), row
polymorphism, the registry-derived signatures (08 §8's named
follow-up).

Doctrine slots (notes/v3/01-core.md, the five questions):
- **Root**: Universe (finite data: the op shapes + the law fields over
  the closed fragment) — the signature is annotation data over the
  carrier, NOT a new root; the cost annotation is the writer shape
  (`Cost.Basic`'s, cited); the journal/clock are the minimal
  execution's face (`Kit.Observer.Execution`'s trace/result/cost).
- **Carrier grade**: the interpretation pair (01 §6) — pure ↔
  cost-graded, the agreement stated in a `Kit.Rel` and packaged as a
  `Kit.Interpretation`; the observer nuance rides `Kit.Observer`
  (cited, not rebuilt).
- **Spine reading**: none — the consumers are the applications'
  signatures (the ecosystem stays open); nothing is emitted.
- **Ladder rung**: rung 3 (the laws as the signature's TYPE fields —
  an unlawful signature doesn't construct) + rung 6 (the lifts'
  law-transfer theorems, small hand theorems citing the source's
  fields — never re-proved).
- **Gate rows**: EffectsTests' axiom self-check + the unlawful-
  signature teeth + the worked-example agreement pins.

Core-only: no mathlib, no Batteries (the cone rule). Imports
Effects.Footprint (Key + State — ONE state model, no parallel table),
Cost.Basic (the cost model — the second reading rides it),
Kit.Relation + Kit.Observer (the agreement's faces).
-/

import Effects.Footprint
import Cost.Basic
import Kit.Observer
import Kit.Relation
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Effects.Signature

/-! ## The signature: the operations + the laws, as data -/

/-- A journal entry (finite — the ids name the app's journal). -/
abbrev Entry := Nat

/-- A read value. -/
abbrev Val := Nat

/-- THE SIGNATURE: the operation set + each operation's type (the
    handler shape over an abstract carrier state `S`) + the LAWS as
    FIELDS — an unlawful signature doesn't construct (rung 3). The
    key-value / journal / clock-flavored fragment the doctrine names;
    CLOSED like the atoms (a new operation is a doctrine act, pattern
    #15). -/
structure Signature (S : Type) where
  /-- Read the value at a key. -/
  get : Key → S → Val × S
  /-- Write a value at a key. -/
  put : Key → Val → S → S
  /-- Append an entry to the journal. -/
  append : Entry → S → S
  /-- Read the clock (one tick). -/
  now : S → Nat × S
  /-- The journal accessor (the laws read it). -/
  journalOf : S → List Entry
  /-- The clock accessor (the laws read it). -/
  clockOf : S → Nat
  /-- THE reads' law: a read after its write sees the write. -/
  get_put : ∀ (k : Key) (v : Val) (s : S), (get k (put k v s)).1 = v
  /-- THE writes' reach: a write never touches the journal. -/
  put_journal : ∀ (k : Key) (v : Val) (s : S), journalOf (put k v s) = journalOf s
  /-- THE journal's law: the journal records what is appended. -/
  append_mem : ∀ (e : Entry) (s : S), e ∈ journalOf (append e s)
  /-- THE clock's law: a tick never rewinds the clock. -/
  now_mono : ∀ (s : S), clockOf s ≤ clockOf (now s).2
  /-- THE reading's law: the reading never outruns the clock. -/
  now_read_le : ∀ (s : S), (now s).1 ≤ clockOf (now s).2

-- The laws' Prop-face projections — the rung-3 laws carried at
-- construction (an unlawful signature is unconstructible: the
-- interpreter lifts discharge them BY CITING the source's fields, and
-- EffectsTests' teeth show the refusal).
attribute [nolint linter.guestlang.zeroCitation "public API: the signature's law, carried at construction (rung 3 — an unlawful signature doesn't construct); discharged by the interpreter lifts in this module + the tests' fixtures and teeth"]
  Signature.get_put Signature.put_journal Signature.append_mem
  Signature.now_mono Signature.now_read_le

/-! ## The program: the shallow embedding -/

/-- A program over a signature: a function parameterized by the
    handlers — the SHALLOW embedding, judged honestly (see the
    header). The same program term runs under every interpreter. -/
def Program (S : Type) (α : Type) : Type := Signature S → S → α × S

/-- The worked KV program: write 42 at key 1, read it back. Reads see
    the pending write — by `get_put`, under EVERY interpreter. -/
def kvProgram {S : Type} : Program S Val :=
  fun sig s => sig.get 1 (sig.put 1 42 s)

/-- The worked journal+clock program: write, read back, journal the
    read value, read the clock. The lane's worked example. -/
def logProgram {S : Type} : Program S Nat :=
  fun sig s =>
    let w := sig.put 1 42 s
    let kv := sig.get 1 w
    let j := sig.append kv.1 kv.2
    sig.now j

/-! ## The pure reference interpreter -/

/-- The reference carrier: cells (THE state model, `Effects.State` —
    one state model, no parallel table), the journal, the clock. -/
structure RefState where
  /-- The key-value cells. -/
  cells : State
  /-- The journal. -/
  journal : List Entry
  /-- The clock. -/
  clock : Nat

/-- The reference read: the cell's value, state unchanged. -/
def pureGet (k : Key) (s : RefState) : Val × RefState := (s.cells k, s)

/-- The reference write: the cell updated, everything else preserved. -/
def purePut (k : Key) (v : Val) (s : RefState) : RefState :=
  { s with cells := fun j => if j = k then v else s.cells j }

/-- The reference append: the entry recorded at the journal's end. -/
def pureAppend (e : Entry) (s : RefState) : RefState :=
  { s with journal := s.journal ++ [e] }

/-- The reference tick: the reading IS the clock; the clock advances. -/
def pureNow (s : RefState) : Nat × RefState := (s.clock, { s with clock := s.clock + 1 })

/-- The reference journal accessor. -/
def refJournal (s : RefState) : List Entry := s.journal

/-- The reference clock accessor. -/
def refClock (s : RefState) : Nat := s.clock

/-- THE reads' law, for the reference (cited by `pureSig`). -/
theorem pure_get_put (k : Key) (v : Val) (s : RefState) :
    (pureGet k (purePut k v s)).1 = v := by
  simp [pureGet, purePut]

/-- THE writes' reach, for the reference (cited by `pureSig`). -/
theorem pure_put_journal (k : Key) (v : Val) (s : RefState) :
    refJournal (purePut k v s) = refJournal s := by
  simp [purePut, refJournal]

/-- THE journal's law, for the reference (cited by `pureSig`). -/
theorem pure_append_mem (e : Entry) (s : RefState) :
    e ∈ refJournal (pureAppend e s) := by
  simp [pureAppend, refJournal]

/-- THE clock's law, for the reference (cited by `pureSig`). -/
theorem pure_now_mono (s : RefState) :
    refClock s ≤ refClock (pureNow s).2 := by
  simp [pureNow, refClock]

/-- THE reading's law, for the reference (cited by `pureSig`). -/
theorem pure_now_read_le (s : RefState) :
    (pureNow s).1 ≤ refClock (pureNow s).2 := by
  simp [pureNow, refClock]

/-- THE PURE REFERENCE INTERPRETER: the base reading. -/
def pureSig : Signature RefState where
  get := pureGet
  put := purePut
  append := pureAppend
  now := pureNow
  journalOf := refJournal
  clockOf := refClock
  get_put := pure_get_put
  put_journal := pure_put_journal
  append_mem := pure_append_mem
  now_mono := pure_now_mono
  now_read_le := pure_now_read_le

/-! ## The interpreter lifts (the ecosystem stays open) -/

/-- The per-operation cost table (the application's cost schedule —
    the data the cost reading threads). -/
structure OpCost where
  /-- The read's cost. -/
  getCost : Nat
  /-- The write's cost. -/
  putCost : Nat
  /-- The append's cost. -/
  appendCost : Nat
  /-- The tick's cost. -/
  nowCost : Nat

/-- The fault-injection carrier: the source state + the injection
    count (the fault log's count — the seed's observability). -/
structure FaultCar (S : Type) where
  /-- The source state. -/
  base : S
  /-- The injections so far. -/
  injected : Nat

namespace Interpreter

/-- THE COST-GRADED INTERPRETER (the second reading): the same
    handlers over the cost-annotated carrier `S × Nat` — the value
    channel is the SOURCE's (definitional), the cost composes through
    `Cost.natCost` (the landed cost lane's model, cited — the writer
    shape's shadow threaded through the carrier). The laws' evidence
    CITES the source signature's fields: the cost reading constructs
    only because the source is lawful. -/
def cost {S : Type} (sig : Signature S) (c : OpCost) : Signature (S × Nat) where
  get k sc :=
    let p := sig.get k sc.1
    (p.1, (p.2, Cost.natCost.compose sc.2 c.getCost))
  put k v sc :=
    let p := sig.put k v sc.1
    (p, Cost.natCost.compose sc.2 c.putCost)
  append e sc :=
    let p := sig.append e sc.1
    (p, Cost.natCost.compose sc.2 c.appendCost)
  now sc :=
    let p := sig.now sc.1
    (p.1, (p.2, Cost.natCost.compose sc.2 c.nowCost))
  journalOf sc := sig.journalOf sc.1
  clockOf sc := sig.clockOf sc.1
  get_put := fun k v sc => sig.get_put k v sc.1
  put_journal := fun k v sc => sig.put_journal k v sc.1
  append_mem := fun e sc => sig.append_mem e sc.1
  now_mono := fun sc => sig.now_mono sc.1
  now_read_le := fun sc => sig.now_read_le sc.1

/-- THE FAULT-INJECTION INTERPRETER (the seed): the source's handlers
    plus the LAW-INVISIBLE injections — a ghost journal entry beside
    every append, a doubled clock tick at every `now` — each counted
    in the carrier. The laws pin the journal's RECORDING
    (`append_mem`) and the clock's DIRECTION (`now_mono`), never the
    journal's exact shape or the clock's step: a lawful injector is
    exactly the faults the laws are blind to (the D7 story's
    interpreter face). A law-VISIBLE injection (dropping the entry,
    rewinding the clock, a stale read) fails to construct — the teeth
    in EffectsTests. -/
def fault {S : Type} (sig : Signature S) (ghost : Entry) :
    Signature (FaultCar S) where
  get k fc :=
    let p := sig.get k fc.base
    (p.1, ⟨p.2, fc.injected⟩)
  put k v fc :=
    let p := sig.put k v fc.base
    ⟨p, fc.injected⟩
  append e fc :=
    let p := sig.append e (sig.append ghost fc.base)
    ⟨p, fc.injected + 1⟩
  now fc :=
    let p := sig.now (sig.now fc.base).2
    (p.1, ⟨p.2, fc.injected + 1⟩)
  journalOf fc := sig.journalOf fc.base
  clockOf fc := sig.clockOf fc.base
  get_put := fun k v fc => sig.get_put k v fc.base
  put_journal := fun k v fc => sig.put_journal k v fc.base
  append_mem := fun e fc => sig.append_mem e (sig.append ghost fc.base)
  now_mono := fun fc =>
    Nat.le_trans (sig.now_mono fc.base) (sig.now_mono (sig.now fc.base).2)
  now_read_le := fun fc => sig.now_read_le (sig.now fc.base).2

end Interpreter

/-! ## The agreement discipline (the interpretation pair) -/

/-- The runs' agreement relation (a `Kit.Rel`, 01 §6): the api result,
    the journal, and the clock agree — the cost annotation is the only
    difference, riding in the carrier's second component. -/
def runRel {S : Type} (α : Type) : Kit.Rel (α × S) (α × (S × Nat)) :=
  fun r₁ r₂ => r₁.1 = r₂.1 ∧ r₁.2 = r₂.2.1

/-- THE interpretation bundle for the worked program: the pure reading
    paired with the cost-graded reading, related by `runRel` (01 §6's
    bundle shape; the shallow discipline's agreement is per-program —
    the term universe is the named exclusion, see the header). -/
def logPair {S : Type} (sig : Signature S) (c : OpCost) :
    Kit.Interpretation (S) (Nat × S) (Nat × (S × Nat)) where
  eval₁ s := logProgram sig s
  eval₂ s := logProgram (Interpreter.cost sig c) (s, 0)
  R := runRel Nat

/-- THE WORKED AGREEMENT: the worked program's pure and cost-graded
    runs agree on the value channel AND the final state — the cost
    annotation is the only difference. The lifts' handlers are the
    source's on the value channel (definitional), so the shallow
    program's two runs are the same term modulo the annotation. -/
theorem logProgram_agrees {S : Type} (sig : Signature S) (c : OpCost) (s : S) :
    (logPair sig c).R ((logPair sig c).eval₁ s) ((logPair sig c).eval₂ s) := by
  simp [logPair, logProgram, Interpreter.cost, runRel]

/-- THE COST HONESTY (no silent undercount): the worked program's
    cost-graded run ends at the model-composition of the four
    operations' costs — every operation's cost appears, exactly once,
    in the model's composition (`Cost.natCost`, cited). -/
theorem logProgram_cost_honest {S : Type} (sig : Signature S) (c : OpCost) (s : S) :
    (logProgram (Interpreter.cost sig c) (s, 0)).2.2
      = c.putCost + c.getCost + c.appendCost + c.nowCost := by
  simp [logProgram, Interpreter.cost, Cost.natCost, Cost.NatCost.compose]

/-! ## The observer face (Kit.Observer, cited) -/

/-- The pure run's execution view: the journal is the trace, the api
    result is the terminal result, the cost channel reads ZERO (the
    pure reference has no cost — the empty annotation). -/
def pureExec {S : Type} (r : Nat × S) (journalOf : S → List Entry) :
    Kit.Execution Nat :=
  { trace := journalOf r.2, result := some r.1, cost := 0 }

/-- The cost run's execution view: same trace/result discipline, the
    cost channel reads the composed annotation. -/
def costExec {S : Type} (r : Nat × (S × Nat)) (journalOf : S → List Entry) :
    Kit.Execution Nat :=
  { trace := journalOf r.2.1, result := some r.1, cost := r.2.2 }

/-- THE API-OBSERVER AGREEMENT: under `Kit.apiObs` the pure and the
    cost-graded runs of the worked program are the SAME execution —
    the api observer sees the terminal result only, and the results
    agree (`logProgram_agrees`, cited). The cost is visible ONLY to
    `Kit.perfObs` — the observer hierarchy's instrument-hiding row
    (04 §4: same result after hiding instrumentation). -/
theorem api_agrees {S : Type} (sig : Signature S) (c : OpCost) (s : S) :
    (Kit.apiObs Nat).see (pureExec (logProgram sig s) sig.journalOf)
      = (Kit.apiObs Nat).see
          (costExec (logProgram (Interpreter.cost sig c) (s, 0)) sig.journalOf) := by
  have h := logProgram_agrees sig c s
  exact congrArg some h.1

/-- THE PERF-OBSERVER VISIBILITY: the cost is NOT hidden from
    `Kit.perfObs` — whenever the schedule is nonzero, the two runs'
    executions differ exactly in the cost channel (the annotation's
    reason to exist; the api face above is the hiding row's other
    half). -/
theorem perf_sees_cost {S : Type} (sig : Signature S) (c : OpCost) (s : S)
    (hpos : c.putCost + c.getCost + c.appendCost + c.nowCost > 0) :
    (Kit.perfObs Nat).see (pureExec (logProgram sig s) sig.journalOf)
      ≠ (Kit.perfObs Nat).see
          (costExec (logProgram (Interpreter.cost sig c) (s, 0)) sig.journalOf) := by
  intro heq
  have h := logProgram_cost_honest sig c s
  simp [pureExec, costExec, Kit.perfObs] at heq
  omega

end Effects.Signature
