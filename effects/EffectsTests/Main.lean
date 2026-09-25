/-
# EffectsTests — the lattice pins, the elaboration teeth, the double-spend pin, the footprint exercise

Positive pins + the MANDATORY negative controls (15-patterns #5). Two
kinds of teeth, both load-bearing:

- **BUILD-TIME teeth** (`#guard_msgs`): the over-permissive composition
  and the double-spend handle FAIL TO ELABORATE — the pins compile the
  refusals into the build itself;
- **RUNTIME controls** (the TestingKit sweep): the sabotaged siblings
  the sweep MUST catch.

Suites:

1. `lattice` — the laws pinned as data: the join's membership, the
   order's decided facts (comm at the data level), the D7 pin (two
   consumes joined check against a one-consume allowance — the row
   CANNOT see the double-spend).
2. `effects-comp` — the composition's join computed at the type level;
   the check boundary elapses on the honest allowance and REFUSES the
   over-permissive one (build-time tooth).
3. `resources` — the split: the kept law + the spent fact at data
   level; the double-spend handle's elaboration refusal (build-time
   tooth); the counted monus tie + its honest ceiling (the count
   truncates, never refuses).
4. `footprint` — the frame rule + the composition exercised: reads
   depend only on the footprint, writes preserve outside it, the seq
   composite is lawful; the clobbering-write sabotage caught.
5. `sweep` — the LCG-seeded property sweep with the mandatory negative
   controls: the join-as-intersection sabotage, the footprint-leak
   sabotage, the monus-refusal sabotage.
6. `signature` — the algebraic presentations (Effects.Signature): the
   pure reference interpreter's laws pinned at data level, the worked
   programs under the pure + cost-graded readings, the agreement pins
   (Kit.Rel + Kit.Interpretation + the api/perf observer faces), the
   cost-honesty pin, and the UNLAWFUL-SIGNATURE teeth (a stale read, a
   clock rewind, a dropped journal entry — each fails to construct).
7. `fault` — the fault-injection seed: lawful (constructs), the
   injections counted, the ghost entry visible, the KV channel
   untouched.

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the laws — NO axioms at all, or the build fails.
-/

import Effects
import LintKit  -- the @[nolint ... "reason"] syntax for the teeth decls
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import EffectsTests.Axioms

open Effects Effects.Resource Effects.Signature TestingKit

namespace EffectsTests

/-! ## The fixture helpers -/

/-- The effect enum from an index (the sweep's draw). -/
def effOf : Nat → Effect
  | 0 => .read | 1 => .write | 2 => .guestCap | 3 => .fail
  | 4 => .consume | 5 => .clock | 6 => .hostIO | _ => .observe

/-! ## Suite 1: the lattice laws, pinned as data -/

-- membership through the join: both sides' members are in
theorem mem_join_both :
    (Effect.read ∈ Row.join [Effect.read, Effect.write] [Effect.observe])
      ∧ (Effect.observe ∈ Row.join [Effect.read, Effect.write] [Effect.observe]) := by
  constructor
  · exact (Row.mem_join _ _ _).mpr (Or.inl (by simp))
  · exact (Row.mem_join _ _ _).mpr (Or.inr (by simp))

-- a NON-member stays out (the union adds, never invents)
theorem mem_join_absent :
    ¬ (Effect.fail ∈ Row.join [Effect.read] [Effect.write]) := by
  intro hx
  rcases (Row.mem_join _ _ _).mp hx with hx | hx
  · exact absurd hx (by simp)
  · exact absurd hx (by simp)

-- the order decides: comm at the data level (both directions)
theorem comm_pin :
    (Row.le [Effect.read, Effect.write] [Effect.write, Effect.read])
      ∧ (Row.le [Effect.write, Effect.read] [Effect.read, Effect.write]) := by
  decide

-- THE D7 data pin: TWO consume computations joined check against a
-- ONE-consume allowance — the row cannot see the double-spend
theorem d7_data_pin :
    Row.le (Row.join [Effect.consume] [Effect.consume]) [Effect.consume] := by
  decide

-- ... and the lattice theorem is the same fact, cited
theorem d7_theorem_pin :
    Row.sameMembers
      (Row.join [Effect.consume] [Effect.consume]) [Effect.consume] :=
  row_blind_to_double_spend

/-! ## Suite 2: the effect-annotated computations -/

def readCell : Comp [Effect.read] Nat := ⟨42⟩
def writeCell : Comp [Effect.write] Unit := ⟨()⟩
def logIt : Comp [Effect.observe] Unit := ⟨()⟩

/-- The composition's join, COMPUTED AT THE TYPE LEVEL: read + write +
    observe — checked against the full allowance (elaborates). -/
def checkedFull : Comp [Effect.read, Effect.write, Effect.observe] Unit :=
  Comp.check ((readCell.bind (fun _ => writeCell)).bind (fun _ => logIt))
    (by decide)

/-- ... and the same composition checked against a redundant but
    SUFFICIENT allowance (the sub-effect discipline: any superset
    admits). -/
def checkedSuper : Comp [Effect.read, Effect.write, Effect.observe, Effect.clock] Unit :=
  Comp.check ((readCell.bind (fun _ => writeCell)).bind (fun _ => logIt))
    (by decide)

/- THE over-permissive tooth: the same composition against an
   allowance MISSING `observe` — no proof exists, the declaration
   fails to elaborate. -/
/-- error: Tactic `decide` proved that the proposition
  ((Row.join [Effect.read] [Effect.write]).join [Effect.observe]).le [Effect.read, Effect.write]
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def overPermissive : Comp [Effect.read, Effect.write] Unit :=
  Comp.check ((readCell.bind (fun _ => writeCell)).bind (fun _ => logIt))
    (by decide)

/-! ## Suite 3: the resources split -/

/-- The fixture context: resources 7 and 3, unspent. -/
def ctx0 : Ctx :=
  ⟨[7, 3], noDup'_cons (by simp) (noDup'_cons (by simp) noDup'_nil)⟩

theorem hd7 : Handle ctx0 7 := ⟨by decide⟩

/-- The split: consuming 7 ONCE — the spent fact rides the type. -/
def split7 : { rest : Ctx // 7 ∉ rest.elems } := hd7.consume

-- the kept law at data level: 3 survives
theorem split_kept : 3 ∈ split7.1.elems :=
  (Ctx.kept_survive ctx0 7 3 (by decide)).mpr (by decide)

-- the spent fact at data level
theorem split_spent : 7 ∉ split7.1.elems := split7.2

/- THE double-spend tooth: a live handle for 7 in the SPLIT context —
   the proof is false, no handle constructs, the declaration fails to
   elaborate. -/
/-- error: Tactic `decide` proved that the proposition
  7 ∈ split7.val.elems
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def doubleSpend : Handle split7.1 7 := ⟨by decide⟩

-- the counted tie: monus spends
theorem count_pin : spendCount 10 3 = some 7 := by decide

-- ... and composes (the monus compose, cited)
theorem count_compose_pin :
    spendCount 10 7 = (spendCount 10 3).bind (fun r => spendCount r 4) :=
  spendCount_compose 10 3 4

-- THE counted discipline's honest ceiling: the count truncates, never
-- refuses — the double-spend is invisible at the value level (D7)
theorem count_blind_pin : spendCount 0 5 = some 0 := monus_cannot_refuse 5

/-! ## Suite 4: the footprint laws, exercised -/

/-- The raw increment-at-1 machinery (defined before the Cmd so the
    laws' proofs can unfold it — the structure instance cannot). -/
def incr1_run : State → Nat := fun s => s 1
def incr1_wr : State → State := fun s k => if k = 1 then s 1 + 1 else s k

theorem incr1_reads_depend (s s' : State) (h : ∀ k, k ∈ [1] → s k = s' k) :
    incr1_run s = incr1_run s' :=
  h 1 (by simp)

theorem incr1_writes_depend (s s' : State) (k : Key) (hk : k ∈ [1])
    (h : ∀ j, j ∈ [1] → s j = s' j) : incr1_wr s k = incr1_wr s' k := by
  cases List.mem_cons.mp hk with
  | inl he =>
    show (if k = 1 then s 1 + 1 else s k) = (if k = 1 then s' 1 + 1 else s' k)
    rw [he]
    simp [h 1 (by simp)]
  | inr hr => exact absurd hr (by simp)

theorem incr1_writes_preserve (s : State) (k : Key) (hk : k ∉ [1]) :
    incr1_wr s k = s k := by
  show (if k = 1 then s 1 + 1 else s k) = s k
  rw [if_neg (fun he => hk (by simp [he]))]

/-- The lawful command: increment the cell at key 1. -/
def cmdIncr1 : Cmd where
  fp := [1]
  run := incr1_run
  wr := incr1_wr
  reads_depend := incr1_reads_depend
  writes_depend := incr1_writes_depend
  writes_preserve := incr1_writes_preserve

/-- The raw increment-at-2 machinery. -/
def incr2_run : State → Nat := fun s => s 2
def incr2_wr : State → State := fun s k => if k = 2 then s 2 + 1 else s k

theorem incr2_reads_depend (s s' : State) (h : ∀ k, k ∈ [2] → s k = s' k) :
    incr2_run s = incr2_run s' :=
  h 2 (by simp)

theorem incr2_writes_depend (s s' : State) (k : Key) (hk : k ∈ [2])
    (h : ∀ j, j ∈ [2] → s j = s' j) : incr2_wr s k = incr2_wr s' k := by
  cases List.mem_cons.mp hk with
  | inl he =>
    show (if k = 2 then s 2 + 1 else s k) = (if k = 2 then s' 2 + 1 else s' k)
    rw [he]
    simp [h 2 (by simp)]
  | inr hr => exact absurd hr (by simp)

theorem incr2_writes_preserve (s : State) (k : Key) (hk : k ∉ [2]) :
    incr2_wr s k = s k := by
  show (if k = 2 then s 2 + 1 else s k) = s k
  rw [if_neg (fun he => hk (by simp [he]))]

def cmdIncr2 : Cmd where
  fp := [2]
  run := incr2_run
  wr := incr2_wr
  reads_depend := incr2_reads_depend
  writes_depend := incr2_writes_depend
  writes_preserve := incr2_writes_preserve

-- THE frame rule, exercised: states agreeing outside [1] still agree
-- outside it after the write
theorem frame_pin (s s' : State) (h : ∀ k, k ∉ [1] → s k = s' k) :
    ∀ k, k ∉ [1] → cmdIncr1.wr s k = cmdIncr1.wr s' k :=
  cmdIncr1.frame s s' h

-- concrete: the write at key 9 is the identity (preserve at data)
def s1 : State := fun _ => 5

theorem concrete_preserve : cmdIncr1.wr s1 9 = 5 := by
  show (if 9 = 1 then s1 1 + 1 else s1 9) = 5
  rw [if_neg (by decide)]
  rfl

-- THE composition: the seq composite is lawful over the JOINED
-- footprint (the frame rule composes — the state-side twin of the
-- rows' join)
theorem seq_pin (s s' : State)
    (h : ∀ k, k ∈ Fp.join cmdIncr1.fp cmdIncr2.fp → s k = s' k) :
    (cmdIncr1.seq cmdIncr2).run s = (cmdIncr1.seq cmdIncr2).run s' :=
  Cmd.seq_reads cmdIncr1 cmdIncr2 s s' h

-- concrete: the composite's run reads key 2 — the key-1 increment is
-- invisible there (0), and the composite's WRITE carries it (1)
theorem concrete_seq_run : (cmdIncr1.seq cmdIncr2).run (fun _ => 0) = 0 := by
  decide

theorem concrete_seq_write :
    (cmdIncr1.seq cmdIncr2).wr (fun _ => 0) 1 = 1 := by
  decide

/- THE footprint-leak tooth: the sabotage claims the write CLOBBERS
   the outside-footprint cell 9 with 99 — caught (writes preserve
   everything outside the footprint). -/
/-- error: Tactic `decide` proved that the proposition
  cmdIncr1.wr (fun x => 5) 9 = 99
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
theorem footprintLeak : cmdIncr1.wr (fun _ => 5) 9 = 99 := by decide

/-! ## Suite 5: the universal join laws + the mandatory negative controls -/

/-- One drawn-instance check, kept as the universal law's body: the
    join's membership law (membership in the join IS membership in
either side), the upper-bound law, and the idempotence — at atoms i, j,
    k of the closed 8-atom lattice. -/
def joinInstanceOk (i j k : Nat) : Bool :=
  let a : Row := [effOf i]
  let b : Row := [effOf j]
  let e : Effect := effOf k
  ((decide (e ∈ Row.join a b)) == ((decide (e ∈ a)) || (decide (e ∈ b))))
    && (decide (Row.le a (Row.join a b))) && (decide (Row.le b (Row.join a b)))
    && (decide (Row.le (Row.join a a) a)) && (decide (Row.le a (Row.join a a)))

/-- THE UNIVERSAL JOIN LAWS (the inherited-correctness audit's F2): the
    old sweep drew 12 seeds from the SAME closed 8-atom world — every
    drawn instance was one of the 512 atom triples, each literally
    decided. The universal theorem decides all of them ONCE
    (decidableNow is the honest tier over a closed finite world; a
    sampled sweep of a decidable closed world understates what is
    known). -/
def joinLawsUniversal : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j =>
    (List.range 8).all fun k => joinInstanceOk i j k

theorem joinLawsUniversal_decided : joinLawsUniversal = true := by
  decide

/-- The split's discipline, swept: consume a drawn resource (≠ 3), the
    other survives, the spent one is gone. -/
def propSplit (t : Tape) : CheckResult := do
  let (r, _) := t.below 8
  if h : r = 3 then
    pure ()  -- the degenerate draw: the fixture needs r ≠ 3
  else
    let c : Ctx := ⟨[r, 3], noDup'_cons
      (fun hr => h (List.mem_cons.mp hr |>.elim id (fun hf => absurd hf (by simp))))
      (noDup'_cons (by simp) noDup'_nil)⟩
    let rest := (⟨by exact List.mem_cons_self ..⟩ : Handle c r).consume
    assert (rest.1.elems.contains 3) "the split lost an unspent resource"
    assert (!rest.1.elems.contains r) "the split did not spend the resource"

/-- The counted + footprint disciplines, swept. -/
def propCountFootprint (t : Tape) : CheckResult := do
  let (n, t₁) := t.below 20
  let (d, t₂) := t₁.below 5
  let (v, _) := t₂.below 100
  -- the monus accounting: a spend reads the truncated remainder
  assert (spendCount n d == some (n - d)) "the monus accounting broke"
  -- the reads' law at data: states agreeing on the footprint agree on
  -- the read, whatever they do outside
  let s : State := fun _ => v
  let s' : State := fun j => if j = 1 then v else v + 7
  assert (cmdIncr1.run s == cmdIncr1.run s')
    "the reads' law broke (a difference outside the footprint leaked in)"

/-- The JOIN-AS-INTERSECTION sabotage: claims the join's membership is
    the AND of the sides' — caught: `read` is in the join of `[read]`
    and `[write]` (one side suffices; the union is not the
    intersection). -/
def negJoinIntersection (_t : Tape) : CheckResult := do
  assert ((decide (Effect.read ∈ Row.join [Effect.read] [Effect.write])) == false)
    "the join-as-intersection sabotage was not caught"

/-- The FOOTPRINT-LEAK sabotage: claims the write clobbers the
    outside-footprint cell 9 — caught (writes preserve outside). -/
def negFootprintLeak (_t : Tape) : CheckResult := do
  assert (cmdIncr1.wr (fun _ => 5) 9 == 99)
    "the footprint-leak sabotage was not caught"

/-- The MONUS-REFUSAL sabotage: claims the count REFUSES an over-spend
    (none) — caught: the count truncates (some 0), never refuses — the
    refusal is the split's, type-level (D7). -/
def negMonusRefusal (_t : Tape) : CheckResult := do
  assert (spendCount 0 5 == none)
    "the monus-refusal sabotage was not caught"

def specLattice : Spec := Spec.ofList "effects-lattice"
  (fun _ => assert joinLawsUniversal
    "the universal join law broke (the 512-atom-triple decision)")
  [ ("join-as-intersection", negJoinIntersection),
    ("monus-refusal", negMonusRefusal) ]
  1 20250901

def specResources : Spec := Spec.ofList "effects-resources"
  (fun t => do
    let _ ← propSplit t
    let _ ← propCountFootprint t)
  [ ("footprint-leak", negFootprintLeak),
    ("join-as-intersection", negJoinIntersection) ]
  12 20250902

/-! ## Suite 6: the signature + the interpreters + the agreement -/

/-- The fixture state: cells read 7, an empty journal, clock 100. -/
def st0 : RefState := { cells := fun _ => 7, journal := [], clock := 100 }

-- the reads' law at data: a read after its write sees the write
theorem sig_get_put_pin : (pureGet 1 (purePut 1 42 st0)).1 = 42 := rfl

-- the writes' reach at data: the journal untouched
theorem sig_put_journal_pin : refJournal (purePut 1 42 st0) = [] := rfl

-- the journal's law at data: the entry is recorded
theorem sig_append_mem_pin : 42 ∈ refJournal (pureAppend 42 st0) := by
  simp [pureAppend, refJournal]

-- the clock's laws at data: the reading is the clock, one tick forward
theorem sig_now_pin :
    (pureNow st0).1 = 100 ∧ refClock (pureNow st0).2 = 101 := ⟨rfl, rfl⟩

-- THE WORKED KV PROGRAM under the pure reference: reads see the write
theorem kv_pure_pin : (kvProgram pureSig st0).1 = 42 := rfl

-- THE WORKED JOURNAL+CLOCK PROGRAM under the pure reference
theorem log_pure_pin :
    (logProgram pureSig st0).1 = 100
    ∧ (logProgram pureSig st0).2.journal = [42]
    ∧ (logProgram pureSig st0).2.clock = 101 := by
  simp [logProgram, pureSig, pureNow, pureAppend, pureGet, purePut, st0]

-- the cost schedule fixture: read 3, write 2, append 5, tick 7
def c1 : OpCost := ⟨3, 2, 5, 7⟩

-- THE SAME PROGRAM under the cost-graded reading: same value, same
-- journal, same clock; the cost is the composed schedule (17)
theorem log_cost_pin :
    (logProgram (Interpreter.cost pureSig c1) (st0, 0)).1 = 100
    ∧ (logProgram (Interpreter.cost pureSig c1) (st0, 0)).2.1.journal = [42]
    ∧ (logProgram (Interpreter.cost pureSig c1) (st0, 0)).2.1.clock = 101
    ∧ (logProgram (Interpreter.cost pureSig c1) (st0, 0)).2.2 = 17 := by
  simp [logProgram, pureSig, Interpreter.cost, Cost.natCost, Cost.NatCost.compose,
        pureNow, pureAppend, pureGet, purePut, st0, c1]

-- the agreement theorem, cited (Kit.Rel + Kit.Interpretation)
theorem agree_pin :
    (logPair pureSig c1).R ((logPair pureSig c1).eval₁ st0)
      ((logPair pureSig c1).eval₂ st0) :=
  logProgram_agrees pureSig c1 st0

-- the cost honesty, cited (no silent undercount)
theorem cost_honest_pin :
    (logProgram (Interpreter.cost pureSig c1) (st0, 0)).2.2
      = c1.putCost + c1.getCost + c1.appendCost + c1.nowCost :=
  logProgram_cost_honest pureSig c1 st0

-- THE API-OBSERVER AGREEMENT, cited: the same execution under Kit.apiObs
theorem api_pin :
    (Kit.apiObs Nat).see (pureExec (logProgram pureSig st0) refJournal)
      = (Kit.apiObs Nat).see
          (costExec (logProgram (Interpreter.cost pureSig c1) (st0, 0)) refJournal) :=
  api_agrees pureSig c1 st0

-- THE PERF-OBSERVER VISIBILITY, cited: the cost is NOT hidden from perf
theorem perf_pin :
    (Kit.perfObs Nat).see (pureExec (logProgram pureSig st0) refJournal)
      ≠ (Kit.perfObs Nat).see
          (costExec (logProgram (Interpreter.cost pureSig c1) (st0, 0)) refJournal) :=
  perf_sees_cost pureSig c1 st0 (by decide)

/- THE UNLAWFUL-SIGNATURE TEETH (the type-level refusals): a signature
   whose laws are unprovable doesn't construct. Three violations, one
   per law family: -/

/-- The stale read: `get` ignores the pending write — `get_put` has no
    proof, the signature fails to construct. -/
def staleGet (_k : Key) (s : RefState) : Val × RefState := (0, s)

/-- error: unsolved goals
k : Key
v : Val
s : RefState
⊢ 0 = v -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def staleSig : Signature RefState where
  get := staleGet
  put := purePut
  append := pureAppend
  now := pureNow
  journalOf := refJournal
  clockOf := refClock
  get_put := by intro k v s; simp [staleGet, purePut]
  put_journal := pure_put_journal
  append_mem := pure_append_mem
  now_mono := pure_now_mono
  now_read_le := pure_now_read_le

/-- The clock rewind: `now` moves the clock BACK — `now_mono` has no
    proof, the signature fails to construct. -/
def rewindNow (s : RefState) : Nat × RefState := (s.clock, { s with clock := s.clock - 1 })

/-- error: unsolved goals
s : RefState
⊢ s.clock ≤ s.clock - 1
---
error: unsolved goals
s : RefState
⊢ s.clock ≤ s.clock - 1 -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def rewSig : Signature RefState where
  get := pureGet
  put := purePut
  append := pureAppend
  now := rewindNow
  journalOf := refJournal
  clockOf := refClock
  get_put := pure_get_put
  put_journal := pure_put_journal
  append_mem := pure_append_mem
  now_mono := by intro s; simp [rewindNow, refClock]
  now_read_le := by intro s; simp [rewindNow, refClock]

/-- The dropped entry: `append` records a ghost INSTEAD of the entry —
    `append_mem` has no proof, the signature fails to construct. -/
def dropAppend (_e : Entry) (s : RefState) : RefState :=
  { s with journal := s.journal ++ [999] }

/-- error: unsolved goals
e : Entry
s : RefState
⊢ e ∈ s.journal ∨ e = 999 -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def dropSig : Signature RefState where
  get := pureGet
  put := purePut
  append := dropAppend
  now := pureNow
  journalOf := refJournal
  clockOf := refClock
  get_put := pure_get_put
  put_journal := pure_put_journal
  append_mem := by intro e s; simp [dropAppend, refJournal]
  now_mono := pure_now_mono
  now_read_le := pure_now_read_le

/-! ## Suite 7: the fault-injection seed -/

/-- The fault-injection interpreter over the pure reference: ghost
    entry 999, law-invisible, counted. -/
def faultI : Signature (FaultCar RefState) := Interpreter.fault pureSig 999

-- THE WORKED PROGRAM under the fault injector: lawful (it constructed),
-- the injections counted (one append + one now = 2), the ghost visible,
-- the clock double-ticked (the reading 101, not 100 — the api face DOES
-- see the fault: the laws pin the clock's DIRECTION, never its step)
theorem fault_pin :
    (logProgram faultI ⟨st0, 0⟩).1 = 101
    ∧ (logProgram faultI ⟨st0, 0⟩).2.base.journal = [999, 42]
    ∧ (logProgram faultI ⟨st0, 0⟩).2.injected = 2 := by
  simp [logProgram, faultI, pureSig, Interpreter.fault, pureNow, pureAppend,
        pureGet, purePut, st0]

-- the KV channel is UNTOUCHED by the seed's injections: the same
-- worked KV program agrees under the pure and the fault readings
theorem kv_fault_pin :
    (kvProgram pureSig st0).1 = (kvProgram faultI ⟨st0, 0⟩).1 := rfl

/-! ## Suite 8: the sweep + the mandatory negative controls -/

/-- The interpreters' discipline, swept: drawn clock + drawn schedule,
    the pure and cost-graded runs agree on the value channel, the
    journal, and the clock; the cost is the composed schedule; the
    fault injector counts 2 and its ghost is visible; the KV channel
    is fault-invisible. -/
def propInterp (t : Tape) : CheckResult := do
  let (c₀, t₁) := t.below 20
  let (g, t₂) := t₁.below 4
  let (p, t₃) := t₂.below 4
  let (a, t₄) := t₃.below 4
  let (n, _) := t₄.below 4
  let st : RefState := { cells := fun _ => 7, journal := [], clock := c₀ }
  let c : OpCost := ⟨g + 1, p + 1, a + 1, n + 1⟩
  let rp := logProgram pureSig st
  let rc := logProgram (Interpreter.cost pureSig c) (st, 0)
  assert (rp.1 == rc.1) "the pure/cost value agreement broke"
  assert (rp.2.journal == rc.2.1.journal) "the pure/cost journal agreement broke"
  assert (rp.2.clock == rc.2.1.clock) "the pure/cost clock agreement broke"
  assert (rc.2.2 == c.putCost + c.getCost + c.appendCost + c.nowCost)
    "the cost honesty broke (a silent undercount)"
  let rf := logProgram (Interpreter.fault pureSig 999) ⟨st, 0⟩
  assert (rf.2.injected == 2) "the fault count broke"
  assert (rf.2.base.journal.contains 999) "the ghost entry vanished"
  assert ((kvProgram pureSig st).1 == (kvProgram faultI ⟨st, 0⟩).1)
    "the fault injector touched the KV channel"

/-- The AGREEMENT sabotage: claims the pure and cost-graded runs'
    api results DIFFER — caught (the cost is an annotation; the value
    channel is the source's). -/
def negAgreement (_t : Tape) : CheckResult := do
  let rp := logProgram pureSig st0
  let rc := logProgram (Interpreter.cost pureSig c1) (st0, 0)
  assert (rp.1 != rc.1) "the agreement sabotage was not caught"

/-- The UNDERCOUNT sabotage: claims the cost-graded run's final cost is
    ZERO — caught (every operation's cost appears in the composed
    annotation: logProgram_cost_honest). -/
def negCostUndercount (_t : Tape) : CheckResult := do
  assert ((logProgram (Interpreter.cost pureSig c1) (st0, 0)).2.2 == 0)
    "the undercount sabotage was not caught"

/-- The GHOST-INVISIBLE sabotage: claims the fault injector's ghost
    entry is NOT in the journal — caught (the seed's fault is data,
    visible in the carrier). -/
def negGhostInvisible (_t : Tape) : CheckResult := do
  assert (!(logProgram faultI ⟨st0, 0⟩).2.base.journal.contains 999)
    "the ghost-invisible sabotage was not caught"

def specSignature : Spec := Spec.ofList "effects-signature"
  propInterp
  [ ("agreement", negAgreement),
    ("cost-undercount", negCostUndercount),
    ("ghost-invisible", negGhostInvisible) ]
  12 20250903

end EffectsTests

def main : IO UInt32 := TestingKit.mainOfSuites [("Effects", [EffectsTests.specLattice, EffectsTests.specResources, EffectsTests.specSignature])]
