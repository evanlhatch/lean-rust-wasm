/-
# WasmCore.ExecMachine — the executor AS a machine (wave 30, A4)

The executor's step/run restated as `Machines.Machine` instances (the
TraceModel root, notes/v3/01-core.md §3): the step relation is the
GRAPH of the landed executor's own functions — never a second
semantics (pattern #1: relation-as-spec + executable checker + the
proved bridge, both directions by definition, so the two readings of
one transition CANNOT drift).

Three faces, one carrier each:

- `flatMachine` — the ONE-STEP face: `Instr`-labeled steps over
  `State`, the graph of `WasmCore.step`'s `.ok` face. A non-`.ok`
  outcome is an honest DISABLED input (`none`), never a silent
  self-loop; the outcome LEDGER below keeps the refusals distinct.
- `execMachine` — the RUN face: the graph of `execList`'s `.ok` face,
  the input a (budget, tape) pair — the fuel discipline rides IN the
  input (01-core §3: the budget is SEMANTICS, so it is data the
  machine consumes, not noise the machine hides).
- `loopMachine` — the wp lane's while carrier: Contracts.WpMachine
  (the bridge file; the wp↔machine simulation lives there).

THE OUTCOME DISCIPLINE ↔ THE TRICHOTOMY: `outcomeVerdict` maps the
layered `Outcome` ledger onto the machine's honest trichotomy —
`.ok` = PROVED (the certificate is the final state), `.trap` = REFUTED
(the witness is the trap kind: DATA, not a string — `refuted_witness`),
`.outOfFuel` = UNKNOWN (budget exhaustion is never a verdict — pinned
at budget 0 by `zeroBudget_unknown` and for flat tapes by
`flat_outOfFuel_honest`), `.unmodeled` = UNKNOWN (outside the executed
fragment — DISTINCT from a trap, the R6 discipline, pinned by
`unmodeled_ne_trap`), `.branch`/`.structural` = the control SIGNALS
(never laundered into either verdict).

THE PAYOFF (A4's accept line): the machines' landed disciplines apply
to the executor with NO new proofs —

- the `Machines.Exec` witness + the tape/record projections
  (Machines.Trace) — `flat_exec_tape`: every successful flat run has
  a witnessing execution whose tape IS the instruction list;
- reachability = run-success (Machines.Basic's two-direction tie) —
  cited, applies verbatim to both machines;
- the conformance battery + the duel: the duel's Lean expectations are
  the EXECUTOR machine's runs (the WasmCoreTests pins run the duel
  family through `execMachine` and compare with `WasmCore.Duel`'s
  committed rows — byte-identical executions, the behavior teeth;
  `duel_arith_machine_run` is the kernel-checked face).

THE DUEL RESTATED (A4): the Lean-exec ≡ wasmtime agreement as a
simulation between machines. The FORMAL half is `execSelfSim` — the
executor machine simulates itself along the state tie — riding A1's
carrier-as-graph bridge: its graph is `Kit.Simulation.toRel`, the
diagonal (`execSelfSim_toRel` cites the bridge's unit row), and the
graph is single-valued (`exec_step_det` — the executor's
determinism, one state + one tape + one budget ⇒ one outcome, the
determinism claim's machine face). The EXTERNAL half — the wasmtime
engine — has no Lean carrier: the agreement is SAMPLED per duel vector
(Kit.Duel's verdict vocabulary; the tier honesty: tested agreement,
never a theorem over unbounded inputs — the host duel runner carries
the same sentence). The TOWER: the source semantics rides
`Guest.Correct`'s Kripke refinement INTO the executor machine (the
landed `run_chain_inv` leg), and `execSelfSim` is the machine-level
leg the duel samples — the composite the wp↔machine bridge
(Contracts.WpMachine) mirrors on the contracts lane.

The five questions (notes/v3/01-core.md):

- **Root**: TraceModel (01-core §3) — the executor's behavior AS the
  machine's executions: the derived views (tapes, records,
  reachability) are Machines.Trace's, tied back to the authoritative
  `execList`/`step` functions by the theorems here.
- **Carrier grade**: pattern #1 at the executor level — the relation
  is the GRAPH of the landed checker (both step bridges by
  definition); every derived view carries a proved tie.
- **Spine reading**: none new — the machine reading rides the ONE
  AST's executor (the last consumer of the spine gains a reading).
- **Ladder rung**: rung 6 — the flat-tape ties are hand theorems with
  named relational content (the fuel-peel induction); the
  one-step/determinism/graph-diagonal faces are `rfl`/cited.
- **Gate row**: WasmCore's row in Gates.Packages' gated set (the
  per-library axiom sweep covers this module through the umbrella);
  WasmCoreTests' machine suite pins the duel's machine face.

Consumer trail: rides `WasmCore.Exec` (the executor — its BEHAVIOR is
untouched: every theorem here CONSUMES `step`/`execList`/`runFunc`,
none redefines them), `WasmCore.Duel` (the committed family the
machine face runs), `Machines.Basic`/`Machines.Trace` (the machine
carrier + the execution views), `Kit.Correspondence` (the simulation
grade + the carrier-as-graph bridge). Core-only (the cone rule — no
mathlib, no Batteries).
-/

import WasmCore.Exec
import WasmCore.Duel
import Machines.Basic
import Machines.Trace
import Kit.Correspondence
import Kit.Relation

namespace WasmCore

/-! ## The flat machine — the executor's one-step face -/

/-- The flat-form classifier: everything the ONE-STEP face applies to
    — the frame forms (`Validate.FrameForm`) and the two call forms
    are the frame machine's (the calls layer's fuel-shared big step),
    and the flat machine refuses them as honest disabled inputs. -/
def FlatForm (i : Instr) : Prop :=
  FrameForm i = False ∧ (∀ fn, i ≠ Instr.call fn) ∧ (∀ ty, i ≠ Instr.callindirect ty)

/-- The flat form's execList equation — `execList_flat` at the
    classifier (the one-step face's reduction, named once). -/
theorem execList_of_flat (m : Module) (fuel : Nat) (s : State) (i : Instr)
    (is : List Instr) (h : FlatForm i) :
    execList m (fuel + 1) s (i :: is)
      = match step s i with
        | .ok s' => execList m fuel s' is
        | .branch d s2 => .branch d s2
        | .trap r => .trap r
        | .structural => .structural
        | .unmodeled => .unmodeled
        | .outOfFuel => .outOfFuel :=
  execList_flat m fuel s i is h.1 h.2.1 h.2.2

/-- The executor's flat step never answers the budget outcome — `step`
    is fuel-free (the fuel discipline lives in `execList` alone). -/
theorem step_ne_outOfFuel (s : State) (i : Instr) : step s i ≠ .outOfFuel := by
  cases i <;> simp [step] <;> (try split) <;> (try split) <;> (try simp)

/-- The step/structural dichotomy: either the step is not the frame
    answer, or the instruction IS a frame form (which `execList`
    dispatches before ever calling `step`). -/
theorem step_structural_or_frame (s : State) (i : Instr) :
    step s i ≠ .structural ∨ FrameForm i = True := by
  cases i <;> simp [step, FrameForm] <;> (try split) <;> (try split) <;> (try simp)

/-- THE FLAT MACHINE: the executor's one-step face as a
    `Machines.Machine` — the step relation is `step`'s `.ok` graph. A
    branch signal, trap, or unmodeled answer is a DISABLED input
    (`none` — the refusal is honest data, never a silent self-loop);
    the outcome ledger below keeps the refusal classes distinct. -/
def flatMachine : Machines.Machine State Instr :=
  ⟨fun s i => match step s i with | .ok s' => some s' | _ => none⟩

/-- THE ONE-STEP BRIDGE (pattern #1, at the executor): the machine's
    step relation IS the graph of the executor's `step` — both
    directions by definition. -/
theorem flat_step_iff (s : State) (i : Instr) (s' : State) :
    flatMachine.step? s i = some s' ↔ step s i = .ok s' := by
  cases h : step s i <;> simp [flatMachine, h]

/-- The flat machine's RUN over a flat tape: the fuel-peel tie,
    forwards — a successful machine run IS the executor's `.ok` run,
    at any budget above the tape (the budget the run consumes is one
    per flat step — the fuel honesty in the statement). -/
theorem flat_run_forwards (m : Module) : ∀ (is : List Instr) (fuel : Nat) (s s' : State),
    (∀ i ∈ is, FlatForm i) → is.length < fuel →
    (flatMachine).run s is = some s' → execList m fuel s is = .ok s' := by
  intro is
  induction is with
  | nil =>
      intro fuel s s' _ hlen hrun
      cases fuel with
      | zero => exact absurd hlen (by simp)
      | succ n =>
          rw [Machines.Machine.run_nil] at hrun
          rw [execList_nil, Option.some.inj hrun]
  | cons i t ih =>
      intro fuel s s' hflat hlen hrun
      cases fuel with
      | zero => exact absurd hlen (by simp)
      | succ n =>
          rw [Machines.Machine.run_cons] at hrun
          obtain ⟨s₁, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
          rw [flat_step_iff s i s₁] at hstep
          have hlen' : t.length < n := by simp at hlen ⊢; omega
          simp only [execList_of_flat m n s i t (hflat i (by simp)), hstep]
          exact ih n s₁ s' (fun i' hi' => hflat i' (List.mem_cons_of_mem _ hi'))
            hlen' hrest

/-- The flat machine's run tie, backwards — the executor's `.ok` run
    at a budget above the tape IS a successful machine run (the
    machine reading recovers the executor, not the reverse alone). -/
theorem flat_run_backwards (m : Module) : ∀ (is : List Instr) (fuel : Nat) (s s' : State),
    (∀ i ∈ is, FlatForm i) → execList m fuel s is = .ok s' →
    is.length < fuel ∧ (flatMachine).run s is = some s' := by
  intro is
  induction is with
  | nil =>
      intro fuel s s' _ hok
      cases fuel with
      | zero => rw [execList_zero] at hok; exact absurd hok (by simp)
      | succ n =>
          rw [execList_nil, Outcome.ok.injEq] at hok
          subst hok
          exact ⟨by simp, Machines.Machine.run_nil (flatMachine) s⟩
  | cons i t ih =>
      intro fuel s s' hflat hok
      cases fuel with
      | zero => rw [execList_zero] at hok; exact absurd hok (by simp)
      | succ n =>
          rw [execList_of_flat m n s i t (hflat i List.mem_cons_self)] at hok
          cases hstep : step s i with
          | ok s₁ =>
              rw [hstep] at hok
              obtain ⟨hl, hrun⟩ := ih n s₁ s'
                (fun i' hi' => hflat i' (List.mem_cons_of_mem _ hi')) hok
              refine ⟨by simp at hl ⊢; omega, ?_⟩
              rw [Machines.Machine.run_cons, (flat_step_iff s i s₁).mpr hstep]
              exact hrun
          | branch d s2 => rw [hstep] at hok; simp at hok
          | trap r => rw [hstep] at hok; simp at hok
          | structural => rw [hstep] at hok; simp at hok
          | unmodeled => rw [hstep] at hok; simp at hok
          | outOfFuel => rw [hstep] at hok; simp at hok

/-- THE FLAT RUN TIE (both directions, one statement): over a flat
    tape the executor's `.ok` run and the machine's successful run are
    THE SAME execution — at any budget above the tape. -/
theorem flat_run_iff (m : Module) (is : List Instr) (fuel : Nat) (s s' : State)
    (hflat : ∀ i ∈ is, FlatForm i) :
    execList m fuel s is = .ok s' ↔ is.length < fuel ∧ (flatMachine).run s is = some s' :=
  ⟨flat_run_backwards m is fuel s s' hflat,
   fun h => flat_run_forwards m is fuel s s' hflat h.1 h.2⟩

/-- A flat tape at a budget above the tape NEVER answers `.outOfFuel`
    — the fuel-peel induction's honesty face (each flat step consumes
    exactly one unit, and the non-`.ok` answers are the honest
    trap/branch data, never the budget). -/
theorem flat_run_other (m : Module) : ∀ (is : List Instr) (fuel : Nat) (s : State),
    (∀ i ∈ is, FlatForm i) → is.length < fuel → execList m fuel s is ≠ .outOfFuel := by
  intro is
  induction is with
  | nil =>
      intro fuel s _ hlen
      cases fuel with
      | zero => exact absurd hlen (by simp)
      | succ n => rw [execList_nil]; simp
  | cons i t ih =>
      intro fuel s hflat hlen
      cases fuel with
      | zero => exact absurd hlen (by simp)
      | succ n =>
          simp only [execList_of_flat m n s i t (hflat i List.mem_cons_self)]
          cases hstep : step s i with
          | ok s₁ =>
              exact ih n s₁ (fun i' hi' => hflat i' (List.mem_cons_of_mem _ hi'))
                (by simp at hlen ⊢; omega)
          | branch d s2 => simp
          | trap r => simp
          | structural => simp
          | unmodeled => simp
          | outOfFuel => exact absurd hstep (step_ne_outOfFuel s i)

/-- THE FUEL HONESTY (01-core §3, at the flat face): a flat tape's
    budget exhaustion is a statement about the BUDGET — it can only
    happen when the budget was below the tape. Never a verdict about
    the program: refuel and the run either completes or answers the
    honest trap/branch data. -/
theorem flat_outOfFuel_honest (m : Module) (is : List Instr) (fuel : Nat) (s : State)
    (hflat : ∀ i ∈ is, FlatForm i) (h : execList m fuel s is = .outOfFuel) :
    fuel ≤ is.length := by
  cases Nat.lt_or_ge is.length fuel with
  | inl hlt => exact absurd h (flat_run_other m is fuel s hflat hlt)
  | inr hge => exact hge

/-! ## The outcome ledger's trichotomy face -/

/-- The executor's verdict — the outcome discipline mapped onto the
    machine's honest trichotomy (01-core §3). -/
inductive ExecVerdict where
  /-- PROVED: the certificate is the final state. -/
  | proved (s : State)
  /-- REFUTED: the witness is the trap kind — data, not a string. -/
  | refuted (t : Trap)
  /-- UNKNOWN: the budget ran out — never a verdict. -/
  | unknownFuel
  /-- UNKNOWN: outside the executed fragment — DISTINCT from a trap
      (the R6 discipline). -/
  | unknownFragment
  /-- The control SIGNALS (branch, structural) — never laundered into
      either verdict. -/
  | signal

/-- The mapping: `.ok` → PROVED, `.trap` → REFUTED, `.outOfFuel` /
    `.unmodeled` → the two UNKNOWNs, the signals → `signal`. -/
def outcomeVerdict : Outcome → ExecVerdict
  | .ok s => .proved s
  | .trap t => .refuted t
  | .branch _ _ => .signal
  | .structural => .signal
  | .unmodeled => .unknownFragment
  | .outOfFuel => .unknownFuel

/-- Zero budget: the honest UNKNOWN — never a verdict (the fuel
    discipline's anchor, `execList_zero` cited). -/
theorem zeroBudget_unknown (m : Module) (s : State) (is : List Instr) :
    outcomeVerdict (execList m 0 s is) = .unknownFuel := by
  simp [execList_zero, outcomeVerdict]

/-- A REFUTED verdict carries its witness: the outcome IS the trap. -/
theorem refuted_witness (o : Outcome) (t : Trap)
    (h : outcomeVerdict o = .refuted t) : o = .trap t := by
  cases o <;> simp_all [outcomeVerdict]

/-- The R6 discipline at the verdict face: the unmodeled UNKNOWN is
    never a trap — an unmodeled SEM is distinct, never laundered. -/
theorem unmodeled_ne_trap (o : Outcome) (t : Trap)
    (h : outcomeVerdict o = .unknownFragment) : o ≠ .trap t := by
  cases o <;> simp_all [outcomeVerdict]

/-! ## The run machine — the executor's execList face -/

/-- THE RUN MACHINE: the executor's `execList` as a `Machines.Machine`
    — the input is the (budget, tape) pair, the step relation is
    `execList`'s `.ok` graph. Every refusal (trap, branch signal,
    unmodeled, outOfFuel) is an honest disabled input; the outcome
    ledger above keeps the refusal classes distinct. -/
def execMachine (m : Module) : Machines.Machine State (Nat × List Instr) :=
  ⟨fun s fi => match execList m fi.1 s fi.2 with
    | .ok s' => some s' | _ => none⟩

/-- THE RUN BRIDGE (pattern #1, at the executor): the machine's step
    relation IS the graph of `execList` — both directions by
    definition. -/
theorem exec_step_iff (m : Module) (s : State) (fi : Nat × List Instr) (s' : State) :
    (execMachine m).step? s fi = some s' ↔ execList m fi.1 s fi.2 = .ok s' := by
  cases h : execList m fi.1 s fi.2 <;> simp [execMachine, h]

/-- THE SINGLE-TAPE TIE: one machine step over the (budget, tape)
    pair IS the executor's run. -/
theorem exec_run_single_iff (m : Module) (fuel : Nat) (is : List Instr) (s s' : State) :
    (execMachine m).run s [(fuel, is)] = some s' ↔ execList m fuel s is = .ok s' := by
  rw [Machines.Machine.run_one]
  exact exec_step_iff m s (fuel, is) s'

/-- THE DETERMINISM (the machine face of 01-core §3's "one state, one
    list, one budget ⇒ one outcome"): the run machine's graph is
    single-valued — the executor machine cannot diverge from itself. -/
theorem exec_step_det (m : Module) (s : State) (fi : Nat × List Instr) (s₁ s₂ : State)
    (h₁ : (execMachine m).step? s fi = some s₁) (h₂ : (execMachine m).step? s fi = some s₂) :
    s₁ = s₂ := Option.some.inj (h₁.symm.trans h₂)

/-- The tapes compose: the machine's run over a two-tape input is the
    executor's sequential composition — the first tape's `.ok` state
    feeds the second (Machines.Basic's run laws at the executor). -/
theorem exec_run_two (m : Module) (f₁ f₂ : Nat) (is₁ is₂ : List Instr)
    (s s' s'' : State)
    (h₁ : execList m f₁ s is₁ = .ok s') (h₂ : execList m f₂ s' is₂ = .ok s'') :
    (execMachine m).run s [(f₁, is₁), (f₂, is₂)] = some s'' := by
  rw [Machines.Machine.run_cons, (exec_step_iff m s (f₁, is₁) s').mpr h₁]
  simp only [Option.bind_some]
  exact (exec_run_single_iff m f₂ is₂ s' s'').mpr h₂

/-! ## The witness + the observers (Machines.Trace's disciplines, applied) -/

/-- THE WITNESS DISCIPLINE, applied to the executor: every successful
    flat machine run has a witnessing `Machines.Exec` execution whose
    tape IS the instruction list — the audit record (the observer
    face) is constructor data along it. -/
theorem flat_exec_tape (is : List Instr) (s s' : State)
    (h : (flatMachine).run s is = some s') :
    ∃ e : Machines.Exec (flatMachine) s s', e.tape = is :=
  ⟨Machines.Exec.run_exec (flatMachine) s h,
   Machines.Exec.tape_run_exec (flatMachine) s is s' h⟩

/-! ## THE DUEL RESTATED (A4) -/

/-- THE DUEL'S FORMAL HALF: the executor machine simulates itself
    along the state tie — `Kit.Simulation.refl` (cited, the identity
    simulation). Its graph (`Kit.Simulation.toRel`) is the diagonal
    (A1's carrier-as-graph bridge; `execSelfSim_toRel` below), and it
    is single-valued (`exec_step_det`) — so the Lean-side expectation
    of every duel row is ONE machine execution. The EXTERNAL half —
    the wasmtime engine — has no Lean carrier: the agreement is
    SAMPLED per duel vector (the tier honesty; the WasmCoreTests pins
    run the family through `execMachine` against `WasmCore.Duel`'s
    committed rows). -/
def execSelfSim (m : Module) (fi : Nat × List Instr) : Kit.Simulation State State :=
  Kit.Simulation.refl State (fun a b => (execMachine m).step a fi b)

/-- The formal half's graph IS the diagonal — the bridge's unit row,
    cited (Kit.Simulation.toRel_refl). -/
theorem execSelfSim_toRel (m : Module) (fi : Nat × List Instr) (a b : State) :
    (execSelfSim m fi).toRel a b ↔ Kit.Rel.refl State a b :=
  Kit.Simulation.toRel_refl State (fun a b => (execMachine m).step a fi b) a b

/-- The duel's arithmetic row's body (the committed module's function
    body, extracted — the ONE copy; `arithBody_pin` pins the
    extraction in values). -/
def arithBody : List Instr :=
  match WasmCore.Duel.arithModule.funcs[0]? with
  | some f => f.body
  | none => []

/-- The extraction pin: the body is the committed twelve-instruction
    arithmetic chain (the duel family's spec, in values). -/
theorem arithBody_pin :
    arithBody = [ .i32const 6, .i32const 7, .op .i32mul
                , .i32const 8, .op .i32add
                , .i32const 3, .op .i32shru
                , .op .i64extendi32u
                , .i64const 36, .op .i64mul
                , .i64const 174, .op .i64sub ] := rfl

/-- THE DUEL'S MACHINE FACE (kernel-checked): the executor machine's
    single-tape run of the committed arithmetic row — at ANY budget
    the body needs — lands exactly on the duel's expectation value 42
    on the stack, from ANY init state (the body touches only the
    operand stack). The machine reading and the committed duel row are
    byte-identical executions. -/
theorem duel_arith_machine_run (init : State) (fuel : Nat) (hf : 12 < fuel) :
    (execMachine WasmCore.Duel.arithModule).run init [(fuel, arithBody)]
      = some { init with stack := Val.i64 42 :: init.stack } := by
  have hflat : ∀ i ∈ arithBody, FlatForm i := by
    intro i hi
    rw [arithBody_pin] at hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    rcases hi with rfl | hi
    · exact ⟨rfl, by simp, by simp⟩
    exact absurd hi (by simp)
  have hrun : (flatMachine).run init arithBody
      = some { init with stack := Val.i64 42 :: init.stack } := rfl
  have hlen : arithBody.length = 12 := by rw [arithBody_pin]; rfl
  rw [exec_run_single_iff]
  exact (flat_run_iff WasmCore.Duel.arithModule arithBody fuel init _ hflat).mpr
    ⟨by omega, hrun⟩

end WasmCore
