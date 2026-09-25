/-
# Guest.SrcMachine — the source fragment AS a machine (wave 30, A4)

The guest's `evalS`/`Src` fragment restated as a `Machines.Machine`
(the TraceModel root, notes/v3/01-core.md §3): the mini-executor's
step is the env-extension's graph — ONE machine, the graph of the
laned semantics' own fold, never a second semantics (pattern #1; both
step directions by definition, so the readings cannot drift).

The fragment: the straight-line ANF let-chain (`Guest.Correct.Src`) —
`lit` binds a u64 literal, `fap` binds a row's application of two
bound indices, `ret` reads. The machine's state is the BINDING
ENVIRONMENT (`Nat → UInt64`); the machine's input is one binding step
(`SrcStep`); the tape is `chainTape` (the chain's bindings in order);
the run lands exactly on `envUpdS` (the bindings' composition —
`srcMachine_run_chain`). The machine is TOTAL: every step applies
(the fragment has no refusals — the honesty is that there is nothing
to refuse: no traps, no budget, no unmodeled sem).

The tie to the landed semantics (three faces):

- `evalS_machine_value` — the VALUE: `evalS e env` reads `retOf e`
  from the run's landing env — the big-step fold and the machine's
  run compute the same value;
- `envUpdS_opW` — the MAP: with the honest map `opW`, the machine's
  landing env IS the machine-side `envUpd` (the Kripke relation's
  evolving index — `Guest.Correct.Realizes`' domain) — this is the
  seam where `Guest.Correct`'s refinement (`run_chain_inv`,
  `run_chain`) composes with the machine reading;
- `adder_machine` — the duel's guest face: the adder chain's machine
  run lands on the bindings' env, and the source value 42 is the
  machine env's read — kernel-checked.

The payoff (A4): the machines' witness + observer disciplines apply
to the source fragment — `srcChain_witness`: every chain's run has a
witnessing `Machines.Exec` execution whose tape IS the binding steps
(the audit record is constructor data along it).

The five questions (notes/v3/01-core.md):

- **Root**: TraceModel (01-core §3) — the source semantics' behavior
  as the machine's executions; the derived views (tape, record) are
  Machines.Trace's, tied back to `evalS`/`envUpdS` here.
- **Carrier grade**: pattern #1 at the fragment level — the relation
  is the graph of the fold's own step; every view carries a tie.
- **Spine reading**: none — the fragment is the lowering's INPUT
  face; the machine reading rides it without new artifacts.
- **Ladder rung**: rung 1 for the machine laws (totality, run ties —
  structural folds) + rung 6 for the map/value ties (the per-primitive
  rows' induction).
- **Gate row**: Guest's row in Gates.Packages' gated set (the
  per-library axiom sweep covers this module through the umbrella);
  GuestTests' pin exercises the adder face.

Consumer trail: rides `Guest.Correct` (the fragment + the semantics +
the honest map + the Kripke refinement), `Machines.Basic`/
`Machines.Trace` (the carrier + the execution views). Core-only (the
cone rule — no mathlib, no Batteries).
-/

import Guest.Correct
import Machines.Basic
import Machines.Trace

namespace Guest

open Guest.Correct

/-! ## The binding step + the machine -/

/-- One binding step of the source fragment: bind a literal, or bind
    a row's application of two bound indices. -/
inductive SrcStep where
  | lit (r : Nat) (v : UInt64)
  | fap (r : Nat) (op : SrcOp) (a b : Nat)
deriving BEq, DecidableEq, Repr

/-- The step's env-extension — the fold's own continuation state
    (`evalS`'s lit/fap arms' extensions, verbatim). -/
def stepEnv : SrcStep → (Nat → UInt64) → (Nat → UInt64)
  | .lit r v, env => fun n => if n = r then v else env n
  | .fap r op a b, env =>
      fun n => if n = r then opEval op (env a) (env b) else env n

/-- THE SOURCE MACHINE: the fragment's mini-executor — state = the
    binding env, step = the binding's extension. Total: every step
    applies (the fragment has no refusals). -/
def srcMachine : Machines.Machine (Nat → UInt64) SrcStep :=
  ⟨fun env st => some (stepEnv st env)⟩

/-- The step bridge (pattern #1): the machine's step relation is the
    graph of `stepEnv` — both directions by definition. -/
theorem src_step_iff (env : Nat → UInt64) (st : SrcStep) (env' : Nat → UInt64) :
    srcMachine.step env st env' ↔ env' = stepEnv st env := by
  constructor
  · intro h
    simp only [Machines.Machine.step, srcMachine] at h
    exact (Option.some.inj h).symm
  · intro h
    simp only [Machines.Machine.step, srcMachine, h]

/-- The tape: the chain's binding steps, in order. -/
def chainTape : Src → List SrcStep
  | .lit r v k => .lit r v :: chainTape k
  | .fap r op a b k => .fap r op a b :: chainTape k
  | .ret _ => []

/-- The run's landing env: the bindings' composition (`evalS`'s
    env-evolution, as data). -/
def envUpdS : Src → (Nat → UInt64) → (Nat → UInt64)
  | .lit r v k, env => envUpdS k (fun n => if n = r then v else env n)
  | .fap r op a b k, env =>
      envUpdS k (fun n => if n = r then opEval op (env a) (env b) else env n)
  | .ret _, env => env

/-- The chain's read: which index the chain's `ret` names. -/
def retOf : Src → Nat
  | .lit _ _ k => retOf k
  | .fap _ _ _ _ k => retOf k
  | .ret r => r

/-! ## The run tie -/

/-- THE RUN TIE: the source machine's run over the chain's tape lands
    exactly on the bindings' env — the mini-executor's run IS the
    fold's env-evolution, both directions of the reading tied. -/
theorem srcMachine_run_chain (e : Src) (env : Nat → UInt64) :
    srcMachine.run env (chainTape e) = some (envUpdS e env) := by
  induction e generalizing env with
  | lit r v k ih =>
      show srcMachine.run env (SrcStep.lit r v :: chainTape k) = _
      rw [Machines.Machine.run_cons]
      show srcMachine.run (stepEnv (SrcStep.lit r v) env) (chainTape k) = _
      rw [ih (stepEnv (SrcStep.lit r v) env)]
      rfl
  | fap r op a b k ih =>
      show srcMachine.run env (SrcStep.fap r op a b :: chainTape k) = _
      rw [Machines.Machine.run_cons]
      show srcMachine.run (stepEnv (SrcStep.fap r op a b) env) (chainTape k) = _
      rw [ih (stepEnv (SrcStep.fap r op a b) env)]
      rfl
  | ret r => rfl

/-! ## The value + map ties -/

/-- THE VALUE TIE: `evalS` computes the read the machine's landing env
    gives at the chain's `ret` index — the big-step fold and the
    machine's run compute the SAME value. -/
theorem evalS_machine_value (e : Src) (env : Nat → UInt64) :
    evalS e env = (envUpdS e env) (retOf e) := by
  induction e generalizing env with
  | lit r v k ih =>
      simp only [evalS, envUpdS, retOf]
      rw [ih (fun n => if n = r then v else env n)]
  | fap r op a b k ih =>
      simp only [evalS, envUpdS, retOf]
      rw [ih (fun n => if n = r then opEval op (env a) (env b) else env n)]
  | ret r => rfl

/-- THE MAP TIE: with the honest map `opW`, the machine's landing env
    IS the machine-side `envUpd` — the Kripke relation's evolving
    index (`Guest.Correct.Realizes`' domain) agrees, so
    `Guest.Correct`'s refinement theorems compose with this run. -/
theorem envUpdS_opW (e : Src) (env : Nat → UInt64) :
    envUpdS e env = envUpd opW e env := by
  induction e generalizing env with
  | lit r v k ih =>
      simp only [envUpdS, envUpd]
      rw [ih]
  | fap r op a b k ih =>
      simp only [envUpdS, envUpd]
      rw [ih]
      congr 1
      funext n
      by_cases h : n = r
      · subst h; simp only [machVal_opW]
      · simp only [h, if_false]
  | ret r => rfl

/-! ## The duel's guest face + the witness -/

/-- THE ADDER'S MACHINE FACE (kernel-checked): the adder chain's
    machine run lands on the bindings' env, and the source value —
    the duel's own 42 — is the machine env's read at the result
    local. -/
theorem adder_machine :
    srcMachine.run env40 (chainTape adderSrc) = some (envUpdS adderSrc env40)
      ∧ evalS adderSrc env40 = (envUpdS adderSrc env40) 3 := by
  refine ⟨srcMachine_run_chain adderSrc env40, ?_⟩
  rw [evalS_machine_value]
  rfl

/-- THE WITNESS DISCIPLINE, applied to the fragment: every chain's run
    has a witnessing `Machines.Exec` execution whose tape IS the
    binding steps (the audit record is constructor data along it). -/
theorem srcChain_witness (e : Src) (env : Nat → UInt64) :
    ∃ ex : Machines.Exec srcMachine env (envUpdS e env), ex.tape = chainTape e :=
  ⟨Machines.Exec.run_exec srcMachine env (srcMachine_run_chain e env),
   Machines.Exec.tape_run_exec srcMachine env (chainTape e) (envUpdS e env)
     (srcMachine_run_chain e env)⟩

end Guest
