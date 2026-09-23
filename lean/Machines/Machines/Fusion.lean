/-
# Machines.Fusion — the dbsp-machine fusion cluster

The canon rows say the machine / event-sourcing / dbsp rows are ONE
phenomenon; this module fuses them at the theorem level. Every bridge
here is a STATEMENT + GLUE over landed laws — no new inductions beyond
the run-unfolding each bridge needs.

1. **D/I as a Kit Iso** (`dI`): dbsp's differentiation/integration pair
   packaged as `CodegenCore.Iso (Dbsp.Stream a) (Dbsp.Stream a)`. Zero-
   initial convention: `D` carries the initial value in its first entry
   (`(D s) 0 = s 0`), so the iso holds on the PLAIN stream type — no
   `s(-1) = 0` subtype needed. Consumed: `Dbsp.derivative_integral`,
   `Dbsp.integral_derivative` (Dbsp.Linear).
2. **The convergence bridge** (`settle_reaches_seminaive`,
   `settle_run_bounded`): the tick cascade's settle and the machine's
   termination certificate are one phenomenon. The settle machine (one
   event = one semi-naive pass, state = value × remaining budget) is
   `Convergent` by `countDown`, so `Convergent.run_length_bound` bounds
   every cascade; when the iterate stabilizes, the settled value IS the
   dbsp fixpoint (`Dbsp.seminaive_ok` — `seminaive_equiv`/`fix_unique`'s
   computed form). Consumed: Dbsp.Recursive + Machines.Convergent.
3. **Bisimulation as stream equality** (`bisim_iff_resp_streams`): for
   deterministic machines, two states are bisimilar (one-step
   tick-agreement — the classical notion; cslib's LTS is NOT re-derived)
   iff their response streams are EQUAL on every input stream, stated
   over `Dbsp.Stream` (the `Machine.InfiniteRun` time-theory). For
   finite-state machines this is decidable by table enumeration — the
   fixture below decides it (Tests/Main.lean pins).

The journal/replay bridge (event sourcing: journal = D ∘ run, replay =
I ∘ journal) lives in `SchemaLang.EventSourced` — schema-lang imports
Machines, not the reverse (the Machines.Fusion home cannot see it).

Cross-type machine pairs (different `State`/`Label` types) are out of
scope until a relational-simulation order lands; the bridge here is the
shared-vocabulary case, which is where stream EQUALITY (not just
relatedness) is stated.
-/

module

public import Machines.Core
public import Machines.Convergent
public import Dbsp.Stream
public import Dbsp.Linear
public import Dbsp.Recursive
public import CodegenCore.Kit
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Function.Iterate

-- Module discipline: all declarations public; bodies exposed
-- (defs/abbrevs/instances must reduce across module boundaries).
@[expose] public section

namespace Machines

variable {G A B : Type} [AddCommGroup A] [AddCommGroup B]

/-- One tick of the machine, TOTAL: fire the label if enabled, else hold
(a blocked event is a no-op — the Sim convention). The deterministic
machine's step as a plain function. -/
def Machine.tick (m : Machine) (l : m.Label) (s : m.State) : m.State :=
  (m.step? s l).getD s

namespace Fusion

/-! ## Bridge 1 — the D/I pair as a Kit Iso -/

/-- **THE D/I ISO**: integration and differentiation are a true bijection
on streams, packaged as the correspondence kit's `CodegenCore.Iso`
(`to := I`, `inv := D`). Both directions are the LANDED laws —
`Dbsp.derivative_integral` (`I ∘ D = id`: replaying the journal
reconstructs the world) and `Dbsp.integral_derivative` (`D ∘ I = id`):
nothing is re-proved here.

The zero-initial convention, stated honestly: `D` is total —
`(D s) 0 = s 0` (`Dbsp.derivative_0`), the first journal entry CARRIES
the initial value, and `I` starts from it (`(I s) 0 = s 0`). Both
composites are identities on the PLAIN `Dbsp.Stream a`; the subtype
`{s | s (-1) = 0}` reading is unnecessary. The symmetric iso (swap
`to`/`inv`) is the same structure; one direction is named. -/
-- Construction note: field-named syntax (`where to := …`) does not parse —
-- `to` is a reserved token in Lean 4 (the Kit's `from`→`inv` lesson, on the
-- other side of the field). Positional `Iso.mk` below.
def dI (a : Type) [AddCommGroup a] : CodegenCore.Iso (Dbsp.Stream a) (Dbsp.Stream a) :=
  CodegenCore.Iso.mk Dbsp.I Dbsp.D
    Dbsp.derivative_integral Dbsp.integral_derivative

/-! ## Bridge 2 — the convergence bridge (cascade settle = machine
termination = dbsp fixpoint) -/

/-- The settle machine: one event = one settle pass of the recursive
rule `R i` (the semi-naive iteration); the state is (current value ×
remaining pass budget). This is the machine shape whose termination
certificate (`Convergent`) and whose fixpoint value (`Dbsp.seminaive`)
the bridge ties. -/
-- `@[reducible]`: the sim's `addMachine` precedent — `(settleMachine R i).State`
-- must unfold in the run statements below (the Sim.lean `addMachine` lesson).
@[reducible]
def settleMachine (R : B → A → A) (i : B) : Machine where
  State := A × Nat
  Label := Unit
  Inv := fun _ => True
  event := fun _ =>
    { guard := fun s => decide (s.2 > 0)
    , action := fun s _ => (R i s.1, s.2 - 1)
    , safety := fun _ _ h => h }

/-- The settle machine's convergence certificate: the variant is the
remaining pass budget, and each settle spends exactly one
(`Convergent.countDown`, k = 1) — the cascade-termination certificate. -/
def settleMachine_convergent (R : B → A → A) (i : B) :
    Convergent (settleMachine R i) :=
  Convergent.countDown _ (fun s => s.2) (fun _ => 1)
    (by intro s l h; cases l; rfl)
    (by intro s l _h; cases l; omega)
    (by intro s l h; cases l; have := of_decide_eq_true h; omega)

omit [AddCommGroup A] [AddCommGroup B] in
/-- The settle machine's run: `f` settle passes from value `x` with
budget `f` reach `(R i)^[f] x` with the budget spent — the cascade IS
the iterate sequence `Dbsp.approxs` tracks (`approxs_apply`). -/
theorem settleMachine_run (R : B → A → A) (i : B) (x : A) :
    ∀ (f : Nat), ∃ tr,
      (settleMachine R i).run (x, f) (List.replicate f ()) =
        some (tr, ((R i)^[f] x, 0)) := by
  intro f
  induction f generalizing x with
  | zero => exact ⟨[], rfl⟩
  | succ f ih =>
    have hstep : (settleMachine R i).step? (x, f + 1) () = some (R i x, f) := by
      show (if decide ((x, f + 1).2 > 0) = true
        then some ((settleMachine R i).event () |>.action (x, f + 1)
          (by rfl)) else none) = some (R i x, f)
      have hpos : decide ((x, f + 1).2 > 0) = true :=
      decide_eq_true (Nat.succ_pos f)
      rw [if_pos hpos]
      rfl
    obtain ⟨tr, hr⟩ := ih (R i x)
    refine ⟨((), (R i x, f)) :: tr, ?_⟩
    rw [List.replicate_succ]
    rw [Machine.run_cons]
    rw [hstep]
    simp only
    rw [hr]
    rfl

/-- **THE CONVERGENCE BRIDGE**: when the iterate stabilizes at pass `n`
(the decidable settle condition — `Dbsp.recursive_fixpoint_ok`'s
hypothesis), the settle machine's cascade terminates EXACTLY at the dbsp
fixpoint: the value the semi-naive evaluator computes
(`Dbsp.seminaive_ok`, via `seminaive_equiv`/`cycle_incremental`). The
machine's termination and the stream-level fixpoint are one phenomenon:
the cascade is the tick loop, the stabilization is the guard going
false, and the settled value is the `fix` point `fix_unique` names. -/
theorem settle_reaches_seminaive (R : B → A → A) (i : B) (n : Nat)
    (heqn : (R i)^[n + 1] 0 = (R i)^[n] 0) :
    ∃ tr, (settleMachine R i).run ((0 : A), n) (List.replicate n ()) =
      some (tr, (Dbsp.seminaive R i, 0)) := by
  obtain ⟨tr, hr⟩ := settleMachine_run R i 0 n
  refine ⟨tr, ?_⟩
  rw [hr, Dbsp.seminaive_ok R i n heqn]

omit [AddCommGroup A] [AddCommGroup B] in
/-- The termination half, consumed: any successful settle cascade is
length-bounded by its starting pass budget —
`Convergent.run_length_bound` at the count-down certificate. -/
theorem settle_run_bounded (R : B → A → A) (i : B) (x : A) (f : Nat)
    (ls : List (settleMachine R i).Label)
    (tr : Machine.Trace (settleMachine R i)) (fin : (settleMachine R i).State)
    (h : (settleMachine R i).run (x, f) ls = some (tr, fin)) :
    ls.length ≤ f :=
  Convergent.run_length_bound (settleMachine_convergent R i) (x, f) ls tr fin h

/-! ## Bridge 3 — bisimulation as stream equality -/

/-- The state after `k` further ticks from time `t` (state `s`): the
non-autonomous iterate of the input stream. -/
def runFrom (m : Machine) (ins : Dbsp.Stream m.Label) (s : m.State) :
    Nat → Nat → m.State
  | _, 0 => s
  | t, k + 1 => runFrom m ins (m.tick (ins t) s) (t + 1) k

/-- The RESPONSE stream: the post-state after each tick under input
stream `ins` (`respStream m s ins t` = the state after ticks `0..t`).
One per tick — the machine's observable output over the dbsp
time-theory (`Machine.InfiniteRun`'s `Dbsp.Stream`). -/
def respStream (m : Machine) (s : m.State) (ins : Dbsp.Stream m.Label) :
    Dbsp.Stream m.State :=
  fun t => runFrom m ins s 0 (t + 1)

/-- Bisimilar states emit equal response streams on every input stream:
the states agree after the first tick (tick-agreement), so the response
streams agree from time 0. -/
theorem respStream_tick_agree (m : Machine) (s₁ s₂ : m.State)
    (h : ∀ l, m.tick l s₁ = m.tick l s₂) (ins : Dbsp.Stream m.Label) :
    respStream m s₁ ins = respStream m s₂ ins := by
  funext t
  cases t with
  | zero => exact h (ins 0)
  | succ t =>
      show runFrom m ins s₁ 0 (t + 2) = runFrom m ins s₂ 0 (t + 2)
      rw [show runFrom m ins s₁ 0 (t + 2)
              = runFrom m ins (m.tick (ins 0) s₁) 1 (t + 1) from rfl,
          show runFrom m ins s₂ 0 (t + 2)
              = runFrom m ins (m.tick (ins 0) s₂) 1 (t + 1) from rfl,
          h (ins 0)]

/-- **THE BISIMULATION BRIDGE** (stream level): two states are bisimilar
— one-step tick-agreement, which for DETERMINISTIC machines is the
classical bisimulation (equal futures; cslib's `IsBisimulation`/LTS is
NOT re-derived here, the canon row points there when a consumer needs
the general nondeterministic story) — iff their response streams are
EQUAL on every input stream (`Dbsp.Stream` of labels ↦ `Dbsp.Stream` of
states). Finite machines: tick-agreement is decidable by table
enumeration (the `machine!` transition table — the fixture in
Tests/Main.lean decides a genuine distinct bisimilar pair plus a
negative control). -/
theorem bisim_iff_resp_streams (m : Machine) (s₁ s₂ : m.State) :
    (∀ l : m.Label, m.tick l s₁ = m.tick l s₂) ↔
      ∀ ins : Dbsp.Stream m.Label, respStream m s₁ ins = respStream m s₂ ins := by
  constructor
  · exact respStream_tick_agree m s₁ s₂
  · intro h l
    exact congrFun (h (fun _ => l)) 0

end Fusion

end Machines

end -- @[expose] public section
