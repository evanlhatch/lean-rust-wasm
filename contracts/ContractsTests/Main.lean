/-
# ContractsTests — the rules' pins, the discharge's teeth, the negative controls

Positive pins + the MANDATORY negative controls (15-patterns #5). Three
kinds of teeth, all load-bearing:

- **BUILD-TIME teeth** (`#guard_msgs`): the WRONG postcondition's
  obligation REFUSES TO DECIDE; a discharge filed under the WRONG TIER
  fails to construct; the WRONG INVARIANT's and the WRONG VARIANT's
  verification conditions REFUSE TO DISCHARGE (the loop discipline's
  honesty: the invariant is required data, and a wrong one is refuted,
  never repaired);
- **RUNTIME controls** (the TestingKit sweep): the sabotaged siblings
  the sweep MUST catch (the exec leak, the too-strong wp, the
  fabricated discharge, the silent vacuity, the wrong invariant, the
  wrong variant, the too-small fuel);
- **the vacuity tripwire** (04 §5): the inconsistent contract's
  satisfaction is PROVABLE — and the point of the test is that the
  honest pairing DECLARES it (`.declaredVacuous`), the unchecked row
  renders as the warning, never a pass.

Suites:

1. `rules` — the bind/seq/cond/composition/monotonicity/consequence
   rules pinned on concrete programs; the soundness exercised; the
   exactness iff (wp = the strongest precondition).
2. `surface` — the contract + the obligations: the VCs suffice
   (symbolic), the result-carrying contract's satisfaction, the point
   discharge fires and is sound at the indexed strength, the
   satisfaction obligation discharges by citation, the feasibility
   rows report honestly.
3. `loops` — the while discipline's worked example (the summing loop:
   invariant + variant + the four VCs discharged), the loop's
   satisfaction filed as the obligation and discharged by citation,
   the loop's point checks through the kit's decidable backend.
4. `sweep` — the LCG-seeded property sweeps with the negative controls.

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the engine's theorems — NO axioms beyond the core triple, or the
build fails.
-/

import Contracts
import LintKit  -- the @[nolint ... "reason"] syntax for the teeth decls
import TestingKit.Spec
import TestingKit.Harness
import ContractsTests.Axioms

open Contracts TestingKit

namespace ContractsTests

/-! ## The fixtures -/

/-- The zero state (the concrete entry state for the point checks). -/
def s0 : State := fun _ => 0

/-- A drawn state: cells 1, 2, 10 pinned, the rest zero. -/
def stOf (a b c : Nat) : State := fun k => if k = 1 then a else if k = 2 then b else c

def incr1 : Prog := .assign 1 (fun s => s 1 + 1)
def incr2 : Prog := .assign 2 (fun s => s 2 + 1)
def both : Prog := Prog.seq incr1 incr2

/-- The branch: if cell 1 is zero, skip; else increment it. -/
def branchProg : Prog :=
  .cond (fun s => s 1 == 0) Prog.skip (Prog.assign 1 (fun s => s 1 + 1))

/-- The value-returning example: read cell 1, write it to cell 2, and
RETURN it — the bind's continuation reads the result (§36's `p >>= k`)
and the result reaches the exit state pair. -/
def rd1 : Prog := .ret (fun s => s 1)
def bindProg : Prog :=
  Prog.bind rd1 (fun x =>
    Prog.bind (Prog.assign 2 (fun _ => x)) (fun _ => .ret (fun s => s 2)))

/-- The honest contract: from cells 1, 2 zero, `both` lands both at 1. -/
def cBoth : Contract Nat where
  requires := fun s => s 1 = 0 ∧ s 2 = 0
  ensures := fun _ _ s' => s' 1 = 1 ∧ s' 2 = 1

/-- The RESULT contract: `bindProg` returns the old cell 1 and lands it
in cell 2 — the postcondition over the RESULT + the state (§36's full
shape, lived-in). -/
def cBind : Contract Nat where
  requires := fun _ => True
  ensures := fun si r sf => r = si 1 ∧ sf 2 = si 1

/-- The WRONG contract: cell 1 lands at 99 — its VC is false, and the
discharge must refuse it (the teeth below). -/
def cWrong : Contract Nat where
  requires := fun s => s 1 = 0 ∧ s 2 = 0
  ensures := fun _ _ s' => s' 1 = 99 ∧ s' 2 = 1

/-- The VACUOUS contract: `requires _ := False` — 04 §5's inconsistent
contract; it admits every implementation, proving nothing. -/
def cVac : Contract Nat where
  requires := fun _ => False
  ensures := fun _ _ _ => True

/-! ## Suite 1: the wp rules, pinned -/

-- THE composition rule WITH the value (the doctrine's exact §36 shape),
-- abstract + concrete
theorem wp_bind_pin (p : Prog) (k : Nat → Prog) (Q : Nat → State → Prop) :
    wp (Prog.bind p k) Q = wp p (fun x => wp (k x) Q) := wp_bind p k Q

-- THE state-only composition rule (the value-ignoring bind)
theorem wp_seq_pin (p q : Prog) (Q : State → Prop) :
    wpS (p.seq q) Q = wpS p (wpS q Q) := wp_seq p q Q

theorem wp_seq_concrete : wpS both (fun s' => s' 1 = 1) =
    wpS incr1 (wpS incr2 (fun s' => s' 1 = 1)) := rfl

-- THE conditional rule, concrete
theorem wp_cond_pin :
    wp branchProg (fun _ s' => s' 1 = 1) =
      fun s => ((s 1 == 0) = true → wp Prog.skip (fun _ s' => s' 1 = 1) s) ∧
               ((s 1 == 0) = false →
                  wp (Prog.assign 1 (fun x => x 1 + 1)) (fun _ s' => s' 1 = 1) s) :=
  wp_cond _ _ _ _

-- monotonicity (the consequence rule's engine)
theorem mono_pin (Q Q' : Nat → State → Prop) (h : ∀ x s, Q x s → Q' x s) (s : State)
    (hs : wp incr1 Q s) : wp incr1 Q' s :=
  wp_mono incr1 Q Q' h s hs

-- THE consequence rule: strengthen the precondition, weaken the
-- postcondition — the derived triple still holds
theorem cons_pin (P P' : Nat → State → Prop) (hP : ∀ x s, P x s → P' x s)
    (hvc : ∀ x s, P' x s → wp incr1 (fun _ s' => s' 1 = 1) s)
    (s : State) (h : P 0 s) :
    wp incr1 (fun _ s' => s' 1 = 1 ∧ True) s :=
  wp_cons incr1 P P' _ _ hP (fun _ _ hq => ⟨hq, trivial⟩) hvc s h

-- THE soundness, exercised at a concrete point: the wp-computed
-- precondition is satisfied, and the execution lands in the postcondition
theorem soundness_pin : (fun _ s' => s' 1 = 1 ∧ s' 2 = 1) 0 (both.exec s0).2 :=
  wp_sound both (fun _ s' => s' 1 = 1 ∧ s' 2 = 1) s0 (by rw [wp_iff]; decide)

-- THE exactness: over the deterministic fragment the wp is the strongest
-- precondition (the iff the sampled agreement rides)
theorem exact_pin (s : State) :
    wp incr1 (fun _ s' => s' 1 = 1) s ↔ (fun _ s' => s' 1 = 1) 0 (incr1.exec s).2 :=
  wp_iff incr1 (fun _ s' => s' 1 = 1) s

/-! ## Suite 2: the contract surface + the obligations -/

-- the exit-cell computations, as the named one-step lemmas (the
-- composite's exec reads through the seq: each cell's write wins)
theorem exec_both_1 (s : State) : (both.exec s).2 1 = s 1 + 1 := by
  simp only [both, incr1, incr2, Prog.seq, Prog.exec, upd]
  simp

theorem exec_both_2 (s : State) : (both.exec s).2 2 = s 2 + 1 := by
  simp only [both, incr1, incr2, Prog.seq, Prog.exec, upd]
  simp
-- THE wp discipline's sufficiency: the VCs suffice for the satisfaction.
-- The domain-specific goal SURFACES (the toolkit hands back exactly
-- `s 1 = 0 ∧ s 2 = 0` at the exit-state computation) and is discharged
-- by the two cell lemmas + arithmetic — the review's §5 shape.
theorem cBoth_sat : cBoth.sat both := by
  apply Contract.sat_of_vc
  intro s hr
  show wp both (fun x s' => cBoth.ensures s x s') s
  rw [wp_iff]
  have hr' : s 1 = 0 ∧ s 2 = 0 := hr
  have h1 : (both.exec s).2 1 = 1 := by rw [exec_both_1]; omega
  have h2 : (both.exec s).2 2 = 1 := by rw [exec_both_2]; omega
  exact ⟨h1, h2⟩

-- THE result contract's satisfaction: the RESULT is lived-in — the
-- returned value is the old cell 1, landed in cell 2 (the bind's value
-- discipline, end to end).
theorem bind_exec (s : State) :
    bindProg.exec s = (s 1, upd 2 (fun _ => s 1) s) := by
  simp only [bindProg, rd1, Prog.exec, upd]
  simp

theorem cBind_sat : cBind.sat bindProg := by
  apply Contract.sat_of_vc
  intro s _
  show wp bindProg (fun x s' => cBind.ensures s x s') s
  rw [wp_iff, bind_exec]
  exact ⟨rfl, rfl⟩

-- the wp at the concrete entry state (the vc's content), then its
-- decidability instance — the routine-fragment route
theorem wp_both_s0 : wp both (fun _ s' => s' 1 = 1 ∧ s' 2 = 1) s0 := by
  rw [wp_iff]
  decide

theorem vcBoth_s0 : cBoth.vc both s0 := wp_both_s0

instance : Decidable (cBoth.vc both s0) := isTrue vcBoth_s0

-- the point discharge FIRES on the honest contract
theorem obl_fires : Contract.pointDischarge "vc-both@s0" `ContractsTests cBoth both s0
    = some (Kit.Evidence.decided true) := by decide

-- ... and its soundness, at the indexed strength: the verdict PROVES the
-- obligation's own claim (the VC)
theorem pointSound_pin : cBoth.vc both s0 :=
  Contract.pointDischarge_sound "vc-both@s0" `ContractsTests cBoth both s0 obl_fires

-- the satisfaction obligation (the provedAtElab route) + its discharge
-- by citation — the payload names the contract + program, the claim is
-- the type index
def satObl : Kit.Obligation (Contract Nat × Prog) (cBoth.sat both) :=
  Contract.obligation "both-sat" `ContractsTests cBoth both

def satDischarged : Kit.Discharged (Contract Nat × Prog) (cBoth.sat both) :=
  { obligation := satObl, evidence := .citedProof `ContractsTests.cBoth_sat }

-- the feasibility rows
def feasBoth : Feasibility cBoth := .witness s0 ⟨rfl, rfl⟩
def feasVac : Feasibility cVac := .declaredVacuous

-- THE vacuity tripwire (04 §5): the inconsistent contract's satisfaction
-- is PROVABLE — and proves nothing. The honest pairing carries the
-- DECLARED row; the unchecked row is the warning, never a pass.
theorem vac_pin : cVac.sat both :=
  Contract.sat_of_inconsistent cVac both (fun _ hf => hf)

def vacSat : Satisfied cVac both := ⟨vac_pin, .declaredVacuous⟩

theorem witness_checked : Feasibility.checked feasBoth = true := rfl
theorem vacuous_declared : Feasibility.checked feasVac = true := rfl
theorem unchecked_not_checked : Feasibility.checked (c := cVac) .unchecked = false := rfl

/-! ### The build-time teeth (the contract surface) -/

-- the wrong contract's VC is FALSE — proved, then the decidability
-- instance carries the refusal
theorem not_vcWrong : ¬ (cWrong.vc both s0) := by
  intro h
  have h1 : ((both.exec s0).2 1 = 99 ∧ (both.exec s0).2 2 = 1) := h
  exact absurd h1.1 (by decide)

instance : Decidable (cWrong.vc both s0) := isFalse not_vcWrong

/- THE discharge's tooth: the WRONG postcondition's obligation surfaces —
   the decide refuses, the declaration fails to elaborate, never a
   silent pass. -/
/-- error: Tactic `decide` proved that the proposition
  cWrong.vc both s0
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
theorem wrongVCTooth : cWrong.vc both s0 := by decide

/- THE mis-wire tooth: a discharge filed under the WRONG TIER (a
   `decided` evidence against a `provedAtElab` obligation) fails to
   construct — the tier mismatch is unrepresentable (Kit.Obligation's
   rule, exercised at the contract surface). -/
/-- error: could not synthesize default value for field 'tierOK' of 'Kit.Discharged' using tactics
---
error: Tactic `decide` proved that the proposition
  (Kit.Evidence.decided true).tier = satObl.tier
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
def miswiredTier : Kit.Discharged (Contract Nat × Prog) (cBoth.sat both) :=
  { obligation := satObl, evidence := .decided true }

/-! ## Suite 3: the loops — the honest while discipline, worked -/

/-- The arithmetic step: from the triangular identity at i, the
identity at i+1 (the summing loop's vBody's domain-specific content —
the VC SURFACES as this hand lemma, never hidden). -/
theorem tri_step (i acc : Nat) (h : i * (i + 1) = acc * 2) :
    (i + 1) * (i + 1 + 1) = (acc + (i + 1)) * 2 := by
  rw [Nat.mul_add, Nat.mul_one] at h
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- THE worked example: the summing loop. Cell 1 = i, cell 2 = acc,
cell 10 = n. While i < n: increment i, add the NEW i to acc. The
INVARIANT (required data): acc*2 = i*(i+1) ∧ i ≤ n — the triangular
identity, div-free. The VARIANT: n - i. -/
def sumWhile : While where
  guard := fun s => s 1 < s 10
  body := Prog.seq (Prog.assign 1 (fun s => s 1 + 1))
                   (Prog.assign 2 (fun s => s 2 + s 1))
  inv := fun s => s 1 * (s 1 + 1) = s 2 * 2 ∧ s 1 ≤ s 10
  var := fun s => s 10 - s 1

def Psum : State → Prop := fun s => s 1 = 0 ∧ s 2 = 0
def Qsum : State → Prop := fun s => s 10 * (s 10 + 1) = s 2 * 2

/-- The body's exit-state cells (the one-step exec lemmas the VCs read
through). -/
theorem sumBody_var (s : State) : (sumWhile.body.exec s).2 1 = s 1 + 1 := by
  simp [sumWhile, Prog.seq, Prog.exec, upd]

theorem sumBody_acc (s : State) : (sumWhile.body.exec s).2 2 = s 2 + s 1 + 1 := by
  simp [sumWhile, Prog.seq, Prog.exec, upd] <;> omega

theorem sumBody_n (s : State) : (sumWhile.body.exec s).2 10 = s 10 := by
  simp [sumWhile, Prog.seq, Prog.exec, upd]

-- The row is a Prop (all four fields are Props) — the defProp linter's
-- note is the point, silenced per-decl.
set_option linter.defProp false in
/-- THE loop's four verification conditions, discharged: vInit + vVar +
vExit by the arithmetic route (omega over the cell lemmas); vBody by
the SURFACED hand lemma `tri_step`. This row is the loop discipline's
whole content — the invariant and variant are data ON the carrier, and
the VCs are exactly what the toolkit demands. -/
def sumVCs : LoopVCs Psum Qsum sumWhile where
  vInit := by
    intro s h
    show s 1 * (s 1 + 1) = s 2 * 2 ∧ s 1 ≤ s 10
    rw [h.1, h.2]
    exact ⟨rfl, Nat.zero_le _⟩
  vBody := by
    intro s hg hin
    have e1 : s 1 < s 10 := by simpa [sumWhile] using hg
    have htri := tri_step (s 1) (s 2) hin.1
    show (sumWhile.body.exec s).2 1 * ((sumWhile.body.exec s).2 1 + 1)
        = (sumWhile.body.exec s).2 2 * 2
      ∧ (sumWhile.body.exec s).2 1 ≤ (sumWhile.body.exec s).2 10
    rw [sumBody_var, sumBody_acc, sumBody_n]
    exact ⟨by omega, by omega⟩
  vVar := by
    intro s hg hin
    have e1 : s 1 < s 10 := by simpa [sumWhile] using hg
    show 0 < s 10 - s 1
      ∧ s 10 - (sumWhile.body.exec s).2 1 < s 10 - s 1
    rw [sumBody_var]
    exact ⟨by omega, by omega⟩
  vExit := by
    intro s hinv hg
    have hle : ¬ s 1 < s 10 := by simpa [sumWhile] using hg
    have hle' : s 1 ≤ s 10 := hinv.2
    show s 10 * (s 10 + 1) = s 2 * 2
    have hn : s 10 = s 1 := by omega
    rw [hn]
    exact hinv.1

/-- The loop's satisfaction, ABSTRACT: the four VCs give the
postcondition at fuel `var + 1` — the weakest-HONEST precondition is
exactly the stated invariant. -/
theorem sumSatAbstract : ∀ s, Psum s → Qsum (sumWhile.run (sumWhile.var s + 1) s) :=
  while_sat Psum Qsum sumWhile sumVCs

/-- The loop's satisfaction at the witness state (the concrete pin:
fuel 6 runs the summing loop to the closed form). -/
theorem sumLoopSat :
    Qsum (sumWhile.run (sumWhile.var (stOf 0 0 5) + 1) (stOf 0 0 5)) :=
  while_sat Psum Qsum sumWhile sumVCs (stOf 0 0 5) ⟨rfl, rfl⟩

/-- The loop's satisfaction filed as the OBLIGATION (the discharge
discipline extends to loops: the claim is the type index, the tier is
the honest provedAtElab — the VCs surfaced in `sumVCs` are the
citation's content). -/
def loopObl : Kit.Obligation While
    (∀ s, Psum s → Qsum (sumWhile.run (sumWhile.var s + 1) s)) :=
  { label := "sum-loop-sat", tier := .provedAtElab
    payload := sumWhile, provenance := `ContractsTests.sumVCs }

def loopDischarged : Kit.Discharged While
    (∀ s, Psum s → Qsum (sumWhile.run (sumWhile.var s + 1) s)) :=
  { obligation := loopObl, evidence := .citedProof `ContractsTests.sumSatAbstract }

/-- The loop's DECIDABLE point check through the kit's backend: the
invariant at the witness state decides TRUE, and the point discharge
fires on it (the VCs' decidable rows ride the same kit face as the
contract surface's). -/
instance : Decidable (sumWhile.inv (stOf 0 0 5)) :=
  isTrue (by
    show (stOf 0 0 5) 1 * ((stOf 0 0 5) 1 + 1) = (stOf 0 0 5) 2 * 2
      ∧ (stOf 0 0 5) 1 ≤ (stOf 0 0 5) 10
    have h1 : (stOf 0 0 5) 1 = 0 := rfl
    have h2 : (stOf 0 0 5) 2 = 0 := rfl
    rw [h1, h2]
    exact ⟨rfl, Nat.zero_le _⟩)

def loopInvObl : Kit.Obligation (While × State) (sumWhile.inv (stOf 0 0 5)) :=
  { label := "sum-inv@witness", tier := .decidableNow
    payload := (sumWhile, stOf 0 0 5), provenance := `ContractsTests.sumVCs }

theorem loopInvFires :
    loopInvObl.decideDischarge = some (Kit.Evidence.decided true) := by decide

/-! ### The loop teeth — the wrong invariant / wrong variant REFUSE -/

/-- The WRONG invariant: `acc = i` (not the triangular identity). Its
body-preservation VC is FALSE — refuted at i = 1, acc = 1, n = 2. -/
def wWrong : While := { sumWhile with inv := fun s => s 2 = s 1 }

/-- The body-preservation VC for the wrong invariant — the LoopVCs
field that CANNOT be built. -/
def vBodyWrong : Prop :=
  ∀ s, wWrong.guard s = true → wWrong.inv s →
    wp wWrong.body (fun _ s' => wWrong.inv s') s

theorem not_vBodyWrong : ¬ vBodyWrong := by
  intro h
  have hg : wWrong.guard (stOf 1 1 2) = true := by decide
  have hi : wWrong.inv (stOf 1 1 2) := by
    show (stOf 1 1 2) 2 = (stOf 1 1 2) 1
    rfl
  have h1 := h (stOf 1 1 2) hg hi
  have e2 : ((wWrong.body.exec (stOf 1 1 2)).2) 2 = 3 := by
    show (upd 2 (fun t => t 2 + t 1) (upd 1 (fun t => t 1 + 1) (stOf 1 1 2))) 2 = 3
    simp [upd, stOf]
  have e1 : ((wWrong.body.exec (stOf 1 1 2)).2) 1 = 2 := by
    show (upd 2 (fun t => t 2 + t 1) (upd 1 (fun t => t 1 + 1) (stOf 1 1 2))) 1 = 2
    simp [upd, stOf]
  have h2 : ((wWrong.body.exec (stOf 1 1 2)).2) 2
      = ((wWrong.body.exec (stOf 1 1 2)).2) 1 := h1
  omega

/-- The wrong invariant's LoopVCs CANNOT be constructed — the structure
refuses (the invariant is required data, and a wrong one is refuted,
never repaired). -/
theorem wrongLoopNoVCs : LoopVCs Psum Qsum wWrong → False :=
  fun h => not_vBodyWrong h.vBody

instance : Decidable vBodyWrong := isFalse not_vBodyWrong

/- THE loop's tooth: the WRONG INVARIANT's VC refuses to discharge —
   the decide refuses, the declaration fails to elaborate, never a
   silent pass (the invariant is REQUIRED, never inferred). -/
/-- error: Tactic `decide` proved that the proposition
  vBodyWrong
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
theorem wrongInvariantTooth : vBodyWrong := by decide

/-- The WRONG variant: constant 5 — not strictly decreasing. Its
variant VC is FALSE (5 < 5 refutes). The carrier is the wrong-VARIANT
carrier (the invariant is the honest one there — only the variant is
sabotaged). -/
def wWrongVar : While := { sumWhile with var := fun _ => 5 }

def vVarWrong : Prop :=
  ∀ s, wWrongVar.guard s = true → wWrongVar.inv s →
    0 < wWrongVar.var s ∧ wWrongVar.var ((wWrongVar.body.exec s).2) < wWrongVar.var s

theorem not_vVarWrong : ¬ vVarWrong := by
  intro h
  have hg : wWrongVar.guard (stOf 1 1 2) = true := by decide
  have hi : wWrongVar.inv (stOf 1 1 2) := by
    show (stOf 1 1 2) 1 * ((stOf 1 1 2) 1 + 1) = (stOf 1 1 2) 2 * 2
      ∧ (stOf 1 1 2) 1 ≤ (stOf 1 1 2) 10
    exact ⟨rfl, by decide⟩
  have h1 := h (stOf 1 1 2) hg hi
  simp only [wWrongVar] at h1
  omega

instance : Decidable vVarWrong := isFalse not_vVarWrong

/- THE loop's second tooth: the WRONG VARIANT's VC refuses — the
   termination certificate is required data too; a non-decreasing
   variant discharges nothing. -/
/-- error: Tactic `decide` proved that the proposition
  vVarWrong
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
theorem wrongVariantTooth : vVarWrong := by decide

/-! ## Suite 4: the LCG-seeded sweeps + the mandatory negative controls -/

/-- The fragment's exec + branch, swept over drawn states; the exec side
of the exactness iff checked at each draw. -/
def propExec (t : Tape) : CheckResult := do
  let (a, t1) := t.below 6
  let (b, t2) := t1.below 6
  let (c, _) := t2.below 6
  let s := stOf a b c
  assert ((both.exec s).2 1 == a + 1) "the seq exec broke at cell 1"
  assert ((both.exec s).2 2 == b + 1) "the seq exec broke at cell 2"
  assert ((both.exec s).2 3 == c) "the seq clobbered the outside cell"
  assert ((branchProg.exec s).2 1 == if a == 0 then a else a + 1)
    "the branch exec broke"
  assert (decide ((fun _ s' => s' 1 = a + 1 ∧ s' 2 = b + 1) 0 (both.exec s).2))
    "the exec side of the exactness iff broke"

/-- The bind's value discipline, swept: the result is the OLD cell 1,
landed in cell 2 — the exec side of the result contract, at each draw. -/
def propBind (t : Tape) : CheckResult := do
  let (a, _) := t.below 6
  let s := stOf a 0 0
  assert ((bindProg.exec s).1 == a) "the bind's result broke"
  assert ((bindProg.exec s).2 2 == a) "the bind's write broke"
  assert ((bindProg.exec (stOf a 5 5)).1 == a)
    "the bind's result ignores the outside cells"

/-- The point discharge's decidability at the drawn admissible states:
the honest contract's exit cells are COMPUTED (1 and 1) whatever the
outside cells hold — the witness is the proof, the instance is honest. -/
instance instVCst (v : Nat) : Decidable (cBoth.vc both (stOf 0 0 v)) :=
  isTrue (by
    show wp both (fun x s' => cBoth.ensures (stOf 0 0 v) x s') (stOf 0 0 v)
    rw [wp_iff]
    show (both.exec (stOf 0 0 v)).2 1 = 1 ∧ (both.exec (stOf 0 0 v)).2 2 = 1
    simp only [both, incr1, incr2, Prog.seq, Prog.exec, upd]
    simp
    exact ⟨rfl, rfl⟩)

/-- The discharge + the feasibility rows, swept. -/
def propDischarge (t : Tape) : CheckResult := do
  let (v, _) := t.below 6
  -- the honest contract's point discharge fires at the admissible
  -- state, whatever the outside cells hold
  assert (Contract.pointDischarge "vc" `ContractsTests cBoth both (stOf 0 0 v)
      == some (Kit.Evidence.decided true))
    "the point discharge broke"
  -- admissibility witnessed at a drawn state (the witness row checks)
  let row : Feasibility cBoth := .witness (stOf 0 0 v) ⟨rfl, rfl⟩
  assert (Feasibility.checked row) "the witness row must report checked"

/-- The summing loop's run, swept over n: the fuel is the variant + 1,
and the closed form lands (the loop discipline's exec side, at each
draw). -/
def propLoop (t : Tape) : CheckResult := do
  let (n, _) := t.below 5
  let s := stOf 0 0 (n + 1)
  -- the variant + 1 fuel reaches the closed form
  assert ((sumWhile.run (n + 1 + 1) s) 1 == n + 1)
    "the summing loop's counter broke"
  assert ((sumWhile.run (n + 1 + 1) s) 2 * 2 == (n + 1) * (n + 1 + 1))
    "the summing loop's accumulator broke"
  -- the run is fuel-honest: fuel exactly the variant runs the loop to
  -- the exit (the counter lands at n + 1, the guard's boundary)
  assert ((sumWhile.run (n + 1) s) 1 == n + 1)
    "the summing loop's fuel sensitivity broke"

/- The EXEC-LEAK sabotage: claims the seq clobbers the outside cell —
   caught (the fragment's writes are footprint-local). -/
def negExecLeak (_t : Tape) : CheckResult :=
  assert ((both.exec (stOf 0 0 0)).2 3 == 999)
    "the exec-leak sabotage was not caught"

/- The TOO-STRONG-WP sabotage: claims the wp of the assignment is the
   identity (treats assign as skip) — caught: at cell 1 = 0 the
   identity-wp is false but the true wp is true (the exactness iff,
   sampled). -/
def negWpTooStrong (_t : Tape) : CheckResult :=
  assert (decide ((fun _ s' => s' 1 = 1) 0 (stOf 0 0 0))
      == decide ((fun _ s' => s' 1 = 1) 0 (incr1.exec (stOf 0 0 0)).2))
    "the too-strong-wp sabotage was not caught"

/- The FABRICATED-DISCHARGE sabotage: claims the wrong contract's point
   discharge fires — caught: the backend refuses (none), never
   fabricates evidence. -/
def negFabricatedDischarge (_t : Tape) : CheckResult :=
  assert ((Contract.pointDischarge "wrong" `ContractsTests cWrong both s0).isSome)
    "the fabricated-discharge sabotage was not caught"

/- The SILENT-VACUITY sabotage: claims the unchecked feasibility row
   passes the report — caught: unchecked is the warning, never a pass
   (04 §5). -/
def negSilentVacuity (_t : Tape) : CheckResult :=
  assert (Feasibility.checked (c := cVac) Feasibility.unchecked)
    "the silent-vacuity sabotage was not caught"

/- The WRONG-INVARIANT sabotage: claims the wrong invariant's
   body-preservation VC discharges — caught: it is false at the
   refuting state (i = 1, acc = 1, n = 2); the instance is the PROVED
   refusal. -/
def negWrongInvariant (_t : Tape) : CheckResult :=
  assert (decide vBodyWrong) "the wrong-invariant sabotage was not caught"

/- The WRONG-VARIANT sabotage: claims the constant variant's VC
   discharges — caught: 5 < 5 is false; the instance is the PROVED
   refusal. -/
def negWrongVariant (_t : Tape) : CheckResult :=
  assert (decide vVarWrong) "the wrong-variant sabotage was not caught"

/- The TOO-SMALL-FUEL sabotage: claims fuel below the variant + 1
   reaches the closed form — caught at the witness state: run 0 is the
   entry state, and the post does not hold there (the variant's fuel
   bound is load-bearing, not decorative). -/
theorem not_Qsum_run0 : ¬ Qsum (sumWhile.run 0 (stOf 0 0 5)) := by
  intro hq
  simp [Qsum, While.run, stOf] at hq

instance : Decidable (Qsum (sumWhile.run 0 (stOf 0 0 5))) := isFalse not_Qsum_run0

def negTooSmallFuel (_t : Tape) : CheckResult :=
  assert (decide (Qsum (sumWhile.run 0 (stOf 0 0 5))))
    "the too-small-fuel sabotage was not caught"

def specWp : Spec := Spec.ofList "contracts-wp"
  propExec
  [ ("exec-leak", negExecLeak), ("too-strong-wp", negWpTooStrong) ]
  12 20250903

def specSurface : Spec := Spec.ofList "contracts-surface"
  propDischarge
  [ ("fabricated-discharge", negFabricatedDischarge),
    ("silent-vacuity", negSilentVacuity) ]
  12 20250904

def specBind : Spec := Spec.ofList "contracts-bind"
  propBind
  [ ("bind-result-leak", negTooSmallFuel),
    ("exec-leak", negExecLeak) ]
  12 20250905

def specLoop : Spec := Spec.ofList "contracts-loop"
  propLoop
  [ ("wrong-invariant", negWrongInvariant),
    ("wrong-variant", negWrongVariant),
    ("too-small-fuel", negTooSmallFuel) ]
  12 20250906

end ContractsTests

def main : IO UInt32 := TestingKit.mainOfSuites
  [("Contracts", [ContractsTests.specWp, ContractsTests.specSurface,
                  ContractsTests.specBind, ContractsTests.specLoop])]
