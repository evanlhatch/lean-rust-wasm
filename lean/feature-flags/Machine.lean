/-
# FeatureFlags Machine — the flag lifecycle (the machine! preset row)

The service's lifecycle discipline, modeled as a Machines machine (the
OrderMachine precedent — the SECOND service's machine, proving the
pattern transfers). States: draft (created, not serving), enabled,
disabled, retired. `stale` = the state no transition produces (the
invariant's non-vacuity witness).

Two projections per Machines.Core: executable (`flagLifecycle.step?` /
`.run`) + proved (`flagLifecycle.tr` + the theorems below).

THE LIFECYCLE'S LAW (what the spec promises): a RETIRED flag can never
serve again — only `reset` (the recovery edge) leaves `retired`. The
re-enable edge exists ONLY from `disabled` (a retired flag's key is
spent; re-enabling it would alias the audit trail — the domain reason
the edge is absent, and the theorem makes its absence permanent).

Deliberate exclusion: no effectful transition payloads (Machines v1 has
no output channel); the data effects ride the schema funcs
(`flag_set_rollout` et al).
-/

import Machines.Dsl
import Machines.Testing
import Machines.Testing

open Machines.Dsl

namespace FeatureFlags

/-! ## The lifecycle -/

inductive FlagState where
  | draft | enabled | disabled | retired | stale
deriving Repr, BEq, DecidableEq, Inhabited

-- (plain comment: doc comments cannot precede machine!)
machine! flagLifecycle where
  State: FlagState
  Inv: fun s => s ≠ .stale
  event: enable guard: (fun s => s = .draft || s = .disabled) action: (fun _ _ => .enabled)
  event: disable guard: (fun s => s = .enabled) action: (fun _ _ => .disabled)
  event: retire guard: (fun s => s = .draft || s = .disabled) action: (fun _ _ => .retired)
  event: reset guard: (fun _ => true) action: (fun _ _ => .draft)

instance : DecidablePred flagLifecycle.Inv := fun s =>
  match s with
  | .stale => isFalse (fun h => h rfl)
  | .draft => isTrue (fun h => FlagState.noConfusion h)
  | .enabled => isTrue (fun h => FlagState.noConfusion h)
  | .disabled => isTrue (fun h => FlagState.noConfusion h)
  | .retired => isTrue (fun h => FlagState.noConfusion h)

/-- The battery state space (stale included — the non-vacuity target). -/
def flagStates : List FlagState :=
  [.draft, .enabled, .disabled, .retired, .stale]

/-- The conformance battery: deadlock-freedom (reset always enabled),
    guard coverage, invariant non-vacuity. -/
def flagConformance : List (String × TestKit.CheckResult) :=
  Machines.Testing.conformance flagLifecycle flagLifecycle.labels flagStates
    flagLifecycle.labels_complete

/-! ## The proved discipline -/

/-- The lifecycle rank: draft 0 → enabled 1 → disabled 2 → retired 3;
    stale rides at 0 (unreachable). -/
def FlagState.rank : FlagState → Nat
  | .draft => 0 | .enabled => 1 | .disabled => 2
  | .retired => 3 | .stale => 0

/-- The lifecycle's MONOTONICITY (the honest statement — the dogfood
    corrected the first draft): the lifecycle is NOT a DAG — the
    re-enable edge (disabled → enabled) DECREASES rank; the
    enable/disable pair is the domain's one CYCLE, and the tick's
    fixpoint machinery (Dbsp.Recursive, fuel-bounded) is what makes a
    cycle legal. What IS monotone: retirement — `retire` strictly
    increases the rank from every state that allows it, and `retired`
    is terminal (below). The acyclic-DAG claim of the order lifecycle
    does not transfer; this is the dogfood's finding, not a weakening
    of a proved statement (the order machine keeps ITS theorem — its
    lifecycle genuinely has no down-grades). -/
theorem retire_advances (s : FlagState) (l : flagLifecycle.Label)
    (hnr : l ≠ .reset) (w : (flagLifecycle.event l).guard s = true)
    (hl : l = .retire) :
    s.rank < ((flagLifecycle.event l).action s w).rank := by
  subst hl
  cases s <;>
    simp [flagLifecycle, flagLifecycle.spec, FlagState.rank] at w ⊢ <;>
    omega

/-- Retired is terminal: only `reset` leaves it. A retired flag can
    never serve again — THE spec promise. -/
theorem retired_never_serves (s s' : FlagState) (l : flagLifecycle.Label)
    (htr : flagLifecycle.tr s l s') (hd : s = .retired) : l = .reset := by
  subst hd
  obtain ⟨w, hw⟩ := htr
  cases l <;> simp [flagLifecycle, flagLifecycle.spec] at w ⊢

/-- The executable shadow: every non-reset event is `none` at retired. -/
theorem retired_step_none (l : flagLifecycle.Label)
    (hnr : l ≠ .reset) : flagLifecycle.step? .retired l = none := by
  cases l <;> simp [flagLifecycle, flagLifecycle.spec] at hnr ⊢

/-- The happy path EXECUTES: create, enable, disable, retire. -/
theorem lifecycle_happy : flagLifecycle.run .draft
    [.enable, .disable, .retire]
    = some ([(.enable, .enabled), (.disable, .disabled), (.retire, .retired)], .retired) :=
  rfl

/-- Out-of-order firing is REJECTED (retire before any state = fine
    from draft, but enable-after-retire is not). -/
theorem lifecycle_reject_reenable : flagLifecycle.run .draft
    [.enable, .disable, .retire, .enable] = none := rfl

/-! ## The emitted table (the driver's data — the matchArms discipline) -/

def flagTrans : List (flagLifecycle.Label × FlagState × FlagState) :=
  [ (.enable, .draft, .enabled)
  , (.enable, .disabled, .enabled)
  , (.disable, .enabled, .disabled)
  , (.retire, .draft, .retired)
  , (.retire, .disabled, .retired)
  , (.reset, .draft, .draft)
  , (.reset, .enabled, .draft)
  , (.reset, .disabled, .draft)
  , (.reset, .retired, .draft)
  , (.reset, .stale, .draft) ]

/-- The structural reading (the emission theorem's subject). -/
def flagTableStep? : flagLifecycle.Label → FlagState → Option FlagState
  | .enable, .draft => some .enabled
  | .enable, .disabled => some .enabled
  | .disable, .enabled => some .disabled
  | .retire, .draft => some .retired
  | .retire, .disabled => some .retired
  | .reset, _ => some .draft
  | _, _ => none

/-- The emitted table IS the machine. -/
theorem flagTableStep?_eq_step? (e : flagLifecycle.Label) (s : FlagState) :
    flagTableStep? e s = flagLifecycle.step? s e := by
  cases s <;> cases e <;> simp [flagTableStep?, flagLifecycle, flagLifecycle.spec]

end FeatureFlags
