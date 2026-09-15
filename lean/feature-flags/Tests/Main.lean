/-
# FeatureFlags tests — the gate files' driver

The dogfood service's gate floor: positive + negative controls over the
impl, elaboration-checked (`#guard` fails the BUILD on drift, not just
the run). The TestKit discipline (PropSpec sweeps with the MANDATORY
negative control, DiffSpec for differential gates) grows in here as the
service does.
-/
import Lean
import TestKit
import FeatureFlags
import FeatureFlagsFn
import Tests.Stress



-- Negative control first: the sentinel id → none.
#guard (FeatureFlagsImpl.flag_get 0).isNone

-- Positive control: a real id → some (the record round-trips).
#guard (FeatureFlagsImpl.flag_get 3).map (·.id) == some 3

-- The rollout gate: > 100 = invalidRollout (the domain error, on the
-- result channel's LEFT-ridden... the error half: `inr`).
#guard (match FeatureFlagsImpl.flag_set_rollout 3 150 with | .inr _ => true | _ => false)
#guard ((match FeatureFlagsImpl.flag_set_rollout 3 150 with | .inl _ => true | _ => false) == false)

-- The sentinel refuses the rollout set too.
#guard (match FeatureFlagsImpl.flag_set_rollout 0 50 with | .inr _ => true | _ => false)

-- The in-range set: locked-store v1 (the honest stub — the error says so).
#guard match FeatureFlagsImpl.flag_set_rollout 3 50 with
  | .inr (FlagError.locked _) => true
  | _ => false

-- The delete: the audit entry back (the action spelled).
#guard match FeatureFlagsImpl.flag_delete 7 with
  | .inl e => e.action == "delete" && e.id == 7
  | _ => false

-- The watch: the empty key = the empty stream.
#guard (FeatureFlagsImpl.flag_watch "").isEmpty
#guard (FeatureFlagsImpl.flag_watch "checkout").map (·.key) == ["checkout"]

def main : IO UInt32 := do
  IO.println "FeatureFlagsTests: guards green (elab-time)"
  match stressChecks with
  | .ok () =>
      IO.println "FeatureFlagsTests: stress sweep green (50-tick LCG + negative control)"
      return 0
  | .error e =>
      IO.eprintln s!"FeatureFlagsTests: stress FAIL: {e}"
      return 1
