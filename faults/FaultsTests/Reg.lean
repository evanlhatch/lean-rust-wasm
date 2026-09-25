/-
# FaultsTests.Reg — the fault lane's consumption module (the build-time pins)

The lane substrate's end-to-end fixture discipline (KitTests.LaneDemo's
shape), at the faults lane: the `@[fault]` entries of `Faults.Spec` replayed
through import; the replay accessor + the fold hook read the live
environment (the `#eval` pins — a drift FAILS THE BUILD); the curated
failures are the `#guard_msgs` negative controls (a message drift FAILS THE
BUILD).

Provenance: fresh (the lane's fixture). Evidence, not architecture — the
five-question block lives in the modules under test.
-/

import Faults.Spec

-- The end-to-end pin: four faults registered, replayed in registration
-- order, materialized into the registry (the fold hook fires).
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  match ← faultRegistry env with
  | .error e => Lean.throwError s!"fault lane fold drifted: {e}"
  | .ok reg =>
    match ← getFaults env with
    | .error e => Lean.throwError s!"fault lane replay refused: {e}"
    | .ok faults =>
      let names := reg.items.map (·.name)
      if names == ["content_hash_mismatch", "journal_corrupt",
                   "lifecycle_illegal_transition", "wasm_trap"]
          && faults.length == 4 then
        pure ()
      else
        Lean.throwError s!"fault lane replay drifted: {names}"

-- THE ENTOURAGE HOOKS (16-surface §3 at the lane face): the registration
-- auto-filled the obligation view + the ledger demand (the lane's own
-- extension as the read collection). A drift FAILS THE BUILD.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let d := faultLedgerDemand env
  if faultObligationView env == ["content_hash_mismatch", "journal_corrupt",
      "lifecycle_illegal_transition", "wasm_trap"]
      && d.collections == [Kit.Ledger.namesOf "Kit.Lane.laneLogExt"]
      && d.rows == [Kit.Ledger.namesOf "content_hash_mismatch",
                    Kit.Ledger.namesOf "journal_corrupt",
                    Kit.Ledger.namesOf "lifecycle_illegal_transition",
                    Kit.Ledger.namesOf "wasm_trap"]
      && d.emitterRev == "register_lane" then
    pure ()
  else
    Lean.throwError "fault lane entourage hooks drifted: the obligation view \
      or the ledger demand did not auto-fill"

/- NEGATIVE CONTROLS, as the ONE teeth shape (Kit.Lane's lane-teeth
    macros — the audit's E3): the control commands are taken VERBATIM
    (the #guard_msgs shape); the expected refusals are computed from
    the mount's OWN Diag constructors (a message or valid-space drift
    fails the build); the dup tooth ALSO pins its valid-list against
    the live registration state. -/
lane_dup_tooth "wasm_trap" ["content_hash_mismatch", "journal_corrupt", "lifecycle_illegal_transition", "wasm_trap"] in
  @[fault] def dupFault : Faults.FaultItem :=
    { name := "wasm_trap"
      display := "duplicate — must refuse"
      category := .fatal
      advice := "no"
      payload := [] }

lane_wrong_tooth Faults.FaultItem in
  @[fault] def wrongFault : Nat := 5
