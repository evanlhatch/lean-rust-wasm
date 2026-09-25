/-
# Faults.Registry — the fault lane's registration (the Kit.Lane mount)

The `@[fault]` attribute: a `def` of `FaultItem` registered into the lane's
append-only env extension (the compile-time event log, 15-patterns #7) —
Kit.Lane's `register_lane` mechanizes the lane recipe's steps 1–2 (notes/v3/
12-construction.md §2). This file is the REGISTRATION module; the
consumption (the `@[fault]` entries, the replay pins, the curated-failure
controls) lives in the NEXT modules — a module's own initializers do not run
during its own elaboration (the KitTests.LaneReg → LaneDemo fixture's
discipline).

Generated names (the base is the `attr :=` clause's):
`faultLaneId` (the lane's identity — data in the ONE log
`Kit.Lane.laneLogExt`), `@[fault]`, `getFaults` (the routed replay
reader), `faultRegistry`, `faultNameOf`, `faultObligationView`,
`faultLedgerDemand`, `faultAttrReg`.

Provenance: mined from `legacy/lean/faults/Faults/Registry.lean` (the
registry's registration discipline — one extension, append on add, the
duplicate-name elaboration refusal) — the guest/host extension SPLIT
deliberately NOT ported (the honest minimal: ONE registry; the split returns
with the guest's wire-variant fold, the legacy's W10.1 consumer). The
legacy's category-drift refusal (`.unsupported`) died with the ctor
(Faults.Item's named exclusion).

Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Lane
import Faults.Item

-- THE MOUNT: the `@[fault]` lane over the lane substrate — entries are
-- `def`s of `FaultItem`, the value evaluated at elaboration, the replay
-- order the registration order, a duplicate name the closed-world refusal
-- (KL0001, decided at the mount).
register_lane Faults.FaultItem where
  naming := fun it => it.name
  attr := fault
