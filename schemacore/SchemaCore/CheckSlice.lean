/-
# SchemaCore.CheckSlice — the check lane's registered fixture

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).

The check lane's end-to-end fixture: the `@[check]` entries append to
the ONE log at elaboration (the default builder — a `def` of the item
type, the value evaluated at elaboration); the replay/legality teeth
are `#eval` pins (a drift FAILS the build); the curated failures are
the `#guard_msgs` negative controls. A module's own initializers do
not run during ITS OWN elaboration, so the mount (SchemaCore.Check)
and the entries (this module) are different modules — the KitTests
LaneReg → LaneDemo discipline.

Provenance: fresh (the fixture IS the lane's first consumer; no
legacy content). The RUNTIME suite's value-level tests ride these
same defs (SchemaTests' checkSpec) — registration is this file, the
tests consume the exported values.

The five questions: root = the check lane's fixture content; carrier =
the CheckItem rows over the Example item; spine reading = the event
log's entries; ladder rung = the teeth are `#eval`/`#guard_msgs`
(elaboration-time); gate row = SchemaTests' checkSpec + the axiom
report.

Core-only.
-/

import SchemaCore.Slice
import SchemaCore.Check

open SchemaCore

/-! ## The fixture rows' carrier -/

/-- The Example item's field list (the fixtures' snapshot — the same
    fields the registered Example carries; the legality teeth pin the
    snapshot against the LIVE registry below). -/
abbrev exampleCheckFields : List Field :=
  [ { name := "ready", ty := .bool }
  , { name := "count", ty := .u64 }
  , { name := "delta", ty := .i64 }
  , { name := "label", ty := .string }
  , { name := "note", ty := .option .string }
  , { name := "tags", ty := .list .string } ]

/-! ## The registered invariants -/

/-- PASSING fixture: Example's count is positive. -/
@[check]
def exampleCountPositive : CheckItem :=
  { name := "example-count-positive"
    schemaRef := "Example"
    fields := exampleCheckFields
    pred := .u64GtLit "count" 0 }

/-- VIOLATED fixture: Example's count is zero (sabotaged sibling —
    real data violates it; its obligation row must show the loud gap +
    the violating rows). -/
@[check]
def exampleCountZero : CheckItem :=
  { name := "example-count-zero"
    schemaRef := "Example"
    fields := exampleCheckFields
    pred := .u64EqLit "count" 0 }

/-! ## The fixture tables (the runtime tests' data) -/

/-- A good table: count = 3 — the passing invariant's discharge fires,
    the violated one shows the loud gap. -/
def goodRow : RowVals exampleCheckFields :=
  .cons (.bool true) (.cons (.u64 3) (.cons (.i64 0)
    (.cons (.string "a") (.cons .none (.cons (.list .nil) .nil)))))

def goodRows : List (RowVals exampleCheckFields) := [goodRow]

/-- The mixed table's violating row: count = 0 — violates BOTH
    fixtures; the violating rows come back AS DATA. -/
def badRow : RowVals exampleCheckFields :=
  .cons (.bool false) (.cons (.u64 0) (.cons (.i64 1)
    (.cons (.string "b") (.cons (.some (.string "n"))
      (.cons (.list (.cons (.string "t") .nil)) .nil)))))

def mixedRows : List (RowVals exampleCheckFields) := [goodRow, badRow]

/-! ## The build-time teeth (the registration + the legality) -/

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  -- the replay: two entries, registration order (the routed fold over
  -- the ONE log — wave-30 A2)
  match ← getChecks env with
  | .error e => throwError s!"check lane replay refused: {e}"
  | .ok checks =>
    unless checks.length == 2
        && checks[0]!.name == "example-count-positive"
        && checks[1]!.name == "example-count-zero" do
      throwError s!"check lane replay drifted: {checks.map (·.name)}"
    -- the fold hook: the registry materializes (nodup decided)
    match ← checkRegistry env with
    | .error e => throwError s!"check lane fold drifted: {e}"
    | .ok reg =>
        unless reg.items.length == 2 do
          throwError "check lane registry drifted: wrong item count"
    -- the legality teeth: BOTH fixtures are well-scoped against the
    -- LIVE universe (the target resolves; the snapshot is not stale;
    -- every read field is on the record)
    match ← getSchemas env with
    | .error e => throwError s!"check lane legality: the universe replay \
      refused: {e}"
    | .ok items =>
      for c in checks do
        unless (c.scopedDiags items).isEmpty do
          throwError s!"check lane legality drifted for `{c.name}`: \
            {c.scopedDiags items}"
    -- the obligation view: both rows compute decidableNow (the claim
    -- index needs no table for the tier's read — `[]` names the type,
    -- the claim's content is not read here)
    unless checks.all (fun c => (c.obligation []).tier == .decidableNow) do
      throwError "check lane obligation tier drifted"

/- NEGATIVE CONTROLS, as the ONE teeth shape (Kit.Lane's lane-teeth
    macros — the audit's E3): the control commands are taken VERBATIM
    (the #guard_msgs shape); the expected refusals are computed from
    the mount's OWN Diag constructors (a message or valid-space drift
    fails the build); the dup tooth ALSO pins its valid-list against
    the live registration state. -/
lane_dup_tooth "example-count-positive" ["example-count-positive", "example-count-zero"] in
  @[check] def dupCheck : CheckItem :=
    { name := "example-count-positive"
      schemaRef := "Example"
      fields := exampleCheckFields
      pred := .lit true }

lane_wrong_tooth SchemaCore.CheckItem in
  @[check] def wrongCheck : Nat := 5
