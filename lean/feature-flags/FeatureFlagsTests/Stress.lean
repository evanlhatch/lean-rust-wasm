/-
# FeatureFlags stress — the Scenario machinery over the FLAG updates

The stress lane: `SchemaLang.Trace`'s Scenario oracle (runScenario /
conforms / diverge) driven over the DOGFOOD schema's updates — the
`rolloutClamp` + `keyEcho` registrations' hand mirrors (the schema-lang
Tests discipline: the runtime pins evaluate the MIRRORS) — with a
50-tick deterministic LCG sweep and the corrupted-final negative
control (conforms must reject + diverge must name the final tick).

Ownership: this module owns the flags-lane stress sweep. The mirror
updates deliberately re-derive from `FeatureFlags`' registrations
NOWHERE — they are hand data (the registry replay needs the
interpreter; the mirrors are the value-level discipline). Negative
controls MANDATORY (TestKit.PropSpec rule, elevated to the tick level).
-/
import SchemaLang.Trace
import TestKit

open SchemaLang TestKit

/-! ## The Flag schema, as the scenario lane sees it -/

/-- The Flag fields (abbrev — the reducibility rule; the HasCol
    instance search walks THIS list). -/
abbrev flagFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"key", .string⟩, ⟨"enabled", .bool⟩
  , ⟨"rollout", .u64⟩, ⟨"tags", .list .string⟩ ]

/-- The row builder: one `RowVals` over `flagFields` (schema order). -/
def flagRow (id : UInt64) (key : String) (enabled : Bool)
    (rollout : UInt64) (tags : List String) : RowVals flagFields :=
  .cons (.u64 id) (.cons (.string key) (.cons (.bool enabled)
    (.cons (.u64 rollout) (.cons (.list (vstrs tags)) .nil))))
where
  /-- The guest string list: `List String` → the closed `VList`. -/
  vstrs : List String → VList .string
    | [] => .nil
    | s :: rest => .cons (.string s) (vstrs rest)

/-- The row's rollout (the raw reading — no hand path). -/
def flagRollout (row : RowVals flagFields) : UInt64 :=
  evalU (.colOf "rollout") row

/-- The row's key (the boxed reading — no hand path). -/
def flagKey (row : RowVals flagFields) : String :=
  match evalV (.colOf "key") row with | .string s => s | _ => ""

/-! ## The registered updates' hand mirrors -/

/-- The rollout clamp (the `rolloutClamp` mirror): any row over 100
    lands at exactly 100 — the guard reads the ORIGINAL row. -/
def flagClamp : UpdateItem flagFields ⟨"rollout", .u64⟩ :=
  { name := "rollout-clamp", guard := .gt (.colOf "rollout") (.lit 100)
  , value := .lit 100, writePath := .there (.there (.there .here)) }

/-- The key echo (the `keyEcho` mirror): a self-reading write on the
    key column — the nonlinear row (the journal carries S0). -/
def flagKeyEcho : UpdateItem flagFields ⟨"key", .string⟩ :=
  { name := "key-echo", guard := .gt (.strlen (.colOf "key")) (.lit 0)
  , value := .colOf "key", writePath := .there .here }

/-! ## The 50-tick deterministic sweep (LCG — no Plausible dependency) -/

/-- `n` update batches from seed `s`: per tick, the LCG's residue mod 3
    chooses the batch shape (clamp-only / clamp+echo / echo-only — the
    sweep exercises guarded-fire, the boundary row, and the echo). -/
def flagBatches : Nat → UInt64 → List (List SomeUpdate)
  | 0, _ => []
  | n + 1, s =>
      let s1 := TestKit.lcg s
      let s2 := TestKit.lcg s1
      let suClamp : SomeUpdate :=
        { fields := flagFields, field := ⟨"rollout", .u64⟩
        , update := flagClamp }
      let suEcho : SomeUpdate :=
        { fields := flagFields, field := ⟨"key", .string⟩
        , update := flagKeyEcho }
      let batch :=
        match s1 % 3 with
        | 0 => [suClamp]
        | 1 => [suClamp, suEcho]
        | _ => [suEcho]
      batch :: flagBatches n s2

/-- The scenario: 3 flags (one over-clamped, one EMPTY key — the
    key-nonempty refusal case, one at the rollout boundary). -/
def flagScenario : Scenario :=
  { fields := flagFields
  , init :=
      [ flagRow 1 "alpha" true 150 ["a"]
      , flagRow 2 "" false 50 []
      , flagRow 3 "beta" true 100 ["b", "c"] ]
  , ticks := flagBatches 50 42 }

/-! ## The checks -/

/-- The stress verdict: the oracle's shape, the sweep's conformance,
    the clamp invariant over EVERY final row, and the corrupted-final
    negative control (conforms rejects + diverge LOCALIZES to tick 50). -/
def stressChecks : TestKit.CheckResult := do
  let oracle := runScenario flagScenario
  let corrupted : List (RowVals flagFields) :=
    [ flagRow 1 "alpha" true 42 ["a"]
    , flagRow 2 "" false 50 []
    , flagRow 3 "beta" true 999 ["b", "c"] ]
  _ ← assertEq "stress: 50 ticks + init = 51 states" oracle.length 51
  _ ← assertEq "stress: oracle output conforms"
    (flagScenario.conforms oracle.getLast!) true
  -- order-independence (the TableEq law, executed on the sweep's end state)
  _ ← assert (flagScenario.conforms oracle.getLast!.reverse)
    "stress: conformance is order-independent"
  -- THE CLAMP: no tick can leave a row over 100 (the guard reads the
  -- original row; the write pins 100)
  _ ← assert (oracle.getLast!.all (fun r => flagRollout r ≤ 100))
    s!"stress: clamp invariant holds on every final row (final rollouts: {oracle.getLast!.map flagRollout})"
  -- non-vacuity: the sweep must have FIRED the clamp — the ONLY update
  -- that changes rollouts is the clamp, so a changed rollout column =
  -- the guard fired somewhere (the vacuous-sweep control)
  _ ← assert ((flagScenario.finalState.map flagRollout) ≠
      (flagScenario.init.map flagRollout))
    "stress: the sweep actually fired (rollout column changed)"
  -- NEGATIVE CONTROL: the corrupted final (rollout 999 — no tick can
  -- produce it, the clamp pins ≤ 100) must REJECT...
  _ ← assertEq "stress: corrupted final rejected"
    (flagScenario.conforms corrupted) false
  -- ...and the divergence must be LOCALIZED: tick 50 + the row mismatch.
  match diverge flagScenario corrupted with
  | some report =>
      _ ← assert (report.contains "tick 50")
        "stress: diverge names the final tick"
      _ ← assert (report.contains "expected row")
        "stress: diverge reports the row mismatch"
  | none => throw "stress: corrupted final reported NO divergence"
