/-
# QLang Tests

The dynamic surface's executable checks, ported from the flatland lineage's
`FlatlandDsl` test driver. Every error path is a NEGATIVE CONTROL: the
unknown-column check pins the did-you-mean rendering (the message is product
surface — TOOLKIT §11.1), the arity/type-mismatch checks pin the compiler's
failure channels, and the filter checks pin the fusion canon (two `filter`
steps ⇒ ONE `Filter` rel with ANDed conditions).

Run: `lake build QLangTests && .lake/build/bin/QLangTests`
-/
import QLang
import Substrait.Emit
import TestKit

open QLang
open Substrait.Typed
open TestKit

/-- The units relation: health, regen — both nullable i32. -/
abbrev units : Schema :=
  [("health", .i32, true), ("regen", .i32, true)]

def editDistanceChecks : CheckResult := do
  _ ← assertEq "ident" (editDistance "health" "health") 0
  _ ← assertEq "one-sub" (editDistance "helth" "health") 1
  _ ← assertEq "empty" (editDistance "" "abc") 3
  _ ← assertEq "case" (editDistance "Health" "health") 1
  .ok ()

def didYouMeanChecks : CheckResult := do
  let dict := ["health", "maxHealth", "name", "mana"]
  _ ← assertEq "helth" (didYouMean "helth" dict) ["health"]
  _ ← assertEq "far" (didYouMean "xyzzy" dict) []
  .ok ()

/-- The happy-path compile: `col "health"` resolves to ordinal 0, i32,
nullable — the instance is DATA (HasCol.ofIndex), not search. -/
def compileColChecks : CheckResult := do
  match compile units (col "health") with
  | .error e => throw s!"compile-col failed: {e}"
  | .ok c =>
      _ ← assertContains "type" (toString (repr c.t)) "SType.i32"
      _ ← assert (c.n == true) "compile-col: health should be nullable"
      match compile units (col "regen") with
      | .error e => throw s!"compile-col regen failed: {e}"
      | .ok c2 =>
          _ ← assertContains "type" (toString (repr c2.t)) "SType.i32"
          -- the RESOLVER's ordinal (the same fold shape sort keys use):
          match colOrdinal units "regen" with
          | .error e => throw s!"col-ordinal failed: {e}"
          | .ok ord => assertEq "ordinal" ord 1
  .ok ()

/-- Negative control: unknown column → `Except` with the did-you-mean
rendering (valid space + suggestion). -/
def unknownColumnCheck : CheckResult :=
  expectErrorContaining ["no column `helth`", "has: health, regen", "did you mean: health"]
    (compile units (col "helth"))

/-- Negative control: arity mismatch. -/
def arityCheck : CheckResult :=
  expectErrorContaining ["arity 1 does not match signature arity 2"]
    (compile units (call (opAddSig false false) [col "health"]))

/-- Negative control: argument type mismatch (`add` over a bool literal). -/
def typeMismatchCheck : CheckResult :=
  expectErrorContaining ["argument type mismatch", "got [Substrait.Typed.SType.i32, Substrait.Typed.SType.bool]"]
    (compile units (add (col "health") (litBool true)))

/-- The golden pipeline: `units |> filter (health > 0) |> project [total]`.
Compiled via the dynamic log, `checked` yields the typed rel; its canonical
text matches the typed surface's shape. -/
def pipelineCheck : CheckResult := do
  let q := Query.table "units" units
    |> Query.filter (gt (col "health") (litI32 0))
    |> Query.project [("total", add (col "health") (col "regen"))]
  match q.checked with
  | .error e => throw s!"pipeline checked failed: {e}"
  | .ok r =>
      match Substrait.Emit.Text.emit r.toPlan with
      | .error e => throw s!"pipeline emit error: {e}"
      | .ok text =>
          _ ← assertContains "filter-node" text "Filter[gt($0, 0:i32):boolean?"
          assertContains "project-node" text "Read[units => health:i32?, regen:i32?]"

/-- The fusion canon: two `filter` steps ⇒ ONE `Filter` rel with ANDed
conditions (structural check on the compiled rel, not the text). -/
def fusionCheck : CheckResult := do
  let q := Query.table "units" units
    |> Query.filter (gt (col "health") (litI32 0))
    |> Query.filter (lt (col "regen") (litI32 100))
  match q.checked with
  | .error e => throw s!"fusion checked failed: {e}"
  | .ok r =>
      match r with
      | .filter (.read _ _) _ => .ok ()  -- single fused node over the read
      | _ => throw "fusion: expected ONE Filter node directly over the read"

/-- Negative control: a non-boolean filter condition is logged, not thrown —
and `checked` surfaces it. -/
def nonBoolFilterCheck : CheckResult := do
  let q := Query.table "units" units |> Query.filter (col "health")
  _ ← assertEq "logged" q.errors.length 1
  expectErrorContaining ["filter condition must be boolean", "i32"] q.checked

/-- Negative control: a failing projection is skipped (schema unchanged) and
its error logged. -/
def failedProjectionCheck : CheckResult := do
  -- successes empty ⇒ output schema = input schema; the failing DExpr
  -- genuinely fails to compile (the successes/failures split is exhaustive)
  let q := Query.table "units" units |> Query.project [("x", col "nope")]
  _ ← assertEq "logged" q.errors.length 1
  _ ← assert (q.errors.head! == (Query.failures units [("x", QLang.col "nope")]).head!) "failed-projection: logged error is the compile failure"
  expectErrorContaining ["no column `nope`"] q.checked
/-- sort/fetch steps: name-resolved sort keys + passthrough fetch. -/
def sortFetchCheck : CheckResult := do
  let q := Query.table "units" units
    |> Query.sort [("health", .ascNullsFirst)]
    |> Query.fetch (some 10) none
  match q.checked with
  | .error e => throw s!"sort/fetch checked failed: {e}"
  | .ok r =>
      match r with
      | .fetch (.sort _ _) _ _ => .ok ()
      | _ => throw "sort/fetch: expected Fetch over Sort"

/-- Negative control: an unknown sort key is logged. -/
def badSortKeyCheck : CheckResult := do
  let q := Query.table "units" units |> Query.sort [("helth", .ascNullsFirst)]
  _ ← assertEq "logged" q.errors.length 1
  expectErrorContaining ["did you mean: health"] q.checked

/-- The registry: find with the valid space + did-you-mean; fromRegistry
reifies the pipeline type from the found schema. -/
def registryCheck : CheckResult := do
  let reg := Registry.empty.add (tableS "units" units)
  _ ← expectErrorContaining ["unknown table `unitz`", "tables: units", "did you mean: units"]
      (reg.find "unitz")
  match reg.find "units" with
  | .error e => throw s!"registry find failed: {e}"
  | .ok t => assertEq "table-name" t.name "units"

def main : IO UInt32 :=
  TestKit.mainOfChecks "QLang" [
    ("edit-distance", editDistanceChecks),
    ("did-you-mean", didYouMeanChecks),
    ("compile-col", compileColChecks),
    ("unknown-column", unknownColumnCheck),
    ("arity", arityCheck),
    ("type-mismatch", typeMismatchCheck),
    ("pipeline", pipelineCheck),
    ("filter-fusion", fusionCheck),
    ("non-bool-filter", nonBoolFilterCheck),
    ("failed-projection", failedProjectionCheck),
    ("sort-fetch", sortFetchCheck),
    ("bad-sort-key", badSortKeyCheck),
    ("registry", registryCheck)
  ]
