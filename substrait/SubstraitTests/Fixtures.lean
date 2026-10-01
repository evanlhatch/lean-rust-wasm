/- # SubstraitTests.Fixtures — the worked fragment's ONE home

The worked schema + rels (the legacy quick-start's shape), shared by
the suites that pin the typed layer (Main) and the typed decode
(TypedDecode). One copy, two importers — the dupDefBodies discipline
(the LK0002 findings' clean fix): the four function signatures were
borne twice, and every fragment def that references them would have
followed. Test-only data, no library surface.
-/

import Substrait

open Substrait Substrait.Proto Substrait.Typed SchemaCore

/-! ## the worked schema (the legacy quick-start's shape) -/

/-- The units table: two nullable i64 columns (declared as `abbrev` —
    the HasCol instance search sees through it). -/
abbrev units : Schema := [("health", .i64, true), ("regen", .i64, true)]

/-- The add signature: over the nullable column + a required literal —
    the null-propagating ret (the substrait function semantics). -/
def addSig : FunctionSig :=
  { name := "add", args := [(.i64, true), (.i64, false)],
    ret := .i64, retNullable := true }

/-- the typed expression: add(health, 0) — by name + by value. -/
def addHealth0 : Expr units .i64 true :=
  call addSig (Args.cons .i64 true (col "health" .i64 true)
    (Args.cons .i64 false (litVal (.i64 0)) Args.nil))

/-- the units READ rel. -/
def readUnits : Rel units units := .read "units" units

/-- The gt signature: the boolean call's signature (the FILTER rel's
    condition rides it). -/
def gtSig : FunctionSig :=
  { name := "gt", args := [(.i64, true), (.i64, false)],
    ret := .bool, retNullable := true }

def filterAdd : Rel units units :=
  .filter readUnits (call gtSig (Args.cons .i64 true addHealth0
    (Args.cons .i64 false (litVal (.i64 0)) Args.nil)))

/-- the AGGREGATE rel: group by regen, count the rows (the computed
    output schema: the grouping key's column then the measure's
    return). -/
def countSig : FunctionSig :=
  { name := "count", args := [], ret := .i64, retNullable := false }

def aggGrouping : List (AnyExpr units) :=
  [pack (col "regen" .i64 true : Expr units .i64 true)]

def aggMeasures : List (Measure units) :=
  [{ sig := countSig, args := [] }]

def aggRel : Rel units (aggregateOut units aggGrouping aggMeasures) :=
  .aggregate readUnits aggGrouping aggMeasures

/-- the SORT rel: by health ascending. -/
def sortRel : Rel units units :=
  .sort readUnits
    [{ key := pack (col "health" .i64 true : Expr units .i64 true),
       direction := .ascNullsFirst }]

/-- the FETCH rel: limit 10. -/
def fetchRel : Rel units units := .fetch readUnits (some 10) none

/-- the SET rel: unionAll of the read with itself. -/
def setRel : Rel units units := .set .unionAll readUnits readUnits

/-- the join demo's schemas (TOP-LEVEL abbrevs; the join's cond rides
    the CONSTRUCTED resolution proof — the concat `sa ++ sb` is not a
    literal schema abbreviation, so the head/tail instance search
    cannot see through it: the search's documented syntactic
    boundary, pinned here where it bites). -/
abbrev sa : Schema := [("a", .i64, false)]

abbrev sb : Schema := [("b", .i64, false)]

/-- the join demo's cond's resolution proof (over the computed concat —
    the proof is BY simp's unfolding; the instance search's boundary
    note above). -/
def joinCondHasA : HasCol (sa ++ sb) "a" .i64 false :=
  ⟨0, by rfl⟩

/-- the equijoin demo's cond: a = 0 (over the CONCAT schema; the
    required-column signature). -/
def eqSig : FunctionSig :=
  { name := "equal", args := [(.i64, false), (.i64, false)],
    ret := .bool, retNullable := false }

def joinCond : Expr (sa ++ sb) .bool false :=
  call eqSig (Args.cons .i64 false (Expr.field "a" .i64 false joinCondHasA)
    (Args.cons .i64 false (litVal (.i64 0)) Args.nil))

def demoJoin : Rel (sa ++ sb) (sa ++ sb) :=
  .join (.read "a" sa) (.read "b" sb) joinCond .inner

/-- the CROSS rel: the condition-free join of the two single-column
    reads (the wire's CrossRel face; the evaluator rides `evalJoin` at
    the always-true cond). -/
def crossRel : Rel (sa ++ sb) (sa ++ sb) :=
  .cross (.read "a" sa) (.read "b" sb)

/-- the WRITE rel: insert the units read into the named table (the
    written table's schema IS the input's output schema — the
    alignment by construction). -/
def writeRel : Rel units units :=
  .write ["mydb", "units"] .insert readUnits
