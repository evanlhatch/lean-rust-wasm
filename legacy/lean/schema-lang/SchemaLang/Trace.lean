/-
# SchemaLang.Trace — the scenario/trace spec item (SPEC-core §11, v2)

ONE artifact, four uses: a SCENARIO = {schema, init world, input batches
per tick}; a TRACE = the per-tick observations; conformance = TABLE
EQUALITY (sorted compare, order-independent). Lean's semantics is THE
ORACLE — `runScenario` is the authority every consumer replays against.

Ownership: this module owns the scenario/trace lane. `SchemaLang.Update`
(the tick stage machine + the row-law layer), `SchemaLang.Update2` (the
batch surface — `SomeUpdate2`, the v1→v2 migration's wrapper for the
scenario batches), `SchemaLang.Validate` (RowVals), `SchemaLang.CodecValue`
(the value codec) are read-only dependencies.

v2 (the v1→v2 migration): the batch type moved from `List SomeUpdate`
to `List SomeUpdate2` — the v2 wrapper (`fields` + `Update2Item`), whose
table-level execute (`SomeUpdate2.apply`) replaces v1's
`SomeUpdate.applyRow`-batch casting. Scope (deliberate, documented):
- ONE table per scenario (`fields` + rows over it). A batch may still
  carry ANY `SomeUpdate2` (the existential rides), but the oracle
  treats an update whose field list mismatches the scenario's as a
  no-op (the guarded-cast discipline — `SomeUpdate2.apply`'s rule).
- The wire codec covers the OBSERVATION half: the fields' row data
  (init + every tick's state). It is schema-out-of-band (the field
  list is the decoder's argument, like a table name) and restricted to
  `CodecClosed` field types (the `FieldsClosed` hypothesis — floats and
  `.ty` refs are outside, the CodecValue doctrine). The UPDATE batches
  (procedures: `VExpr`/`ColPath`) have NO wire form here — they are
  compiled artifacts riding the emitter lane, not observations.
- `TableEq` sorts by the row's canonical wire key (`rowKey` =
  `canonKey`: the concatenated `encodeValue` bytes) — the rows' ORDER
  is not observable; the byte key is injective on the codec-closed
  universe (the round-trip theorem: equal bytes decode equal).
- C8 (best-effort): vs `Machines.Machine.run`/`Dbsp.Stream` re-typing
  — NOT done (the oracle stays a pure fold over the batch list; a
  machine-shaped tick would need a step type the scenario does not
  carry — left mechanical, see the task report).

GADT note: rows ride `RowVals` directly (no nested `List (Value t)`
inside a GADT — the VList lesson applies unchanged).
-/

module

public import SchemaLang.Update
public import SchemaLang.Update2
public import SchemaLang.CodecValue

@[expose] public section

namespace SchemaLang

/-! ## The scenario item -/

/-- The reified scenario: the table's fields, the initial world, and
    one update-batch per tick. The batches are the INPUTS; everything
    else is the oracle's business. The batches ride the v2 wrapper
    (`SomeUpdate2` — the v1→v2 migration); the field-list mismatch
    rule is `SomeUpdate2.apply`'s guarded cast. -/
structure Scenario where
  /-- The table's fields (the schema, in registration order). -/
  fields : List Field
  /-- The initial rows (tick 0's state). -/
  init : List (RowVals fields)
  /-- The input updates: one batch per tick (`ticks[k]` runs over tick
      k's state). -/
  ticks : List (List SomeUpdate2)

/-- One tick: the batch folds over the rows in registration order
    (v1's acyclic single-pass cascade — TickCascade's substrate). First
    arg is the BATCH (a `List SomeUpdate2`) — deliberately NOT a
    `Scenario`-namespaced def, so no dot-notation confusion. Each
    update executes through `SomeUpdate2.apply` (the guarded cast: a
    matching table runs, a foreign one passes through). -/
def tickRows (batch : List SomeUpdate2) {fs : List Field}
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  batch.foldl (fun acc u => SomeUpdate2.apply u acc) rows

/-- The per-tick states AFTER tick 0: `tickTrace batches rows` = the
    states following each batch in `batches`, threaded. -/
def tickTrace (batches : List (List SomeUpdate2)) {fs : List Field}
    (rows : List (RowVals fs)) : List (List (RowVals fs)) :=
  match batches with
  | [] => []
  | b :: bs =>
      let next := tickRows b rows
      next :: tickTrace bs next

/-- THE ORACLE: tick 0 = init; tick k+1 = cascade (ticks[k]) over
    tick k. Lean's semantics IS the authority — the engine's output is
    replayed against this. -/
def runScenario (s : Scenario) : List (List (RowVals s.fields)) :=
  s.init :: tickTrace s.ticks s.init

/-- The final state (the fold view of the oracle's last tick). -/
def Scenario.finalState (s : Scenario) : List (RowVals s.fields) :=
  s.ticks.foldl (fun rows batch => tickRows batch rows) s.init

/-! ## TableEq — the conformance relation -/

/-- Lexicographic byte comparison (the row-key order). -/
def bytesLex : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then bytesLex xs ys else x < y

def insertKey (x : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [x]
  | y :: ys => if bytesLex x y then x :: y :: ys else y :: insertKey x ys

/-- The sorted row keys (insertion sort — oracle code, the lists are
    the table's rows). -/
def sortKeys : List (List UInt8) → List (List UInt8)
  | [] => []
  | x :: xs => insertKey x (sortKeys xs)

/-! ## CanonKey — the row's canonical wire key (C3) -/

/-- A row's canonical key (C3): its fields' encoded values,
    concatenated in schema order — the wire form, injective on the
    codec-closed universe by the round-trip theorem. The fold over
    the field spine; `rowKey` routes through it (one authority). -/
def canonKey : (fs : List Field) → RowVals fs → List UInt8
  | [], .nil => []
  | f :: fs, .cons v vs => encodeValue f.ty v ++ canonKey fs vs

/-- A row's canonical key (the historic name; routes through
    `canonKey` — same bytes, one definition). -/
def rowKey (fs : List Field) (row : RowVals fs) : List UInt8 :=
  canonKey fs row

/-- THE CONFORMANCE RELATION: sorted-compare of the rows' canonical
    keys — ORDER-INDEPENDENT (the rows' order is not observable). The
    checker the engine's output is replayed against. -/
def TableEq (fs : List Field) (a b : List (RowVals fs)) : Bool :=
  sortKeys (a.map (rowKey fs)) == sortKeys (b.map (rowKey fs))

/-- The conformance verdict: does the engine's final state match the
    oracle's? -/
def Scenario.conforms (s : Scenario)
    (engineRows : List (RowVals s.fields)) : Bool :=
  TableEq s.fields s.finalState engineRows

/-! ## The localized divergence report -/

/-- The first mismatching row pair over the SORTED keys (the report
    reads the same order-independent relation `TableEq` decides). -/
def firstKeyMismatch : List (List UInt8) → List (List UInt8) → Option String
  | [], [] => none
  | [], y :: _ => some s!"unexpected row {repr y}"
  | x :: _, [] => some s!"missing row {repr x}"
  | x :: xs, y :: ys =>
      if x == y then firstKeyMismatch xs ys
      else some s!"expected row {repr x}, got {repr y}"

/-- The row-mismatch report over two states (sorted compare). -/
def keyMismatchReport (fs : List Field) (expected got : List (RowVals fs)) :
    String :=
  match firstKeyMismatch (sortKeys (expected.map (rowKey fs)))
      (sortKeys (got.map (rowKey fs))) with
  | some d => d
  | none => "sorted row keys equal but the table compare disagreed"

/-- THE DIVERGENCE REPORT: `none` iff the engine's rows conform. A
    non-conforming engine output is localized: if the rows equal some
    EARLIER oracle tick's state, the engine STALLED at that tick; else
    the report names the final tick and the first row mismatch (over
    the sorted keys). The bug-report artifact's seed. -/
def diverge (s : Scenario) (engineRows : List (RowVals s.fields)) :
    Option String :=
  let trace := runScenario s
  let lastTick := trace.length - 1
  if TableEq s.fields trace.getLast! engineRows then none
  else
    match trace.findIdx? (fun st => TableEq s.fields st engineRows) with
    | some k =>
        some s!"tick {k}: engine output equals the oracle's tick {k} state and never advances (stalled after tick {k})"
    | none =>
        some (s!"tick {lastTick}: " ++
          keyMismatchReport s.fields trace.getLast! engineRows)

/-! ## The wire codec — the observation half (closed fields) -/

/-- The codec-closed field list: every field's type is in
    `CodecClosed` (floats and `.ty` refs excluded — the CodecValue
    doctrine). The round-trip theorem's hypothesis. -/
inductive FieldsClosed : List Field → Type where
  | nil : FieldsClosed []
  | cons : {f : Field} → {fs : List Field} → CodecClosed f.ty →
      FieldsClosed fs → FieldsClosed (f :: fs)

/-- Encode one row: the fields' values in schema order (no framing —
    the values are self-delimiting; a row over `[]` is empty). -/
def encRowVals : (fs : List Field) → RowVals fs → List UInt8
  | [], .nil => []
  | f :: fs, .cons v vs => encodeValue f.ty v ++ encRowVals fs vs

/-- Decode one row: the field list is the decoder's argument (the
    schema rides out of band — like a table name). -/
def decRowVals? : (fs : List Field) → List UInt8 →
    Option (RowVals fs × List UInt8)
  | [], bs => some (.nil, bs)
  | f :: fs, bs =>
      match decVal? f.ty bs with
      | none => none
      | some (v, r) =>
          match decRowVals? fs r with
          | none => none
          | some (rv, r2) => some (.cons v rv, r2)

/-- THE ROW ROUND TRIP, append form: over the codec-closed fields,
    decode (encode row ++ rest) = some (row, rest). Composition of
    CodecValue's per-type theorem through the row spine. -/
theorem decRowVals_encRowVals_append {fs : List Field}
    (h : FieldsClosed fs) :
    ∀ (row : RowVals fs) (rest : List UInt8),
      decRowVals? fs (encRowVals fs row ++ rest) = some (row, rest) := by
  induction h with
  | nil => intro row rest; cases row; simp [encRowVals, decRowVals?]
  | @cons f fs hc hfs ih =>
      intro row rest
      cases row with
      | cons v vs =>
          simp only [encRowVals, List.append_assoc, decRowVals?,
            decode_encodeValue_append f.ty hc v, ih]

/-- Encode a row list (length-prefixed — the list combinator). -/
def encRows (fs : List Field) (rows : List (RowVals fs)) : List UInt8 :=
  Codec.encList (encRowVals fs) rows

/-- Decode a row list. -/
def decRows? (fs : List Field) (bs : List UInt8) :
    Option (List (RowVals fs) × List UInt8) :=
  Codec.decList? (decRowVals? fs) bs

/-- The row-list round trip, append form. -/
theorem decRows_encRows_append {fs : List Field} (h : FieldsClosed fs)
    (rows : List (RowVals fs)) (rest : List UInt8) :
    decRows? fs (encRows fs rows ++ rest) = some (rows, rest) :=
  Codec.decList_encList_append (encRowVals fs) (decRowVals? fs)
    (fun row rest => decRowVals_encRowVals_append h row rest) rows rest

/-- Encode a whole trace: the per-tick observations (length-prefixed
    list of row lists). -/
def encTrace (fs : List Field) (trace : List (List (RowVals fs))) :
    List UInt8 :=
  Codec.encList (encRows fs) trace

/-- Decode a whole trace. -/
def decTrace? (fs : List Field) (bs : List UInt8) :
    Option (List (List (RowVals fs)) × List UInt8) :=
  Codec.decList? (decRows? fs) bs

/-- The TRACE round trip, append form: the scenario's observation half
    survives the wire (init + every tick's state). -/
theorem decTrace_encTrace_append {fs : List Field} (h : FieldsClosed fs)
    (trace : List (List (RowVals fs))) (rest : List UInt8) :
    decTrace? fs (encTrace fs trace ++ rest) = some (trace, rest) :=
  Codec.decList_encList_append (encRows fs) (decRows? fs)
    (fun rows rest => decRows_encRows_append h rows rest) trace rest

end SchemaLang
