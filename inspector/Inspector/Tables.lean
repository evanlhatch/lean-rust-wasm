/-
# Inspector.Tables — the system's own data as tables (C5's schema faces)

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/design-wave-30.md C5 (the inspector eats qlang —
the ledger/registry/snapshot as tables; the introspection dogfoods the
query language, qlang's SECOND consumer); notes/v3/02-data-plane.md §2
(the same expression as executable query and logical proposition); the
SchemaCore discipline (the table's fields ARE a schema — the honest
minimal shape, `QueryTests.QLangSpecs`' fixtures' face).

THE THREE TABLES (each: the schema face + the row face + the readers):

- the provenance ledger's rows (`Kit.Ledger.LedgerRow`) — the list
  fields ride the ledger file's OWN csv spellings (`namesCsv`/`strsCsv`
  are the persisted format's list faces; the table's list columns are
  the csv fields, which is also the honest minimal shape: the Pred
  fragment has no list atoms to read anything finer);
- the code registry's rows (`Kit.CodeRegistry.CodeRow`) — `retired` is
  the honest `bool` (the fragment has no bool ATOM to filter on — the
  named friction; the column is still the schema's);
- the snapshot's items (`SchemaCore.Item`) — one row per (item, field)
  pair, the ty as `Snapshot.tyText`'s paren encoding (the snapshot
  format's own spelling, no spaces — the format's separator law).

THE ENGINE FACE: the inspector's hand-rolled filter/map shapes become
`qlang!` queries over these tables (`Query.QLang`'s surface) evaluated
by `Query.Eval.evalQ` at Bool weights (set semantics). The engine's
answer is a CANONICAL SET (sorted, weight-collapsed); the render faces
that need the table's order walk the TABLE through the query's
membership verdict (`selectRows` — the query decides the predicate, the
render keeps the table's order, so the pinned byte output is
order-identical). Projection faces read the canonical order honestly
(`projectRows`) — a did-you-mean list renders sorted, which no pin
distinguishes and which is the more deterministic face anyway.

The queries (the migrated shapes; the consumers in Why/LedgerView):

- `qLedgerAll` — the backward table's scan face;
- `qLedgerDemands` — the forward table's name universe (the projection);
- `qObligGaps` / `qObligFlagged` — the sweep's two count filters;
- `qObligLabels` — the why-miss's did-you-mean universe (the projection);
- the five `qTier*` — the tiers' distribution's closed filters.

KEPT HAND (the friction list — each names the gap): the
runtime-parameterized lookups (`backwardAnswer`'s path,
`forwardAnswer`'s name, `why`'s label — the qlang! predicate literals
are ELABORATION-TIME; a runtime parameter is not expressible), the
orphans (an anti-join against a runtime list — no set difference in
the fragment), the per-name affected filter (`Kit.Ledger.forward` —
proved conservatism, consumed; a csv-membership predicate the fragment
lacks), the zero-citation census (a NameMap graph, not a table; the
not-any shape is a universal the fragment excludes).

The five questions (notes/v3/01-core.md):
- root: none — the inspector's data faces over the lanes' own rows.
- carrier grade: none — the tables are the DATA's schema face; the
  queries ride `Q`'s (self-typed at elaboration).
- spine reading: the introspection stage's query face — the system's
  own rows through the ONE query language.
- ladder rung: none — the agreement is the bridge's (proved at
  `Query.TypedBridge`); this module evaluates and renders.
- gate row: InspectorTests' tables suite (the schema faces' pins + the
  byte-compat teeth) + the existing 12/12 (byte-compatible where
  pinned).

Cone: the inspector is host tooling (cone-high) — imports Query (the
query lane, whose QLang mounts the surface) + Kit.Ledger +
Kit.CodeRegistry + SchemaCore.Snapshot. No cycle (the query lane never
imports the inspector).
-/

import Kit.Ledger
import Kit.CodeRegistry
import SchemaCore.Snapshot
import Query
import Inspector.Obligations

namespace Inspector.Tables

open Query SchemaCore ZSet
open Kit.Ledger (LedgerRow namesCsv strsCsv)

/-! ## the provenance ledger's table -/

/-- The ledger's schema face: the row's fields as columns. The list
    fields (`demand.rows`, `demand.collections`, `obligations`) ride
    the ledger file's OWN csv spellings — the table's honest minimal
    shape (the fragment has no list atoms; the csv IS the persisted
    format's list face). -/
def ledgerFields : List Field :=
  [ { name := "path", ty := .string }
  , { name := "emitter", ty := .string }
  , { name := "specRows", ty := .string }
  , { name := "collections", ty := .string }
  , { name := "emitterRev", ty := .string }
  , { name := "hash", ty := .u64 }
  , { name := "obligations", ty := .string } ]

/-- One ledger row's table face (the csv fields are the persisted
    spellings — `namesCsv`/`strsCsv`, consumed). -/
def ledgerRowOf (a : LedgerRow) : RowVals ledgerFields :=
  .cons (.string a.path) $
  .cons (.string a.emitter) $
  .cons (.string (namesCsv a.demand.rows)) $
  .cons (.string (namesCsv a.demand.collections)) $
  .cons (.string a.demand.emitterRev) $
  .cons (.u64 a.contentHash) $
  .cons (.string (strsCsv a.obligations)) $
  .nil

/-- The ledger's rows, as table rows (order preserved). -/
def ledgerRowsOf (rows : List LedgerRow) : List (RowVals ledgerFields) :=
  rows.map ledgerRowOf

/-! ## the code registry's table -/

/-- The code registry's schema face: name, code, the retired tombstone
    (the honest `bool`; the fragment has no bool ATOM — the named
    friction, the column is still the schema's). -/
def codeRowFields : List Field :=
  [ { name := "name", ty := .string }
  , { name := "code", ty := .u64 }
  , { name := "retired", ty := .bool } ]

/-- One registry row's table face. -/
def codeRowOf (r : Kit.CodeRow) : RowVals codeRowFields :=
  .cons (.string r.name) $ .cons (.u64 (UInt64.ofNat r.code)) $
  .cons (.bool r.retired) $ .nil

/-- The registry's rows, as table rows (order preserved). -/
def codeRowsOf (rows : List Kit.CodeRow) : List (RowVals codeRowFields) :=
  rows.map codeRowOf

/-! ## the snapshot's items table -/

/-- The snapshot's schema face: ONE ROW PER (item, field) pair — the
    universe snapshot's item lines flattened (the ty as `tyText`'s
    paren encoding, the format's own no-space spelling). -/
def itemFields : List Field :=
  [ { name := "item", ty := .string }
  , { name := "field", ty := .string }
  , { name := "ty", ty := .string } ]

/-- The snapshot's items, as table rows (one per (item, field) pair). -/
def itemRowsOf : List Item → List (RowVals itemFields)
  | [] => []
  | it :: rest =>
      (it.fields.map fun f =>
        .cons (.string it.name) $
        .cons (.string f.name) $
        .cons (.string (tyText f.ty)) $
        .nil)
      ++ itemRowsOf rest

/-! ## the obligation rows' table (the sweep's faces) -/

/-- The obligation rows' schema face: the sweep's fields as columns.
    The tier/discharge ride their RENDERED closed spellings
    (`Tier.render` / `DischargeState.tag`); `defects` is the
    acceptance-shape defect COUNT (the flagged filter's u64 face — the
    fragment has no bool atoms, and `defects > 0` is the honest
    reading). `observer`/`ecode` are the `getD ""` faces — the table
    face answers counts, never the observer's honesty discipline
    (which is `InspRow.defects`' data-level check, consumed unchanged). -/
def obligFields : List Field :=
  [ { name := "lane", ty := .string }
  , { name := "label", ty := .string }
  , { name := "tier", ty := .string }
  , { name := "provenance", ty := .string }
  , { name := "payload", ty := .string }
  , { name := "observer", ty := .string }
  , { name := "ecode", ty := .string }
  , { name := "discharge", ty := .string }
  , { name := "defects", ty := .u64 } ]

/-- One obligation row's table face. -/
def obligRowOf (r : InspRow) : RowVals obligFields :=
  .cons (.string r.lane) $
  .cons (.string r.label) $
  .cons (.string r.tier.render) $
  .cons (.string r.provenance.toString) $
  .cons (.string r.payload) $
  .cons (.string (r.observer.getD "")) $
  .cons (.string (r.eCode.getD "")) $
  .cons (.string r.discharge.tag) $
  .cons (.u64 (UInt64.ofNat r.defects.length)) $
  .nil

/-- The obligation rows, as table rows (order preserved). -/
def obligRowsOf (rows : List InspRow) : List (RowVals obligFields) :=
  rows.map obligRowOf

/-! ## the readers (the render face's column reads) -/

/-- The string column's read. The `""` fallback is UNREACHABLE on a
    self-typed query's rows (the schema pins every column — a projected
    row carries exactly the projected fields); the total face needs a
    value, and the fallback is never a fabricated comparison. -/
def readStr {fs : List Field} (row : RowVals fs) (n : String) : String :=
  match RowVals.project? fs row n with
  | some ⟨.string, .string s⟩ => s
  | _ => ""

/-- The u64 column's read (the `0` fallback's reachability note as
    above). -/
def readU64 {fs : List Field} (row : RowVals fs) (n : String) : UInt64 :=
  match RowVals.project? fs row n with
  | some ⟨.u64, .u64 v⟩ => v
  | _ => 0

/-! ## the engine face (the query's answer, the render's order) -/

/-- The select-only query's answer, in the TABLE's order: the engine's
    answer is a canonical SET (`evalQ` at Bool weights — sorted,
    weight-collapsed); the render face walks the TABLE through the
    query's membership verdict. The query decides the predicate; the
    render keeps the table's order — the pinned byte output is
    order-identical to the hand filter's. -/
def selectRows {fs : List Field} (q : Q fs fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  let m := evalQ q (tableW rows true)
  rows.filter (fun r => weightW m r)

/-- The projection query's answer rows, in the engine's canonical
    order (sorted). The consumers that need the table's order do not
    project (the render walks the table); the projected consumers
    (did-you-mean universes) render sorted — the honest order change,
    pinned nowhere. -/
def projectRows {fs gs : List Field} (q : Q fs gs)
    (rows : List (RowVals fs)) : List (RowVals gs) :=
  (evalQ q (tableW rows true)).rep.map (·.1)

/-! ## the queries (the migrated shapes, as qlang! values) -/

/-- The backward table's scan face (the from stage). -/
def qLedgerAll : Q ledgerFields ledgerFields :=
  qlang!{ from ledgerFields }

/-- The forward table's name universe: the demand columns, projected
    (the drop projection's named narrowing — order-preserving). -/
def qLedgerDemands :=
  qlang!{ from ledgerFields then project [.specRows, .collections] }

/-- The sweep's GAP filter: the discharge tag's closed spelling
    (`DischargeState.tag`'s openGap arm). -/
def qObligGaps : Q obligFields obligFields :=
  qlang!{ from obligFields then select (discharge == "NONE RECORDED (GAP)") }

/-- The sweep's FLAGGED filter: the defect count's u64 face. -/
def qObligFlagged : Q obligFields obligFields :=
  qlang!{ from obligFields then select (defects > 0) }

/-- The why-miss's did-you-mean universe: the labels, projected. -/
def qObligLabels :=
  qlang!{ from obligFields then project [.label] }

/-- The tiers' distribution's five closed filters (the closed tier
    set's render spellings, `Tier.render`). -/
def qTierProvedAtElab : Q obligFields obligFields :=
  qlang!{ from obligFields then select (tier == "proved-at-elab") }

def qTierDecidableNow : Q obligFields obligFields :=
  qlang!{ from obligFields then select (tier == "decidable-now") }

def qTierGeneratedCheck : Q obligFields obligFields :=
  qlang!{ from obligFields then select (tier == "generated-check") }

def qTierOracleSwept : Q obligFields obligFields :=
  qlang!{ from obligFields then select (tier == "oracle-swept") }

def qTierGuestVerified : Q obligFields obligFields :=
  qlang!{ from obligFields then select (tier == "guest-verified") }

/-- The five tier filters, paired with the closed tier set in the
    distribution's order (`Inspector.Trust.tierDistribution`'s
    consumer). -/
def tierQueries :
    List (Kit.Tier × Q obligFields obligFields) :=
  [ (.provedAtElab, qTierProvedAtElab)
  , (.decidableNow, qTierDecidableNow)
  , (.generatedCheck, qTierGeneratedCheck)
  , (.oracleSwept, qTierOracleSwept)
  , (.guestVerified, qTierGuestVerified) ]

/-! ## the code registry's + the snapshot's dogfood queries -/

/-- The registry's live-code names (the tombstones ride `retired`'s
    bool column — the fragment has no bool atom, so the LIVE face is
    the whole name universe; the named friction). -/
def qCodeNames :=
  qlang!{ from codeRowFields then project [.name] }

/-- The snapshot's item names (one per (item, field) row — the
    dedup'd universe is the render's face). -/
def qItemNames :=
  qlang!{ from itemFields then project [.item] }

end Inspector.Tables
