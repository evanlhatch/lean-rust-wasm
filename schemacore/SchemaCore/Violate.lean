/-
# SchemaCore.Violate — the violation lane: invariants as violation queries

Owner: the bidirectional-slice agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §7-8 (the change
interface + THE STRONGEST SINGLE COMPOSITION: the violation relations;
the state invariant `Valid db ↔ violations db = []`; a proposed delta
updates the violation relation; empty permits commit), notes/v3/
02-data-plane.md §1 (a failed check carries the violating rows AS
DATA), notes/v3/15-patterns.md #1 (relation + executable checker +
proved bridge — here the relation is the violation QUERY, the state
invariant is the bridge's iff).

THE WORKED FIXTURE (03 §9's first slice): two keyed tables —
`account` (id/owner/balance) + `transfer` (tid/src/dst/amount) — with
the non-negative-balance invariant and the transfer→account foreign
keys. The three violation queries of 03 §8's table, at slice size:

- `DuplicateKeys`   → `dupIds` (the account ids occurring twice+);
- `NegativeBalances`→ `negativeAccounts` (the account rows below zero);
- `MissingReferences`→ `danglingSrc`/`danglingDst` (the transfer rows
  whose endpoint fails to resolve among the account ids).

Every query is executable AND returns the violations AS DATA
(`Violation` — the diagnostic's payload, never a bare `false`); the
state invariant `Valid` is the honest Prop (keys unique, balances
non-negative, references resolve — the Keys lane's canonical meanings
at the fixture's reading); `valid_iff` is THE STATE-INVARIANT THEOREM,
both directions (pattern #1's bridge, at the table tier — `Pred`'s
bridge is the row tier, `Check.lean` the registered-item tier).

THE INCREMENTAL FACE — NAMED, NOT FAKED: the queries above recompute
over the whole table (the honest first cut a proposal check uses — see
`Commit.checkDelta`). The change-proportional discipline — a proposed
delta updates the VIOLATION RELATION itself (`ΔV = V(B+ΔB) − V(B)`),
the foundation proving incremental = full recomputation ONCE
(`incrementalize_ok` at the circuit theory) — is the dbsp-circuit
wave's content. Nothing here pretends to it.

Deliberate exclusions (the leftover rule): the registered-item mount
(`Check.lean`'s lane — the fixture's invariants are SLICE data, not
registry rows; the item-level mount gains its consumer when the first
generated surface declares an invariant); i64/aggregate Pred atoms
(`Pred`'s own exclusion note — the balance reading is the positional
GADT reader, not a `Pred` atom); composite keys (the Keys lane's v1
granularity).

The five questions (notes/v3/01-core.md): root = the data plane's
constraint face (02 §1-2 — the shared authority over valid worlds);
carrier = the GADT-indexed rows over the abbrev field lists (a
mistyped row unconstructible; the positional readers total by the
index, the abbrev rule 06 §3); spine reading = none — the queries are
the substrate `Commit`'s check consumes; ladder rung = `valid_iff` is
the small hand kind (list-filter bridges, one induction); gate row =
SchemaTests' violateSpec + the axiom report.

Core-only (imports SchemaCore.Keys + SchemaCore.Update — the cone
rule; the queries ride the Keys lane's canonical meanings and the
update lane's shared `RowDelta` substrate is NOT re-invented here).
-/

import SchemaCore.Keys
import SchemaCore.Update

namespace SchemaCore

/-! ## The fixture's schema (the abbrev rule — the GADT index unfolds) -/

/-- The account table's schema: `id` (the primary key), `owner`,
    `balance` (SIGNED — the overdraft face must be representable). -/
abbrev accountFields : List Field :=
  [ { name := "id", ty := .u64 }
  , { name := "owner", ty := .string }
  , { name := "balance", ty := .i64 } ]

/-- The transfer table's schema: `tid` (primary key), the two endpoints
    (`src`/`dst` — the foreign keys into `account`), `amount`. -/
abbrev transferFields : List Field :=
  [ { name := "tid", ty := .u64 }
  , { name := "src", ty := .u64 }
  , { name := "dst", ty := .u64 }
  , { name := "amount", ty := .u64 } ]

/-- The account table's declared key (the Keys lane's drift-free data:
    the declaration names the key field, never the target's internals). -/
def accountDecl : KeyDecl :=
  { record := "account", fields := accountFields, key := "id" }

/-- The transfer table's declared key + the TWO foreign keys into
    `account` (the drift-free rule: `target` is the record NAME — the
    checker resolves the target's own `KeyDecl`). -/
def transferDecl : KeyDecl :=
  { record := "transfer", fields := transferFields, key := "tid"
  , foreign := [ { field := "src", target := "account" }
               , { field := "dst", target := "account" } ] }

/-! ## The positional readers (total by the GADT index) -/

/-- The account's id (the key column). -/
def accId : RowVals accountFields → UInt64
  | .cons (.u64 i) (.cons (.string _) (.cons (.i64 _) .nil)) => i

/-- The account's balance (the signed column the invariant reads). -/
def accBal : RowVals accountFields → Int64
  | .cons (.u64 _) (.cons (.string _) (.cons (.i64 b) .nil)) => b

/-- The account with one column rewritten (the write is the update
    lane's GADT discipline at the fixture's granularity: the row
    INDEX makes a mistyped write unconstructible). -/
def withBal : RowVals accountFields → Int64 → RowVals accountFields
  | .cons (.u64 i) (.cons (.string o) (.cons (.i64 _) .nil)), b =>
      .cons (.u64 i) (.cons (.string o) (.cons (.i64 b) .nil))

/-- The transfer's id. -/
def trId : RowVals transferFields → UInt64
  | .cons (.u64 t) (.cons (.u64 _) (.cons (.u64 _) (.cons (.u64 _) .nil))) => t

/-- The transfer's source account. -/
def trSrc : RowVals transferFields → UInt64
  | .cons (.u64 _) (.cons (.u64 s) (.cons (.u64 _) (.cons (.u64 _) .nil))) => s

/-- The transfer's destination account. -/
def trDst : RowVals transferFields → UInt64
  | .cons (.u64 _) (.cons (.u64 _) (.cons (.u64 d) (.cons (.u64 _) .nil))) => d

/-- The transfer's amount. -/
def trAmount : RowVals transferFields → UInt64
  | .cons (.u64 _) (.cons (.u64 _) (.cons (.u64 _) (.cons (.u64 a) .nil))) => a

/-! ## The database -/

/-- THE DATABASE: the two keyed tables. The committed delta (03 §7) is
    the change interface over BOTH — `Commit.Deltas` lowers a proposal
    onto each table's own key. -/
structure Db where
  /-- The account table (keyed on `id`). -/
  accounts : List (RowVals accountFields)
  /-- The transfer ledger (keyed on `tid`). -/
  transfers : List (RowVals transferFields)

/-- The account ids (the key images, positionally — the GADT index
    makes the projection total; `Keys.keyImages?`'s Option discipline
    is the NAME-keyed generic form, the one this fixture specializes). -/
def accIds (rows : List (RowVals accountFields)) : List UInt64 :=
  rows.map accId

/-! ## The count law (the duplicate-key bridge's leg) -/

/-- `Nodup` IS the all-counts-≤-1 property (the duplicate-key query's
    emptiness is exactly key uniqueness — the bridge's content; the
    ∀-membership packaging rides core's `List.nodup_iff_count`). -/
theorem nodup_iff_count_le_one {α : Type} [BEq α] [LawfulBEq α] (ids : List α) :
    ids.Nodup ↔ ∀ x, x ∈ ids → ids.count x ≤ 1 := by
  rw [List.nodup_iff_count]
  constructor
  · exact fun h x _ => h x
  · intro h a
    cases hc : ids.count a with
    | zero => omega
    | succ n =>
        have hmem : a ∈ ids := (List.count_pos_iff).mp (by rw [hc]; omega)
        have hle := h a hmem
        rw [hc] at hle
        omega

/-! ## The violation queries (03 §8's table, executable) -/

/-- THE DUPLICATE-KEY QUERY: every account id occurring more than once
    (once per occurrence — the data is the diagnosis, 02 §1). -/
def dupIds (ids : List UInt64) : List UInt64 :=
  ids.filter (fun k => decide (ids.count k > 1))

/-- THE NEGATIVE-BALANCE QUERY: every account row whose balance is
    below zero (the rows AS DATA — the diagnostic's payload). -/
def negativeAccounts (rows : List (RowVals accountFields)) :
    List (RowVals accountFields) :=
  rows.filter (fun r => decide (accBal r < 0))

/-- THE MISSING-REFERENCE QUERY, source face: every transfer whose
    `src` fails to resolve among the account ids. -/
def danglingSrc (ts : List (RowVals transferFields)) (ids : List UInt64) :
    List (RowVals transferFields) :=
  ts.filter (fun t => !decide (trSrc t ∈ ids))

/-- THE MISSING-REFERENCE QUERY, destination face. -/
def danglingDst (ts : List (RowVals transferFields)) (ids : List UInt64) :
    List (RowVals transferFields) :=
  ts.filter (fun t => !decide (trDst t ∈ ids))

/-! ## The per-query emptiness bridges (one leg each — pattern #1) -/

/-- The duplicate-key query's emptiness IS `Nodup`. -/
theorem dupIds_eq_nil_iff {ids : List UInt64} :
    dupIds ids = [] ↔ ids.Nodup := by
  rw [dupIds, List.filter_eq_nil_iff, nodup_iff_count_le_one]
  constructor
  · intro h x hx
    have hle := h x hx
    simp only [decide_eq_true_iff] at hle
    omega
  · intro h x hx
    have hle := h x hx
    simp only [decide_eq_true_iff]
    omega

/-- The negative-balance query's emptiness IS the no-negative-balance
    property. -/
theorem negativeAccounts_eq_nil_iff (rows : List (RowVals accountFields)) :
    negativeAccounts rows = [] ↔ ∀ r, r ∈ rows → ¬ (accBal r < 0) := by
  rw [negativeAccounts, List.filter_eq_nil_iff]
  constructor
  · intro h r hr hbad
    exact h r hr (by rw [decide_eq_true_iff]; exact hbad)
  · intro h r hr hdec
    exact h r hr (of_decide_eq_true hdec)

/-- The missing-reference query's emptiness IS resolution (the
    foreign key's canonical meaning, at the fixture's reader). -/
theorem dangling_eq_nil_iff (get : RowVals transferFields → UInt64)
    (ts : List (RowVals transferFields)) (ids : List UInt64) :
    ts.filter (fun t => !decide (get t ∈ ids)) = [] ↔ ∀ t, t ∈ ts → get t ∈ ids := by
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h t ht
    have key := h t ht
    cases hd : decide (get t ∈ ids) with
    | true => exact of_decide_eq_true hd
    | false =>
        rw [hd] at key
        simp at key
  · intro h t ht
    have hd : (!decide (get t ∈ ids)) = false :=
      congrArg Bool.not (decide_eq_true_iff.mpr (h t ht))
    rw [hd]
    decide

/-! ## The violations as data (02 §1) -/

/-- THE VIOLATION DATA: one constructor per query — the failed check's
    payload carries the offending key image or the offending ROW, never
    a bare `false`. -/
inductive Violation where
  /-- An account id occurring more than once. -/
  | dupId (k : UInt64)
  /-- An account row whose balance is negative — the row itself. -/
  | negative (r : RowVals accountFields)
  /-- A transfer row whose `src` does not resolve — the row itself. -/
  | danglingSrc (t : RowVals transferFields)
  /-- A transfer row whose `dst` does not resolve — the row itself. -/
  | danglingDst (t : RowVals transferFields)

/-- The violation's rendering (diagnostics + test pins; NOT byte-tied). -/
def Violation.render : Violation → String
  | .dupId k => s!"duplicate account id {k}"
  | .negative r => s!"negative balance: {Pred.renderRow accountFields r}"
  | .danglingSrc t => s!"unresolved src: {Pred.renderRow transferFields t}"
  | .danglingDst t => s!"unresolved dst: {Pred.renderRow transferFields t}"

/-- THE VIOLATION RELATION (executable): the four queries' union, in
    query order. THE STATE INVARIANT's right side is its emptiness. -/
def violations (db : Db) : List Violation :=
  (dupIds (accIds db.accounts)).map Violation.dupId
    ++ (negativeAccounts db.accounts).map Violation.negative
    ++ (danglingSrc db.transfers (accIds db.accounts)).map Violation.danglingSrc
    ++ (danglingDst db.transfers (accIds db.accounts)).map Violation.danglingDst

/-! ## The state invariant — the spec of record -/

/-- THE STATE INVARIANT (the honest Prop): account ids unique, balances
    non-negative, transfer endpoints resolve. This is the spec the
    checker decides — never the checker's shadow of itself. -/
def Valid (db : Db) : Prop :=
  (accIds db.accounts).Nodup
    ∧ (∀ r, r ∈ db.accounts → ¬ (accBal r < 0))
    ∧ (∀ t, t ∈ db.transfers →
        trSrc t ∈ accIds db.accounts ∧ trDst t ∈ accIds db.accounts)

/-- THE STATE-INVARIANT THEOREM (03 §8's composition, both directions):
    the database is valid iff the violation relation is EMPTY. The
    violation query is the invariant's decision — pattern #1's bridge
    at the table tier. -/
theorem valid_iff (db : Db) : Valid db ↔ violations db = [] := by
  constructor
  · intro h
    obtain ⟨hnd, hneg, hfk⟩ := h
    have e1 : dupIds (accIds db.accounts) = [] := dupIds_eq_nil_iff.mpr hnd
    have e2 : negativeAccounts db.accounts = [] :=
      (negativeAccounts_eq_nil_iff db.accounts).mpr hneg
    have e3 : danglingSrc db.transfers (accIds db.accounts) = [] :=
      (dangling_eq_nil_iff trSrc _ _).mpr (fun t ht => (hfk t ht).1)
    have e4 : danglingDst db.transfers (accIds db.accounts) = [] :=
      (dangling_eq_nil_iff trDst _ _).mpr (fun t ht => (hfk t ht).2)
    simp [violations, e1, e2, e3, e4]
  · intro h
    -- `++` is LEFT-associated in `violations`: ((a ++ b) ++ c) ++ d
    obtain ⟨h123, h4⟩ := List.append_eq_nil_iff.mp h
    obtain ⟨h12, h3⟩ := List.append_eq_nil_iff.mp h123
    obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp h12
    refine ⟨?_, ?_, ?_⟩
    · exact dupIds_eq_nil_iff.mp (List.map_eq_nil_iff.mp h1)
    · exact (negativeAccounts_eq_nil_iff db.accounts).mp
        (List.map_eq_nil_iff.mp h2)
    · intro t ht
      exact ⟨(dangling_eq_nil_iff trSrc _ _).mp (List.map_eq_nil_iff.mp h3) t ht,
        (dangling_eq_nil_iff trDst _ _).mp (List.map_eq_nil_iff.mp h4) t ht⟩

end SchemaCore
