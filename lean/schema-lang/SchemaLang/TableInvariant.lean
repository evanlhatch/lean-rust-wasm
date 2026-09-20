/-
# SchemaLang.TableInvariant — table-level invariants via aggregation predicates (W8.8)

The canon row: **a unique/conservation constraint = a table-level
invariant via an aggregation predicate** (canon Part 3; runbook W8.7's
minimal honest set: sum/count/unique). Where the ROW-level lane
(`SchemaLang.Invariant`) predicates on ONE row (`VExpr fields .bool`,
checked per-row in the generated boundary code), this lane predicates
on the whole TABLE (`List (RowVals fields)`) — a row-local check
cannot see the row-set, so the two lanes are different checking tiers
ENTIRELY.

## Where the aggregate check RUNS (the tier answer)

An aggregate check is O(table) over a MATERIALIZED table. The
obligation ladder's rungs (`CodegenCore.Obligation.Tier`), read
against that shape:

- `generatedCheck` (the row lane's `boundaryCheck` rung): a per-row
  emitted fn cannot see the table — structurally unavailable; and the
  byte-tie bars a new emitted artifact this order regardless (no
  emitter reads this registry — the `SchemaLang.Keys` discipline: an
  OWN registry, additive, the emitters' `List Item` fold untouched).
  LOUD `none`.
- `provedAtElab`: the row lane's cited-theorem shape is a ROW verdict
  (`validates e row = true`); a ∀-tables table claim is FALSE for the
  canonical client (conservation holds of REACHABLE tables, not all
  tables — a sabotaged table violates it by construction). The
  preservation theorem (the ledger's `total_post_conserves`) is the
  UPDATE lane's obligation (W8.3's consumer), not a table-invariant
  citation. LOUD `none`.
- `oracleSwept`: unwired (W6.3 phase 3). LOUD `none`.
- `guestVerified`: notes/design-guest-verified.md §7.1 + §9 decision 4
  — table-level aggregations get NO witness in the v1 calculus; the
  tier REFUSES, it never silently degrades. LOUD `none`.
- `decidableNow` — THE COMPUTED RUNG (`TableInvItem.tierOf`): the
  aggregate over a materialized table is a closed Bool computation, so
  the check RUNS where the table is materialized — the caller PRESENTS
  the table to the discharge and the kernel decides (the
  PROVIDED-table shape is the guestVerified arm's PROVIDED-witness
  shape, `SchemaObligation.discharge`, one ladder down). No provided
  table, a FALSE verdict, or a hand-set tier = the loud `none`:
  discharge refuses, it does not fabricate evidence.

The end state (runbook W8.7): the aggregate is a dbsp MEASURE
maintained incrementally (W4.5's linear measure operator — the check
goes O(delta)); that lane is an emitter/circuit event, out of scope
here. The row lane's `Tier` inductive is deliberately NOT extended:
no rung of the ROW-level ladder fits a table predicate (above), and
the kit's `decidableNow` covers the provided-table decide — the
aggregate shape needs no new tier case.

## The surface

- `TableAgg` — `countLe`/`countEq` (cardinality bounds), `sum field
  target` (conservation: a linear equality over ONE u64 stock, summed
  in ℕ — exact, the ledger study's ℤ discipline; the amount's machine
  width is the wire's concern), `unique field` (the row-set is a
  FUNCTION from the field to the row — the Keys lane's
  `FieldVal.nodup` reading, lifted off the declared key to any field).
- `TableInvItem` + `TableAgg.check` — the declaration data + the
  executable predicate over `List (RowVals fields)`.
- `tableInvCheck` — the elaboration-gate checker (String diagnostics,
  the `checkCitation?` precedent — `SchemaDiag` is a closed inductive
  outside this order's file scope).
- `tableInvCheck` / `tableInvWellFormed` + `TableInvsWellFormed` +
  `tableInvCheck_eq_nil_iff` / `tableInvWellFormed_iff` — the Wf lane's
  table sibling: the diagnostic authority, the Bool projection, the
  reasoning authority, and the proved bridge (the `Keys.lean` family,
  mirrored rung for rung).
- `TableInvItem.obligation` / `tableObligations` /
  `TableObligation.discharge` — the obligation view (the kit's
  `Obligation` instantiated at the item), with soundness, completeness,
  and the mis-wire check as theorems.
- `TableInvItem.checkOn` — the existential eliminator (the
  `InvariantItem.checkOn`/`guardCastApply` discipline: a table for
  another schema REFUSES, never misreads).

Ownership: the table-invariant lane (this module +
Meta.TableInvariant's command + registry). Deliberate exclusions:
multi-stock weighted conservation (Σ aᵢ·xᵢ = c — the canon's full
"linear equality over stocks"; v1 is the single-stock instance, the
ledger's shape), non-u64 sum columns (a Ty-typed measure is W4.5's
operator), the four non-computed rungs (above), emitter consumption
(byte-tie), the preservation statement (the update lane's obligation),
composite/multi-field uniqueness (v1: single field, the Keys lane's
granularity).
-/

module

public import SchemaLang.Keys

@[expose] public section

namespace SchemaLang

/-! ## The aggregation shapes -/

/-- The aggregation predicates (the minimal honest set — runbook
    W8.7's sum/count/unique): cardinality bounds over the row count,
    conservation as a single-stock u64 sum equality (ℕ arithmetic —
    exact, no machine-width wrap), uniqueness of a field's images. -/
inductive TableAgg where
  | countLe (bound : Nat)
  | countEq (bound : Nat)
  | sum (field : String) (target : Nat)
  | unique (field : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The aggregation's rendering (diagnostics + test pins). -/
def TableAgg.render : TableAgg → String
  | .countLe b => s!"count ≤ {b}"
  | .countEq b => s!"count = {b}"
  | .sum f t => s!"sum {f} = {t}"
  | .unique f => s!"unique {f}"

instance : ToString TableAgg := ⟨TableAgg.render⟩

/-- The u64 projection chain: EVERY row projects the field and every
    projection IS a u64 (a missing field or a string-typed column is a
    refusal, never a zero — the `guardCastApply` discipline at the
    column level). -/
def columnU64? {fs : List Field} (rows : List (RowVals fs)) (n : String) :
    Option (List UInt64) :=
  rows.mapM fun r =>
    match RowVals.project? fs r n with
    | some ⟨.u64, .u64 v⟩ => some v
    | _ => none

/-- THE CHECK — the invariant's predicate over the table. `countLe`/
    `countEq` read the row count; `sum` projects the column (ℕ-exact)
    and compares against the target; `unique` projects the field and
    demands all-distinct images (`FieldVal.nodup` — the key lane's
    all-distinct, byte-equality via the codec image with the TYPE
    guard). A projection failure refuses (`false`) rather than
    misreads. -/
def TableAgg.check {fs : List Field} (agg : TableAgg) (rows : List (RowVals fs)) :
    Bool :=
  match agg with
  | .countLe b => Nat.ble rows.length b
  | .countEq b => rows.length == b
  | .sum f target =>
      match columnU64? rows f with
      | some vs => (vs.map UInt64.toNat).sum == target
      | none => false
  | .unique f =>
      match rows.mapM (fun r => RowVals.project? fs r f) with
      | some ks => FieldVal.nodup ks
      | none => false

/-! ## The item -/

/-- The registered table-invariant row: the name, the referenced
    record's registry name, the field-list snapshot (the registry read
    — the `SchemaInvariant.fields`/`KeyDecl.fields` precedent: the row
    claims are typed by it, a stale snapshot is a finding not a silent
    re-read), and the aggregation. -/
structure TableInvItem where
  name : String
  schemaRef : String
  fields : List Field
  agg : TableAgg
deriving Repr, BEq, DecidableEq, Inhabited

/-- The safe executor (the `InvariantItem.checkOn` discipline): the
    table's field list must EQUAL the item's — the `DecidableEq` guard
    carries the proof, the check runs on the cast table, a table for
    another schema executes as `false` (type mismatch = refusal). -/
@[irreducible]  -- the W6.13 opacity discipline (`InvariantItem.checkOn`)
def TableInvItem.checkOn {fs : List Field} (ti : TableInvItem)
    (rows : List (RowVals fs)) : Bool :=
  guardCastApply (F := fun fs => List (RowVals fs)) (G := fun _ => Bool) false
    (fun (rows : List (RowVals ti.fields)) => ti.agg.check rows) rows

/-- The match case: at the item's OWN field list the guard collapses
    and the check runs on the table itself (the interface — consumers
    never unfold the irreducible `checkOn`). -/
theorem TableInvItem.checkOn_self (ti : TableInvItem)
    (rows : List (RowVals ti.fields)) :
    ti.checkOn rows = ti.agg.check rows := by
  simp only [TableInvItem.checkOn]  -- the irreducible-safe unfold
  exact guardCastApply_self (F := fun fs => List (RowVals fs)) (G := fun _ => Bool)
    false (fun (rows : List (RowVals ti.fields)) => ti.agg.check rows) rows

/-- The mismatch case: a table for another schema refuses. -/
theorem TableInvItem.checkOn_of_ne {fs : List Field} (ti : TableInvItem)
    (hne : fs ≠ ti.fields) (rows : List (RowVals fs)) :
    ti.checkOn rows = false := by
  simp only [TableInvItem.checkOn]  -- the irreducible-safe unfold
  exact guardCastApply_of_ne (F := fun fs => List (RowVals fs)) (G := fun _ => Bool)
    hne false (fun (rows : List (RowVals ti.fields)) => ti.agg.check rows) rows

/-! ## The elaboration-gate checker (String diagnostics — the `checkCitation?` precedent) -/

/-- The did-you-mean suffix, empty when no candidate is near (the
    `schema_invariant` hint shape). -/
def tableInvDidYouMean (target : String) (cands : List String) : String :=
  let near := CodegenCore.didYouMean target cands
  if near.isEmpty then "" else s!" — did you mean: {String.intercalate ", " near}?"

/-- The referenced-field rung: the aggregation's field resolves on the
    record (FIRST match — the WF lane's reading); `sum` additionally
    demands a u64 column (the conservation arithmetic is ℕ-exact over
    u64 stocks — v1's fragment, the module header's exclusions). -/
def TableAgg.fieldDiags (rec : String) (fields : List Field) : TableAgg → List String
  | .countLe _ | .countEq _ => []
  | .unique f =>
      if fields.any (·.name == f) then []
      else [s!"field `{f}` is not on record `{rec}`"
        ++ tableInvDidYouMean f (fields.map (·.name))]
  | .sum f _ =>
      match fields.find? (·.name == f) with
      | none =>
          [s!"field `{f}` is not on record `{rec}`"
            ++ tableInvDidYouMean f (fields.map (·.name))]
      | some fd =>
          if fd.ty = .u64 then []
          else [s!"field `{f}` has type `{reprStr fd.ty}` — the conservation sum reads a u64 column (v1)"]

/-- One declaration against the universe: the record name must RESOLVE
    to an `Item.record`, the stored field list must BE the record's
    (a stale snapshot is a finding), then the aggregation's field
    rung (against the RECORD's fields — the authority). -/
def TableInvItem.diags (items : List Item) (ti : TableInvItem) : List String :=
  match items.find? (fun it => it.name == ti.schemaRef) with
  | none =>
      [s!"`{ti.schemaRef}` is not a registered record"
        ++ tableInvDidYouMean ti.schemaRef (items.filterMap fun it =>
          match it with | .record n _ => some n | _ => none)]
  | some it =>
      match it with
      | .record _ fields =>
          (if fields = ti.fields then []
           else [s!"the stored field list is stale — `{ti.schemaRef}`'s fields drifted"])
            ++ ti.agg.fieldDiags ti.schemaRef fields
      | _ => [s!"`{ti.schemaRef}` is not a record — table invariants name records"]

/-- The declaration-set check: ALL per-declaration diagnostics + the
    dup scan (one name per invariant). Empty list = well formed; the
    `schema_table_invariant` command runs this SAME checker as its
    elaboration gate (one authority, two mount points — the
    `registerSchemaKeys` pattern). -/
def tableInvCheck (items : List Item) (tis : List TableInvItem) : List String :=
  let ns := tis.map (·.name)
  let dupDiags := (dupNames ns).map
    fun n => s!"duplicate table-invariant name `{n}`"
  tis.flatMap (TableInvItem.diags items) ++ dupDiags

/-- The Bool projection (derived from the diagnostic authority — one
    authority, two readings). -/
def tableInvWellFormed (items : List Item) (tis : List TableInvItem) : Bool :=
  (tableInvCheck items tis).isEmpty

/-! ## The reasoning authority + the bridge (the Wf lane's table sibling)

The `Keys.lean` family, mirrored rung for rung: the checker's String
rungs get Prop mirrors (`TableAggFieldOk` ← `TableAgg.fieldDiags`,
`TableInvOk` ← `TableInvItem.diags`), each with its `_eq_nil_iff`
bridge, packed under `TableInvsWellFormed` and bridged to the Bool
gate by `tableInvWellFormed_iff` (the `universeWellFormed_iff` shape).
-/

/-- The aggregation's field rung as a Prop (the `TableAgg.fieldDiags`
    mirror): a count bound is unconditional; `unique` demands the field
    ON the record (first match — the WF lane's reading); `sum`
    additionally demands the column BE u64 (the ℕ-exact conservation
    fragment). -/
def TableAggFieldOk (rec : String) (fields : List Field) : TableAgg → Prop
  | .countLe _ | .countEq _ => True
  | .unique f => fields.any (·.name == f) = true
  | .sum f _ => ∃ fd, fields.find? (·.name == f) = some fd ∧ fd.ty = .u64

/-- The field rung's bridge. -/
theorem TableAgg.fieldDiags_eq_nil_iff {rec : String} {fields : List Field}
    (agg : TableAgg) :
    agg.fieldDiags rec fields = [] ↔ TableAggFieldOk rec fields agg := by
  cases agg with
  | countLe b => simp [TableAgg.fieldDiags, TableAggFieldOk]
  | countEq b => simp [TableAgg.fieldDiags, TableAggFieldOk]
  | unique f =>
      simp only [TableAgg.fieldDiags, TableAggFieldOk]
      by_cases h : fields.any (·.name == f) = true <;> simp [h]
  | sum f target =>
      simp only [TableAgg.fieldDiags, TableAggFieldOk]
      rcases Option.eq_none_or_eq_some (fields.find? (·.name == f)) with
        hf | ⟨fd, hfd⟩
      · simp only [hf, reduceCtorIdx]
        constructor
        · intro hc; exact absurd hc (List.cons_ne_nil _ _)
        · rintro ⟨fd, h1, _⟩
          nomatch h1
      · rw [hfd]
        by_cases hty : fd.ty = .u64 <;> simp [hty]

/-- One table-invariant declaration as a Prop (the `TableInvItem.diags`
    mirror): the record name RESOLVES to an `Item.record`, the stored
    field list IS the record's (no stale snapshot), and the
    aggregation's field rung holds against the RECORD's fields. -/
def TableInvOk (items : List Item) (ti : TableInvItem) : Prop :=
  ∃ fields : List Field,
    items.find? (fun it => it.name == ti.schemaRef)
      = some (.record ti.schemaRef fields)
    ∧ fields = ti.fields
    ∧ TableAggFieldOk ti.schemaRef fields ti.agg

/-- The per-declaration bridge. -/
theorem TableInvItem.diags_eq_nil_iff {items : List Item} {ti : TableInvItem} :
    ti.diags items = [] ↔ TableInvOk items ti := by
  unfold TableInvItem.diags TableInvOk
  generalize h : items.find? (fun it => it.name == ti.schemaRef) = x
  cases x with
  | none =>
      exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
        fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
  | some it =>
      have h2 := List.find?_some h
      cases it with
      | record rn fields =>
          have hrn : rn = ti.schemaRef := beq_iff_eq.mp h2
          subst hrn
          show ((if fields = ti.fields then ([] : List String)
                  else [s!"the stored field list is stale — `{ti.schemaRef}`'s fields drifted"])
                ++ ti.agg.fieldDiags ti.schemaRef fields) = [] ↔ _
          by_cases hfs : fields = ti.fields
          · rw [if_pos hfs, List.append_eq_nil_iff]
            constructor
            · intro hok
              exact ⟨fields, rfl, hfs,
                (TableAgg.fieldDiags_eq_nil_iff ti.agg).mp hok.right⟩
            · rintro ⟨w, hw, hwt, hok3⟩
              cases hw
              exact ⟨rfl, (TableAgg.fieldDiags_eq_nil_iff ti.agg).mpr hok3⟩
          · rw [if_neg hfs]
            exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
              fun hok => by
                obtain ⟨w, hw, hwt, _⟩ := hok
                cases hw
                exact absurd hwt hfs⟩
      | variant cn cs =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
      | func s =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩
      | resource rn =>
          exact ⟨fun hc => absurd hc (List.cons_ne_nil _ _),
            fun hok => by obtain ⟨w, h1, _⟩ := hok; cases h1⟩

/-- THE REASONING AUTHORITY for table invariants (the `KeysWellFormed`
    sibling): every declaration checks against the universe, and
    invariant names are unique (one name per invariant). -/
def TableInvsWellFormed (items : List Item) (tis : List TableInvItem) : Prop :=
  (∀ ti, ti ∈ tis → TableInvOk items ti) ∧ (tis.map (·.name)).Nodup

/-- Master bridge: the executable authority and the relation agree. -/
theorem tableInvCheck_eq_nil_iff {items : List Item} {tis : List TableInvItem} :
    tableInvCheck items tis = [] ↔ TableInvsWellFormed items tis := by
  have hUC : tableInvCheck items tis =
      tis.flatMap (TableInvItem.diags items)
        ++ (dupNames (tis.map (·.name))).map
          (fun n => s!"duplicate table-invariant name `{n}`") := rfl
  rw [hUC, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    List.map_eq_nil_iff, dupNames_eq_nil_iff]
  constructor
  · intro h
    exact ⟨fun ti hti => TableInvItem.diags_eq_nil_iff.mp (h.1 ti hti), h.2⟩
  · intro h
    exact ⟨fun ti hti => TableInvItem.diags_eq_nil_iff.mpr (h.1 ti hti), h.2⟩

/-- The Bool gate's bridge (`universeWellFormed_iff` shape): the gate's
    `true` eliminates the diagnostic fold's findings AND certifies the
    relation. -/
theorem tableInvWellFormed_iff {items : List Item} {tis : List TableInvItem} :
    tableInvWellFormed items tis = true ↔ TableInvsWellFormed items tis := by
  have hbr := tableInvCheck_eq_nil_iff (items := items) (tis := tis)
  cases hc : tableInvCheck items tis with
  | nil => exact ⟨fun _ => hbr.mp hc, fun _ => by simp [tableInvWellFormed, hc]⟩
  | cons d ds =>
      exact ⟨fun h => by simp [tableInvWellFormed, hc] at h, fun hwf => by
        have hnil := hbr.mpr hwf
        rw [hc] at hnil
        exact absurd hnil (List.cons_ne_nil d ds)⟩

/-! ## The obligation view (what a table invariant MEANS, as data)

The substrate is the kit's `Obligation` (`SchemaLang.Keys`' sibling
lane): a table-invariant declaration produces ONE obligation; the
computed tier is `decidableNow`; the discharge's evidence is the
kernel's decide over a PROVIDED materialized table. -/

/-- The schema-level table-invariant obligation: the kit's shape at
    the item row (`abbrev`, not `def` — reducible, the kit
    discipline). -/
abbrev TableObligation := CodegenCore.Obligation TableInvItem

/-- The computed tier: a table aggregate over a materialized table is
    a closed Bool computation — the `decidableNow` rung (the module
    header's tier answer). No citation lane (a ∀-tables claim is false
    for conservation; preservation is the update lane's theorem) and
    no generated-check lane (byte-tie — no emitter reads this
    registry). -/
def TableInvItem.tierOf : TableInvItem → CodegenCore.Obligation.Tier :=
  fun _ => .decidableNow

/-- The obligation VIEW of one declaration (additive — the declaration
    and the emitters are untouched; the byte-tie holds). Provenance is
    the name as a declaration key (the `SchemaObligation`
    precedent). -/
def TableInvItem.obligation (ti : TableInvItem) : TableObligation :=
  { label := ti.name
  , tier := ti.tierOf
  , payload := ti
  , provenance := ti.name.toName }

/-- The view's tier IS the computed tier. -/
theorem TableInvItem.obligation_tier (ti : TableInvItem) :
    ti.obligation.tier = ti.tierOf := rfl

/-- All table-invariant obligations of a declaration set (the
    enumeration the tests pin). -/
def tableObligations (tis : List TableInvItem) : List TableObligation :=
  tis.map (·.obligation)

/-- THE CLAIM, at a PROVIDED materialized table: the aggregation's
    check holds of THAT table. The table is the discharge's input (the
    guestVerified arm's PROVIDED-witness shape) — the declaration alone
    materializes no canonical table here (the Keys lane's all-default
    singleton is VACUOUS for uniqueness and FALSE for any nonzero
    conservation target; the honest claim is over the table the caller
    is actually checking). -/
abbrev TableObligation.holdsOn (o : TableObligation)
    (table : List (RowVals o.payload.fields)) : Prop :=
  o.payload.agg.check table = true

/-- THE DISCHARGE. A `decidableNow` row's evidence is the kernel's
    verdict over the PROVIDED table (the KIT's verdict combinator
    `decideEvidence`, the claim `holdsOn t`); the other four rungs are
    the loud gap — a hand-set tier the lane cannot name (the module
    header's rung-by-rung reading), a FALSE verdict (a sabotaged
    table), or no provided table — discharge refuses, it does not
    fabricate evidence. -/
def TableObligation.discharge (o : TableObligation)
    (table : Option (List (RowVals o.payload.fields)) := none) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .decidableNow =>
      match table with
      | some t => CodegenCore.Obligation.decideEvidence (o.holdsOn t)
      | none => none
  | .provedAtElab | .generatedCheck | .oracleSwept | .guestVerified => none

/-- SOUNDNESS of the decidableNow backend: a `.decided true` verdict
    on a provided table means the aggregation's check HOLDS of that
    table (the kernel's own computation — no new trust base, no
    fabricated evidence). Routes through the kit's
    `decideEvidence_sound` — the proof object is shared. -/
theorem TableObligation.discharge_decidableNow_sound (o : TableObligation)
    (t : List (RowVals o.payload.fields)) (ht : o.tier = .decidableNow)
    (h : o.discharge (some t) = some (.decided true)) : o.holdsOn t := by
  unfold TableObligation.discharge at h
  rw [ht] at h
  exact CodegenCore.Obligation.decideEvidence_sound h

/-- COMPLETENESS of the decidableNow backend: a table the check holds
    of discharges to the `.decided true` evidence — the backend FIRES
    on the claims it can decide (the tier's `isSome` is not
    vacuous). -/
theorem TableObligation.discharge_decidableNow_of_holds (o : TableObligation)
    (t : List (RowVals o.payload.fields)) (ht : o.tier = .decidableNow)
    (h : o.holdsOn t) :
    o.discharge (some t) = some (.decided true) := by
  unfold TableObligation.discharge
  rw [ht]
  exact CodegenCore.Obligation.decideEvidence_of_claim h

/-- The decidableNow arm's verdict, as the Bool equation it decides
    (`decide` over a Bool equality — the rewrite shape the mis-wire
    check consumes). -/
theorem TableObligation.decideEvidence_holdsOn_eq (o : TableObligation)
    (t : List (RowVals o.payload.fields)) :
    CodegenCore.Obligation.decideEvidence (o.holdsOn t) =
      match o.payload.agg.check t with
      | true => some (.decided true)
      | false => none := by
  unfold TableObligation.holdsOn CodegenCore.Obligation.decideEvidence
  cases hc : o.payload.agg.check t with
  | true => simp [hc]
  | false => simp [hc]

/-- The mis-wire check (the kit's `Evidence.tier` agreement): a fired
    discharge's evidence belongs to the obligation's own tier — only
    `decidableNow` fires at all, so the agreement is the lane's
    totality pin. -/
theorem TableObligation.discharge_tier_agrees (o : TableObligation)
    (table : Option (List (RowVals o.payload.fields)))
    (ev : CodegenCore.Obligation.Evidence)
    (h : o.discharge table = some ev) : ev.tier = o.tier := by
  obtain ⟨label, tier, payload, provenance⟩ := o
  cases tier with
  | decidableNow =>
      cases table with
      | none => simp [TableObligation.discharge] at h
      | some t =>
          simp only [TableObligation.discharge,
            TableObligation.decideEvidence_holdsOn_eq] at h
          cases hc : payload.agg.check t with
          | true =>
              have h2 : some (CodegenCore.Obligation.Evidence.decided true) = some ev := by
                simpa only [TableObligation.discharge, hc] using h
              obtain rfl := Option.some.inj h2
              rfl
          | false => simp [TableObligation.discharge, hc] at h
  | provedAtElab => simp [TableObligation.discharge] at h
  | generatedCheck => simp [TableObligation.discharge] at h
  | oracleSwept => simp [TableObligation.discharge] at h
  | guestVerified => simp [TableObligation.discharge] at h

end SchemaLang
