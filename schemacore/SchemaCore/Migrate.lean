/- # SchemaCore.Migrate — the upcaster derivation + the composition law

Owner: the migration-lane agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §2 (THE LOCAL MIGRATION LAW:
`migration (applyOld s e) = applyNew (migration s) (upcast e)` — replay
preservation follows ONCE by induction; this module LANDS that
induction at the keyed-table rung) + notes/v3/08-capabilities.md §19
(migrations: the diff computes the change set — a Z-set of items;
composition: v1→v2 + v2→v3 = v1→v3; upcasters derived for the closed
change enum; STABLE IDENTITIES REQUIRED) + notes/v3/03-bidirectional.md
§7 (the trichotomy: the upcaster works on DELTAS — the journal replays
them; events are never rewritten in place).

Consumes (never edits): `SchemaCore.Diff` — the change set
(`fieldDiffsOf`), the remedy half (`FieldMigration`/`Migration` +
`Migration.remedies`, the `widenBounded` exemplar with its
per-instance soundness obligation), the verdict (`verdictOf`);
`SchemaCore.Event` — the journal, the replay (the I fold), and the
migration seed (`MigrationSeed`/`replayMigrated?` — the LOUD refusal
for the unwitnessed); `SchemaCore.Delta` — the keyed semantics
(`keyedUpsert`/`keyedErase`/`deltaApply`/`journalApply`).

## The shapes

- `MigrateRefusal` — the derivation's LOUD refusals, each NAMING its
  obligation: a removed field has no value-map target for gone data;
  a retyped field with no matching remedy; a reordered/mid-inserted
  field (v1's derivation is order-aligned — the parallel field walk
  pairs heads); an unstable key (the key field must be carried
  UNCHANGED — 08 §19's stable identities, enforced not assumed); an
  added field whose type has no default (a cap-0 `bounded` is
  uninhabited). There is NO partial migration: the derivation returns
  the plan or the refusal, never both.
- `FieldPlan old new` — the DERIVED upcaster as data: a head-parallel
  plan over the two field lists. Three steps: `carry` (same field),
  `retype` (name-coherent retyped field + the total value map built
  from the registered `FieldMigration` — the GADT index makes a
  renamed field unconstructible), `fill` (an ADDED field at the END of
  the new list, from the type's default). Removals and reorders have
  NO constructor — the derivation refuses them instead (the plan
  grammar is the refusal's type-level face).
- `FieldPlan.upcast` — the value-level migration: rows map through the
  plan (the derived function the remedies determine). `upcastDelta` —
  the event-level upcaster: inserts/updates map their rows; a remove
  rides its key UNCHANGED (stable identities — and `FieldVal` is
  schema-independent, so the GADT cannot catch a lie; `stableKey` +
  the derivation's `keyUnstable` refusal are the guard).
- `FieldPlan.stableKey` — the key-stability premise as decidable data:
  no step retypes, adds, or fills the key field. `toMigration` mounts
  the plan as a `Kit.Migration` between the two keyed-table change
  structures, WITH the local law as its field.
- THE ONE INDUCTION (`FieldPlan.upcast_journalApply`): the migrated
  replay IS the replay of the migrated log —
  `replay key (log.map upΔ) (rows.map up) = (replay key log rows).map up`
  — proved ONCE, by induction over the log, from the per-delta
  commutation (`upcast_deltaApply`), which itself rests on the
  projection-stability lemma (`project_key_stable`). This is 01 §2's
  "replay preservation follows ONCE by induction", landed.
- THE COMPOSITION LAW (`FieldPlan.comp` + `upcast_comp` +
  `compMigrations`): v1→v2 followed by v2→v3 IS v1→v3 — the composed
  plan's upcaster is the composition of the upcasters (the one
  induction over `comp`), and the composed `Kit.Migration`'s local law
  follows from the components' by ONE rewrite chain
  (`compMigrations`), no new induction. HONEST BOUNDARY: the
  composition lives at the UPCASTER level; the remedy REGISTRY is
  per-diff (a v1→v3 diff needs a 42→200 remedy — the two hops'
  42→100 and 100→200 remedies do not match it by type). The tests pin
  both faces.
- The event-lane integration (`MigrationSeed.ofPlan`/`deriveSeed`):
  the derived plan mounts the Event lane's seed — the upcaster is the
  DERIVED one, the witness is the operator's acceptance, and the gate
  still refuses an unwitnessed replay (`replayMigrated?`, consumed
  not copied).

Deliberate exclusions (the leftover rule): mid-list additions and
reorders (the derivation refuses — `fieldReordered`; the stable-id
lane, D13, is the named follow-up); renames (the plan's `retype` ctor
carries name coherence, so a renamed field is unconstructible — the
diff's rename CANDIDACY stays a report line in Diff.lean); key
retypes (refused — a migrated key is a different entity set); wire
bytes for the plan (the seed's upcaster is Lean data; a plan codec
lands with the first remote-migration consumer).

A kernel-opacity note (06 §2): `deriveFieldPlan` is a wf-recursive
definition — runtime-pin it in tests (compiled evaluation), never
`rfl`/`decide` it in the kernel. The LAWS are structural over the
plan GADT and kernel-clean.

The five questions (notes/v3/01-core.md):
- root: Change (01 §2) — the migration ladder's LOCAL LAW, at the
  keyed-table rung, crossed with the journal (TraceModel) through the
  replay.
- carrier grade: the plan GADT (a wrongly-shaped or renamed upcast is
  unconstructible — the index rides the constructor) + the
  `Kit.Migration` mount (the law as a field — a migration without the
  law is not constructible).
- spine reading: the Interpretation stage's migration consumer —
  snapshot (old) vs registry (new) → the derived upcaster → the
  journal's replay.
- ladder rung: the laws are hand theorems over the plan fold (rung 6);
  the derivation is executable data (decide-grade over concrete
  schemas, wf-reduced — runtime-pinned, see the kernel note).
- gate row: SchemaTests' migrateSpec (+ the refusal teeth, the
  mandatory negative controls) + the axiom report.

Core-only (imports Diff + Event — the cone rule; both are
SchemaCore-rooted).
-/

import SchemaCore.Diff
import SchemaCore.Event
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace SchemaCore

/-! ## The refusals (each names its obligation) -/

/-- THE MIGRATION REFUSALS: the derivation returns the plan or one of
    these — never a partial migration (the event lane's refusal
    discipline, at the derivation rung). -/
inductive MigrateRefusal where
  | /-- A field is gone: no value-map target for gone data. -/
    fieldRemoved (item field : String)
  | /-- A field is retyped with no matching registered remedy. -/
    fieldUnremedied (item field : String)
  | /-- Fields reordered (or an addition before the old list is
      exhausted): v1's derivation is order-aligned. -/
    fieldReordered (item field : String)
  | /-- The key field must be carried UNCHANGED (08 §19: stable
      identities required) — a retype or an add at the key refuses. -/
    keyUnstable (item field : String)
  | /-- An added field's type has no default value (a cap-0 `bounded`
      is uninhabited). -/
    noDefault (item field : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The closed universe's small transports -/

/-- The type match as DATA: `some h` carries the propositional
    equality (the closed `Ty` universe's decidable comparison — a
    mismatched remedy is unconstructible downstream, not filtered).
    The `PLift` is the honest box: a proof is a Prop, an `Option` a
    Type. -/
def Ty.eqMatch? (a b : Ty) : Option (PLift (a = b)) :=
  if h : a = b then some (PLift.up h) else none

/-- The type's DEFAULT VALUE (the `fill` source): an honest option —
    a cap-0 `bounded` is uninhabited, so an added field of that type
    has no default and the derivation refuses (`noDefault`). -/
def Ty.migrateDefault : (t : Ty) → Option (Value t)
  | .bool => some (.bool false)
  | .u64 => some (.u64 0)
  | .i64 => some (.i64 0)
  | .string => some (.string "")
  | .option _ => some .none
  | .list _ => some (.list VList.nil)
  | .result ok _ => (Ty.migrateDefault ok).map (fun v => Value.ok v)
  | .map _ _ => some (.map VMap.nil)
  | .set _ => some (.set VList.nil)
  | .bounded cap => if h : 0 < cap then some (.bounded ⟨0, h⟩) else none

/-- A field IS its name and type (the plan's `carry` needs it). -/
theorem Field.eq_of_name_ty {a b : Field} (hn : a.name = b.name)
    (ht : a.ty = b.ty) : a = b := by
  cases a with
  | mk an aty =>
    cases b with
    | mk bnb bty =>
      cases hn
      cases ht
      rfl

/-! ## The plan: the derived upcaster as data -/

/-- THE DERIVED UPCASTER: a head-parallel plan over the old and new
    field lists. `retype` carries name coherence IN the constructor
    (a renamed field is unconstructible); `fill` only ever extends an
    exhausted old list (additions at the END); removals have no
    constructor — the derivation refuses them. -/
inductive FieldPlan : List Field → List Field → Type where
  | /-- Both schemas end: nothing left to map. -/
    nil : FieldPlan [] []
  | /-- The same field on both sides: the value rides unchanged. -/
    carry (f : Field) : FieldPlan old new → FieldPlan (f :: old) (f :: new)
  | /-- A retyped field: the total value map (built from the
      registered `FieldMigration`), the NAME coherence in the type. -/
    retype (fOld fNew : Field) (hname : fOld.name = fNew.name)
      (map : Value fOld.ty → Value fNew.ty) :
      FieldPlan old new → FieldPlan (fOld :: old) (fNew :: new)
  | /-- An ADDED field (the old list is exhausted): every old row
      fills the default. -/
    fill (f : Field) (v : Value f.ty) : FieldPlan [] new → FieldPlan [] (f :: new)

/-- THE VALUE-LEVEL UPCASTER: rows map through the plan (the derived
    function the remedies determine — positional, total). -/
def FieldPlan.upcast : {old new : List Field} →
    FieldPlan old new → RowVals old → RowVals new
  | _, _, .nil, .nil => .nil
  | _, _, .carry _ p, .cons v vs => .cons v (upcast p vs)
  | _, _, .retype _ _ _ m p, .cons v vs => .cons (m v) (upcast p vs)
  | _, _, .fill _ v p, .nil => .cons v (upcast p .nil)

/-- THE EVENT-LEVEL UPCASTER: inserts/updates map their rows through
    the plan; a remove rides its key UNCHANGED (stable identities —
    valid exactly under `stableKey`, which the derivation enforces). -/
def FieldPlan.upcastDelta {old new : List Field} (p : FieldPlan old new) :
    RowDelta old → RowDelta new
  | .insert r => .insert (p.upcast r)
  | .update r => .update (p.upcast r)
  | .remove k => .remove k

/-- The key-stability premise, as decidable data: no step retypes,
    adds, or fills the key field — the key column is carried verbatim
    (08 §19: stable identities required). -/
def FieldPlan.stableKey (key : String) :
    {old new : List Field} → FieldPlan old new → Bool
  | _, _, .nil => true
  | _, _, .carry _ p => stableKey key p
  | _, _, .retype _ fN _ _ p => !(fN.name == key) && stableKey key p
  | _, _, .fill f _ p => !(f.name == key) && stableKey key p

/-! ## The key-stability laws (the local law's substrate) -/

/-- The projection is STABLE under a key-stable upcast: the key
    column's image is identical before and after (the plan carries the
    key field verbatim — one induction over the plan). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.project_key_stable (key : String) :
    ∀ {old new : List Field} (p : FieldPlan old new),
      p.stableKey key = true → ∀ r : RowVals old,
        RowVals.project? new (p.upcast r) key = RowVals.project? old r key := by
  intro old new p
  induction p with
  | nil =>
      intro _ r
      cases r
      rfl
  | carry f p ih =>
      intro h r
      cases r with
      | cons v vs =>
          have h' : p.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h
          show RowVals.project? _ (.cons v (p.upcast vs)) key
            = RowVals.project? _ (.cons v vs) key
          simp only [RowVals.project?]
          by_cases hf : (f.name == key) = true
          · simp only [if_pos hf]
          · simp only [if_neg hf]
            exact ih h' vs
  | retype fO fN hn m p ih =>
      intro h r
      cases r with
      | cons v vs =>
          simp only [FieldPlan.stableKey, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          have hnfN : ¬((fN.name == key) = true) := by
            cases hb : (fN.name == key) with
            | false => simp
            | true => rw [hb] at h1; simp at h1
          have hnfO : ¬((fO.name == key) = true) := by rw [hn]; exact hnfN
          show RowVals.project? _ (.cons (m v) (p.upcast vs)) key
            = RowVals.project? _ (.cons v vs) key
          simp only [RowVals.project?, if_neg hnfN, if_neg hnfO]
          exact ih h2 vs
  | fill f v p ih =>
      intro h r
      cases r
      simp only [FieldPlan.stableKey, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hnf : ¬((f.name == key) = true) := by
        cases hb : (f.name == key) with
        | false => simp
        | true => rw [hb] at h1; simp at h1
      show RowVals.project? _ (.cons v (p.upcast .nil)) key
        = RowVals.project? _ .nil key
      simp only [RowVals.project?, if_neg hnf, ih h2 .nil]

/-- The key match is stable (the upsert gate's premise). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.sameKey_stable (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true)
    (a b : RowVals old) :
    sameKey key a b = sameKey key (p.upcast a) (p.upcast b) := by
  unfold sameKey
  rw [FieldPlan.project_key_stable key p h a,
      FieldPlan.project_key_stable key p h b]

/-- The key-image match is stable (the erase gate's premise). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.sameKeyImg_stable (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true)
    (row : RowVals old) (k : FieldVal) :
    sameKeyImg key row k = sameKeyImg key (p.upcast row) k := by
  unfold sameKeyImg
  rw [FieldPlan.project_key_stable key p h row]

/-! ## The per-delta commutation + THE ONE INDUCTION -/

/-- The keyed UPSERT commutes with a key-stable upcast (one induction
    over the table, the projection-stability lemma at the gate). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_keyedUpsert (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true) (r : RowVals old) :
    ∀ rows : List (RowVals old),
      keyedUpsert key (p.upcast r) (rows.map p.upcast)
        = (keyedUpsert key r rows).map p.upcast
  | [] => rfl
  | row :: rs => by
      simp only [keyedUpsert, List.map_cons]
      rw [← FieldPlan.sameKey_stable key p h row r]
      by_cases hc : sameKey key row r = true
      · simp [hc]
      · simp only [if_neg hc]
        simp [FieldPlan.upcast_keyedUpsert key p h r rs]

/-- The keyed ERASE commutes with a key-stable upcast (the mirror). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_keyedErase (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true) (k : FieldVal) :
    ∀ rows : List (RowVals old),
      keyedErase key k (rows.map p.upcast)
        = (keyedErase key k rows).map p.upcast
  | [] => rfl
  | row :: rs => by
      simp only [keyedErase, List.map_cons]
      rw [← FieldPlan.sameKeyImg_stable key p h row k]
      by_cases hc : sameKeyImg key row k = true
      · simp [hc]
      · simp only [if_neg hc]
        simp [FieldPlan.upcast_keyedErase key p h k rs]

/-- The per-delta law: `upcast (applyOld rows d) = applyNew (upcast rows) (upΔ d)`
    — the LOCAL MIGRATION EQUATION's per-event face (01 §2). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_deltaApply (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true) (d : RowDelta old)
    (rows : List (RowVals old)) :
    deltaApply key (p.upcastDelta d) (rows.map p.upcast)
      = (deltaApply key d rows).map p.upcast := by
  cases d with
  | insert r => exact FieldPlan.upcast_keyedUpsert key p h r rows
  | update r => exact FieldPlan.upcast_keyedUpsert key p h r rows
  | remove k => exact FieldPlan.upcast_keyedErase key p h k rows

/-- THE ONE INDUCTION (01 §2: "replay preservation follows ONCE by
    induction"): the migrated replay IS the replay of the migrated
    log. The whole replay-preservation content of the migration lane,
    discharged here once for every derived plan. -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_journalApply (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true) :
    ∀ (log : List (RowDelta old)) (rows : List (RowVals old)),
      journalApply key (log.map p.upcastDelta) (rows.map p.upcast)
        = (journalApply key log rows).map p.upcast
  | [], rows => rfl
  | d :: rest, rows => by
      show journalApply key (p.upcastDelta d :: rest.map p.upcastDelta)
            (rows.map p.upcast)
        = (journalApply key rest (deltaApply key d rows)).map p.upcast
      rw [show journalApply key (p.upcastDelta d :: rest.map p.upcastDelta)
              (rows.map p.upcast)
            = journalApply key (rest.map p.upcastDelta)
                (deltaApply key (p.upcastDelta d) (rows.map p.upcast)) from rfl,
        FieldPlan.upcast_deltaApply key p h d rows,
        FieldPlan.upcast_journalApply key p h rest (deltaApply key d rows)]

/-- The doctrine's replay spelling of the same law. -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_replay (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true)
    (log : List (RowDelta old)) (rows : List (RowVals old)) :
    replay key (log.map p.upcastDelta) (rows.map p.upcast)
      = (replay key log rows).map p.upcast :=
  FieldPlan.upcast_journalApply key p h log rows

/-- The plan mounted as a `Kit.Migration` between the two keyed-table
    change structures — the law field is THE LOCAL LAW (01 §2), not a
    separate claim: `d.apply (migrate s) (upcast e) = (c.apply s e).map migrate`
    holds by the one induction above. -/
def FieldPlan.toMigration (key : String) {old new : List Field}
    (p : FieldPlan old new) (h : p.stableKey key = true) :
    Kit.Migration
      (journalApplicable key (fs := old)).toComposable.toApplicable
      (journalApplicable key (fs := new)).toComposable.toApplicable where
  migrate rows := rows.map p.upcast
  upcast log := log.map p.upcastDelta
  localLaw rows log := by
    show some (journalApply key (log.map p.upcastDelta) (rows.map p.upcast))
      = (some (journalApply key log rows)).map (fun t => t.map p.upcast)
    rw [FieldPlan.upcast_journalApply key p h log rows]
    rfl

/-! ## THE COMPOSITION LAW (08 §19): v1→v2 + v2→v3 = v1→v3 -/

/-- The composed plan: the two hops' head-parallel walks fuse. The
    composite's `retype` chains the value maps; a mid-hop `fill`'s
    default flows through the next hop's step. (The grammar's totality
    is exactly the derivable-plan shape: `fill` only at an exhausted
    old list — the pruned arms are index-impossible.) -/
def FieldPlan.comp : {old mid new : List Field} →
    FieldPlan mid new → FieldPlan old mid → FieldPlan old new
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .carry f p23, .carry _ p12 => .carry f (comp p23 p12)
  | _, _, _, .carry f p23, .retype fO _ hn m p12 =>
      .retype fO f hn m (comp p23 p12)
  | _, _, _, .carry f p23, .fill _ v p12 => .fill f v (comp p23 p12)
  | _, _, _, .retype fM fN hn m p23, .carry _ p12 =>
      .retype fM fN hn m (comp p23 p12)
  | _, _, _, .retype _ fN hn23 m23 p23, .retype fO _ hn12 m12 p12 =>
      .retype fO fN (hn12.trans hn23) (fun v => m23 (m12 v)) (comp p23 p12)
  | _, _, _, .retype _ fN _ m23 p23, .fill _ v p12 =>
      .fill fN (m23 v) (comp p23 p12)
  | _, _, _, .fill f v p23, .nil => .fill f v (comp p23 .nil)

/-- Key stability survives composition (the composed plan can mount
    `toMigration` too). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.stableKey_comp (key : String) {old mid new : List Field} :
    ∀ (p23 : FieldPlan mid new) (p12 : FieldPlan old mid),
      p23.stableKey key = true → p12.stableKey key = true →
        (FieldPlan.comp p23 p12).stableKey key = true := by
  intro p23
  induction p23 generalizing old with
  | nil =>
      intro p12 _ _
      cases p12
      rfl
  | carry f p ih =>
      intro p12 h23 h12
      have h23' : p.stableKey key = true := by
        simpa [FieldPlan.stableKey] using h23
      cases p12 with
      | carry _ p12 =>
          have h12' : p12.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h12
          simp only [FieldPlan.comp, FieldPlan.stableKey]
          exact ih p12 h23' h12'
      | retype fO fM hn m p12 =>
          have hx : (!(f.name == key)) = true ∧ p12.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h12
          simp only [FieldPlan.comp, FieldPlan.stableKey, hx.1,
            ih p12 h23' hx.2, Bool.and_true]
      | fill _ v p12 =>
          have hx : (!(f.name == key)) = true ∧ p12.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h12
          simp only [FieldPlan.comp, FieldPlan.stableKey, hx.1,
            ih p12 h23' hx.2, Bool.and_true]
  | retype fM fN hn m p ih =>
      intro p12 h23 h12
      have h23x : (!(fN.name == key)) = true ∧ p.stableKey key = true := by
        simpa [FieldPlan.stableKey] using h23
      cases p12 with
      | carry _ p12 =>
          have h12' : p12.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h12
          simp only [FieldPlan.comp, FieldPlan.stableKey, h23x.1,
            ih p12 h23x.2 h12', Bool.and_true]
      | retype fO fM' hn12 m12 p12 =>
          have hx : p12.stableKey key = true := by
            have hx' := h12
            simp only [FieldPlan.stableKey, Bool.and_eq_true] at hx'
            exact hx'.2
          simp only [FieldPlan.comp, FieldPlan.stableKey, h23x.1,
            ih p12 h23x.2 hx, Bool.and_true]
      | fill _ v p12 =>
          have hx : p12.stableKey key = true := by
            have hx' := h12
            simp only [FieldPlan.stableKey, Bool.and_eq_true] at hx'
            exact hx'.2
          simp only [FieldPlan.comp, FieldPlan.stableKey, h23x.1,
            ih p12 h23x.2 hx, Bool.and_true]
  | fill f v p ih =>
      intro p12 h23 _
      cases p12 with
      | nil =>
          have h23x : (!(f.name == key)) = true ∧ p.stableKey key = true := by
            simpa [FieldPlan.stableKey] using h23
          simp only [FieldPlan.comp, FieldPlan.stableKey, h23x.1,
            ih (FieldPlan.nil : FieldPlan [] []) h23x.2 rfl, Bool.and_true]

/-- THE COMPOSITION LAW, value level: the composed plan's upcaster IS
    the composition of the upcasters — the ONE induction (over `comp`),
    no new proof content per hop. -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcast_comp {old mid new : List Field} :
    ∀ (p23 : FieldPlan mid new) (p12 : FieldPlan old mid) (r : RowVals old),
      (FieldPlan.comp p23 p12).upcast r = p23.upcast (p12.upcast r) := by
  intro p23
  induction p23 generalizing old with
  | nil =>
      intro p12 r
      cases p12
      cases r
      rfl
  | carry f p ih =>
      intro p12 r
      cases p12 with
      | carry _ p12 =>
          cases r with
          | cons v vs =>
              simp only [FieldPlan.comp, FieldPlan.upcast]
              rw [ih p12 vs]
      | retype fO fM hn m p12 =>
          cases r with
          | cons v vs =>
              simp only [FieldPlan.comp, FieldPlan.upcast]
              rw [ih p12 vs]
      | fill g v p12 =>
          cases r
          simp only [FieldPlan.comp, FieldPlan.upcast]
          rw [ih p12 .nil]
  | retype fM fN hn m p ih =>
      intro p12 r
      cases p12 with
      | carry _ p12 =>
          cases r with
          | cons v vs =>
              simp only [FieldPlan.comp, FieldPlan.upcast]
              rw [ih p12 vs]
      | retype fO fM' hn12 m12 p12 =>
          cases r with
          | cons v vs =>
              simp only [FieldPlan.comp, FieldPlan.upcast]
              rw [ih p12 vs]
      | fill g v p12 =>
          cases r
          simp only [FieldPlan.comp, FieldPlan.upcast]
          rw [ih p12 .nil]
  | fill f v p ih =>
      intro p12 r
      cases p12 with
      | nil =>
          cases r
          simp only [FieldPlan.comp, FieldPlan.upcast]
          rw [ih (FieldPlan.nil : FieldPlan [] []) .nil]
          rfl

/-- The composition law, event level: the composed plan's upcaster is
    the composition (the rows ride the SAME induction). -/
@[nolint linter.guestlang.zeroCitation "public API: the migration lane's law layer (Migrate.lean's module doc — THE ONE INDUCTION / the composition laws; the runtime face is exercised by SchemaTests.Migrate)"]
theorem FieldPlan.upcastDelta_comp {old mid new : List Field}
    (p23 : FieldPlan mid new) (p12 : FieldPlan old mid) (d : RowDelta old) :
    (FieldPlan.comp p23 p12).upcastDelta d
      = p23.upcastDelta (p12.upcastDelta d) := by
  cases d with
  | insert r => simp [upcastDelta, upcast_comp p23 p12]
  | update r => simp [upcastDelta, upcast_comp p23 p12]
  | remove k => rfl

/-- THE MIGRATION COMPOSITION at the `Kit.Migration` level (generic):
    the composite's local law follows from the components' by ONE
    rewrite chain — 01 §2's ladder, 08 §19's v1→v3. -/
def compMigrations {S₀ Δ₀ S₁ Δ₁ S₂ Δ₂}
    (c : Kit.Applicable S₀ Δ₀) (d : Kit.Applicable S₁ Δ₁)
    (e : Kit.Applicable S₂ Δ₂)
    (m₁ : Kit.Migration c d) (m₂ : Kit.Migration d e) : Kit.Migration c e where
  migrate s := m₂.migrate (m₁.migrate s)
  upcast x := m₂.upcast (m₁.upcast x)
  localLaw s x := by
    show e.apply (m₂.migrate (m₁.migrate s)) (m₂.upcast (m₁.upcast x))
      = (c.apply s x).map (fun s' => m₂.migrate (m₁.migrate s'))
    rw [m₂.localLaw (m₁.migrate s) (m₁.upcast x), m₁.localLaw s x]
    cases h : c.apply s x <;> simp

/-! ## The derivation: the diff's change set + the remedies → the plan -/

/-- One finding's remedied-ness: additions are safe; a removal or a
    retype is unremedied when NO registered migration remedies it
    (consumes `Migration.remedies` — one notion of "remedied"). -/
def fieldDiffUnremedied (item : String) (ms : List Migration) :
    FieldDiff → Bool
  | .fieldAdded _ => false
  | fd => !(ms.any fun m => m.remedies (.changed item [fd]))

/-- The FIRST unremedied finding (the derivation's refusal, named) —
    `none` when the registered remedies cover the change set. -/
def firstUnremedied? (item : String) (fds : List FieldDiff)
    (ms : List Migration) : Option FieldDiff :=
  fds.find? (fieldDiffUnremedied item ms)

/-- The registered remedy, transported to the FOUND field's types (the
    derivation's retype lane; `none` = the remedy's types do not match
    the finding). The casts are the closed universe's definitional
    transports — `h.down` unpacks the `PLift`'d equality. -/
def FieldMigration.at? (fm : FieldMigration) (tOld tNew : Ty) :
    Option (Value tOld → Value tNew) :=
  match Ty.eqMatch? tOld fm.oldTy with
  | none => none
  | some h1 =>
      match Ty.eqMatch? tNew fm.newTy with
      | none => none
      | some h2 =>
          some fun v =>
            cast (congrArg Value h2.down.symm)
              (fm.apply (cast (congrArg Value h1.down) v))

/-- THE DERIVATION WALK: the head-parallel plan from the registered
    remedies. Total: the plan or a named `MigrateRefusal` (never a
    partial migration). The walk re-checks everything the diff saw —
    the positional face the name-keyed diff cannot see (a reordered
    schema diffs CLEAN and still refuses here; the test pins it).
    wf-recursive — runtime-pin only (06 §2's kernel-opacity note). -/
def deriveFieldPlan (item : String) (key : String)
    (remedies : List FieldMigration) (old new : List Field) :
    Except MigrateRefusal (FieldPlan old new) :=
  match old, new with
  | [], [] => .ok .nil
  | [], fN :: new' =>
      if fN.name == key then .error (.keyUnstable item fN.name)
      else
        match Ty.migrateDefault fN.ty with
        | some v =>
            FieldPlan.fill fN v <$> deriveFieldPlan item key remedies [] new'
        | none => .error (.noDefault item fN.name)
  | fO :: _, [] => .error (.fieldRemoved item fO.name)
  | fO :: old', fN :: new' => by
      by_cases hname : fO.name = fN.name
      · by_cases hty : fO.ty = fN.ty
        · -- the same field (a Field IS its name + ty): carried
          have hfEq : fO = fN := Field.eq_of_name_ty hname hty
          subst hfEq
          exact FieldPlan.carry _ <$> deriveFieldPlan item key remedies old' new'
        · -- names equal, types differ: the RETYPE lane — the remedy
          -- lookup transports the registered map to the found types
          cases hk : fN.name == key with
          | true => exact .error (.keyUnstable item fN.name)
          | false =>
              exact
                (match
                    (remedies.filter (fun fm => fm.field == fN.name)).filterMap
                      (fun fm => fm.at? fO.ty fN.ty) |>.head? with
                  | some m =>
                      FieldPlan.retype fO fN hname m <$>
                        deriveFieldPlan item key remedies old' new'
                  | none => .error (.fieldUnremedied item fN.name))
      · exact .error (.fieldReordered item fO.name)
termination_by old.length + new.length

/-- THE UPCASTER DERIVATION (08 §19): the diff computes the change
    set; the registered remedies cover it; the derivation returns the
    plan. The pre-check consumes `Migration.remedies` directly — the
    first unremedied finding IS the refusal, with its field named.
    (The walk's positional refusals remain live behind it: the diff is
    name-keyed and order-free, the plan is positional.) -/
def deriveUpcaster (key : String) (ms : List Migration)
    (oldIt newIt : Item) : Except MigrateRefusal (FieldPlan oldIt.fields newIt.fields) :=
  match firstUnremedied? oldIt.name (fieldDiffsOf oldIt newIt) ms with
  | none =>
      let remedies :=
        (ms.find? fun m => m.item == oldIt.name).map (·.fields) |>.getD []
      deriveFieldPlan oldIt.name key remedies oldIt.fields newIt.fields
  | some (.fieldRemoved n) => .error (.fieldRemoved oldIt.name n)
  | some (.fieldTypeChanged n _ _) => .error (.fieldUnremedied oldIt.name n)
  -- unreachable: `firstUnremedied?`'s predicate filters additions out;
  -- the arm is the match's totality, not a path
  | some (.fieldAdded n) => .error (.fieldUnremedied oldIt.name n)

/-! ## The event-lane integration (the seed consumes the derivation) -/

/-- The derived plan mounts the event lane's `MigrationSeed`: the
    upcaster is the DERIVED one, the witness is the operator's
    acceptance — the gate (`replayMigrated?`) still refuses an
    unwitnessed replay. Consumed, not copied. -/
def MigrationSeed.ofPlan {old new : List Field} (p : FieldPlan old new)
    (label witness : String) : MigrationSeed old new where
  label := label
  upcast := p.upcastDelta
  witness? := some witness

/-- The FULL derivation: diff → remedies → plan → the event lane's
    seed. The journal replays through `replayMigrated?` under the
    witness; the replay discipline is Event.lean's, the upcaster is
    this lane's. -/
def deriveSeed (key : String) (ms : List Migration) (oldIt newIt : Item)
    (label witness : String) :
    Except MigrateRefusal (MigrationSeed oldIt.fields newIt.fields) :=
  deriveUpcaster key ms oldIt newIt |>.map fun p =>
    MigrationSeed.ofPlan p label witness

end SchemaCore

/-! ## the module's law-summary (the honest ledger)

PROVED: `Field.eq_of_name_ty`, `FieldPlan.project_key_stable` (the
projection's stability — the key-stability substrate),
`sameKey_stable`/`sameKeyImg_stable`, `upcast_keyedUpsert`/
`upcast_keyedErase` (the keyed semantics commutes with a key-stable
upcast), `upcast_deltaApply` (the LOCAL LAW's per-event face),
`upcast_journalApply`/`upcast_replay` (THE ONE INDUCTION — replay
preservation), `toMigration` (the law as the mount's field),
`stableKey_comp` (the premise survives composition), `upcast_comp`/
`upcastDelta_comp` (the composition law: two hops ≡ the composed plan,
ONE induction), `compMigrations` (the composed local law from the
components', one rewrite chain). NO `sorry`, NO `axiom`.

Honest residue: the derivation's own correctness (deriveFieldPlan
returns a stableKey plan / matches the diff's findings) is
RUNTIME-PINNED in SchemaTests, not proved — the wf recursion makes the
induction kernel-hostile and the pins cover every refusal arm; the
remedy REGISTRY is per-diff (the composition lives at the upcaster —
the v1→v3 direct diff needs its own remedy; the tests pin the
boundary). Mid-list additions/reorders and key retypes REFUSE (loud);
the stable-id lane is the named follow-up.
-/
