/-
# SchemaCore.Diff — the snapshot-pair diff + the breaking verdict + the remedy seed

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §2 (names are
presentation — the rename honesty) + §7 (a DELTA is a NET change — the
diff erases intermediate history) + decisions.md D13 (migration
discovery needs stable identities — the stable-id lane is the NAMED
follow-up, the honest first cut flags a delete+add pair as a possible
rename candidate in the report, never silently merges) +
notes/v3/15-patterns.md #1 (relation-as-spec + executable checker +
proved bridge) and #5 (the mandatory negative controls).

Mined from `legacy/lean/schema-lang/SchemaLang/Diff.lean` (the
`Diff.diff`/`backwardCompatible_iff` shape — ported at the slice's
`Item` = record-of-fields universe) + `Migration.lean` (the
`FieldMigration` remedy half, `CompatVerdict`, the exit-code
discipline, the worked exemplar) + `BreakingMain.lean` (the gate's
verdict/exit contract).

## The shapes

- `Diff.diff old new : List Change` — the item-level NET change between
  two snapshots over the name key: removals, then changes (with the
  field-level evidence), then additions. A name in both trees
  contributes at most one finding; a name changed twice within a batch
  leaves ONE net finding (03 §7: the diff is the net change —
  intermediate history is erased by design; the EVENT log, not the
  delta, carries history).
- `backwardCompatible` — the compatibility relation: every old
  well-formed state maps forward. Over the name-keyed item change set
  the honest first cut: additions are replay-safe (no old data
  references them); a removal or reshape strands old readers. The
  `backwardCompatible_iff` bridge is pattern #1 (the spec's two faces).
- `CompatVerdict` + `verdictOf` + `exitCode` — the three-way verdict
  (clean / remedied / unremedied) and the gate's exit semantics:
  clean → 0; remedied → 0 WITH the remedy evidence named in the
  report (shippable, but apply the migration + re-baseline);
  unremedied → 2 — the LOUD warning (`just gates` fails on 2).
- `FieldMigration` — the remedy half: a retyped field plus its TOTAL
  value map as Lean data (`Value oldTy → Value newTy` — the function's
  TYPE is the soundness shape), and the per-instance obligation: the
  diagram `eval ∘ apply = the same number` commutes (the exemplar:
  `widenBounded_sound`). Removals are honestly UNREMEDIED (no value-map
  target for gone data — the honest verdict, not an oversight).

Deliberate: NO new E-codes here. The diff/verdict is total data — it
has no failure KINDS; the gate's refusals (absent/corrupt baseline)
ride the snapshot parser's SN registry codes + the gate's loud lines.
A new failure kind would allocate an `SB` family in the persisted
registry first.

Stable identities (D13): the tree's items are NAME-keyed TODAY. A
delete+add pair with agreeing field contents is a POSSIBLE rename —
`renameCandidates` names it in the report; the diff NEVER merges it
(the stable-id lane lands when the first consumer needs rename
CERTAINTY, not candidacy).

Core-only (imports Kit-riding SchemaCore only — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Change — the net state change between two universe snapshots
  (03 §7's delta face, at the universe level).
- carrier grade: first-order data over the closed `Ty`/`Item` universe;
  the laws are PROVED over concrete lists (pattern #1's bridge).
- spine reading: the Interpretation stage's OTHER consumer — snapshot
  (old) vs registry replay (new) → the verdict.
- ladder rung: `decide`-grade — the verdict over concrete snapshots
  reduces by `rfl`/`decide`.
- gate row: `gates breaking` (the exit-code discipline IS the row).
-/

import SchemaCore.Item
import SchemaCore.Snapshot
import SchemaCore.Value

namespace SchemaCore

/-! ## The field-level finding (the evidence a migration tool needs) -/

/-- One field-level finding between two same-name items: not just
    "changed" but WHICH field was added, removed, or retyped — the old
    and new type both carried. -/
inductive FieldDiff where
  | fieldAdded (name : String)
  | fieldRemoved (name : String)
  | fieldTypeChanged (name : String) (oldTy newTy : Ty)
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString FieldDiff where
  toString
    | .fieldAdded n => s!"added field {n}"
    | .fieldRemoved n => s!"removed field {n}"
    | .fieldTypeChanged n oldTy newTy =>
        s!"field {n}: {tyText oldTy} → {tyText newTy}"

/-- The field-level evidence between two same-name items, old-field
    order first (removals, then type changes), then additions in new
    order. The type comparison is the DERIVED equality over the closed
    `Ty` universe — the slice has no open-world reference to compare
    through (Ty.lean's header note). -/
def fieldDiffsOf (prev it : Item) : List FieldDiff :=
  let newNames := it.fields.map (·.name)
  let oldNames := prev.fields.map (·.name)
  let removed := prev.fields.filterMap fun f =>
    if newNames.contains f.name then none else some (.fieldRemoved f.name)
  let changed := prev.fields.filterMap fun f =>
    match it.fields.find? (fun g => g.name == f.name) with
    | some g => if f.ty == g.ty then none else some (.fieldTypeChanged f.name f.ty g.ty)
    | none => none
  let added := it.fields.filterMap fun f =>
    if oldNames.contains f.name then none else some (.fieldAdded f.name)
  removed ++ changed ++ added

/-! ## The change set (the Z-set discipline: the NET change) -/

/-- One compatibility finding between two universe versions. -/
inductive Change where
  | removed (name : String)            -- was referenceable, is gone: BREAKING
  | added (name : String)              -- new item: safe
  | changed (name : String) (fieldDiffs : List FieldDiff)  -- same name, different shape: BREAKING, with field evidence
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString Change where
  toString
    | .removed n => s!"removed {n}"
    | .added n => s!"added {n}"
    | .changed n fds => s!"changed {n} ({String.intercalate "; " (fds.map toString)})"

/-- The universe diff: the NET change between two snapshots over the
    name key (03 §7 — a delta erases intermediate history). Findings in
    the legacy order: removals, changes, additions (input order within
    each). A same-name pair with identical fields contributes NOTHING —
    the net discipline's zero. -/
def diff (old new : List Item) : List Change :=
  let newNames := new.map (·.name)
  let oldNames := old.map (·.name)
  let removed := old.filter (fun it => !newNames.contains it.name)
    |>.map (fun it => Change.removed it.name)
  let added := new.filter (fun it => !oldNames.contains it.name)
    |>.map (fun it => Change.added it.name)
  let changed := new.filterMap fun it =>
    match old.find? (fun o => o.name == it.name) with
    | some prev =>
        let fds := fieldDiffsOf prev it
        if fds = [] then none else some (.changed it.name fds)
    | none => none
  removed ++ changed ++ added

/-! ## The rename honesty (D13: names are presentation) -/

/-- A removed+added PAIR whose field contents agree exactly — a
    possible rename. The diff NEVER merges it (the tree's items are
    name-keyed; the stable-id lane is the named follow-up); the REPORT
    names the candidacy so a human decides. -/
def renameCandidates (old new : List Item) : List (String × String) :=
  let oldNames := old.map (·.name)
  let added := new.filter (fun it => !oldNames.contains it.name)
  old.filterMap fun o =>
    (added.find? fun n => o.fields == n.fields).map fun n => (o.name, n.name)

/-! ## The compatibility relation + the bridge (pattern #1) -/

/-- True iff `new` is backward-compatible with `old` (nothing removed,
    nothing reshaped). Additions are safe. THE RELATION'S READING: every
    old well-formed state maps forward — an addition needs no map (no
    old data references it); a removal or reshape leaves old data (and
    old readers) stranded, which is exactly the breaking surface. -/
def backwardCompatible (old new : List Item) : Bool :=
  let d := diff old new
  d.all fun c => match c with | .added _ => true | _ => false

/-- The pointwise reading of `backwardCompatible`'s fold. -/
theorem Change.added_of_true {c : Change} :
    (match c with | .added _ => true | _ => false) = true ↔ ∃ n, c = .added n := by
  cases c <;> simp

/-- THE BRIDGE: `backwardCompatible` is the clean-verdict reading of the
    diff — true iff EVERY finding is an addition, i.e. iff the breaking
    subset is empty. One authority — the `diff` change list — two
    readings (15 #1: relation-as-spec + checker + proved bridge). -/
theorem backwardCompatible_iff {old new : List Item} :
    backwardCompatible old new = true ↔
      ∀ c ∈ diff old new, ∃ n, c = .added n := by
  simp only [backwardCompatible, List.all_eq_true]
  constructor
  · intro h c hc; exact Change.added_of_true.mp (h c hc)
  · intro h c hc; exact Change.added_of_true.mpr (h c hc)

/-! ## The remedy half (the migration carries its soundness obligation) -/

/-- One field remedy: a retyped field plus its TOTAL value map, as Lean
    data, typed by the schema types themselves — the function's TYPE is
    the soundness shape (`oldTy` values in, `newTy` values out, no
    partiality expressible; the GADT `Value` index makes a mismatched
    payload unconstructible). The obligation `eval ∘ apply = the same
    number` is discharged PER INSTANCE (see `widenBounded_sound`) — a
    remedy without its soundness theorem is not a remedy. -/
structure FieldMigration where
  /-- the field on the CHANGED item this remedies -/
  field : String
  oldTy : Ty
  newTy : Ty
  apply : Value oldTy → Value newTy

/-- Remedy evidence for ONE breaking-changed item: per retyped field,
    the total old→new value map. -/
structure Migration where
  /-- the item name (matches `Change.changed n _`) -/
  item : String
  /-- per-field remedies, keyed by the CHANGED field's name -/
  fields : List FieldMigration

/-- Does this migration REMEDY a change? A `.changed` is remedied when
    every breaking field finding has a matching remedy (the retyped
    field, with exactly the found old/new types). Additions are safe
    (no old data exists to map); REMOVALS ARE HONESTLY UNREMEDIED (no
    value-map target for gone data). -/
def Migration.remedies (m : Migration) (c : Change) : Bool :=
  match c with
  | .added _ => true
  | .removed _ => false
  | .changed n fds =>
      n == m.item && fds.all fun
        | .fieldAdded _ => true
        | .fieldTypeChanged f oldTy newTy =>
            m.fields.any fun fm =>
              fm.field == f && fm.oldTy == oldTy && fm.newTy == newTy
        | .fieldRemoved _ => false

/-! ## The exemplar: the bounded-cap widening (the slice's honest
     widening — the tree's scalars are u64/i64/bool/string, so the
     legacy u32→u64 exemplar ports to the cap lane: bounded n →
     bounded m, n ≤ m) -/

/-- A bounded-cap widening remedy for `field`: every value under cap
    `n` maps to the SAME number under cap `m` (widening, not
    reinterpretation). `Fin.cast` is the total map — the cap lives IN
    the type (Ty.lean), so the remedy needs no partiality. -/
def widenBounded (field : String) (n m : Nat) (h : n ≤ m) : FieldMigration where
  field := field
  oldTy := .bounded n
  newTy := .bounded m
  apply := fun v => match v with
    | .bounded f => .bounded (Fin.castLE h f)

/-- SOUNDNESS, in the diagram-commutes shape: applying the remedy to an
    old value yields the new-typed value OF THE SAME NUMBER — the
    non-vacuous content is the `Fin.val` equation (the bare `apply v =
    .bounded (Fin.cast h f)` would be the definition restated). The
    obligation every registered remedy carries. -/
theorem widenBounded_sound (f : Fin n) :
    Value.eval (.bounded m)
      ((widenBounded field n m h).apply (Value.bounded f)) = Fin.castLE h f := rfl

/-! ## The verdict (the three-way gate contract) -/

/-- The breaking gate's verdict: three-way, so a breaking change WITH
    remedy evidence reports differently from one without. -/
inductive CompatVerdict where
  | clean        -- no breaking changes (additions are safe)
  | remedied     -- breaking changes, EVERY one with matching remedy evidence
  | unremedied   -- ≥1 breaking change without remedy evidence
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString CompatVerdict where
  toString
    | .clean => "clean"
    | .remedied => "remedied"
    | .unremedied => "unremedied"

/-- The breaking subset of a diff: anything but `.added`. One
    definition — `verdictOf` and the gate consume the same filter
    (never a second notion of "breaking" at a call site). -/
def breakingOf (changes : List Change) : List Change :=
  changes.filter fun c => match c with | .added _ => false | _ => true

/-- The verdict over a diff plus the available remedy evidence.
    Breaking = anything but `.added`; remedied requires EVERY breaking
    change covered by some migration. -/
def verdictOf (changes : List Change) (migrations : List Migration) : CompatVerdict :=
  if breakingOf changes = [] then .clean
  else if (breakingOf changes).all fun c => migrations.any (·.remedies c) then .remedied
  else .unremedied

/-- The breaking filter's cons equation (the bridge proof's step). -/
theorem breakingOf_cons (c : Change) (cs : List Change) :
    breakingOf (c :: cs)
      = match c with
        | .added _ => breakingOf cs
        | _ => c :: breakingOf cs := by
  cases c <;> simp [breakingOf]

/-- The breaking subset is empty iff every finding is an addition —
    the two faces of ONE fact (the legacy `backwardCompatible_iff`'s
    filter-side twin). -/
theorem breakingOf_nil_iff {changes : List Change} :
    breakingOf changes = [] ↔ ∀ c ∈ changes, ∃ n, c = .added n := by
  induction changes with
  | nil => simp [breakingOf]
  | cons c cs ih =>
      cases c with
      | added n =>
          constructor
          · intro h c' hc'
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact ⟨n, rfl⟩
            · exact ih.mp h c' hc'
          · intro h
            exact ih.mpr (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
      | removed n =>
          constructor
          · intro h
            rw [breakingOf_cons] at h
            exact absurd h (by simp)
          · intro h
            have hcon := h (Change.removed n) (List.Mem.head _)
            exact absurd hcon (by simp)
      | changed n fd =>
          constructor
          · intro h
            rw [breakingOf_cons] at h
            exact absurd h (by simp)
          · intro h
            have hcon := h (Change.changed n fd) (List.Mem.head _)
            exact absurd hcon (by simp)

/-- THE VERDICT BRIDGE: `verdictOf = .clean` iff the breaking subset is
    empty — the verdict's clean face is exactly the compatibility
    relation's decision (composed with `backwardCompatible_iff` in
    `verdictOf_diff_clean_iff` below). -/
theorem verdictOf_eq_clean_iff {changes : List Change} {ms : List Migration} :
    verdictOf changes ms = .clean ↔ breakingOf changes = [] := by
  by_cases h : breakingOf changes = []
  · simp [verdictOf, h]
  · by_cases h2 : (breakingOf changes).all fun c => ms.any (·.remedies c)
    · simp [verdictOf, h, h2]
    · simp [verdictOf, h, h2]

/-- THE FULL BRIDGE (pattern #1, both faces tied): the verdict over the
    diff of two snapshots is `clean` EXACTLY when the relation holds.
    The gate runs the checker; the theorem says the checker is the
    relation's decision. -/
theorem verdictOf_diff_clean_iff (old new : List Item) (ms : List Migration) :
    verdictOf (diff old new) ms = .clean ↔ backwardCompatible old new = true := by
  rw [verdictOf_eq_clean_iff, breakingOf_nil_iff, backwardCompatible_iff]

/-- The gate's exit semantics — the ONLY mapping (exes consume this,
    never hand-map at call sites):

    - `clean` → 0 (silent success);
    - `remedied` → 0 WITH the remedy evidence NAMED in the report —
      shippable, but action required (apply the migration to the event
      log, then re-baseline the snapshot); the evidence chain is the
      report's job, not the exit code's;
    - `unremedied` → 2 — the LOUD warning: the change breaks consumers
      with no remedy, and `just gates` fails on 2. (The legacy tree
      shipped remedied → 2; this gate makes the UNREMEDIED case the
      loud one — a remedy never applied is a report line, not a
      failure.) -/
def CompatVerdict.exitCode : CompatVerdict → UInt32
  | .clean => 0
  | .remedied => 0
  | .unremedied => 2

end SchemaCore

/-! ## the module's law-summary (the honest ledger)

PROVED: `Change.added_of_true`, `backwardCompatible_iff` (the relation
bridges the diff), `breakingOf_cons`, `breakingOf_nil_iff`,
`verdictOf_eq_clean_iff`, `verdictOf_diff_clean_iff` (the verdict's
clean face IS the relation's decision), `widenBounded_sound` (the
exemplar remedy's soundness obligation). NO `sorry`, NO `axiom`.
Honest residue: rename detection is CANDIDACY-level (name-keyed trees —
D13's stable-id lane is the named follow-up); the remedy registry's
AUTHORING surface (registering `Migration`s for the gate to consume) is
the gate-side follow-up.
-/
