/-
# SchemaCore.Check — the check lane (invariants as registered items)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/12-construction.md §2 (the lane recipe:
item + mount + legality + obligation view + tests); notes/v3/
15-patterns.md #4 (the obligation as data — a registered invariant
produces an obligation row; discharge rides the KIT backends, never a
hand-rolled trio); notes/v3/02-data-plane.md §1-2 (the checker's
failure carries the violating rows AS DATA — the diagnostic shape is
Kit.Diag's, one envelope); notes/v3/04-verification.md §2
(obligations).

The lane (mined from legacy `SchemaLang.Invariant` + `TableInvariant`,
ported fresh at slice size):

- `CheckItem` — the invariant item: name, the target item's registry
  name, the field-list snapshot, and the `Pred` typed BY that snapshot
  (the legacy `SchemaInvariant` existential-wrapper shape: a row for
  another schema cannot be applied — the GADT index rides the stored
  fields; the executor casts only after a data-equality guard).
- `checkRows` / `checkOn` — the executable check over a table;
  `checkOn`'s verdict is a CONSTRUCTOR, never a smuggled Bool (04 §6):
  `.checked ok` is a real result, `.foreignSchema` is the refusal —
  `checkOn_of_ne` pins the refusal's exact face, never misreads.
- The legality Statement — `scopedDiags` (the diagnostic authority) +
  `CheckLegal` (the reasoning authority) + `scopedDiags_eq_nil_iff`
  (the proved bridge): the target resolves in the universe, the stored
  field snapshot is the target's, and every field name the Pred reads
  is ON the target.
- The obligation view — ONE obligation row per registered invariant,
  tier COMPUTED as `decidableNow` (the legacy TableInvariant rung
  reading: over a PROVIDED materialized table the claim is a closed
  decide — the caller presents the table, the kernel decides); the
  discharge rides `Kit.Obligation.decideDischarge` — `none` is the
  loud gap (a false claim or a mis-set tier; the backend refuses, it
  does not fabricate evidence).
- The mount — `register_lane CheckItem` (Kit.Lane: the recipe's steps
  1-2 in one kit call): `checkExt` (the append-only compile-time event
  log), `@[check]` (the attribute; the entry is a `def` of the item
  type, evaluated at elaboration), `getChecks` / `checkRegistry` /
  `checkNameOf` / `checkAttrReg`.

Honest gap (named, per the recipe's step 3): the MOUNT does not gate
legality — the substrate's default builder evaluates the `def` value
and cannot run the legality checker (the `builder :=` clause is pure;
a MetaM legality-gated builder is a later order). Legality is enforced
at the STATEMENT level: `scopedDiags` + its bridge, consumed by tests
and downstream surfaces. Tier honesty (the other rungs are loud
`none`): `provedAtElab` — no citation resolver consumer this order;
`generatedCheck` — no emitter reads this registry (the byte-tie bars
the artifact); `oracleSwept`/`guestVerified` — unwired. The legacy
TableInvariant module header carries the rung-by-rung argument.

The five questions (notes/v3/01-core.md): root = the check lane
(invariants as registered items — the constraint becomes the shared
authority, 02 §1's derived uses start here); carrier = the GADT-typed
pred + the registry's nodup-in-type; spine reading = registration =
append → replay = the accessor → the obligation row = the lane's
output; ladder rung = `decidableNow` (computed); gate row = SchemaTests'
checkSpec + the axiom report + CheckSlice's build-time teeth.

Core-only (imports SchemaCore.Pred + Kit.Lane — the cone rule).
-/

import Kit.Lane
import SchemaCore.Pred

open Kit

namespace SchemaCore

/-! ## The field-equality decision (the guard's instance) -/

/- `Field` equality — GENERATED, not hand-walked (06 §7: generation >
   hand-writing; the closed-case script this replaces — cases over
   both fields, two nested decEq splits, two congrArg injections —
   is exactly the shape the deriving handler produces; String + Ty
   both carry DecidableEq, and the instance lives HERE with the
   consumer that needs it). -/
deriving instance DecidableEq for Field

/-! ## The invariant item -/

/-- The registered invariant: the name, the target item's registry
    name, the field-list snapshot (the registry read — a stale
    snapshot is a FINDING, never a silent re-read), and the predicate
    typed by that snapshot (a foreign-schema row cannot be applied). -/
structure CheckItem where
  name : String
  schemaRef : String
  fields : List Field
  pred : Pred fields

instance : Inhabited CheckItem :=
  ⟨{ name := "", schemaRef := "", fields := [], pred := .lit false }⟩

/-! ## The executable check -/

/-- The verdict of the guarded executor: a REAL check result at the
    item's own field list (the Bool the predicate decided), or a
    REFUSAL — the table belongs to another schema, so no check ran.
    The refusal is its own constructor, never smuggled into a `false`
    that would conflate it with a genuine failed check (04 §6: the
    verdict vocabulary is ctors, never strings-or-Bool-overloads). -/
inductive CheckVerdict where
  /-- A real check ran: this is the predicate's decision. -/
  | checked (ok : Bool)
  /-- No check ran: the table is for another schema (the guard's
      refusal — the legacy `guardCastApply` discipline, honest face). -/
  | foreignSchema
  deriving BEq, Repr

/-- The check over a table typed by the item's OWN field list. -/
def CheckItem.checkRows (ci : CheckItem) (rows : List (RowVals ci.fields)) : Bool :=
  rows.all (fun r => ci.pred.check r)

/-- The safe executor: a table for ANOTHER schema refuses
    (`.foreignSchema` — no check ran, so no Bool is reported); at the
    item's OWN field list the verdict is the real check, wrapped
    (the field-list guard is the DecidableEq instance, never a silent
    misread — the legacy `checkOn`/`guardCastApply` discipline). -/
def CheckItem.checkOn (ci : CheckItem) {fs : List Field}
    (rows : List (RowVals fs)) : CheckVerdict :=
  if h : fs = ci.fields then
    CheckVerdict.checked (CheckItem.checkRows ci (cast (by rw [h]) rows))
  else .foreignSchema

/-- At the item's OWN field list the guard collapses to the all-check
    (wrapped in `.checked`). -/
theorem CheckItem.checkOn_self (ci : CheckItem)
    (rows : List (RowVals ci.fields)) :
    ci.checkOn rows = CheckVerdict.checked (ci.checkRows rows) := by
  simp only [checkOn]
  split
  · next h => simp
  · next h => simp at h

/-- A table for another schema refuses — the STRONGER pin: the
    verdict's exact face is `.foreignSchema`, not a `checked` of any
    Bool (no check ran, so no decision is reported). -/
theorem CheckItem.checkOn_of_ne (ci : CheckItem) {fs : List Field}
    (hne : fs ≠ ci.fields) (rows : List (RowVals fs)) :
    ci.checkOn rows = CheckVerdict.foreignSchema := by
  simp only [checkOn]
  split
  · next h => exact absurd h hne
  · next => rfl

/-! ## The claim + the table bridge -/

/-- The claim over a provided table: EVERY row satisfies the
    predicate (the spec — the checker's `all` is its decidable
    shadow). -/
def CheckItem.holds (ci : CheckItem) (rows : List (RowVals ci.fields)) : Prop :=
  ∀ r ∈ rows, ci.pred.Sat r

/-- THE TABLE BRIDGE (pattern #1 at the lane level — one induction
    over the table, the per-row direction cited from `Pred.check_iff`,
    never re-proved). -/
theorem CheckItem.checkRows_iff (ci : CheckItem)
    (rows : List (RowVals ci.fields)) :
    ci.checkRows rows = true ↔ ci.holds rows := by
  constructor
  · intro h r hr
    exact ci.pred.check_sound r (List.all_eq_true.mp h r hr)
  · intro h
    exact List.all_eq_true.mpr
      (fun r hr => ci.pred.check_complete r (h r hr))

/-- The claim's decision procedure: the table check itself — the
    bridge above makes it DECIDE THE CLAIM, not the checker's private
    Bool. -/
instance checkHoldsDec (ci : CheckItem) (rows : List (RowVals ci.fields)) :
    Decidable (ci.holds rows) :=
  decidable_of_iff _ (ci.checkRows_iff rows)

/-! ## The violating-rows discipline (02 §1) -/

/-- THE VIOLATING ROWS: a failed table check carries the failing rows
    AS DATA — every row whose verdict is `false`, in table order. -/
def CheckItem.violating (ci : CheckItem) (rows : List (RowVals ci.fields)) :
    List (RowVals ci.fields) :=
  rows.filter (fun r => !ci.pred.check r)

/-- The violation's Diag (Kit.Diag — the ONE envelope; the closed-world
    constructor carries the offending row's DATA + the valid space).
    An all-passing table renders the honest `none`-row message. -/
def CheckItem.violationDiag (ci : CheckItem) (rows : List (RowVals ci.fields)) :
    Diag :=
  Diag.closedWorld ⟨"SC1001"⟩
    s!"invariant `{ci.name}` on `{ci.schemaRef}` violated — \
      {toString (ci.violating rows).length} violating row(s)"
    .error
    (match ci.violating rows with
      | r :: _ => Pred.renderRow ci.fields r
      | [] => "none")
    [s!"a row satisfying `{ci.pred.render}`"]

/-! ## The legality Statement (well-scopedness over the target's fields) -/

/-- The predicate's referenced field names (the legality surface). -/
def Pred.reads {fs : List Field} : Pred fs → List String
  | .lit _ => []
  | .u64EqLit n _ => [n]
  | .u64GtLit n _ => [n]
  | .u64Eq a b => [a, b]
  | .strEqLit n _ => [n]
  | .and p q => p.reads ++ q.reads
  | .or p q => p.reads ++ q.reads
  | .not p => p.reads

/-- The filter's law (the unknown-names reading, once). -/
theorem filterUnknown_nil_iff {reads fieldNames : List String} :
    (reads.filter (fun n => !fieldNames.contains n)) = [] ↔
      ∀ n, n ∈ reads → n ∈ fieldNames := by
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h n hn
    have hb := h n hn
    cases hc : fieldNames.contains n with
    | false => rw [hc] at hb; simp at hb
    | true => exact List.contains_iff_mem.mp hc
  · intro h n hn
    have hmem := h n hn
    have hc : fieldNames.contains n = true := List.contains_iff_mem.mpr hmem
    rw [hc]
    simp

/-- The diagnostic authority: the target resolves in the universe, the
    stored field snapshot is the target's, and every field name the
    Pred reads is ON the target. Empty = legal. -/
def CheckItem.scopedDiags (items : List Item) (ci : CheckItem) : List String :=
  match items.find? (fun it => it.name == ci.schemaRef) with
  | none => [s!"`{ci.schemaRef}` is not a registered item — the \
      invariant's target must be in the universe"]
  | some it =>
      (if it.fields = ci.fields then [] else
        [s!"the stored field snapshot is stale — `{ci.schemaRef}`'s \
          fields drifted"])
        ++ ((ci.pred.reads.filter
              (fun n => !((ci.fields.map (·.name)).contains n))).map
            fun n => s!"field `{n}` is not on record `{ci.schemaRef}`")

/-- THE LEGALITY STATEMENT (the Prop the checker projects). -/
def CheckLegal (items : List Item) (ci : CheckItem) : Prop :=
  (∃ it, items.find? (fun x => x.name == ci.schemaRef) = some it
    ∧ it.fields = ci.fields)
  ∧ ∀ n, n ∈ ci.pred.reads → n ∈ ci.fields.map (·.name)

/-- THE LEGALITY BRIDGE: the diagnostic authority and the reasoning
    authority agree (the `*_eq_nil_iff` family's shape — one fold,
    both directions). -/
theorem CheckItem.scopedDiags_eq_nil_iff (items : List Item) (ci : CheckItem) :
    ci.scopedDiags items = [] ↔ CheckLegal items ci := by
  unfold scopedDiags CheckLegal
  cases hf : items.find? (fun it => it.name == ci.schemaRef) with
  | none => simp
  | some it =>
      simp only
      have hex : (∃ it', some it = some it' ∧ it'.fields = ci.fields)
          ↔ it.fields = ci.fields := by
        constructor
        · rintro ⟨it', hsome, hfields⟩
          rw [Option.some.inj hsome]
          exact hfields
        · intro h
          exact ⟨it, rfl, h⟩
      rw [hex, List.append_eq_nil_iff]
      constructor
      · rintro ⟨hif, hmap⟩
        refine ⟨?_, ?_⟩
        · by_cases hdec : it.fields = ci.fields
          · exact hdec
          · rw [if_neg hdec] at hif; simp at hif
        · rw [List.map_eq_nil_iff] at hmap
          exact filterUnknown_nil_iff.mp hmap
      · rintro ⟨hfields, hreads⟩
        rw [if_pos hfields]
        refine ⟨rfl, ?_⟩
        rw [List.map_eq_nil_iff]
        exact filterUnknown_nil_iff.mpr hreads

/-! ## The obligation view (what a registered invariant MEANS, as data) -/

/-- The registered invariant's obligation row over a PROVIDED table
    (15-patterns #4): the label, the COMPUTED tier — `decidableNow`,
    because over a provided materialized table the claim is a closed
    decide — the payload (the scope's field names), the provenance —
    and THE CLAIM AS THE TYPE INDEX: the row is `Obligation _
    (ci.holds rows)`, the per-row predicate itself. The data-level
    fields (label/tier/payload/provenance) do not depend on `rows`;
    only the claim index does — so a discharge of this row can never
    prove a different proposition than the table it was built for
    (the mis-wire rule's deepest promotion). -/
def CheckItem.obligation (ci : CheckItem) (rows : List (RowVals ci.fields)) :
    Obligation (List String) (ci.holds rows) :=
  { label := s!"schema/{ci.schemaRef}/{ci.name}"
    tier := .decidableNow
    payload := ci.fields.map (·.name)
    provenance := `SchemaCore }

/-- THE DISCHARGE — via the kit's decidableNow backend, NEVER a
    hand-rolled trio: the claim discharged is the obligation's OWN
    index (`ci.holds rows`; the `Decidable` instance is the table
    bridge's `checkHoldsDec`), there is no claim parameter to mis-wire.
    `none` is the loud gap (a false claim or a mis-set tier; the
    backend refuses, it does not fabricate evidence). -/
def CheckItem.dischargeOn (ci : CheckItem) (rows : List (RowVals ci.fields)) :
    Option Evidence :=
  (ci.obligation rows).decideDischarge

/-- The discharge's SOUNDNESS — a citation of the kit backend's
    theorem (never a re-proof), at the indexed strength: the type says
    the discharge proves THIS table's claim. -/
theorem CheckItem.dischargeOn_sound (ci : CheckItem)
    (rows : List (RowVals ci.fields))
    (h : ci.dischargeOn rows = some (.decided true)) : ci.holds rows :=
  Obligation.decideDischarge_sound (ci.obligation rows) rfl h

/-- The discharge's COMPLETENESS — a true claim fires the backend. -/
theorem CheckItem.dischargeOn_complete (ci : CheckItem)
    (rows : List (RowVals ci.fields)) (hc : ci.holds rows) :
    ci.dischargeOn rows = some (.decided true) :=
  Obligation.decideDischarge_of_claim (ci.obligation rows) rfl hc

/-! ## The mount — `@[check]`, by `Kit.Lane.register_lane` -/

/- The check lane's registration (the lane recipe's steps 1-2 in one
    kit call). Generates: `checkExt` (the append-only compile-time
    event log), `@[check]` (the attribute mount — the entry is a `def`
    of the item type, evaluated at elaboration), `getChecks` (the
    replay accessor), `checkRegistry` (the fold hook — the replay
    materialized into a `Kit.DataRegistry`), `checkNameOf` (the
    registry's lookup key), `checkAttrReg` (the attribute's
    initializer). The entries live in the NEXT module (a module's own
    initializers do not run during its own elaboration) — see
    `SchemaCore.CheckSlice`. -/
register_lane CheckItem where
  attr := check
  naming := fun it => it.name

end SchemaCore
