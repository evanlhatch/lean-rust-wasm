/-
# SchemaLang.Error — check-eliminates-error theorems (W6.11)

The runbook pattern (W6.11, notes/review-2026-09-16's CheckedProp row):
where an `Except`- or `Option`-returning consumer sits behind a Bool /
Decidable check, prove the check ELIMINATES the failure path —
`check x = true → f x ≠ none` — so the checker is proved SUFFICIENT,
not merely sound. Where the checker is exact, the completeness half is
proved too and the lane is packed as a `CodegenCore.CheckedProp` with
`.proved` completeness (the canon row's first consumers — the review
named W6.11 as its consumer order). Where the check alone is NOT
sufficient, nothing here patches the checker: the exact guard is named
and the gap is pinned by executed witnesses in Tests/Main.lean.

The lanes (each names the error constructor it rules out):

1. LAYOUT — `inB` guards `flatIdx` / `Coords.ofList?` (`none` =
   out-of-bounds). The `some → inB` half already existed (the `.2` of
   `flatIdxT_ofList`); the missing half was the elimination. EXACT
   checker: both directions proved → `coordsChecked`.
2. VORTEX LOWERING — `Ty.lower` refuses (returns `none`) on three
   classes: async (`banAsync`'s class), `result` (the deliberate
   refusal arm — the promised tag+payload union has not landed), and
   unresolvable `.ty` refs. `banAsync` ALONE is insufficient (the
   `.result` counterexample is pinned in Tests/Main.lean) — reported,
   not patched. The EXACT guard is the triple, proved as an iff.
3. SUBSCHEMA MIGRATION — `Subschema.ofMem?` (`none` = breaking). The
   two directions already existed as `ofMem?_some_of_forall_mem` /
   `ofMem?_none_of_breaking`; this module states the iff and packs the
   lane as `subschemaChecked` (`.proved` completeness — decidable list
   membership over `Field`'s `DecidableEq`).
4. DELTA — `Item.keyOf` / `Item.changeTy` (`none` = no change type): a
   non-empty field list eliminates it (the first-field key convention).
5. SNAPSHOT close-out — `Open.close` errors ONLY on a `ret`-less func;
   a present `ret` eliminates it. The full write-gate theorem
   (`namesEncodable items = true → (Snapshot.parse (Snapshot.render
   items)).isOk`) is DEFERRED: it needs a `String.splitOn`/`List.span`
   lemma surface over `Char` runs that the imported libraries do not
   carry (the format's line/keyword reasoning, not a schema fact).
   Cost verdict: two landing attempts failed on the string-lemma surface
   (2026-09-22); the PropSpec sweep + the Lean↔Rust differential carry
   the executable evidence; the law stays deferred until the lemma
   surface exists upstream.
6. VARIANT ACCESS — `VRow.isName` guards `CasePath.payloadOf` (`none` =
   the fired tag is not this arm; the evaluator's 0-analog). The check
   is exact UNDER unique case names (`payloadOf_isSome_of_isName`);
   with duplicate case names it is INSUFFICIENT (a deeper duplicate
   fires: check passes, read misses) — counterexample pinned in
   Tests/Main.lean, checker not patched (the W6.11 rule).
7. THE UNIVERSE GATE — `universeWellFormed` (the Bool projection)
   agrees with `WellFormed` by composition with the W3.5 bridge.

Ownership: the error/refinement lane for the schema-lang package.
Deliberate exclusions: `subschemaViaDiff?`'s `fieldDiffsOf`-gate →
evidence link (Subschema.lean's header defers the `find?`/`contains`
reasoning, out of theorem scope v1 — untouched); GuestGate's bans
(codegen-core's package, not this file's scope); Snapshot's full
write-gate (above). No existing declaration is changed; nothing here
is a new authority — every theorem composes the lane's own checker
with its own consumer.
-/

module

public import CodegenCore
public import SchemaLang.Delta
public import SchemaLang.Layout
public import SchemaLang.Snapshot
public import SchemaLang.Subschema
public import SchemaLang.Vortex.Lower
public import SchemaLang.Wf

@[expose] public section

namespace SchemaLang

/-! ## Lane 1 — Layout: `inB` eliminates the coordinate parsers' `none` -/

/-- The bounds check eliminates `flatIdx`'s `none`: in-bounds
    coordinates get their row-major offset. -/
theorem flatIdx_eq_some_of_inB {dims cs : List Nat} (h : inB dims cs = true) :
    flatIdx dims cs = some (dot cs (strides dims)) := by
  unfold flatIdx
  rw [if_pos h]

/-- The bounds check eliminates the coordinate parse's failure: in-bounds
    wire coordinates ALWAYS parse into typed ones. -/
theorem Coords.ofList?_isSome_of_inB :
    ∀ (dims cs : List Nat), inB dims cs = true →
      ∃ t, Coords.ofList? dims cs = some t
  | [], [], _ => ⟨(), rfl⟩
  | [], _ :: _, h => by simp [inB] at h
  | _ :: _, [], h => by simp [inB] at h
  | d :: ds, c :: rest, h => by
      simp only [inB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hcd, hrest⟩ := h
      obtain ⟨t, ht⟩ := Coords.ofList?_isSome_of_inB ds rest hrest
      refine ⟨(⟨c, hcd⟩, t), ?_⟩
      simp only [Coords.ofList?]
      rw [show Fin.ofList? d c = some ⟨c, hcd⟩ from by
        unfold Fin.ofList?; exact dif_pos hcd, ht]

/-- The elimination form (the runbook's statement shape). -/
theorem Coords.ofList?_ne_none_of_inB {dims cs : List Nat}
    (h : inB dims cs = true) : Coords.ofList? dims cs ≠ none := by
  obtain ⟨t, ht⟩ := Coords.ofList?_isSome_of_inB dims cs h
  rw [ht]
  exact Option.some_ne_none t

/-- The completeness half, named for the lane (it rode inside
    `flatIdxT_ofList`): a successful parse certifies the bounds check. -/
theorem Coords.inB_of_ofList?_eq_some {dims cs : List Nat} {t : CoordsOf dims}
    (h : Coords.ofList? dims cs = some t) : inB dims cs = true :=
  (flatIdxT_ofList dims cs t h).2

/-- The coordinate-parse lane as the canon's `CheckedProp`: the checker
    is EXACT, so completeness is `.proved`. -/
def coordsChecked : CodegenCore.CheckedProp (List Nat × List Nat) :=
  CodegenCore.CheckedProp.ofComplete
    (fun p => (Coords.ofList? p.1 p.2).isSome = true)
    (fun p => inB p.1 p.2)
    (fun p h => Option.isSome_iff_exists.mpr (Coords.ofList?_isSome_of_inB p.1 p.2 h))
    (fun p h => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
      exact Coords.inB_of_ofList?_eq_some ht)

/-! ## Lane 2 — the Vortex lowering: the EXACT guard is a triple

`Ty.lower`'s `none` arms are `.future`/`.stream` (the field-position
ban), `.result` (the deliberate refusal), and `.ty n` with `sem n =
none` (the unresolvable ref). `banAsync` covers the FIRST class only —
its insufficiency is a documented design fact (`Ty.lowerChecked`'s own
`.result → none` arm), pinned as a counterexample in Tests/Main.lean,
NOT patched. The exact checker is the triple below; it is complete. -/

/-- No `.result` node anywhere in the type — the refusal arm's class as
    a Bool, `banAsync`'s sibling guard. -/
def Ty.noResult : Ty → Bool
  | .option a => a.noResult
  | .result _ _ => false
  | .list a => a.noResult
  | .map _ v => v.noResult  -- the key is a `KeyTy` scalar: result-free
  | .set _ => true          -- a `KeyTy` scalar: result-free
  | .future a => a.noResult
  | .stream a => a.noResult
  | .tensor _ a => a.noResult
  | _ => true

namespace Vortex

/-- THE elimination theorem for the lowering lane, in iff form: the
    lowering succeeds EXACTLY when async-free (`banAsync`), result-free
    (`noResult`), and every `.ty` ref resolves under `sem`. Sound
    direction (`.mp` reversed — `mpr`): the guards eliminate the `none`
    path; complete direction (`mp`): a successful lowering certifies
    all three guards, so the triple is an EXACT checker. -/
theorem Ty.lower_isSome_iff (sem : VortexSem) (null : Nullability) (t : Ty) :
    (Ty.lower sem null t).isSome = true ↔
      t.banAsync = true ∧ t.noResult = true ∧
        ∀ n, n ∈ t.tyRefs → (sem n).isSome = true := by
  induction t generalizing null with
  | bool => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | u8 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | u16 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | u32 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | u64 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | i8 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | i16 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | i32 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | i64 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | f32 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | f64 => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | string => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | bytes => exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
      fun _ => rfl⟩
  | option a ih => exact ih .nullable
  | result ok err =>
      -- the refusal arm: `none` always, and the triple's `noResult`
      -- conjunct is `false` — both directions close by confusion
      exact ⟨fun h => by simp [Ty.lower] at h, fun h => Bool.noConfusion h.2.1⟩
  | list a ih =>
      cases hl : Ty.lower sem .nonNullable a with
      | none =>
          exact ⟨fun h => by simp [Ty.lower, hl] at h, fun h => by
            have hg := (ih .nonNullable).mpr h
            rw [hl] at hg
            exact Bool.noConfusion hg⟩
      | some inner =>
          exact ⟨fun _ => (ih .nonNullable).mp (by rw [hl]; rfl),
            fun _ => by simp [Ty.lower, hl]⟩
  | map k v ih =>
      -- the entry struct's key always lowers (`KeyTy.lower` is total);
      -- the iff reduces to the VALUE's, whose guards are the map's
      -- (each guard's map arm IS the value's verdict, definitionally)
      cases hl : Ty.lower sem .nonNullable v with
      | none =>
          exact ⟨fun h => by simp [Ty.lower, hl] at h, fun h => by
            have hg := (ih .nonNullable).mpr h
            rw [hl] at hg
            exact Bool.noConfusion hg⟩
      | some inner =>
          exact ⟨fun _ => (ih .nonNullable).mp (by rw [hl]; rfl),
            fun _ => by simp [Ty.lower, hl]⟩
  | set k =>
      exact ⟨fun _ => ⟨rfl, rfl, fun _ hn => absurd hn List.not_mem_nil⟩,
        fun _ => rfl⟩
  | future a =>
      exact ⟨fun h => by simp [Ty.lower] at h, fun h => Bool.noConfusion h.1⟩
  | stream a =>
      exact ⟨fun h => by simp [Ty.lower] at h, fun h => Bool.noConfusion h.1⟩
  | tensor dims a ih =>
      cases hl : Ty.lower sem .nonNullable a with
      | none =>
          exact ⟨fun h => by simp [Ty.lower, hl] at h, fun h => by
            have hg := (ih .nonNullable).mpr h
            rw [hl] at hg
            exact Bool.noConfusion hg⟩
      | some inner =>
          exact ⟨fun _ => (ih .nonNullable).mp (by rw [hl]; rfl),
            fun _ => by simp [Ty.lower, hl]⟩
  | ty n =>
      constructor
      · intro h
        refine ⟨rfl, rfl, fun m hm => ?_⟩
        rw [show Ty.tyRefs (.ty n) = [n] from rfl, List.mem_singleton] at hm
        subst m
        cases hs : sem n with
        | none =>
            rw [show Ty.lower sem null (.ty n) = (sem n).map (·.withNullability null)
              from rfl, hs] at h
            exact Bool.noConfusion h
        | some _ => rfl
      · intro h
        have hres := h.2.2 n (by
          rw [show Ty.tyRefs (.ty n) = [n] from rfl]
          exact List.mem_singleton_self n)
        cases hs : sem n with
        | none => rw [hs] at hres; exact Bool.noConfusion hres
        | some _ =>
            rw [show Ty.lower sem null (.ty n) = (sem n).map (·.withNullability null)
              from rfl, hs, Option.map_some, Option.isSome_some]

/-- The elimination corollary (the runbook's statement shape): the three
    guards pass ⟹ the lowering cannot fail. -/
theorem Ty.lower_ne_none_of_checks (sem : VortexSem) (null : Nullability) (t : Ty)
    (hb : t.banAsync = true) (hnr : t.noResult = true)
    (hres : ∀ n, n ∈ t.tyRefs → (sem n).isSome = true) :
    Ty.lower sem null t ≠ none := by
  intro hnone
  have his := (Ty.lower_isSome_iff sem null t).mpr ⟨hb, hnr, hres⟩
  rw [hnone] at his
  exact Bool.noConfusion his

end Vortex

/-! ## Lane 3 — the migration search: exact, and packed as a `CheckedProp` -/

/-- The migration lane's checker is EXACT: the embedding search succeeds
    iff every old field survives (name AND type). Sound =
    `ofMem?_some_of_forall_mem`; complete = the contrapositive of
    `ofMem?_none_of_breaking` (both pre-existing — this is the iff they
    compose into). -/
theorem Subschema.ofMem?_isSome_iff_forall_mem {newFs oldFs : List Field} :
    (Subschema.ofMem? newFs oldFs).isSome = true ↔
      ∀ f, f ∈ oldFs → f ∈ newFs := by
  constructor
  · intro h f hfold
    by_contra hfnew
    obtain ⟨sub, hsub⟩ := Option.isSome_iff_exists.mp h
    rw [Subschema.ofMem?_none_of_breaking newFs f oldFs hfold hfnew] at hsub
    exact (Option.some_ne_none sub) hsub.symm
  · intro h
    obtain ⟨sub, hsub⟩ := Subschema.ofMem?_some_of_forall_mem newFs oldFs h
    exact Option.isSome_iff_exists.mpr ⟨sub, hsub⟩

/-- The lane as the canon's `CheckedProp` (the review's consumer order):
    the check is decidable membership over `Field`'s `DecidableEq`;
    BOTH directions proved, so completeness is `.proved`. -/
def subschemaChecked : CodegenCore.CheckedProp (List Field × List Field) :=
  CodegenCore.CheckedProp.ofComplete
    (fun p => ∀ f, f ∈ p.1 → f ∈ p.2)
    (fun p => p.1.all fun f => p.2.any fun g => decide (f = g))
    (fun p h => by
      have hall := List.all_eq_true.mp h
      intro f hf
      obtain ⟨g, hg, hfg⟩ := List.any_eq_true.mp (hall f hf)
      exact (of_decide_eq_true hfg) ▸ hg)
    (fun p h => by
      apply List.all_eq_true.mpr
      intro f hf
      apply List.any_eq_true.mpr
      exact ⟨f, h f hf, decide_eq_true rfl⟩)

/-! ## Lane 4 — the delta key convention -/

/-- A record with fields HAS a key (the first-field convention): the
    `none` arm of `Item.keyOf` is eliminated by non-emptiness. -/
theorem Item.keyOf_isSome_of_fields_ne_nil {n : String} {fields : List Field}
    (h : fields ≠ []) : (Item.keyOf (.record n fields)).isSome = true := by
  cases fields with
  | nil => exact absurd rfl h
  | cons f rest => rfl

/-- …and so the change type exists (the four delta lowerings'
    `keyOf`-gated emission fires). -/
theorem Item.changeTy_isSome_of_fields_ne_nil {n : String} {fields : List Field}
    (h : fields ≠ []) : (Item.changeTy (.record n fields)).isSome = true := by
  cases fields with
  | nil => exact absurd rfl h
  | cons f rest => rfl

/-! ## Lane 5 — the snapshot close-out -/

/-- A func WITH its `ret` line always closes: the `ret`-less error
    constructor (the writer's own invariant — the write side always
    emits `ret`) is eliminated by the guard. -/
theorem Snapshot.Open.close_isOk_of_ret {n : String} {ps : List (String × Ty)}
    {r : Ty} {sem : Option FuncSem} :
    (Snapshot.Open.close (.func n ps (some r) sem)).isOk = true := rfl

/-! ## Lane 6 — the variant accessor: `isName` exact under unique case names -/

/-- A `CasePath n t cs` witnesses that `n` names a case of `cs`. -/
theorem CasePath.mem_map_fst {cs : List VariantCase} {n : String} {t : Ty}
    (p : CasePath n t cs) : n ∈ cs.map Prod.fst := by
  induction p with
  | here =>
      rw [List.map_cons]
      exact List.mem_cons_self
  | there p ih =>
      rw [List.map_cons]
      exact List.mem_cons_of_mem _ ih

/-- A row cannot fire a name the case list lacks. -/
theorem VRow.isName_eq_false_of_not_mem {n : String} {cs : List VariantCase}
    (row : VRow cs) (h : n ∉ cs.map Prod.fst) : row.isName n = false := by
  induction row with
  | here p =>
      rename_i m u cs'
      simp only [VRow.isName]
      rw [List.map_cons] at h
      rw [Bool.eq_false_iff]
      intro hbeq
      exact h (List.mem_cons.mpr (.inl (beq_iff_eq.mp hbeq).symm))
  | there r ih =>
      simp only [VRow.isName]
      apply ih
      intro hn
      apply h
      rw [List.map_cons]
      exact List.mem_cons_of_mem _ hn

/-- THE elimination: with unique case names, the tag check passing means
    the payload read cannot miss. WITHOUT uniqueness the check is
    insufficient (the deeper-duplicate counterexample is pinned in
    Tests/Main.lean) — reported, not patched. -/
theorem CasePath.payloadOf_isSome_of_isName {cs : List VariantCase} {n : String}
    {t : Ty} (p : CasePath n t cs) :
    (cs.map Prod.fst).Nodup → (row : VRow cs) → row.isName n = true →
      (p.payloadOf row).isSome = true := by
  induction p with
  | here =>
      intro hnd row h
      cases row with
      | here payload => rfl
      | there r =>
          rw [List.map_cons] at hnd
          obtain ⟨hnin, _⟩ := List.nodup_cons.mp hnd
          simp only [VRow.isName] at h
          rw [VRow.isName_eq_false_of_not_mem r hnin] at h
          exact Bool.noConfusion h
  | there p ih =>
      intro hnd row h
      rename_i m u cs'
      rw [List.map_cons] at hnd
      obtain ⟨hnin, hnd'⟩ := List.nodup_cons.mp hnd
      cases row with
      | here payload =>
          simp only [VRow.isName] at h
          have hmn : m = n := beq_iff_eq.mp h
          exact absurd (hmn ▸ CasePath.mem_map_fst p) hnin
      | there r =>
          simp only [VRow.isName] at h
          exact ih hnd' r h

/-! ## Lane 7 — the universe gate's two readings agree -/

/-- The Bool gate and the relation agree: `universeWellFormed` (the
    `isEmpty` projection) composed with the W3.5 bridge. The gate's
    `true` eliminates the diagnostic fold's findings AND certifies the
    relation. -/
theorem universeWellFormed_iff {items : List Item} :
    universeWellFormed items = true ↔ WellFormed items := by
  have hbr := universeCheck_eq_nil_iff (items := items)
  cases hc : universeCheck items with
  | nil =>
      exact ⟨fun _ => hbr.mp hc, fun _ => by simp [universeWellFormed, hc]⟩
  | cons d ds =>
      exact ⟨fun h => by simp [universeWellFormed, hc] at h, fun hwf => by
        have hnil := hbr.mpr hwf
        rw [hc] at hnil
        exact absurd hnil (List.cons_ne_nil d ds)⟩

end SchemaLang
