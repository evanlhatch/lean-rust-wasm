/-
# SchemaLang.Wf — `WellFormed` as an inductive relation + the checker bridge

The cedar pattern (relation as the reasoning authority + executable
checker + proved bridge). `universeCheck` (SchemaLang/Item.lean) stays the
EXECUTABLE authority — tooling reads its `SchemaDiag`s. `WellFormed` here
is the REASONING authority — the Prop downstream proofs (and W7.9's
`CheckedUniverse`) quantify over. `universeCheck_sound` /
`universeCheck_complete` are the bridge: a driver discharges once via the
checker and transports into the relation.

Own module, not Item.lean: the item model + the executable checker stay
proof-free for the emitter cone; the relation carries the List/count
lemma development.

Deliberate exclusion: consumers are NOT re-quantified here — W7.9 owns
the `{ items // WellFormed items }` bundling at the drivers.
-/

import SchemaLang.Item

namespace SchemaLang

/-! ## The Prop family (mirrors of `Ty.check` / `Ty.banAsync` /
    `checkSchemaIdent` / `Item.check` / the dup scan) -/

/-- Every `.ty` reference resolves against `known` (the Prop mirror of
    `Ty.check`'s `unknownRef` arm — same recursion). -/
inductive TyRefsOk (known : List String) : Ty → Prop where
  | bool : TyRefsOk known .bool
  | u8 : TyRefsOk known .u8
  | u16 : TyRefsOk known .u16
  | u32 : TyRefsOk known .u32
  | u64 : TyRefsOk known .u64
  | i8 : TyRefsOk known .i8
  | i16 : TyRefsOk known .i16
  | i32 : TyRefsOk known .i32
  | i64 : TyRefsOk known .i64
  | f32 : TyRefsOk known .f32
  | f64 : TyRefsOk known .f64
  | string : TyRefsOk known .string
  | bytes : TyRefsOk known .bytes
  | option {a : Ty} : TyRefsOk known a → TyRefsOk known (.option a)
  | result {ok err : Ty} : TyRefsOk known ok → TyRefsOk known err →
      TyRefsOk known (.result ok err)
  | list {a : Ty} : TyRefsOk known a → TyRefsOk known (.list a)
  | future {a : Ty} : TyRefsOk known a → TyRefsOk known (.future a)
  | stream {a : Ty} : TyRefsOk known a → TyRefsOk known (.stream a)
  | tensor {dims : List Nat} {a : Ty} : TyRefsOk known a →
      TyRefsOk known (.tensor dims a)
  | ty {n : String} : n ∈ known → TyRefsOk known (.ty n)

/-- No `future`/`stream` anywhere in the type (the Prop mirror of
    `Ty.banAsync` — the field-position ban, WIT grammar). -/
inductive NoAsyncTy : Ty → Prop where
  | bool : NoAsyncTy .bool
  | u8 : NoAsyncTy .u8
  | u16 : NoAsyncTy .u16
  | u32 : NoAsyncTy .u32
  | u64 : NoAsyncTy .u64
  | i8 : NoAsyncTy .i8
  | i16 : NoAsyncTy .i16
  | i32 : NoAsyncTy .i32
  | i64 : NoAsyncTy .i64
  | f32 : NoAsyncTy .f32
  | f64 : NoAsyncTy .f64
  | string : NoAsyncTy .string
  | bytes : NoAsyncTy .bytes
  | option {a : Ty} : NoAsyncTy a → NoAsyncTy (.option a)
  | result {ok err : Ty} : NoAsyncTy ok → NoAsyncTy err → NoAsyncTy (.result ok err)
  | list {a : Ty} : NoAsyncTy a → NoAsyncTy (.list a)
  | tensor {dims : List Nat} {a : Ty} : NoAsyncTy a → NoAsyncTy (.tensor dims a)
  | ty {n : String} : NoAsyncTy (.ty n)

/-- The identifier gate as a Prop (the `checkSchemaIdent` mirror — the
    context string is diag-only, so the Prop drops it). -/
def LegalIdent (name : String) : Prop :=
  CodegenCore.Emit.kebab name ∉ witReserved
    ∧ CodegenCore.Emit.snake name ∉ rustReserved

/-- One item, well-formed against the universe's type names (the
    `Item.check` mirror — the same four finding classes: async-in-field,
    reserved idents, unresolved refs, plus the universe-level dup scan
    in `WellFormed`). -/
inductive ItemWf (known : List String) : Item → Prop where
  | record {n : String} {fields : List Field} :
      (∀ f, f ∈ fields → NoAsyncTy f.ty) →
      (∀ f, f ∈ fields → LegalIdent f.name) →
      (∀ f, f ∈ fields → TyRefsOk known f.ty) →
      ItemWf known (.record n fields)
  | variant {n : String} {cases : List VariantCase} :
      (∀ c t, (c, some t) ∈ cases → NoAsyncTy t) →
      (∀ c p, (c, p) ∈ cases → LegalIdent c) →
      (∀ c t, (c, some t) ∈ cases → TyRefsOk known t) →
      ItemWf known (.variant n cases)
  | func {s : FuncSig} :
      (∀ p t, (p, t) ∈ s.params → TyRefsOk known t) →
      TyRefsOk known s.ret →
      ItemWf known (.func s)
  | resource {n : String} : ItemWf known (.resource n)

/-- THE REASONING AUTHORITY: every item checks against the universe's
    type names, and item names are unique (the `universeCheck` mirror,
    finding class by finding class). -/
inductive WellFormed : List Item → Prop where
  | mk {items : List Item} :
      (∀ it, it ∈ items → ItemWf (Item.typeNames items) it) →
      (items.map Item.name).Nodup →
      WellFormed items

/-! ## The bridge, piece by piece -/

theorem tyCheck_eq_nil_iff {known : List String} {t : Ty} :
    t.check known = [] ↔ TyRefsOk known t := by
  induction t with
  | bool => exact ⟨fun _ => .bool, fun _ => rfl⟩
  | u8 => exact ⟨fun _ => .u8, fun _ => rfl⟩
  | u16 => exact ⟨fun _ => .u16, fun _ => rfl⟩
  | u32 => exact ⟨fun _ => .u32, fun _ => rfl⟩
  | u64 => exact ⟨fun _ => .u64, fun _ => rfl⟩
  | i8 => exact ⟨fun _ => .i8, fun _ => rfl⟩
  | i16 => exact ⟨fun _ => .i16, fun _ => rfl⟩
  | i32 => exact ⟨fun _ => .i32, fun _ => rfl⟩
  | i64 => exact ⟨fun _ => .i64, fun _ => rfl⟩
  | f32 => exact ⟨fun _ => .f32, fun _ => rfl⟩
  | f64 => exact ⟨fun _ => .f64, fun _ => rfl⟩
  | string => exact ⟨fun _ => .string, fun _ => rfl⟩
  | bytes => exact ⟨fun _ => .bytes, fun _ => rfl⟩
  | option a ih =>
      constructor
      · intro h; exact .option (ih.mp h)
      · intro h; cases h with | option ha => exact ih.mpr ha
  | result ok err ihOk ihErr =>
      constructor
      · intro h
        have h' : ok.check known ++ err.check known = [] := h
        exact .result (ihOk.mp (List.append_eq_nil_iff.mp h').1)
          (ihErr.mp (List.append_eq_nil_iff.mp h').2)
      · intro h
        cases h with
        | result hOk hErr =>
            exact List.append_eq_nil_iff.mpr ⟨ihOk.mpr hOk, ihErr.mpr hErr⟩
  | list a ih =>
      constructor
      · intro h; exact .list (ih.mp h)
      · intro h; cases h with | list ha => exact ih.mpr ha
  | future a ih =>
      constructor
      · intro h; exact .future (ih.mp h)
      · intro h; cases h with | future ha => exact ih.mpr ha
  | stream a ih =>
      constructor
      · intro h; exact .stream (ih.mp h)
      · intro h; cases h with | stream ha => exact ih.mpr ha
  | tensor dims a ih =>
      constructor
      · intro h; exact .tensor (ih.mp h)
      · intro h; cases h with | tensor ha => exact ih.mpr ha
  | ty n =>
      constructor
      · intro h
        -- defeq ascription exposes the `if` (no equation-lemma unfold)
        have h' : (if known.contains n then ([] : List SchemaDiag)
            else [.unknownRef n (CodegenCore.didYouMean n known) known]) = [] := h
        split at h'
        · rename_i hc; exact .ty (List.contains_iff_mem.mp hc)
        · exact absurd h' (List.cons_ne_nil _ _)
      · intro h
        cases h with
        | ty hn =>
            show (if known.contains n then ([] : List SchemaDiag)
              else [.unknownRef n (CodegenCore.didYouMean n known) known]) = []
            split
            · rfl
            · rename_i hc
              exact absurd (List.contains_iff_mem.mpr hn) hc

theorem banAsync_iff_noAsyncTy {t : Ty} :
    t.banAsync = true ↔ NoAsyncTy t := by
  induction t with
  | bool => exact ⟨fun _ => .bool, fun _ => rfl⟩
  | u8 => exact ⟨fun _ => .u8, fun _ => rfl⟩
  | u16 => exact ⟨fun _ => .u16, fun _ => rfl⟩
  | u32 => exact ⟨fun _ => .u32, fun _ => rfl⟩
  | u64 => exact ⟨fun _ => .u64, fun _ => rfl⟩
  | i8 => exact ⟨fun _ => .i8, fun _ => rfl⟩
  | i16 => exact ⟨fun _ => .i16, fun _ => rfl⟩
  | i32 => exact ⟨fun _ => .i32, fun _ => rfl⟩
  | i64 => exact ⟨fun _ => .i64, fun _ => rfl⟩
  | f32 => exact ⟨fun _ => .f32, fun _ => rfl⟩
  | f64 => exact ⟨fun _ => .f64, fun _ => rfl⟩
  | string => exact ⟨fun _ => .string, fun _ => rfl⟩
  | bytes => exact ⟨fun _ => .bytes, fun _ => rfl⟩
  | option a ih =>
      constructor
      · intro h; exact .option (ih.mp h)
      · intro h; cases h with | option ha => exact ih.mpr ha
  | result ok err ihOk ihErr =>
      constructor
      · intro h
        have h' : (ok.banAsync && err.banAsync) = true := h
        have hand := Bool.and_eq_true _ _ ▸ h'
        exact .result (ihOk.mp hand.1) (ihErr.mp hand.2)
      · intro h
        cases h with
        | result hOk hErr =>
            have : (ok.banAsync && err.banAsync) = true :=
              Bool.and_eq_true _ _ ▸ ⟨ihOk.mpr hOk, ihErr.mpr hErr⟩
            exact this
  | list a ih =>
      constructor
      · intro h; exact .list (ih.mp h)
      · intro h; cases h with | list ha => exact ih.mpr ha
  | future a _ =>
      exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | stream a _ =>
      exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | tensor dims a ih =>
      constructor
      · intro h; exact .tensor (ih.mp h)
      · intro h; cases h with | tensor ha => exact ih.mpr ha
  | ty n => exact ⟨fun _ => .ty, fun _ => rfl⟩

/-- The field-level async diag arm as a Prop. -/
theorem banAsync_ite_nil_iff {t : Ty} {d : SchemaDiag} :
    (if t.banAsync then ([] : List SchemaDiag) else [d]) = [] ↔ NoAsyncTy t := by
  cases hb : t.banAsync with
  | true =>
      -- the if is closed (`if true = true …`): `rfl` and the casts reduce
      exact ⟨fun _ => banAsync_iff_noAsyncTy.mp hb, fun _ => rfl⟩
  | false =>
      exact ⟨fun h => absurd h (List.cons_ne_nil _ _),
        fun hna => by
          have := banAsync_iff_noAsyncTy.mpr hna
          rw [hb] at this
          exact Bool.noConfusion this⟩

theorem checkSchemaIdent_eq_nil_iff {ctx name : String} :
    checkSchemaIdent ctx name = [] ↔ LegalIdent name := by
  have w : (witReserved.contains (CodegenCore.Emit.kebab name) = true) ↔
      CodegenCore.Emit.kebab name ∈ witReserved := List.contains_iff_mem
  have r : (rustReserved.contains (CodegenCore.Emit.snake name) = true) ↔
      CodegenCore.Emit.snake name ∈ rustReserved := List.contains_iff_mem
  unfold checkSchemaIdent LegalIdent
  dsimp only
  split
  · rename_i hif
    exact ⟨fun h => absurd h (List.cons_ne_nil _ _), fun h => by
      rcases Bool.or_eq_true _ _ ▸ hif with hw | hr
      · exact absurd (w.mp hw) h.1
      · exact absurd (r.mp hr) h.2⟩
  · rename_i hif
    have hboth := not_or.mp (Bool.or_eq_true _ _ ▸ hif)
    exact ⟨fun _ =>
        ⟨fun hk => absurd (w.mpr hk) hboth.1,
         fun hk => absurd (r.mpr hk) hboth.2⟩,
      fun _ => rfl⟩

/-- The per-item mirror. -/
theorem itemCheck_eq_nil_iff {known : List String} {it : Item} :
    Item.check known it = [] ↔ ItemWf known it := by
  cases it with
  | record n fields =>
      constructor
      · intro h
        simp only [Item.check] at h
        rw [List.flatMap_eq_nil_iff] at h
        refine .record (fun f hf => ?_) (fun f hf => ?_) (fun f hf => ?_)
        · have h1 : (if f.ty.banAsync then ([] : List SchemaDiag)
                else [.asyncField n f.name])
              ++ checkSchemaIdent (s!"field of `{n}`") f.name
              ++ f.ty.check known = [] := h f hf
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
          exact banAsync_ite_nil_iff.mp h1.1.1
        · have h1 : (if f.ty.banAsync then ([] : List SchemaDiag)
                else [.asyncField n f.name])
              ++ checkSchemaIdent (s!"field of `{n}`") f.name
              ++ f.ty.check known = [] := h f hf
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
          exact checkSchemaIdent_eq_nil_iff.mp h1.1.2
        · have h1 : (if f.ty.banAsync then ([] : List SchemaDiag)
                else [.asyncField n f.name])
              ++ checkSchemaIdent (s!"field of `{n}`") f.name
              ++ f.ty.check known = [] := h f hf
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
          exact tyCheck_eq_nil_iff.mp h1.2
      · intro h
        cases h with
        | record hna hid href =>
            simp only [Item.check]
            rw [List.flatMap_eq_nil_iff]
            intro f hf
            show (if f.ty.banAsync then ([] : List SchemaDiag)
                else [.asyncField n f.name])
              ++ checkSchemaIdent (s!"field of `{n}`") f.name
              ++ f.ty.check known = []
            rw [List.append_eq_nil_iff, List.append_eq_nil_iff]
            exact ⟨⟨banAsync_ite_nil_iff.mpr (hna f hf),
              checkSchemaIdent_eq_nil_iff.mpr (hid f hf)⟩,
              tyCheck_eq_nil_iff.mpr (href f hf)⟩
  | variant n cases =>
      constructor
      · intro h
        simp only [Item.check] at h
        rw [List.flatMap_eq_nil_iff] at h
        refine .variant (fun c t hct => ?_) (fun c p hcp => ?_) (fun c t hct => ?_)
        · have h1 : (if t.banAsync then ([] : List SchemaDiag)
                else [.asyncField n c])
              ++ checkSchemaIdent (s!"case of `{n}`") c
              ++ t.check known = [] := h (c, some t) hct
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
          exact banAsync_ite_nil_iff.mp h1.1.1
        · cases p with
          | none =>
              have h1 : checkSchemaIdent (s!"case of `{n}`") c = [] := h (c, none) hcp
              exact checkSchemaIdent_eq_nil_iff.mp h1
          | some t =>
              have h1 : (if t.banAsync then ([] : List SchemaDiag)
                    else [.asyncField n c])
                  ++ checkSchemaIdent (s!"case of `{n}`") c
                  ++ t.check known = [] := h (c, some t) hcp
              rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
              exact checkSchemaIdent_eq_nil_iff.mp h1.1.2
        · have h1 : (if t.banAsync then ([] : List SchemaDiag)
                else [.asyncField n c])
              ++ checkSchemaIdent (s!"case of `{n}`") c
              ++ t.check known = [] := h (c, some t) hct
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
          exact tyCheck_eq_nil_iff.mp h1.2
      · intro h
        cases h with
        | variant hna hid href =>
            simp only [Item.check]
            rw [List.flatMap_eq_nil_iff]
            intro x hx
            cases x with
            | mk c p =>
                cases p with
                | none =>
                    show checkSchemaIdent (s!"case of `{n}`") c = []
                    exact checkSchemaIdent_eq_nil_iff.mpr (hid c none hx)
                | some t =>
                    show (if t.banAsync then ([] : List SchemaDiag)
                        else [.asyncField n c])
                      ++ checkSchemaIdent (s!"case of `{n}`") c
                      ++ t.check known = []
                    rw [List.append_eq_nil_iff, List.append_eq_nil_iff]
                    exact ⟨⟨banAsync_ite_nil_iff.mpr (hna c t hx),
                      checkSchemaIdent_eq_nil_iff.mpr (hid c (some t) hx)⟩,
                      tyCheck_eq_nil_iff.mpr (href c t hx)⟩
  | func s =>
      constructor
      · intro h
        have h' : (s.params.flatMap fun (_, t) => t.check known)
            ++ s.ret.check known = [] := h
        rw [List.append_eq_nil_iff] at h'
        rw [List.flatMap_eq_nil_iff] at h'
        refine .func (fun p t hpt => ?_) (tyCheck_eq_nil_iff.mp h'.2)
        have h1 : t.check known = [] := h'.1 (p, t) hpt
        exact tyCheck_eq_nil_iff.mp h1
      · intro h
        cases h with
        | func hp hr =>
            exact List.append_eq_nil_iff.mpr ⟨
              List.flatMap_eq_nil_iff.mpr fun x hx => by
                cases x with
                | mk p t => exact tyCheck_eq_nil_iff.mpr (hp p t hx),
              tyCheck_eq_nil_iff.mpr hr⟩
  | resource n =>
      exact ⟨fun _ => .resource, fun _ => rfl⟩

/-- `eraseDups` of a cons is a cons (its equation), so nil inputs are
    the only nil outputs. -/
theorem eraseDups_eq_nil_iff {l : List String} : l.eraseDups = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons x xs => rw [List.eraseDups_cons]; simp

/-- Nodup via the per-name multiplicity the checker's dup scan counts. -/
theorem nodup_iff_countP_le_one {ns : List String} :
    ns.Nodup ↔ ∀ n, n ∈ ns → ns.countP (· == n) ≤ 1 := by
  constructor
  · intro hnd
    induction ns with
    | nil => intro n hn; cases hn
    | cons x xs ih =>
        rw [List.nodup_cons] at hnd
        intro n hn
        rw [List.countP_cons]
        rcases List.mem_cons.mp hn with rfl | hnxs
        · -- the head case (`x` substituted by `n`)
          have hz : xs.countP (· == n) = 0 := by
            rw [List.countP_eq_zero]
            intro b hb hbn
            exact hnd.1 (beq_iff_eq.mp hbn ▸ hb)
          rw [hz, if_pos (beq_self_eq_true n)]
          omega
        · have hxn : ¬ ((x == n) = true) := by
            intro hxx
            exact hnd.1 (beq_iff_eq.mp hxx ▸ hnxs)
          rw [if_neg hxn, Nat.add_zero]
          exact ih hnd.2 n hnxs
  · intro h
    induction ns with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
        rw [List.nodup_cons]
        refine ⟨?_, ih ?_⟩
        · intro hx
          have hle := h x List.mem_cons_self
          rw [List.countP_cons, if_pos (beq_self_eq_true x)] at hle
          have hz : xs.countP (· == x) = 0 := by omega
          rw [List.countP_eq_zero] at hz
          exact hz x hx (beq_self_eq_true x)
        · intro n hn
          have hle := h n (List.mem_cons_of_mem x hn)
          rw [List.countP_cons] at hle
          by_cases hxn : (x == n) = true
          · have heq := beq_iff_eq.mp hxn
            subst heq
            rw [if_pos (beq_self_eq_true x)] at hle
            omega
          · rw [if_neg hxn, Nat.add_zero] at hle
            exact hle

/-- The dup-diagnostic arm in Prop form. -/
theorem dupDiags_eq_nil_iff {ns : List String} :
    ((ns.filter fun n => ns.countP (· == n) > 1).eraseDups.map
        SchemaDiag.dupName = []) ↔ ns.Nodup := by
  rw [List.map_eq_nil_iff, eraseDups_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    refine nodup_iff_countP_le_one.mpr fun n hn => Nat.not_lt.mp fun hgt => h n hn ?_
    exact decide_eq_true hgt
  · intro hnd n hn hp
    have hgt : ns.countP (· == n) > 1 := of_decide_eq_true hp
    have hle := nodup_iff_countP_le_one.mp hnd n hn
    omega

/-! ## The bridge -/

/-- Master bridge: the executable authority and the relation agree. -/
theorem universeCheck_eq_nil_iff {items : List Item} :
    universeCheck items = [] ↔ WellFormed items := by
  have hUC : universeCheck items =
      items.flatMap (Item.check (Item.typeNames items))
        ++ ((items.map Item.name).filter
              fun n => (items.map Item.name).countP (· == n) > 1).eraseDups.map
            SchemaDiag.dupName := rfl
  rw [hUC, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, dupDiags_eq_nil_iff]
  constructor
  · intro h
    exact .mk (fun it hit => itemCheck_eq_nil_iff.mp (h.1 it hit)) h.2
  · intro h
    cases h with
    | mk hitems hnodup =>
        exact ⟨fun it hit => itemCheck_eq_nil_iff.mpr (hitems it hit), hnodup⟩

/-- The bridge, sound direction: a clean checker run transports INTO
    the relation (the driver's discharge route). -/
theorem universeCheck_sound {items : List Item} :
    universeCheck items = [] → WellFormed items :=
  universeCheck_eq_nil_iff.mp

/-- The bridge, complete direction: the relation certifies a clean
    checker run (nothing the relation admits escapes the checker). -/
theorem universeCheck_complete {items : List Item} :
    WellFormed items → universeCheck items = [] :=
  universeCheck_eq_nil_iff.mpr

/-! ## W7.9 phase 2 — the evidence rides the type -/

/-- The CHECKED universe: the item list bundled with its `WellFormed`
    evidence. A driver discharges ONCE (the executable `universeCheck`
    + `universeCheck_sound`); consumers quantify over the bundle —
    well-formedness is carried BY THE TYPE, not by a comment or a
    defensive re-check. `abbrev` (reducible): instance search and
    unfolding see through it (the RowVals discipline). -/
abbrev CheckedUniverse := { items : List Item // WellFormed items }

/-- Inversion, the record-field async arm: a `WellFormed` universe's
    record fields are async-free AT EVERY DEPTH (the `ItemWf.record`
    arm projected out of the universe fold). W7.9's emitter consumers
    (the Vortex lowering, first) read their per-field evidence through
    this projection. -/
theorem WellFormed.noAsync_of_record_field {items : List Item}
    (hwf : WellFormed items) {n : String} {fields : List Field}
    (hit : Item.record n fields ∈ items) {f : Field} (hf : f ∈ fields) :
    NoAsyncTy f.ty := by
  cases hwf with
  | mk hitems _ =>
      cases hitems _ hit with
      | record hna _ _ => exact hna f hf

end SchemaLang
