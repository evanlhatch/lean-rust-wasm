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

module

public import SchemaLang.Item

@[expose] public section

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
  | map {k : KeyTy} {v : Ty} : TyRefsOk known v → TyRefsOk known (.map k v)
  | set {k : KeyTy} : TyRefsOk known (.set k)
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
  | map {k : KeyTy} {v : Ty} : NoAsyncTy v → NoAsyncTy (.map k v)
  | set {k : KeyTy} : NoAsyncTy (.set k)
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
      cases ≠ [] →
      ItemWf known (.variant n cases)
  | func {s : FuncSig} :
      (∀ p t, (p, t) ∈ s.params → TyRefsOk known t) →
      TyRefsOk known s.ret →
      ItemWf known (.func s)
  | resource {n : String} : ItemWf known (.resource n)

/-! ## W8.13 — the recursive-type discipline (relation side)

The executable authority is `inlineSucc` / `inlineReaches?` /
`inlineCycleDiags` (Item.lean); here: the reasoning authority. The
relations are FUEL-INDEXED at the same bound the checker uses
(`items.length + 1`) — the bridge is then a direct structural
induction, no pumping argument. (A cycle longer than the vertex count
repeats a vertex and contains a shorter cycle; the unbounded reading
follows informally — the proved form is the bound-uniform one.) -/

/-- A path of ≤ `k` inline-ref steps from `n` to `p`. The reflexive-
transitive closure of `inlineSucc`, fuel-indexed to mirror
`inlineReaches?`'s recursion shape exactly. -/
inductive InlinePathB (items : List Item) : Nat → String → String → Prop where
  | refl {k : Nat} {n : String} : InlinePathB items k n n
  | step {k : Nat} {n m p : String}
      (h : m ∈ inlineSucc items n) (hp : InlinePathB items k m p) :
      InlinePathB items (k + 1) n p

/-- An INLINE ref-cycle on `n`: an edge out of `n` whose head paths back
to `n` within `items.length + 1` steps. Zero-length paths are
excluded (the edge is real), so a bare record with no refs is never
cyclic. -/
inductive InlineCycle (items : List Item) : String → Prop where
  | mk {n m : String}
      (he : m ∈ inlineSucc items n)
      (hp : InlinePathB items (items.length + 1) m n) : InlineCycle items n

/-- THE RECURSIVE-TYPE DISCIPLINE (W8.13): no type item sits on an
inline ref-cycle — every cycle passes `list` (the boxed position), so
every rendered type is finite-size (Rust `Vec` indirection; WIT
`list<T>`; the canonical ABI's heap form). Recursion ITSELF is legal —
the fuel-indexed semantics (`refSem` precedent) never needed
acyclicity; this gates the TARGET RENDERINGS only. -/
def InlineAcyclic (items : List Item) : Prop :=
  ∀ n, n ∈ Item.typeNames items → ¬ InlineCycle items n

/-- A type item reaches ITSELF by the zero-step path at any fuel (the
    refl arm's executable form — the induction's refl case reduces to
    this). -/
theorem inlineReaches?_self (items : List Item) (n : String) (k : Nat) :
    inlineReaches? items n k n = true := by
  cases k with
  | zero => exact beq_self_eq_true n
  | succ k =>
      rw [inlineReaches?]
      exact Bool.or_eq_true_iff.mpr (Or.inl (beq_self_eq_true n))

/-- The checker finds what the relation admits: a bounded path means
`inlineReaches?` fires (induction on the fuel index — the relation's
shape mirrors the checker's recursion exactly). -/
theorem inlineReaches?_pathB (items : List Item) (p : String) :
    ∀ {k : Nat} {m : String}, InlinePathB items k m p →
      inlineReaches? items p k m = true := by
  intro k m h
  induction h with
  | refl => exact inlineReaches?_self _ _ _
  | step hm _ ih =>
      rw [inlineReaches?]
      exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨_, hm, ih⟩))

/-- The checker finds ONLY what the relation admits (soundness):
induction on the fuel, generalizing the start vertex. -/
theorem inlineReaches?_sound (items : List Item) (root : String) :
    ∀ (k : Nat) (m : String), inlineReaches? items root k m = true →
      InlinePathB items k m root := by
  intro k
  induction k with
  | zero =>
      intro m h
      rw [inlineReaches?] at h
      have hme : m = root := beq_iff_eq.mp h
      subst hme
      exact .refl
  | succ k ih =>
      intro m h
      rw [inlineReaches?] at h
      rcases Bool.or_eq_true _ _ ▸ h with hmr | hany
      · have hme : m = root := beq_iff_eq.mp hmr
        subst hme
        exact .refl
      · have ⟨q, hq, hqr⟩ := List.any_eq_true.mp hany
        exact .step hq (ih q hqr)

/-- The cycle scan is EMPTY iff the universe is inline-acyclic (both
directions: the scan reports exactly the relation's cycles, at the
same fuel bound). -/
theorem inlineCycleDiags_eq_nil_iff {items : List Item} :
    inlineCycleDiags items = [] ↔ InlineAcyclic items := by
  constructor
  · intro hnil n hn hcyc
    cases hcyc with
    | mk he hp =>
        have hmem := List.filterMap_eq_nil_iff.mp hnil n hn
        rw [if_pos (List.any_eq_true.mpr ⟨_, he,
          inlineReaches?_pathB items n hp⟩)] at hmem
        cases hmem
  · intro hacy
    rw [inlineCycleDiags, List.filterMap_eq_nil_iff]
    intro n hn
    refine if_neg fun hany => ?_
    have ⟨q, hq, hqr⟩ := List.any_eq_true.mp hany
    exact hacy n hn ⟨hq, inlineReaches?_sound items n (items.length + 1) q hqr⟩

/-! ## W10.x — the emitter-bug lane (relation side)

Two more rules, both found by the WIT sweep's caught emitter bugs:

1. POST-MANGLE NAME UNIQUENESS — `kebab` is NOT injective ("FooBar",
   "foo-bar", "foo_bar" → "foo-bar"), so the pre-mangle nodup does not
   imply the emitted surface's uniqueness. The rule: the MANGLED name
   list is nodup (`names.map mangle` — the mangler is a pure function,
   so the rule is executable and the checker scans it directly).
2. NONEMPTY VARIANTS — a zero-case variant has no wire meaning and no
   value constructs; WIT's grammar refuses it ("empty variant"). The
   rule lives on the `ItemWf.variant` arm (it is a per-item fact).

With these, Core.lean's mangling claim becomes true BY THE RULE: a
`WellFormed` universe cannot emit colliding WIT identifiers or an empty
variant — the emitters consume checked universes.

-/ 

/-- THE REASONING AUTHORITY: every item checks against the universe's
    type names, item names are unique PRE-MANGLE, the MANGLED names are
    unique too (the kebab mangling is not injective — W10.x), and no
    type item sits on an inline ref-cycle (W8.13's recursive-type
    discipline — `InlineAcyclic`). -/
inductive WellFormed : List Item → Prop where
  | mk {items : List Item} :
      (∀ it, it ∈ items → ItemWf (Item.typeNames items) it) →
      (items.map Item.name).Nodup →
      ((items.map Item.name).map CodegenCore.Emit.kebab).Nodup →
      InlineAcyclic items →
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
  | map k v ih =>
      constructor
      · intro h; exact .map (ih.mp h)
      · intro h; cases h with | map ha => exact ih.mpr ha
  | set k =>
      exact ⟨fun _ => .set, fun _ => rfl⟩
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
  | map k v ih =>
      constructor
      · intro h; exact .map (ih.mp h)
      · intro h; cases h with | map ha => exact ih.mpr ha
  | set k =>
      exact ⟨fun _ => .set, fun _ => rfl⟩
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
        cases cases with
        | nil => simp [Item.check] at h
        | cons c cs =>
            simp only [Item.check, List.nil_append] at h
            rw [List.flatMap_eq_nil_iff] at h
            refine .variant (fun c t hct => ?_) (fun c p hcp => ?_)
              (fun c t hct => ?_) (List.cons_ne_nil c cs)
            · have h1 : (if t.banAsync then ([] : List SchemaDiag)
                    else [.asyncField n c])
                  ++ checkSchemaIdent (s!"case of `{n}`") c
                  ++ t.check known = [] := h (c, some t) hct
              rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h1
              exact banAsync_ite_nil_iff.mp h1.1.1
            · cases p with
              | none =>
                  have h1 : checkSchemaIdent (s!"case of `{n}`") c = [] :=
                    h (c, none) hcp
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
        | variant hna hid href hne =>
            cases cases with
            | nil => exact absurd rfl hne
            | cons c cs =>
                simp only [Item.check, List.nil_append]
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

/-- The dup-diagnostic arm, GENERALIZED over the diag constructor is
    `dupNamesDiags_eq_nil_iff` (Item.lean — the dup-scan idiom lives
    there once); the item lane's instance: -/
theorem dupDiags_eq_nil_iff {ns : List String} :
    ((dupNames ns).map SchemaDiag.dupName = []) ↔ ns.Nodup :=
  dupNamesDiags_eq_nil_iff SchemaDiag.dupName

/-- The post-mangle collision scan's arm (W10.x): the scan is EMPTY iff
    the MANGLED name list has no duplicates — the same reduction as the
    pre-mangle dup scan, at the mangling (`names.map mangle` is the
    rule; the mangler is a pure function). -/
theorem mangleCollDiags_eq_nil_iff {ns : List String} :
    mangleCollDiags ns = [] ↔ (ns.map CodegenCore.Emit.kebab).Nodup :=
  dupNamesDiags_eq_nil_iff (fun m => SchemaDiag.mangledCollision m
    (ns.filter fun n => CodegenCore.Emit.kebab n == m))

/-! ## The bridge -/

/-- Master bridge: the executable authority and the relation agree. -/
theorem universeCheck_eq_nil_iff {items : List Item} :
    universeCheck items = [] ↔ WellFormed items := by
  have hUC : universeCheck items =
      items.flatMap (Item.check (Item.typeNames items))
        ++ (dupNames (items.map Item.name)).map SchemaDiag.dupName
        ++ mangleCollDiags (items.map Item.name)
        ++ inlineCycleDiags items := rfl
  rw [hUC, List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff, dupDiags_eq_nil_iff, mangleCollDiags_eq_nil_iff,
      inlineCycleDiags_eq_nil_iff]
  constructor
  · intro h
    exact .mk (fun it hit => itemCheck_eq_nil_iff.mp (h.1.1.1 it hit))
      h.1.1.2 h.1.2 h.2
  · intro h
    cases h with
    | mk hitems hnodup hmangle hacy =>
        exact ⟨⟨⟨fun it hit => itemCheck_eq_nil_iff.mpr (hitems it hit), hnodup⟩,
          hmangle⟩, hacy⟩

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
  | mk hitems _ _ _ =>
      cases hitems _ hit with
      | record hna _ _ => exact hna f hf

end SchemaLang
