/-
# SchemaCore.Describe — the typed description universe (D19's meta-universe)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/05-codegen.md §3 (the deriving protocol:
reflect ONCE into the typed description — "a small typed universe of
supported structure — primitive / product / sum / optional / sequence /
reference / refinement / dependent field — interpreted into the Lean
type; the ONE deliberate meta-universe, its instances are our types" —
then derive via GENERIC definitions + GENERIC theorems, thin wrappers
per declaration); notes/v3/decisions.md D19 (the description layer) +
D12 (capability-directed, lazy derivation); notes/v3/06-lean-rules.md
§2 (structural recursion; wf opacity) + §7 (one reifier family).

## The universe (the honest minimal set the slice + near lanes need)

- `prim t` — a leaf, delegating to the CLOSED boundary universe `Ty`
  (SchemaCore.Ty). ONE leaf universe: no parallel primitive set — the
  four scalars + option/list/result/map/set/bounded ride `Ty`, whose
  `toType` reification and `renderTy` fold are REUSED, not re-invented
  (06 §7).
- `option d` — optional.
- `list d` — sequence.
- `product name fields` — the record; `name` is the Lean declaration's
  name (provenance-faithful, the same discipline as `Item.name`);
  `fields` is an ordered `name × description` list. The LIST (not a
  sibling cons chain) makes `Descr` a NESTED (not mutual) inductive —
  the interpretation rides the `where`-clause auxiliary and stays
  STRUCTURAL (kernel-visible, `rfl`-reducible over concrete values;
  verified — a mutual `Descr`/sibling block could not infer structural
  recursion across the `List`/projection boundary, 06 §2).

DELIBERATELY EXCLUDED (each names its reason — the leftover rule):

- `sum` as a first-class ctor — the sum shape rides `Ty.result` under
  `prim` (the reifier maps `Sum a b` to `.prim (.result …)`); no near
  lane declares tagged-union structures (`@[schema]` registers records
  only — Register's one shape), so a `sum` ctor has no consumer yet.
- `reference` — named-type references are open-world (they need the
  wellFormed resolution lane); the slice has no second registered item
  to reference (the same reason `Ty` excludes `.ty`).
- `refinement` — the boundary's refinement (`Ty.bounded`) rides `prim`
  cap-in-type; first-class refinement DESCRIPTIONS wait for a lane
  that declares one.
- `dependent field` — D20's lane; nothing consumes it yet.

## The reflection (the slice's `@[schema]` — CONVERGED)

ONE reflection path: `describe` (below) reflects a declared structure
into THIS universe; `itemOfDescr` flattens the description onto the
registry's first-order `Item`; the `@[schema]` mount
(SchemaCore.Register) CONSUMES that composed route
(`reflectItemViaDescr`) — the registry is a consumer of the
description layer, never a parallel reflector (05 §3: reflect ONCE
into the typed description, derive the rest). The reifier family the
walk needs (`natLitOf?` / `keyOfExpr?` / `tyOfExpr?` /
`ctorArgTypes`) lives HERE — one module, one expr walk, so the import
stays acyclic (Register → Describe). The lane's `Except String`
builder contract flattens the route's curated `Kit.Diag` exactly ONCE
at the substrate boundary (Register's `reflectStruct` adapter); the
pre-convergence name survives only because SchemaTests.Main's
twin-path pin still cites it. The coherence laws
(`tyOfDescr_denotes`, `deriveRender_coherent` — the description's
denotation and rendering ARE the boundary's wherever both speak) are
the factored fact `tyOfDescr_some`'s two citations.

## The functorial deepening (16-surface §4.4) — the honest shape

`Descr` IS the pattern functor's fixed point, in the only form that
pays at this size: the initial object its inductive declaration
already gives (no category machinery is imported — the functor's
algebras are the RECORD below, the fixed point's universal property
is the fold). Every derivation over the description is an ALGEBRA
(`DescrAlg`: one row per constructor + the field-sibling rows) and
every walk is `foldDescr`/`foldFields` — ONE recursion, the handlers
supply rows. The correctness claims ride the same record at `Prop`:
**the generic correctness theorem** is the fold itself at the claim
algebra (`law_of_rows`) — a handler built as a fold whose per-ctor
claim rows are lawful is correct, by the ONE induction the fold
performs. The per-capability theorems (`tyOfDescr_some` here;
`deriveCodec_correct`/`deriveDec_eq` in Derive.lean) are INSTANCES:
they supply rows, never inductions.

Honest residue (each named): `badTagRefused` (Derive.lean) is NOT an
algebra — its option row re-enters the child DECODER (the parser
direction consumes the input stream, the algebra's rows receive
already-built subresults — the same reason `decVal` stays a hand match
in Fold.lean); `hasOption`/`encNonempty` are entourage plumbing with
no proof family — an algebra would add five rows to retire zero
inductions. The row bridge (`toRowF`/`ofRowF`) composes over the
field LIST, not `Descr` — its one-cons-case inductions are already
minimal and their leaf content rides the value-level round trips
(the `Ty` fold's discipline, deepened in Fold.lean).

Core-only EXCEPT the reflector (the meta declarations below — the
elaboration-time surface; the pure universe + interpretation +
derivations are core and never import meta names).

The five questions (notes/v3/01-core.md):
- root: Universe — the ONE deliberate meta-universe (D19): closed
  description codes + total denotation (`Descr.Ty`); the description
  universe's initial-algebra face is the `DescrAlg` fold below.
- carrier: the interpretation is a Type-valued fold (wrong-shape
  denotations unrepresentable; the product's tuple is the canonical
  row shape — the record↔tuple bridge is the row-iso lane); the
  handlers/claims are `DescrAlg` values at any `Sort`.
- spine reading: the REFLECTION stage's typed face — declaration →
  `describe` → `Descr` → (the ONE walk's algebras) → capability
  surface.
- ladder rung: the fold is structural (kernel-visible; concrete
  descriptions reduce by `rfl`); the claims are algebra rows.
- gate row: the axiom report (SchemaCore roots) + SchemaTests' pins +
  the curated-refusal negative controls (build-time teeth via `#eval`).
-/

import Lean
import Kit
import SchemaCore.Ty
import SchemaCore.Fold
import SchemaCore.Item

namespace SchemaCore

/-! ## The description universe -/

/-- THE ONE deliberate meta-universe (05 §3, D19): a supported-structure
    description. CLOSED — a new ctor extends every consumer's match
    (the compiler drives it; Ty.lean's closed-universe discipline).
    The ctor set + exclusions are the module header's. -/
inductive Descr where
  /-- A leaf: the closed boundary universe's type (ONE leaf universe). -/
  | prim (t : Ty)
  /-- Optional. -/
  | option (d : Descr)
  /-- Sequence. -/
  | list (d : Descr)
  /-- The record: the Lean declaration's name (provenance-faithful) +
      the ordered field list (name × description), registration order. -/
  | product (name : String) (fields : List (String × Descr))
deriving Repr, BEq, Inhabited

/-! ## The interpretation — the meta-universe's denotation -/

mutual
  /-- The product arm's denotation: the field tuple, right-nested,
      `Unit`-terminated. REDUCIBLE: the dependent matches over
      `Descr.Ty`'s product rows (the deriving layer's codecs/bridges)
      unify against this at instances transparency — a semireducible
      spelling defeats the index unification. -/
  @[reducible]
  def prodTyOf : List (String × Descr) → Type
    | [] => Unit
    | (_, d) :: rest => Descr.Ty d × prodTyOf rest

  /-- `Descr.Ty` — the description's denotation: the Lean type the
      description describes. The leaf delegates to `Ty.toType` (ONE
      reification family); the product's denotation is the canonical
      TUPLE shape (the record↔tuple bridge is the row-iso lane —
      SchemaCore.RowVals + the SchemaTests fixture's `Kit.Iso`),
      computed by `prodTyOf` (the structural field walk; a mutual
      block over a sibling cons chain could not infer structural
      recursion here). -/
  @[reducible]
  def Descr.Ty : Descr → Type
    | .prim t => t.toType
    | .option d => Option d.Ty
    | .list d => List d.Ty
    | .product _ fs => prodTyOf fs
end

/-- The denotation reduces over concrete descriptions (structural,
    kernel-visible — no wf opacity). -/
example : Descr.Ty (.prim .u64) = UInt64 := rfl
example : Descr.Ty (.product "x" []) = Unit := rfl
example : Descr.Ty (.product "Example"
  [("ready", .prim .bool), ("count", .prim .u64)]) =
  (Bool × (UInt64 × Unit)) := rfl

/-! ## The functorial deepening — the ONE walk over the description
    (16-surface §4.4) -/

/-- THE DESCRIPTION ALGEBRA (16-surface §4.4's pattern functor read as
    data): one row per `Descr` constructor + the field-sibling rows
    (the `ValueAlg` discipline — ONE record carries the whole nested
    family). The carrier `P` rides any `Sort`: `Type`-valued `P` are
    the handlers (the codec's encoder/decoder, the drawer), `Prop`-
    valued `P` are the correctness claims — the SAME record, the SAME
    fold. A new `Descr` constructor refuses to compile until every
    algebra grows its row (15-patterns #15's compiler-driven extension
    point, one level up from `TyAlg`).

    Hand-written, not `declare_fold`-generated: the generator's scope
    refuses the NESTED shape (the product's `List (String × Descr)`
    field is `Kit.Derive.Fold` eKD0005's named exclusion), exactly
    like the GADT family's `foldValue`. -/
structure DescrAlg (P : Descr → Sort u) (Q : List (String × Descr) → Sort u) where
  /-- The leaf row: the boundary universe's type rides raw. -/
  prim : ∀ (t : Ty), P (.prim t)
  /-- The optional row: receives the child's result. -/
  option : ∀ (d : Descr), P d → P (.option d)
  /-- The sequence row: receives the child's result. -/
  list : ∀ (d : Descr), P d → P (.list d)
  /-- The record row: receives the field walk's result. -/
  product : ∀ (n : String) (fs : List (String × Descr)), Q fs → P (.product n fs)
  /-- The empty field list. -/
  pnil : Q []
  /-- One field: the field's name + description ride raw, the field's
      result and the tail's result are the subresults. -/
  pcons : ∀ (fn : String) (d : Descr) (fs : List (String × Descr)),
      P d → Q fs → Q ((fn, d) :: fs)

mutual
/-- THE ONE WALK (the initial-algebra fold over the description —
    01 §1 at the meta-universe): mutual over the field sibling,
    structural (the same nested shape `drawDescr` walks),
    kernel-visible. Every derivation over `Descr` is THIS walk
    applied to an algebra; a new ctor extends it exactly once. -/
def foldDescr {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) : (d : Descr) → P d
  | .prim t => alg.prim t
  | .option d => alg.option d (foldDescr alg d)
  | .list d => alg.list d (foldDescr alg d)
  | .product n fs => alg.product n fs (foldFields alg fs)

def foldFields {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) : (fs : List (String × Descr)) → Q fs
  | [] => alg.pnil
  | (fn, d) :: rest => alg.pcons fn d rest (foldDescr alg d) (foldFields alg rest)
end

/-- The equation set (06 §5 — consumers prove against these, never
    against brecOn plumbing). All `rfl`: the recursion is structural,
    so the equations are kernel reduction. -/
theorem foldDescr_prim {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) (t : Ty) :
    foldDescr alg (.prim t) = alg.prim t := rfl
theorem foldDescr_option {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) (d : Descr) :
    foldDescr alg (.option d) = alg.option d (foldDescr alg d) := rfl
theorem foldDescr_list {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) (d : Descr) :
    foldDescr alg (.list d) = alg.list d (foldDescr alg d) := rfl
theorem foldDescr_product {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) (n : String) (fs : List (String × Descr)) :
    foldDescr alg (.product n fs) = alg.product n fs (foldFields alg fs) := rfl
theorem foldFields_nil {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) : foldFields alg [] = alg.pnil := rfl
theorem foldFields_cons {P : Descr → Sort u} {Q : List (String × Descr) → Sort u}
    (alg : DescrAlg P Q) (fn : String) (d : Descr) (fs : List (String × Descr)) :
    foldFields alg ((fn, d) :: fs)
      = alg.pcons fn d fs (foldDescr alg d) (foldFields alg fs) := rfl

/-- THE GENERIC CORRECTNESS THEOREM (16-surface §4.4's "one generic
    correctness theorem instead of per-handler proofs"): a correctness
    claim family `C` over the descriptions whose per-ctor ROWS are
    lawful (each composite claim built from the children's claims —
    the algebra's rows) holds EVERYWHERE, by the ONE induction the
    fold performs. The per-capability theorems are instances: they
    supply the rows (`tyOfDescr_some` here; `deriveCodec_correct` /
    `deriveDec_eq` in Derive.lean), never an induction. -/
theorem law_of_rows {C : Descr → Prop} {CF : List (String × Descr) → Prop}
    (alg : DescrAlg C CF) : ∀ d, C d := foldDescr alg

/-! ## The projection into the boundary universe -/

/-- The projection ALGEBRA: the description's projection into the
    closed boundary universe `Ty` (the registry's field type) as a
    `DescrAlg` value — the rows verbatim from the pre-fold walk. -/
def tyAlg : DescrAlg (fun _ => Option Ty) (fun _ => Option Ty) where
  prim t := some t
  option _ rest := .option <$> rest
  list _ rest := .list <$> rest
  product _ _ _ := none
  pnil := none
  pcons _ _ _ _ rest := rest

/-- The description's projection into the closed boundary universe `Ty`
    (the registry's field type). `none` = the description is a PRODUCT
    — a record, not a boundary leaf. This is the interop spine: the
    registry's `Item` reads descriptions THROUGH it. MIGRATED to the
    ONE walk (16-surface §4.4). -/
def tyOfDescr : Descr → Option Ty := foldDescr tyAlg

/-- The projection's equation set (the fold's rows at the concrete
    algebra — the coherence proof below cites these). -/
theorem tyOfDescr_prim (t : Ty) : tyOfDescr (.prim t) = some t := rfl
theorem tyOfDescr_option (d : Descr) :
    tyOfDescr (.option d) = Option.map (.option) (tyOfDescr d) := rfl
theorem tyOfDescr_list (d : Descr) :
    tyOfDescr (.list d) = Option.map (.list) (tyOfDescr d) := rfl
theorem tyOfDescr_product (n : String) (fs : List (String × Descr)) :
    tyOfDescr (.product n fs) = none := rfl

/-! ## The first generic derivation — the rendering (the proof the layer pays) -/

/-- The rendering ALGEBRA (the rows verbatim from the pre-fold walk).
    Leaf positions DELEGATE to the boundary's one renderer (`renderTy`
    — 06 §7's one-reifier-family rule); a product renders as its
    wire-name reference — the record BODY is the emitter lane's
    (`SchemaCore.Emit.renderWit` over the registry), never duplicated
    here. -/
def renderAlg : DescrAlg (fun _ => String) (fun _ => String) where
  prim t := renderTy t
  option _ rest := s!"option<{rest}>"
  list _ rest := s!"list<{rest}>"
  product n _ _ := s!"record<{kebabName ((n.splitOn ".").getLast!)}>"
  pnil := ""
  pcons _ _ _ _ rest := rest

/-- THE FIRST GENERIC DERIVATION over the description (05 §3 step 2's
    shape): the WIT-flavored type rendering — MIGRATED to the ONE walk
    (16-surface §4.4): the handler IS an algebra value. -/
def deriveRender : Descr → String := foldDescr renderAlg

/-- The rendering's equation set (the coherence proof below cites
    these). The product row's name mangling is string machinery —
    equation lemmas, not `rfl` pins (the same tier as `kebabName`). -/
theorem deriveRender_prim (t : Ty) : deriveRender (.prim t) = renderTy t := rfl
theorem deriveRender_option (d : Descr) :
    deriveRender (.option d) = s!"option<{deriveRender d}>" := rfl
theorem deriveRender_list (d : Descr) :
    deriveRender (.list d) = s!"list<{deriveRender d}>" := rfl
theorem deriveRender_product (n : String) (fs : List (String × Descr)) :
    deriveRender (.product n fs)
      = s!"record<{kebabName ((n.splitOn ".").getLast!)}>" := rfl

/-- THE COHERENCE CLAIM ALGEBRA: the factored fact's per-ctor rows —
    the option/list rows compose the child's coherence (the ONLY
    content), the product row refuses (a product projects to `none`).
    The instance below is `law_of_rows`' first citation — the induction
    is the fold's, performed ONCE in the generic theorem. -/
def coherenceAlg :
    DescrAlg
      (P := fun d => ∀ t, tyOfDescr d = some t →
        Descr.Ty d = t.toType ∧ deriveRender d = renderTy t)
      (Q := fun _ => True) where
  prim t := fun t' h => by
    rw [tyOfDescr_prim] at h
    cases h
    exact ⟨rfl, rfl⟩
  option d ih := by
    intro t' h
    cases hd : tyOfDescr d with
    | none => rw [tyOfDescr_option, hd, Option.map_none] at h; cases h
    | some t0 =>
        rw [tyOfDescr_option, hd] at h
        simp only [Option.map_some] at h
        cases h
        show Option d.Ty = Option t0.toType ∧
          s!"option<{deriveRender d}>" = s!"option<{renderTy t0}>"
        rw [(ih t0 hd).1, (ih t0 hd).2]
        exact ⟨rfl, rfl⟩
  list d ih := by
    intro t' h
    cases hd : tyOfDescr d with
    | none => rw [tyOfDescr_list, hd, Option.map_none] at h; cases h
    | some t0 =>
        rw [tyOfDescr_list, hd] at h
        simp only [Option.map_some] at h
        cases h
        show List d.Ty = List t0.toType ∧
          s!"list<{deriveRender d}>" = s!"list<{renderTy t0}>"
        rw [(ih t0 hd).1, (ih t0 hd).2]
        exact ⟨rfl, rfl⟩
  product _ _ _ := fun t h => by
    rw [tyOfDescr_product] at h
    cases h
  pnil := trivial
  pcons _ _ _ _ _ := trivial

/-- THE FACTORED COHERENCE FACT (the pre-deepening twin `fun_induction`
    scripts retired — the two laws below are its two CITATIONS): a
    description that projects to `t` BOTH denotes `t`'s reification
    AND renders as `t`'s rendering — the projection is the only road
    into the boundary universe. THE GENERIC THEOREM'S FIRST INSTANCE:
    the proof is `law_of_rows` over `coherenceAlg` — the per-ctor rows
    above, no induction here (16-surface §4.4). -/
theorem tyOfDescr_some (d : Descr) :
    ∀ t, tyOfDescr d = some t →
      Descr.Ty d = t.toType ∧ deriveRender d = renderTy t :=
  law_of_rows coherenceAlg d

/-- LAW: the projection and the denotation agree — wherever the
    description projects to `t`, its denotation IS `t`'s reification
    (the description layer adds the RECORD dimension; it does not
    re-interpret the leaves). First citation of the factored fact. -/
theorem tyOfDescr_denotes (d : Descr) :
    ∀ t, tyOfDescr d = some t → Descr.Ty d = t.toType :=
  fun t h => (tyOfDescr_some d t h).1

/-- LAW (the anti-parallelism guarantee, mechanically): wherever the
    description projects into the boundary universe, the derived
    rendering IS the boundary's rendering. The description layer is
    not a parallel renderer — it is the record layer over the ONE
    `Ty` fold. Second citation of the factored fact. -/
theorem deriveRender_coherent (d : Descr) :
    ∀ t, tyOfDescr d = some t → deriveRender d = renderTy t :=
  fun t h => (tyOfDescr_some d t h).2

/-! ## The bridge onto the registry's first-order rows -/

/-- The flattening ALGEBRA: the field walk as a `DescrAlg` value (the
    sub-results' shapes ride the rows; the cons row reads the field's
    OWN description — the name + description ride raw). -/
def itemAlg :
    DescrAlg (P := fun _ => Unit) (Q := fun _ => Except Kit.Diag (List Field)) where
  prim _ := ()
  option _ _ := ()
  list _ _ := ()
  product _ _ _ := ()
  pnil := .ok []
  pcons fn d _ _ rest' :=
    match tyOfDescr d with
    | some t => (rest').map fun fs' => { name := fn, ty := t } :: fs'
    | none =>
        .error (Kit.Diag.closedWorld ⟨"SD0006"⟩
          s!"`{fn}`: a nested product field is outside the registry's \
            first-order row shape — a row holds one `Ty` per field"
          .error fn
          ["a leaf, option, or list field (something `tyOfDescr` maps)"])

/-- The field walk: an ordered field list flattens to the registry's
    `List Field` (registration order). MIGRATED to the ONE walk (the
    field sibling of `foldDescr`). A NESTED PRODUCT field is outside
    the row shape — the curated refusal (`SD0006`). -/
def itemOfFields : List (String × Descr) → Except Kit.Diag (List Field) :=
  foldFields itemAlg

/-- The bridge: a description flattens onto the registry's `Item` (the
    describe → register direction). A NON-PRODUCT description is not a
    record — the curated refusal (`SD0005`). -/
def itemOfDescr (d : Descr) : Except Kit.Diag Item :=
  match d with
  | .product n fs =>
      (itemOfFields fs).map fun fields => { name := n, fields }
  | _ =>
      .error (Kit.Diag.closedWorld ⟨"SD0005"⟩
        "not a record — the registry's rows are records"
        .error (deriveRender d)
        ["a product description"])

/-! ## The reifier family — the ONE expression walk -/

/-- The cap argument's Nat extraction: the literal spellings `Fin`'s
    binder carries (`42` as a literal, or `OfNat.ofNat 42 …` —
    elaborated Nat numerals arrive unfolded through the instance). A
    non-literal cap is the loud refusal (`none`), never a default.
    `partial` (the written reason): the `Expr` subterm walk is not
    structural — the same allowance as `tyOfExpr?` itself (06 §7). -/
partial def natLitOf? (e : Lean.Expr) : Option Nat :=
  let e := e.headBeta
  match e.getAppFn, e.getAppArgs with
  | .lit (.natVal n), _ => some n
  | .const c _, args =>
      match c, args with
      | ``OfNat.ofNat, #[_, a, _] => natLitOf? a
      | _, _ => none
  | _, _ => none

/-- The KEY reifier: a Lean type expression → the closed scalar
    sub-universe, when the type is one of the four scalars. Map keys
    reify DIRECTLY as `KeyTy` — the key position is below the first
    `Ty` fold (Ty.lean's discipline; `KeyTy.toTy` is the coherence). -/
def keyOfExpr? (e : Lean.Expr) : Option KeyTy :=
  let e := e.headBeta
  match e.getAppFn, e.getAppArgs with
  | .const c _, _ =>
    match c with
    | ``Bool => some .bool
    | ``UInt64 => some .u64
    | ``Int64 => some .i64
    | ``String => some .string
    | _ => none
  | _, _ => none

/-- Partial reifier: a Lean type expression → the closed `Ty`, when the
    type is in the boundary fragment. The match over `Ty`'s Lean
    spellings is the SECOND fold every new `Ty` constructor extends.
    The sum shape rides `Sum a b` → `.result`; the map shape rides
    `List (K × V)` → `.map` (the key reified as a `KeyTy`); the bounded
    lane's base type rides `Fin cap` → `.bounded cap`. The SET shape
    has NO Lean spelling here — `List K` reifies to `.list K` (the
    honest reading); a set field needs a wrapper-typed authoring
    surface, so `.set`'s consumer waits (the leftover rule). -/
partial def tyOfExpr? (e : Lean.Expr) : Option Ty :=
  let e := e.headBeta
  match e.getAppFn, e.getAppArgs with
  | .const c _, args =>
    match c, args with
    | ``Bool, #[] => some .bool
    | ``UInt64, #[] => some .u64
    | ``Int64, #[] => some .i64
    | ``String, #[] => some .string
    | ``Option, #[a] => .option <$> tyOfExpr? a
    | ``Sum, #[a, b] =>
        match tyOfExpr? a, tyOfExpr? b with
        | some x, some y => some (.result x y)
        | _, _ => none
    | ``Fin, #[cap] =>
        (.bounded ·) <$> natLitOf? cap
    | ``List, #[a] =>
        -- the MAP shape: `List (K × V)` reifies to `.map K V` when the
        -- key is a closed scalar; a non-scalar key or a non-reifiable
        -- value is the loud refusal (none), never a silent `.list`
        match a.getAppFn, a.getAppArgs with
        | .const c _, #[k, v] =>
            match c with
            | ``Prod =>
                match keyOfExpr? k with
                | some k =>
                    match tyOfExpr? v with
                    | some v => some (.map k v)
                    | none => none
                | none => .list <$> tyOfExpr? a
            | _ => .list <$> tyOfExpr? a
        | _, _ => .list <$> tyOfExpr? a
    | _, _ => none
  | _, _ => none

/-- The explicit binder types of a ctor's type, in declaration order
    (a flat structure's fields — no subobject parents, no typeclass
    binders at this size). -/
def ctorArgTypes : Lean.Expr → List Lean.Expr
  | .forallE _ d b bi =>
      if bi.isExplicit then d :: ctorArgTypes b else ctorArgTypes b
  | .letE _ _ _ b _ => ctorArgTypes b
  | _ => []

/-! ## The reflector (meta) — the elaboration-time entry -/

/-- The supported fragment, spelled for the refusal's valid space (the
    closed-world rule: errors enumerate the valid moves). -/
def describeFragment : List String :=
  ["Bool", "UInt64", "Int64", "String", "Option _", "List _", "Sum _ _"]

/-- The got-slot's FULL type text: a tiny pure renderer over the type
    expression (the reflector is monad-free — a delaborator would need
    `MetaM`). The whole expr renders — head AND spine (`List (Prod
    String UInt64)` says the full type, never a bare `List` head that
    misnames an association list as a plain sequence). Non-const/
    non-app shapes (not in this fragment's refusals) fall back to
    `(complex)`. -/
def typeExprString : Lean.Expr → String
  | .const c _ => c.toString
  | .app f a =>
      match f with
      | .const c _ => s!"{c.toString} ({typeExprString a})"
      | _ => s!"{typeExprString f} {typeExprString a}"
  | _ => "(complex)"

/-- The field-type classifier: a Lean type expression → its description.
    Wrappers reflect AS wrappers (`Option` → `.option`, `List` →
    `.list`); EVERYTHING else — the four scalars, the sum shape
    (`Sum a b`), the map shape (`List (K × V)`), the bounded base
    (`Fin cap`) — is the reifier's own verdict lifted ONE way
    (`.prim <$> tyOfExpr?`): the description layer adds the WRAPPER
    dimension and never a second leaf walk (ONE reifier family, ONE
    module). `partial` (the written reason): the `Expr` subterm walk
    is not structural — the same allowance as `tyOfExpr?` itself,
    ratcheting down only. -/
meta partial def descrOfExpr? (e : Lean.Expr) : Option Descr :=
  let e := e.headBeta
  match e.getAppFn, e.getAppArgs with
  | .const c _, args =>
      match c, args with
      | ``Option, #[a] => .option <$> descrOfExpr? a
      | ``List, #[a] =>
          -- the MAP shape is `tyOfExpr?`'s verdict on the WHOLE expr:
          -- `List (K × V)` reifies to `.map k v` (the association-list
          -- spelling — the fixture's documented intent) and lifts to the
          -- leaf `.prim (.map k v)`; any other element re-classifies as
          -- a plain sequence. (`tyOfExpr?`'s map detection lives in its
          -- OWN `List` arm — the verdict must be asked of the full
          -- `List (K × V)` expression, never of the bare `K × V`
          -- element, whose head is not in `tyOfExpr?`'s fragment.)
          match tyOfExpr? e with
          | some (.map k v) => some (.prim (.map k v))
          | _ => .list <$> descrOfExpr? a
      | _, _ => (.prim ·) <$> tyOfExpr? e
  | _, _ => none

/-- THE elaboration-time reflector (05 §3 step 1): a declared structure
    → its description. Pure over the environment — NO monad, the
    refusals are `Kit.Diag` VALUES (testable at elaboration, pinnable
    in SchemaTests); every refusal is the closed-world Diag (got + the
    valid space + the ONE engine's did-you-mean), never a sentinel.

    E-codes (call-site literals; the persisted allocation rides the
    code-registry consumer lane — Kit.Diag's note):
    `SD0001` not a structure; `SD0002` field type outside the fragment;
    `SD0003` flatness/arity; `SD0004` ctor not found. -/
meta def describe (env : Lean.Environment) (declName : Lean.Name) :
    Except Kit.Diag Descr :=
  if !(Lean.isStructure env declName) then
    .error (Kit.Diag.closedWorld ⟨"SD0001"⟩
      s!"`{declName}` is not a structure — `describe` reflects records; \
        the fields ARE the schema"
      .error declName.toString
      ["a flat structure whose field types are in the boundary fragment"])
  else
    let fieldNames := Lean.getStructureFields env declName
    let ctor := Lean.getStructureCtor env declName
    match env.find? ctor.name with
    | some (.ctorInfo ci) =>
        let tys := ctorArgTypes ci.type
        if tys.length != fieldNames.size then
          .error (Kit.Diag.closedWorld ⟨"SD0003"⟩
            s!"`{declName}`: {fieldNames.size} fields but {tys.length} ctor \
              binders — flat structures only at this size"
            .error declName.toString
            ["a flat structure (no subobject parents, no typeclass binders)"])
        else
          let step (acc : Except Kit.Diag (List (String × Descr)))
              (pair : Lean.Name × Lean.Expr) :
              Except Kit.Diag (List (String × Descr)) :=
            match acc with
            | .error e => .error e
            | .ok fs =>
                match descrOfExpr? pair.2 with
                | none =>
                    let got := typeExprString pair.2
                    .error (Kit.Diag.closedWorld ⟨"SD0002"⟩
                      s!"`{declName}.{pair.1}`: the field type is outside the \
                        supported fragment — `describe` reflects the boundary \
                        universe's leaves, wrapped in option/list/sum"
                      .error got describeFragment)
                | some d => .ok (fs ++ [(pair.1.toString, d)])
          match (fieldNames.toList.zip tys).foldl step (.ok []) with
          | .error e => .error e
          | .ok fs =>
              .ok (.product declName.toString fs)
    | none | some _ =>
        .error { code := ⟨"SD0004"⟩
                 message := s!"`{declName}`: structure ctor not found" }

/-- THE `@[schema]` route — the CONVERGED reflection (05 §3: reflect
    → Descr → the item): `describe`, then flatten, BOTH stages on the
    curated `Kit.Diag` surface (05 §4) — the route adds no error
    drift. The lane's `Except String` contract flattens this ONCE at
    the substrate boundary (SchemaCore.Register's builder adapter). -/
meta def reflectItemViaDescr (env : Lean.Environment) (declName : Lean.Name) :
    Except Kit.Diag Item :=
  describe env declName >>= itemOfDescr

end SchemaCore
