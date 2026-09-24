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

Core-only EXCEPT the reflector (the meta declarations below — the
elaboration-time surface; the pure universe + interpretation +
derivations are core and never import meta names).

The five questions (notes/v3/01-core.md):
- root: Universe — the ONE deliberate meta-universe (D19): closed
  description codes + total denotation (`Descr.Ty`).
- carrier: the interpretation is a Type-valued fold (wrong-shape
  denotations unrepresentable; the product's tuple is the canonical
  row shape — the record↔tuple bridge is the row-iso lane).
- spine reading: the REFLECTION stage's typed face — declaration →
  `describe` → `Descr` → (generic derivation) → capability surface.
- ladder rung: the derivations are structural folds (kernel-visible;
  concrete descriptions reduce by `rfl`); the coherence laws are
  functional inductions.
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

/-! ## The projection into the boundary universe -/

/-- The description's projection into the closed boundary universe `Ty`
    (the registry's field type). `none` = the description is a PRODUCT
    — a record, not a boundary leaf. This is the interop spine: the
    registry's `Item` reads descriptions THROUGH it. -/
def tyOfDescr : Descr → Option Ty
  | .prim t => some t
  | .option d => .option <$> tyOfDescr d
  | .list d => .list <$> tyOfDescr d
  | .product _ _ => none

/-! ## The first generic derivation — the rendering (the proof the layer pays) -/

/-- THE FIRST GENERIC DERIVATION over the description (05 §3 step 2's
    shape): the WIT-flavored type rendering, one structural fold,
    generic over `Descr`. Leaf positions DELEGATE to the boundary's
    one renderer (`renderTy` — 06 §7's one-reifier-family rule); a
    product renders as its wire-name reference — the record BODY is
    the emitter lane's (`SchemaCore.Emit.renderWit` over the registry),
    never duplicated here. -/
def deriveRender : Descr → String
  | .prim t => renderTy t
  | .option d => s!"option<{deriveRender d}>"
  | .list d => s!"list<{deriveRender d}>"
  | .product n _ => s!"record<{kebabName ((n.splitOn ".").getLast!)}>"

/-- THE FACTORED COHERENCE FACT (the twin `fun_induction` scripts
    collapsed — the two laws below are its two CITATIONS, one case
    script total): a description that projects to `t` BOTH denotes
    `t`'s reification AND renders as `t`'s rendering — the projection
    is the only road into the boundary universe. -/
theorem tyOfDescr_some (d : Descr) :
    ∀ t, tyOfDescr d = some t →
      Descr.Ty d = t.toType ∧ deriveRender d = renderTy t := by
  fun_induction tyOfDescr d
  case case1 t0 =>
    intro t h
    cases h
    exact ⟨rfl, rfl⟩
  case case2 d ih =>
    intro t h
    cases hd : tyOfDescr d with
    | none =>
        rw [hd] at h
        exact absurd h (by simp)
    | some t0 =>
        rw [hd] at h
        rw [show Ty.option <$> some t0 = some (.option t0) from rfl] at h
        cases h
        show Option d.Ty = Option t0.toType ∧
          s!"option<{deriveRender d}>" = s!"option<{renderTy t0}>"
        rw [(ih t0 hd).1, (ih t0 hd).2]
        exact ⟨rfl, rfl⟩
  case case3 d ih =>
    intro t h
    cases hd : tyOfDescr d with
    | none =>
        rw [hd] at h
        exact absurd h (by simp)
    | some t0 =>
        rw [hd] at h
        rw [show Ty.list <$> some t0 = some (.list t0) from rfl] at h
        cases h
        show List d.Ty = List t0.toType ∧
          s!"list<{deriveRender d}>" = s!"list<{renderTy t0}>"
        rw [(ih t0 hd).1, (ih t0 hd).2]
        exact ⟨rfl, rfl⟩
  case case4 _ _ =>
    intro t h
    exact absurd h (by simp)

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

/-- The field walk: an ordered field list flattens to the registry's
    `List Field` (registration order). A NESTED PRODUCT field is
    outside the row shape — the curated refusal (`SD0006`). -/
def itemOfFields : List (String × Descr) → Except Kit.Diag (List Field)
  | [] => .ok []
  | (fn, fd) :: rest =>
      match tyOfDescr fd with
      | some t => (itemOfFields rest).map fun fs' => { name := fn, ty := t } :: fs'
      | none =>
          .error (Kit.Diag.closedWorld ⟨"SD0006"⟩
            s!"`{fn}`: a nested product field is outside the registry's \
              first-order row shape — a row holds one `Ty` per field"
            .error fn
            ["a leaf, option, or list field (something `tyOfDescr` maps)"])

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
