/-
# LeanSubstrait.Typed.ToProto

Lowering from the schema-indexed layer to the wire-faithful `Proto` layer.

`Rel.toProto : Rel inS outS → Proto.Rel` erases every schema/proof index:
ordinals begin life as runtime data (`Column.ordinal`) and anchors are
computed at emission — so there is nothing to erase from proofs.

**Anchor assignment.**  Extension URN/function/type anchors are *computed at
emission* from the declaration list a plan uses:

1. `Rel.toCtx` walks the typed rel once (bottom-up, children first) and
   builds an `ExtCtx` with distinct (urn, name) pairs for functions and
   extension types, in first-use order, plus the distinct URNs they belong to.
2. Anchors are the 1-based indices into those lists (urn anchor 1..K,
   function anchor 1..N, type anchor 1..M) — deterministic for a given rel.
3. `Rel.toProto` and `Rel.toPlan` share the same context, so
   `ScalarFunction.function_reference` and the `=== Extensions` declarations
   are consistent by construction.

The public signatures match the design exactly: `Rel.toProto : Rel inS outS →
Proto.Rel` and `Rel.toPlan : Rel inS outS → Proto.Plan`.
-/
import LeanSubstrait.Typed.Rel
import LeanSubstrait.Proto.Plan

namespace LeanSubstrait.Typed

/-! ## Extension context (anchors computed at emission) -/

/-- Core Lean has no `List.enum`; local (index, value) enumeration helper. -/
def enumerate (xs : List α) : List (Nat × α) :=
  let rec go : Nat → List α → List (Nat × α)
    | _, [] => []
    | i, x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

/--
The extension declarations a plan uses, collected in deterministic
(first-use, bottom-up) order.  Anchors are 1-based indices into these lists.
-/
structure ExtCtx where
  urns : List String
  functions : List (String × String)  -- (urn, name)
  types : List (String × String)      -- (urn, name)
deriving Repr, Inhabited

/-- The empty context. -/
def ExtCtx.empty : ExtCtx := { urns := [], functions := [], types := [] }

/-- 1-based index of the first element equal to `x`, else 0. -/
def indexOf1 (x : α) [BEq α] (xs : List α) : Nat :=
  match xs.findIdx? (fun y => y == x) with
  | some i => i + 1
  | none   => 0

namespace ExtCtx

/-- URN anchor for an URN (0 when undeclared — a construction bug, since `toCtx` adds every URN it uses). -/
def urnAnchor (c : ExtCtx) (urn : String) : Nat := indexOf1 urn c.urns

/-- Function anchor for an (urn, name) pair. -/
def functionAnchor (c : ExtCtx) (urn name : String) : Nat := indexOf1 (urn, name) c.functions

/-- Type anchor for an (urn, name) pair. -/
def typeAnchor (c : ExtCtx) (urn name : String) : Nat := indexOf1 (urn, name) c.types

/-- Add an URN if absent (first-use order maintained). -/
def addUrn (c : ExtCtx) (urn : String) : ExtCtx :=
  if urn.isEmpty then c else if c.urns.contains urn then c else { c with urns := c.urns ++ [urn] }

/-- Add a function declaration (plus its URN) if absent. -/
def addFunction (c : ExtCtx) (urn name : String) : ExtCtx :=
  let c := c.addUrn urn
  if c.functions.contains (urn, name) then c else { c with functions := c.functions ++ [(urn, name)] }

/-- Add a type declaration (plus its URN) if absent. -/
def addType (c : ExtCtx) (urn name : String) : ExtCtx :=
  let c := c.addUrn urn
  if c.types.contains (urn, name) then c else { c with types := c.types ++ [(urn, name)] }

/-- The `SimpleExtensionUrn` list (anchor order). -/
def toUrns (c : ExtCtx) : List Proto.SimpleExtensionUrn :=
  (enumerate c.urns).map (fun (i, urn) => { extensionUrnAnchor := i + 1, urn := urn })

/-- The `SimpleExtensionDeclaration` list (functions, then types; anchor order). -/
def toDeclarations (c : ExtCtx) : List Proto.ExtensionDeclaration :=
  (enumerate c.functions).map (fun (i, (urn, name)) =>
      .function (indexOf1 urn c.urns) (i + 1) name) ++
  (enumerate c.types).map (fun (i, (urn, name)) =>
      .extType (indexOf1 urn c.urns) (i + 1) name)

/-- True when nothing is declared (nothing to emit in `=== Extensions`). -/
def isEmpty (c : ExtCtx) : Bool :=
  c.urns.isEmpty && c.functions.isEmpty && c.types.isEmpty

/-- Merge two contexts: fold `d`'s declarations into `c` (first-use order kept). -/
def merge (c d : ExtCtx) : ExtCtx :=
  d.urns.foldl (fun c u => c.addUrn u) c
    |> fun c => d.functions.foldl (fun c (u, n) => c.addFunction u n) c
    |> fun c => d.types.foldl (fun c (u, n) => c.addType u n) c

end ExtCtx

/-! ## Collecting the declarations a rel uses -/

/-! Fold an `Expr`'s functions into the context (value-first for dot notation).
(`mutual` needed: `Expr.addSigs` and `Args.addSigs` call each other.) -/
mutual
  def Expr.addSigs (e : Expr s t n) (c : ExtCtx) : ExtCtx :=
    match e with
    | .call sig args => args.addSigs (c.addFunction sig.urn sig.name)
    | _ => c

  /-- Fold an `Args` spine's functions into the context. -/
  def Args.addSigs (a : Args s ts) (c : ExtCtx) : ExtCtx :=
    match a with
    | .nil => c
    | .cons t n e rest => rest.addSigs (e.addSigs c)
end

/-- Fold a `AnyExpr`'s functions into the context. -/
def AnyExpr.addSigs (x : AnyExpr s) (c : ExtCtx) : ExtCtx :=
  match x with
  | .mk _ _ e => e.addSigs c

/-- Type references of a typed type (extension types only; first-use order). -/
def SType.typeRefs : SType → List (String × String)
  | .userDefined urn name _ => [(urn, name)]
  | .list e                 => e.typeRefs
  | .map k v                => k.typeRefs ++ v.typeRefs
  | .struct fs              => fs.map SType.typeRefs |>.flatten
  | _                       => []

/-- Type references of a schema (columns, in order). -/
def Schema.typeRefs (s : Schema) : List (String × String) :=
  s.map (fun (_, t, _) => t.typeRefs) |>.flatten

/--
Collect the extension context of a typed rel: every function signature in
every expression/measure, plus every extension type in every read schema —
bottom-up, children first, first-use order.
-/
def Rel.toCtx {inS outS : Schema} (rel : Rel inS outS) : ExtCtx :=
  match rel with
  | .read _ schema =>
      schema.typeRefs.foldl (fun c (urn, name) => c.addType urn name) ExtCtx.empty
  | .filter input cond =>
      cond.addSigs input.toCtx
  | .project input outs _ =>
      outs.foldl (fun c pr => pr.expr.addSigs c) input.toCtx
  | .aggregate input grouping measures =>
      let c := input.toCtx
      let c := grouping.foldl (fun c ae => ae.addSigs c) c
      measures.foldl (fun c m => m.args.foldl (fun c ae => ae.addSigs c) c) c
  | .sort input _ =>
      input.toCtx
  | .fetch input _ _ =>
      input.toCtx
  | .join left right cond _ =>
      cond.addSigs (ExtCtx.merge left.toCtx right.toCtx)
  | .set _ left right =>
      ExtCtx.merge left.toCtx right.toCtx
  | .write _ _ _ input =>
      input.toCtx
  | .extensionSingle _ input =>
      input.toCtx

/-! ## Type lowering -/

/-! Lower a typed parameter to the wire `Proto.PParam`.
(`mutual` needed: `toProtoParam` and `toProtoType` call each other.) -/
mutual
  def toProtoParam (ctx : ExtCtx) : SParam → Proto.PParam
  | .boolean b  => .boolean b
  | .integer i  => .integer i
  | .string s   => .string s
  | .enum e     => .enum e
  | .null t     => .null (toProtoType ctx t)
  | .dataType t => .dataType (toProtoType ctx t)

  /-- Lower a typed `SType` to the wire `Proto.PType` (nullability carried separately). -/
  def toProtoType (ctx : ExtCtx) : SType → Proto.PType
  | .bool   => .bool   .required
  | .i8     => .i8     .required
  | .i16    => .i16    .required
  | .i32    => .i32    .required
  | .i64    => .i64    .required
  | .fp32   => .fp32   .required
  | .fp64   => .fp64   .required
  | .string => .string .required
  | .binary => .binary .required
  | .decimal p s => .decimal p s .required
  | .list e      => .list (toProtoType ctx e) .required
  | .map k v     => .map (toProtoType ctx k) (toProtoType ctx v) .required
  | .struct fs   => .struct (fs.map (toProtoType ctx)) .required
  | .userDefined urn name params =>
      .userDefined (ctx.typeAnchor urn name) (params.map (toProtoParam ctx)) .required

  /-- Apply the column/expression nullability to a lowered type (always explicit). -/
  def withNullable : Proto.PType → Bool → Proto.PType
  | .bool _      , true  => .bool .nullable
  | .bool _      , false => .bool .required
  | .i8 _        , true  => .i8 .nullable
  | .i8 _        , false => .i8 .required
  | .i16 _       , true  => .i16 .nullable
  | .i16 _       , false => .i16 .required
  | .i32 _       , true  => .i32 .nullable
  | .i32 _       , false => .i32 .required
  | .i64 _       , true  => .i64 .nullable
  | .i64 _       , false => .i64 .required
  | .fp32 _      , true  => .fp32 .nullable
  | .fp32 _      , false => .fp32 .required
  | .fp64 _      , true  => .fp64 .nullable
  | .fp64 _      , false => .fp64 .required
  | .string _    , true  => .string .nullable
  | .string _    , false => .string .required
  | .binary _    , true  => .binary .nullable
  | .binary _    , false => .binary .required
  | .decimal p s _, true  => .decimal p s .nullable
  | .decimal p s _, false => .decimal p s .required
  | .list e _    , true  => .list e .nullable
  | .list e _    , false => .list e .required
  | .map k v _   , true  => .map k v .nullable
  | .map k v _   , false => .map k v .required
  | .struct fs _ , true  => .struct fs .nullable
  | .struct fs _ , false => .struct fs .required
  | .userDefined a p _, true  => .userDefined a p .nullable
  | .userDefined a p _, false => .userDefined a p .required
end

/-- Lower a schema column `(name, t, n)` to a wire type with its nullability. -/
def toProtoColType (ctx : ExtCtx) : SchemaCol → Proto.PType
  | (_, t, n) => withNullable (toProtoType ctx t) n

/-! ## Expression lowering -/

/-- Lower a literal payload to the wire literal type. -/
def toProtoLiteralValue : LiteralValue t → Proto.LiteralType
  | .bool b    => .bool b
  | .i8 v      => .i8 v
  | .i16 v     => .i16 v
  | .i32 v     => .i32 v
  | .i64 v     => .i64 v
  | .fp32 v    => .fp32 v
  | .fp64 v    => .fp64 v
  | .string s  => .string s
  | .binary b  => .binary b

/-! Lower a typed expression to the wire (ordinals/anchors computed here).
Value-first so dot notation (`e.toProto ctx`) works.  (`mutual` needed:
`Expr.toProto` and `Args.toProto` call each other.) -/
mutual
  def Expr.toProto (e : Expr s t n) (ctx : ExtCtx) : Proto.Expression :=
    match e with
    | .literal _ nv v =>
        Proto.Expression.literal { literalType := toProtoLiteralValue v, nullable := nv }
    | @Expr.field _ c _ _ _ =>
        Proto.Expression.field { ordinal := c.ordinal, segment := none }
    | .call sig args =>
        Proto.Expression.scalarFunction
          (ctx.functionAnchor sig.urn sig.name)
          (args.toProto ctx)
          (withNullable (toProtoType ctx sig.ret) sig.retNullable)

  /-- Lower an `Args` spine to proto expressions. -/
  def Args.toProto (a : Args s ts) (ctx : ExtCtx) : List Proto.Expression :=
    match a with
    | .nil => []
    | .cons t n e rest => e.toProto ctx :: rest.toProto ctx
end

/-! ## Relation lowering -/

/-- Lower a typed rel to a wire rel, using the given context for anchors.  Value-first so dot notation works. -/
def Rel.toProtoWith (rel : Rel inS outS) (ctx : ExtCtx) : Proto.Rel :=
  match rel with
  | .read table schema =>
      Proto.Rel.read { readType := .namedTable [table]
                       baseSchema := some { fields := schema.map (toProtoColType ctx), names := schema.names }
                       common := none }
  | .filter input cond =>
      Proto.Rel.filter { condition := cond.toProto ctx, input := input.toProtoWith ctx, common := none }
  | .project input outs emit =>
      Proto.Rel.project { expressions := outs.map (fun pr => pr.expr.toProto ctx)
                          input := input.toProtoWith ctx
                          common := emit.map (fun m =>
                            { emit := some (.emit m), advancedExtension := none }) }
  | .aggregate input grouping measures =>
      Proto.Rel.aggregate
        { groupingExpressions := grouping.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
          measures := measures.map (fun m =>
            { measure :=
              { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } })
          input := input.toProtoWith ctx, common := none }
  | .sort input orderBy =>
      Proto.Rel.sort { sorts := orderBy.map (fun k =>
                          ⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                           k.direction⟩)
                       input := input.toProtoWith ctx, common := none }
  | .fetch input limit offset =>
      Proto.Rel.fetch { limit := limit, offset := offset, input := input.toProtoWith ctx, common := none }
  | .join left right cond jt =>
      Proto.Rel.join { joinType := jt, left := left.toProtoWith ctx, right := right.toProtoWith ctx
                       condition := cond.toProto ctx, postJoinFilter := none, common := none }
  | .set op left right =>
      Proto.Rel.set { op := op, inputs := [left.toProtoWith ctx, right.toProtoWith ctx], common := none }
  | .write op table tableSchema input =>
      Proto.Rel.write { tableName := table, op := op
                        tableSchema := tableSchema.map (fun sc =>
                          { fields := sc.map (toProtoColType ctx), names := sc.names })
                        input := input.toProtoWith ctx, common := none }
  | .extensionSingle detail input =>
      Proto.Rel.extensionSingle { input := input.toProtoWith ctx, detail := some detail, common := none }

/--
The public design signature: lower a typed rel to a wire `Proto.Rel`, with all
anchors computed at emission from the rel's own declaration list.
-/
def Rel.toProto (rel : Rel inS outS) : Proto.Rel :=
  rel.toProtoWith rel.toCtx

/-- Lower a typed rel to a full `Proto.Plan` (extensions + single top-level rel). -/
def Rel.toPlan {inS outS : Schema} (rel : Rel inS outS) : Proto.Plan :=
  let ctx := rel.toCtx
  { version := none
    extensionUrns := ctx.toUrns
    extensions := ctx.toDeclarations
    relations := [Proto.PlanRel.rel (rel.toProtoWith ctx)] }

end LeanSubstrait.Typed
