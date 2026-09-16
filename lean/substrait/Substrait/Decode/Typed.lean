/-
# Substrait.Decode.Typed — the typed decode (decodeExpr/decodeArgs) and its re-encode theorem

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
-/
import Substrait.Decode.Plan
import Substrait.Typed

namespace Substrait.Decode

open Substrait.Typed

/-- anchor → (urn, name) — the decode-side inverse of `ExtCtx.functions`'s
    1-based `indexOf1` anchoring. -/
abbrev FnInv := List (Nat × String × String)

/-- The decode-side anchor→(urn, name) table: keys starting at `a`, in
    declaration order (the inverse of `ExtCtx`'s `indexOf1` anchoring). -/
def fnInvGo : Nat → List (String × String) → FnInv
  | _, [] => []
  | a, f :: rest => (a, f.1, f.2) :: fnInvGo (a + 1) rest

/-- Build the decode-side function context from the emission context
    (anchors are 1-based, first-use order — `ExtCtx.indexOf1`'s inverse). -/
def fnInvOf (ctx : ExtCtx) : FnInv := fnInvGo 1 ctx.functions

/-- anchor lookup. -/
def fnOf (inv : FnInv) (a : Nat) : Option (String × String) :=
  (inv.find? (fun e => e.1 == a)).map (fun e => (e.2.1, e.2.2))

/-- Strip nullability: the wire `PType` back to the nullability-free `SType`.
    `userDefined` needs an anchor→type registry (absent here) — `none`. -/
def stOfPType : Proto.PType → Option SType
  | .bool _ => some .bool
  | .i8 _ => some .i8
  | .i16 _ => some .i16
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .fp32 _ => some .fp32
  | .fp64 _ => some .fp64
  | .string _ => some .string
  | .binary _ => some .binary
  | .decimal p s _ => some (.decimal p s)
  | .list e _ => (.list ·) <$> stOfPType e
  | .map k v _ => do
      let k' ← stOfPType k
      let v' ← stOfPType v
      pure (.map k' v')
  | .struct fs _ => (.struct ·) <$> fs.mapM stOfPType
  | .userDefined _ _ _ => none

/-- The wire nullability as a Bool (`false` = required, the typed layer's
    convention). -/
def pTypeNullable (t : Proto.PType) : Bool := nullabilityOf t == .nullable

/-- Build a `HasCol` instance from the runtime schema: the class's `resolves`
    field IS the `get?` proof, so a successful `Schema.get?` manufactures the
    instance the GADT constructors demand. -/
def hasColAt (s : Schema) (i : Nat) (nm : String) (t : SType) (n : Bool)
    (h : Schema.get? s i = some (nm, t, n)) : Substrait.Typed.HasCol s nm t n :=
  { index := i, resolves := h }

/-- Decode a wire literal into the typed literal expression (packed with its
    `(t, n)` indices — `AnyExpr` is the type-erased package).  `null:t` has no
    typed literal — `none`. -/
def decodeLiteral (s : Schema) : Proto.Literal → Option (AnyExpr s)
  | { literalType := .bool b, nullable := n } =>
      some (AnyExpr.mk .bool n (Expr.literal .bool n (.bool b)))
  | { literalType := .i8 v, nullable := n } =>
      some (AnyExpr.mk .i8 n (Expr.literal .i8 n (.i8 v)))
  | { literalType := .i16 v, nullable := n } =>
      some (AnyExpr.mk .i16 n (Expr.literal .i16 n (.i16 v)))
  | { literalType := .i32 v, nullable := n } =>
      some (AnyExpr.mk .i32 n (Expr.literal .i32 n (.i32 v)))
  | { literalType := .i64 v, nullable := n } =>
      some (AnyExpr.mk .i64 n (Expr.literal .i64 n (.i64 v)))
  | { literalType := .fp32 v, nullable := n } =>
      some (AnyExpr.mk .fp32 n (Expr.literal .fp32 n (.fp32 v)))
  | { literalType := .fp64 v, nullable := n } =>
      some (AnyExpr.mk .fp64 n (Expr.literal .fp64 n (.fp64 v)))
  | { literalType := .string v, nullable := n } =>
      some (AnyExpr.mk .string n (Expr.literal .string n (.string v)))
  | { literalType := .binary v, nullable := n } =>
      some (AnyExpr.mk .binary n (Expr.literal .binary n (.binary v)))
  | { literalType := .null _, nullable := _ } => none

/-- The type-erased argument spine (the decode-side package over `Args`, the
    same flattening pattern as `AnyExpr`). -/
inductive AnyArgs (s : Schema) : Type where
  | mk (ts : List (SType × Bool)) (a : Args s ts)

mutual
/-- Decode a wire argument list into the typed spine. -/
def decodeArgs (s : Schema) (inv : FnInv) : List Proto.Expression → Option (AnyArgs s)
  | [] => some (AnyArgs.mk [] Args.nil)
  | e :: rest =>
      match decodeExpr s inv e with
      | some (AnyExpr.mk t n ex) =>
          match decodeArgs s inv rest with
          | some (AnyArgs.mk ts spine) => some (AnyArgs.mk ((t, n) :: ts) (Args.cons t n ex spine))
          | none => none
      | none => none

/-- **The typed decode**: a wire `Proto.Expression` over schema `s`, against
    the decode-side anchor context, yields the packed typed expression (or
    `none` outside the typed grammar — see the exclusions above). -/
def decodeExpr (s : Schema) (inv : FnInv) : Proto.Expression → Option (AnyExpr s)
  | .literal lit => decodeLiteral s lit
  | .field { ordinal := i, segment := none } =>
      match h : s.get? i with
      | some (nm, t, n) =>
          some (AnyExpr.mk t n (@Expr.field s ({ name := nm, ordinal := i } : Column) t n
            (hasColAt s i nm t n h)))
      | none => none
  | .field { ordinal := _, segment := some _ } => none
  | .scalarFunction a args outTy =>
      match fnOf inv a with
      | none => none
      | some (urn, name) =>
          match decodeArgs s inv args with
          | none => none
          | some (AnyArgs.mk ts spine) =>
              match stOfPType outTy with
              | none => none
              | some ret =>
                  let sig := FunctionSig.mkSig name urn ts ret (pTypeNullable outTy) true
                  some (AnyExpr.mk sig.ret sig.retNullable (Expr.call sig spine))
  | .ifThen _ _ | .cast _ _ _ | .subquery _ _ => none
end

/-! ## the typed decode: round-trip evidence -/

/-- Anchor lookup hits the head key. -/
theorem fnOf_go_eq (a : Nat) (f : String × String) (ys : List (String × String)) :
    fnOf (fnInvGo a (f :: ys)) a = some (f.1, f.2) := by
  simp [fnOf, fnInvGo]

/-- Anchor lookup skips a smaller head key. -/
theorem fnOf_go_gt (a k : Nat) (f : String × String) (ys : List (String × String))
    (hk : a < k) :
    fnOf (fnInvGo a (f :: ys)) k = fnOf (fnInvGo (a + 1) ys) k := by
  have hne : (((a, f.1, f.2) : Nat × String × String).1 == k) = false := by
    cases hb : (((a, f.1, f.2) : Nat × String × String).1 == k)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) (Nat.ne_of_lt hk)
  simp only [fnOf, fnInvGo, List.find?_cons]
  cases hb : a == k
  · rfl
  · exact absurd (beq_iff_eq.mp hb) (Nat.ne_of_lt hk)

/-- **Anchor-lookup inversion (kernel-checked)**: a declaration's `indexOf1`
    anchor looks up to exactly that declaration in the decode-side table —
    the emission/decode anchor round trip, general over every context. -/
theorem fnOf_fnInvGo_findIdx : ∀ (a : Nat) (xs : List (String × String)) (x : String × String)
    (i : Nat), xs.findIdx? (fun p => p == x) = some i →
    fnOf (fnInvGo a xs) (a + i) = some x := by
  intro a xs
  induction xs generalizing a with
  | nil => intro x i h; simp at h
  | cons f ys ih =>
    intro x i hfi
    rw [List.findIdx?_cons] at hfi
    by_cases hfx : (f == x) = true
    · rw [if_pos hfx] at hfi
      have hi : 0 = i := Option.some.inj hfi
      subst hi
      rw [Nat.add_zero, fnOf_go_eq]
      have hfx' : f = x := beq_iff_eq.mp hfx
      simp [hfx']
    · rw [if_neg hfx] at hfi
      cases hys : ys.findIdx? (fun p => p == x) with
      | none => rw [hys] at hfi; simp at hfi
      | some j =>
        rw [hys] at hfi
        simp at hfi
        rw [fnOf_go_gt a (a + i) f ys (by omega)]
        rw [show a + i = (a + 1) + j from by omega]
        rw [ih (a + 1) x j hys]

/-! ## the re-encode form: decode → lower recovers the same wire term -/

/-- Re-lowering a decoded argument spine. -/
def argsLower (p : AnyArgs s) (ctx : ExtCtx) : List Proto.Expression :=
  match p with
  | .mk _ spine => spine.toProto ctx

/-- Re-lowering a decoded expression. -/
def anyLower (p : AnyExpr s) (ctx : ExtCtx) : Proto.Expression :=
  match p with
  | .mk _ _ e => e.toProto ctx

-- Ordinal safety: every field reference in `e` points at a schema column
-- (the authoring surface `col` guarantees this — its ordinal IS the
-- `HasCol` index, and `resolves` pins that ordinal in range).  The GADT
-- itself does not enforce it — `Expr.field` takes the column and the
-- instance independently — so the general re-encode theorem carries the
-- predicate explicitly.
mutual
def Expr.okS (ctx : ExtCtx) (s : Schema) : {t : SType} → {n : Bool} → Expr s t n → Prop
  | _, _, .literal .. => True
  | _, _, @Expr.field _ c _ _ _ => s.get? c.ordinal ≠ none
  | _, _, .call sig args =>
      Args.okS ctx s args ∧ stOfPType (toProtoType ctx sig.ret) = some sig.ret

def Args.okS (ctx : ExtCtx) (s : Schema) : {ts : List (SType × Bool)} → Args s ts → Prop
  | _, .nil => True
  | _, .cons _ _ e rest => Expr.okS ctx s e ∧ Args.okS ctx s rest
end

/-- `setNull` preserves the type's shape, so `stOfPType` (which strips
    nullability) cannot see it. -/
private theorem stOfPType_setNull (n : Proto.Nullability) (t : Proto.PType) :
    stOfPType (setNull n t) = stOfPType t := by
  cases t <;> simp [setNull, stOfPType]

/-- `withNullable` is invisible to `stOfPType`. -/
theorem stOfPType_withNullable (t : Proto.PType) (b : Bool) :
    stOfPType (withNullable t b) = stOfPType t := by
  show stOfPType (setNull (if b then .nullable else .required) t) = stOfPType t
  exact stOfPType_setNull _ _

/-- `setNull` sets the nullability marker. -/
private theorem nullabilityOf_setNull (n : Proto.Nullability) (t : Proto.PType) :
    nullabilityOf (setNull n t) = n := by
  cases t <;> rfl

/-- `pTypeNullable` inverts the nullability `withNullable` sets. -/
theorem pTypeNullable_withNullable (t : Proto.PType) (b : Bool) :
    pTypeNullable (withNullable t b) = b := by
  show (nullabilityOf (setNull (if b then .nullable else .required) t) == .nullable) = b
  rw [nullabilityOf_setNull]
  cases b <;> rfl

/-- **Literal inversion (kernel-checked)**: decoding the lowered literal
    recovers the packed typed literal — general over the whole `LiteralValue`
    family. -/
theorem decodeLiteral_of_toProto (v : LiteralValue t) (nv : Bool) (s : Schema) :
    decodeLiteral s { literalType := toProtoLiteralValue v, nullable := nv } =
      some (AnyExpr.mk t nv (Expr.literal t nv v)) := by
  cases v <;> rfl

/-- The `get?`-level form of the field inversion (the instance-free slice the
    HasCol version rests on). -/
theorem decodeExpr_field_of_get (s : Schema) (i : Nat) (nm : String) (t : SType) (n : Bool)
    (h : Schema.get? s i = some (nm, t, n)) :
    decodeExpr s [] (Proto.Expression.field { ordinal := i, segment := none }) =
      some (AnyExpr.mk t n (@Expr.field s ({ name := nm, ordinal := i } : Column) t n
        (hasColAt s i nm t n h))) := by
  simp only [decodeExpr]
  split
  · next nm' t' n' heq =>
      have ht : (nm, t, n) = (nm', t', n') := Option.some.inj (h.symm.trans heq)
      have h1 : nm = nm' := congrArg Prod.fst ht
      have h23 : (t, n) = (t', n') := congrArg Prod.snd ht
      have h2 : t = t' := congrArg Prod.fst h23
      have h3 : n = n' := congrArg Prod.snd h23
      subst h1
      subst h2
      subst h3
      rfl
  · next heq =>
      rw [heq] at h
      simp at h

/-- **Field inversion (kernel-checked)**: decoding the lowered field reference
    recovers the packed typed column reference — general over every schema,
    with the `HasCol` instance's own `resolves` proof supplying the ordinal
    lookup (the class field IS the correctness statement). -/
theorem decodeExpr_field_of_toProto (s : Schema) (nm : String) (t : SType) (n : Bool)
    (h : Substrait.Typed.HasCol s nm t n) :
    decodeExpr s [] (Proto.Expression.field { ordinal := h.index, segment := none }) =
      some (pack (@Expr.field s { name := nm, ordinal := h.index } t n h)) := by
  exact decodeExpr_field_of_get s h.index nm t n h.resolves

/-! ## the master re-encode theorem: decode → lower recovers the wire term -/

/- The wire-level round trip: for EVERY typed expression `e` (with its field
   references ordinal-safe and its call output types decodable — the `okS`
   predicate, which the authoring surface `col`/`call` always satisfies),
   decoding `e`'s lowered form and re-lowering the result recovers the same
   wire term.  This is the composition the binary/text wire actually
   consumes: anchors and ordinals round-trip; names (erased by the wire
   shape) are re-derived from the schema. -/
mutual
/-- The args re-encode: decoding a spine's lowered form and re-lowering
    the decode recovers the SAME wire list. -/
theorem decodeArgs_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {ts : List (SType × Bool)} (a : Args s ts), Args.okS ctx s a →
      (decodeArgs s inv (a.toProto ctx)).map (fun p => argsLower p ctx) = some (a.toProto ctx) := by
  intro ts a
  match a with
  | .nil =>
      intro _
      simp [Args.toProto, decodeArgs, argsLower]
  | .cons t n e rest =>
      intro hok
      have he : Expr.okS ctx s e := hok.1
      have hrest : Args.okS ctx s rest := hok.2
      show Option.map (fun p => argsLower p ctx)
          (decodeArgs s inv (e.toProto ctx :: rest.toProto ctx)) =
        some (e.toProto ctx :: rest.toProto ctx)
      simp only [decodeArgs]
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none =>
          have hinv := decodeExpr_reEnc s inv ctx hfn e he
          rw [hd] at hinv
          simp at hinv
      | some p =>
          cases p with
          | mk t' n' ex =>
              simp only [hd]
              have hlow : ex.toProto ctx = e.toProto ctx := by
                have hinv := decodeExpr_reEnc s inv ctx hfn e he
                rw [hd] at hinv
                simpa [anyLower] using hinv
              cases hd2 : decodeArgs s inv (rest.toProto ctx) with
              | none =>
                  have hinv := decodeArgs_reEnc s inv ctx hfn rest hrest
                  rw [hd2] at hinv
                  simp at hinv
              | some q =>
                  cases q with
                  | mk ts' spine =>
                      simp only [hd2]
                      have hlow2 : spine.toProto ctx = rest.toProto ctx := by
                        have hinv := decodeArgs_reEnc s inv ctx hfn rest hrest
                        rw [hd2] at hinv
                        simpa [argsLower] using hinv
                      show some ((Args.cons t' n' ex spine).toProto ctx) = _
                      simp only [Args.toProto]
                      rw [hlow, hlow2]

/-- THE re-encode theorem: for EVERY typed expression `e` (with its
    field references ordinal-safe and its call output types decodable —
    the `okS` predicate, which the authoring surface `col`/`call`
    always satisfies), decoding `e`'s lowered form and re-lowering the
    result recovers the same wire term. This is the composition the
    binary/text wire actually consumes: anchors and ordinals
    round-trip; names (erased by the wire shape) are re-derived from
    the schema. -/
theorem decodeExpr_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okS ctx s e →
      (decodeExpr s inv (e.toProto ctx)).map (fun p => anyLower p ctx) = some (e.toProto ctx) := by
  intro t n e
  match e with
  | .literal t' nv v =>
      intro _
      show (decodeExpr s inv (Proto.Expression.literal
        { literalType := toProtoLiteralValue v, nullable := nv })).map (fun p => anyLower p ctx) =
        some (Proto.Expression.literal { literalType := toProtoLiteralValue v, nullable := nv })
      rw [show decodeExpr s inv (Proto.Expression.literal
          { literalType := toProtoLiteralValue v, nullable := nv }) =
        decodeLiteral s { literalType := toProtoLiteralValue v, nullable := nv } from rfl,
        decodeLiteral_of_toProto v nv s]
      simp [anyLower, Expr.toProto]
  | @Expr.field _ c _ _ h =>
      intro hok
      show (decodeExpr s inv (Proto.Expression.field
        { ordinal := c.ordinal, segment := none })).map (fun p => anyLower p ctx) =
        some (Proto.Expression.field { ordinal := c.ordinal, segment := none })
      simp only [decodeExpr]
      split
      · next nm t' n' h1 =>
          simp [anyLower, Expr.toProto]
      · next h1 =>
          exact absurd h1 hok
  | .call sig args =>
      intro hok
      have hargs : Args.okS ctx s args := hok.1
      have hret : stOfPType (toProtoType ctx sig.ret) = some sig.ret := hok.2
      have hfn' := hfn sig
      show Option.map (fun p => anyLower p ctx)
          (decodeExpr s inv (Proto.Expression.scalarFunction
            (ctx.functionAnchor sig.urn sig.name) (args.toProto ctx)
            (withNullable (toProtoType ctx sig.ret) sig.retNullable))) =
        some (Proto.Expression.scalarFunction (ctx.functionAnchor sig.urn sig.name)
          (args.toProto ctx) (withNullable (toProtoType ctx sig.ret) sig.retNullable))
      simp only [decodeExpr, hfn']
      cases hd : decodeArgs s inv (args.toProto ctx) with
      | none =>
          have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
          rw [hd] at hinv
          simp at hinv
      | some q =>
          cases q with
          | mk ts' spine =>
              simp only [hd]
              have hlow2 : spine.toProto ctx = args.toProto ctx := by
                have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
                rw [hd] at hinv
                simpa [argsLower] using hinv
              have hret' : stOfPType (withNullable (toProtoType ctx sig.ret) sig.retNullable) =
                  some sig.ret := by
                rw [stOfPType_withNullable]
                exact hret
              rw [hret']
              simp [anyLower, Expr.toProto, FunctionSig.mkSig, pTypeNullable_withNullable,
                hlow2]

end

-- ── the typed rel decode: Proto.Rel → Typed.Rel ────────────────────────────

/-!

The wire relation `Proto.Rel` decoded back into the schema-indexed
`Substrait.Typed.Rel` GADT — the inverse of `Typed.Rel.toProtoWith`, the same
`decode → re-lower = id` discipline as the expression layer above.

Deliberate exclusions / canonicalizations (the typed grammar has no syntax
for them):
- `cross`, `extensionLeaf`, `extensionMulti`: no `Typed.Rel` constructor —
  `none`.
- `ReadRel.readType = virtualTable`: the typed layer has only named-table
  reads — `none`; a named-table path longer than one element is rejected too
  (`Typed.Rel.read` carries a single table name).
- `RelCommon.emit = direct` decodes to the typed `emit := none` — the same
  canonicalization the text decoder documents (direct vs absent emit kinds
  are indistinguishable in the typed grammar).
- `ProjectRel` carries no column names: decoded projections get placeholder
  names `""` (the wire never sees them; `projectOut` positions are the
  contract).  Sort keys keep only the ordinal + direction the wire carries;
  the name is re-derived from the decoded input schema.
- Square-input nodes (`filter`/`aggregate`/`sort`/`fetch`) demand the decoded
  input's input/output schemas to agree — a wire filter over a width-changing
  child is valid Substrait but outside the typed grammar, so it decodes to
  `none` (the typed `filter` literally takes `Rel s s`).
- `WriteRel.tableSchema` present but undecodable → `none`; absent → typed
  `none`.
- `ExtensionSingleRel.detail = none` → `none` (the typed ctor requires a
  detail string; the lowering always writes one).

Schema equality checks use the `DecidableEq SType` instance from `Schema.lean`
(defined via `SType.eqAns`).

Termination note: the mutual-block `Proto.Rel` defeats Lean's structural
recursion, its derived `sizeOf` simproc disagrees with the instance funs, and
`sizeOf` in a definition body hits an LCNF codegen failure — so the recursion
is well-founded on the ACTUAL `sizeOf` instance, with the decreasing goals
discharged by the `wf*_size` lemmas (proved from the instance funs,
simproc-free).

-/

/-- The type-erased relation package (the `AnyExpr` pattern at the rel
    level): `Rel` is indexed by input/output schemas, heterogeneous decode
    results erase both indices. -/
inductive AnyRel : Type where
  | mk (inS outS : Schema) (r : Rel inS outS)

/-- Re-lowering a decoded rel (the wire-level comparison point). -/
def relLower (a : AnyRel) (ctx : ExtCtx) : Proto.Rel :=
  match a with
  | .mk _ _ r => r.toProtoWith ctx

/-- Cast a rel to its square form (`s = s'` pinned). -/
def Rel.castSq {s s' : Schema} (h : s = s') (r : Rel s s') : Rel s s :=
  match h with | rfl => r

/-- Cast a rel across two schema equalities (the `set` shape). -/
def Rel.cast2 {s1 s1' s2 s2' : Schema} (h1 : s1 = s2) (h2 : s1' = s2')
    (r : Rel s2 s2') : Rel s1 s1' :=
  match h1, h2 with | rfl, rfl => r

/-- The cast is invisible to lowering (used by the master theorem). -/
theorem Rel.castSq_toProtoWith {s s' : Schema} (h : s = s') (r : Rel s s') (ctx : ExtCtx) :
    (Rel.castSq h r).toProtoWith ctx = r.toProtoWith ctx := by
  cases h; rfl

/-- The two-schema cast is invisible to lowering. -/
theorem Rel.cast2_toProtoWith {s1 s1' s2 s2' : Schema} (h1 : s1 = s2) (h2 : s1' = s2')
    (r : Rel s2 s2') (ctx : ExtCtx) :
    (Rel.cast2 h1 h2 r).toProtoWith ctx = r.toProtoWith ctx := by
  cases h1; cases h2; rfl

/-- A decoded rel packaged with its (proven-equal) input/output schema — the
    shape the square-input nodes (`filter`/`aggregate`/`sort`/`fetch`) demand.
    (Lean patterns cannot bind one variable twice, so the square package —
    not a repeated-variable pattern — carries the equality.) -/
structure SqRel where
  schema : Schema
  rel : Rel schema schema

def squareOf : AnyRel → Option SqRel
  | .mk s s' r => if h : s = s' then some ⟨s, Rel.castSq h r⟩ else none

/-- Decode a wire `NamedStruct` back into a schema: names and field types
    must have the same length, every field type must decode (`stOfPType`),
    nullability from the wire marker. -/
def schemaOfFields : List String → List Proto.PType → Option Schema
  | [], [] => some []
  | name :: names, t :: ts =>
      match stOfPType t with
      | none => none
      | some t' =>
          match schemaOfFields names ts with
          | none => none
          | some rest => some ((name, t', pTypeNullable t) :: rest)
  | _, _ => none

/-- Read-schema well-formedness: every column's lowered wire type decodes
    back to it.  The read branch's re-encode hypothesis. -/
def schemaOk (ctx : ExtCtx) (sc : Schema) : Prop :=
  ∀ c ∈ sc, stOfPType (toProtoColType ctx c) = some c.2.1

/-- The schema inversion: a well-formed schema's lowering decodes back to it. -/
theorem schemaOfFields_of_toProto (ctx : ExtCtx) :
    ∀ (sc : Schema), schemaOk ctx sc →
      schemaOfFields sc.names (sc.map (toProtoColType ctx)) = some sc := by
  intro sc
  induction sc with
  | nil => intro _; rfl
  | cons c sc ih =>
      intro hok
      obtain ⟨nm, t, n⟩ := c
      have hc : stOfPType (toProtoColType ctx (nm, t, n)) = some t := hok _ (by simp)
      have hnull : pTypeNullable (toProtoColType ctx (nm, t, n)) = n := by
        show pTypeNullable (withNullable (toProtoType ctx t) n) = n
        rw [pTypeNullable_withNullable]
      simp only [List.map_cons, Schema.names, schemaOfFields, hc, hnull,
        ih (fun c2 hc2 => hok c2 (by simp [hc2]))]

/-- The wire emit kind back to the typed mapping (`.direct` canonicalized to
    `none` — the documented lossiness; the lowering never writes `.direct`). -/
def emitOf : Option Proto.RelCommon → Option (List Nat)
  | some { emit := some (.emit m), advancedExtension := _ } => some m
  | _ => none

/-- Re-pack a decoded argument spine into the type-erased list (the
    `Measure.args` shape). -/
def argsPack {s : Schema} : {ts : List (SType × Bool)} → Args s ts → List (AnyExpr s)
  | _, .nil => []
  | _, .cons t n e rest => AnyExpr.mk t n e :: argsPack rest

/-- The wire argument list of a type-erased expression list. -/
def anyExprsLower {s : Schema} (xs : List (AnyExpr s)) (ctx : ExtCtx) :
    List Proto.Expression :=
  xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)

/-- The cons step of `anyExprsLower` (the helpers' iota-exposing rewrite). -/
theorem anyExprsLower_cons {s : Schema} (x : AnyExpr s) (xs : List (AnyExpr s))
    (ctx : ExtCtx) :
    anyExprsLower (x :: xs) ctx =
      (match x with | .mk _ _ e => e.toProto ctx) :: anyExprsLower xs ctx := rfl

/-- Decode a projection list (placeholder names — the wire carries none). -/
def decodeProjections (s : Schema) (inv : FnInv) :
    List Proto.Expression → Option (List (Projection s))
  | [] => some []
  | e :: rest =>
      match decodeExpr s inv e with
      | some (AnyExpr.mk t n ex) =>
          match decodeProjections s inv rest with
          | some ps => some ({ name := "", dtype := t, nullable := n, expr := ex } :: ps)
          | none => none
      | none => none

/-- Decode a grouping-key list. -/
def decodeAnyExprs (s : Schema) (inv : FnInv) :
    List Proto.Expression → Option (List (AnyExpr s))
  | [] => some []
  | e :: rest =>
      match decodeExpr s inv e with
      | some x =>
          match decodeAnyExprs s inv rest with
          | some xs => some (x :: xs)
          | none => none
      | none => none

/-- Lower a measure to its wire shape (the `ToProto` aggregate arm's
    per-measure slice, factored for the round-trip theorem). -/
def measureLower {s : Schema} (ctx : ExtCtx) (m : Measure s) : Proto.AggregateMeasure :=
  { measure := { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                 args := anyExprsLower m.args ctx
                 outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } }

/-- The `ToProto` grouping arm's map IS `anyExprsLower` (the wire-eq bridge). -/
theorem groupings_wire_eq {s : Schema} (ctx : ExtCtx) (xs : List (AnyExpr s)) :
    xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
      anyExprsLower xs ctx := rfl

/-- The `ToProto` measures arm's map IS `measureLower`-mapped (the wire-eq
    bridge). -/
theorem measures_wire_eq {s : Schema} (ctx : ExtCtx) (ms : List (Measure s)) :
    ms.map (fun m =>
      { measure :=
          { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
            args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
            outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } }) =
      ms.map (measureLower ctx) := rfl

/-- Decode a measure list: anchor lookup + argument decode + output type
    decode per measure. -/
def decodeMeasures (s : Schema) (inv : FnInv) :
    List Proto.AggregateMeasure → Option (List (Measure s))
  | [] => some []
  | ⟨am⟩ :: rest =>
      match fnOf inv am.functionReference with
      | none => none
      | some (urn, name) =>
          match decodeArgs s inv am.args with
          | some (AnyArgs.mk ts spine) =>
              match stOfPType am.outputType with
              | some ret =>
                  match decodeMeasures s inv rest with
                  | some ms =>
                      some ({ sig := FunctionSig.mkSig name urn ts ret
                                (pTypeNullable am.outputType) true
                              args := argsPack spine } :: ms)
                  | none => none
              | none => none
          | none => none

/-- Lower a sort key to its wire shape (the `ToProto` sort arm's per-key
    slice). -/
def sortFieldLower {s : Schema} (k : SortKey s) : Proto.SortField :=
  ⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none }, k.direction⟩

/-- Decode a sort-key list: every sort expression must be a plain field
    reference with its ordinal inside the decoded input schema (the typed
    `SortKey` has no expression support). -/
def decodeSortKeys (s : Schema) : List Proto.SortField → Option (List (SortKey s))
  | [] => some []
  | ⟨.field { ordinal := i, segment := none }, dir⟩ :: rest =>
      match s.get? i with
      | some (nm, _, _) =>
          match decodeSortKeys s rest with
          | some ks => some ({ col := { name := nm, ordinal := i }, direction := dir } :: ks)
          | none => none
      | none => none
  | _ :: _ => none


end Substrait.Decode
