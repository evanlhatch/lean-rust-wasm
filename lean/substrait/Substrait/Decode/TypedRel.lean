/-
# Substrait.Decode.TypedRel — the size facts, the typed decodeRel, and the rel re-encode capstone

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
-/

module

public import Substrait.Decode.Typed

@[expose] public section

namespace Substrait.Decode

open Substrait.Typed

/-! ## the size facts the decode's well-founded recursion needs -/

/-- A wire rel's children are strictly smaller in the actual `sizeOf`
    instance (proved from the instance funs — the derived `sizeOf` simproc
    disagrees with itself on this mutual block, so no `simp [sizeOf]`). -/
theorem wf_filter_size (fr : Proto.FilterRel) :
    sizeOf fr.input < sizeOf (Proto.Rel.filter fr) := by
  cases fr with
  | mk c i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_project_size (pr : Proto.ProjectRel) :
    sizeOf pr.input < sizeOf (Proto.Rel.project pr) := by
  cases pr with
  | mk e i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_aggregate_size (ar : Proto.AggregateRel) :
    sizeOf ar.input < sizeOf (Proto.Rel.aggregate ar) := by
  cases ar with
  | mk g m i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_sort_size (sr : Proto.SortRel) :
    sizeOf sr.input < sizeOf (Proto.Rel.sort sr) := by
  cases sr with
  | mk k i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_fetch_size (fr : Proto.FetchRel) :
    sizeOf fr.input < sizeOf (Proto.Rel.fetch fr) := by
  cases fr with
  | mk l o i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_join_size (jr : Proto.JoinRel) :
    sizeOf jr.left < sizeOf (Proto.Rel.join jr) ∧
      sizeOf jr.right < sizeOf (Proto.Rel.join jr) := by
  cases jr with
  | mk jt l r c pf cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_write_size (wr : Proto.WriteRel) :
    sizeOf wr.input < sizeOf (Proto.Rel.write wr) := by
  cases wr with
  | mk tn op ts i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_extensionSingle_size (er : Proto.ExtensionSingleRel) :
    sizeOf er.input < sizeOf (Proto.Rel.extensionSingle er) := by
  cases er with
  | mk i d cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_set_size (sr : Proto.SetRel) (l r : Proto.Rel) (hI : sr.inputs = [l, r]) :
    sizeOf l < sizeOf (Proto.Rel.set sr) ∧ sizeOf r < sizeOf (Proto.Rel.set sr) := by
  cases sr with
  | mk op inputs cm =>
      subst hI
      cases op <;>
        unfold sizeOf <;>
        simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24,
          Proto.SetRel._sizeOf_inst, Proto.EmitKind._sizeOf_6] <;>
        omega

/-- **The typed rel decode**: a wire `Proto.Rel` decoded back into the packed
    typed relation (or `none` outside the typed grammar — see the exclusions
    above).  The child schemas come from the decode; every node that indexes
    an expression over its input schema uses the decoded child schema. -/
def decodeRel (inv : FnInv) : Proto.Rel → Option AnyRel
  | .read r =>
      match r.readType with
      | .namedTable [table] =>
          match r.baseSchema with
          | some ns =>
              match schemaOfFields ns.names ns.fields with
              | some sc => some (AnyRel.mk sc sc (Rel.read table sc))
              | none => none
          | none => none
      | _ => none
  | .filter fr =>
      match decodeRel inv fr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeExpr s inv fr.condition with
              | some (AnyExpr.mk .bool n ce) =>
                  some (AnyRel.mk s s (Rel.filter ri ce))
              | _ => none
          | none => none
      | none => none
  | .project pr =>
      match decodeRel inv pr.input with
      | some (AnyRel.mk s p ri) =>
          match decodeProjections p inv pr.expressions with
          | some outs =>
              some (AnyRel.mk s (projectOut p outs)
                (Rel.project ri outs (emitOf pr.common)))
          | none => none
      | none => none
  | .aggregate ar =>
      match decodeRel inv ar.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeAnyExprs s inv ar.groupingExpressions with
              | some grouping =>
                  match decodeMeasures s inv ar.measures with
                  | some measures =>
                      some (AnyRel.mk s (aggregateOut s grouping measures)
                        (Rel.aggregate ri grouping measures))
                  | none => none
              | none => none
          | none => none
      | none => none
  | .sort sr =>
      match decodeRel inv sr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeSortKeys s sr.sorts with
              | some ks => some (AnyRel.mk s s (Rel.sort ri ks))
              | none => none
          | none => none
      | none => none
  | .fetch fr =>
      match decodeRel inv fr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              some (AnyRel.mk s s (Rel.fetch ri fr.limit fr.offset))
          | none => none
      | none => none
  | .join jr =>
      match decodeRel inv jr.left with
      | some (AnyRel.mk sl sl' rl) =>
          match decodeRel inv jr.right with
          | some (AnyRel.mk sr sr' rr) =>
              match decodeExpr (sl' ++ sr') inv jr.condition with
              | some (AnyExpr.mk .bool n ce) =>
                  some (AnyRel.mk (sl ++ sr) (sl' ++ sr')
                    (Rel.join rl rr ce jr.joinType))
              | _ => none
          | none => none
      | none => none
  | .cross _ => none
  | .set { op := op, inputs := [l, r], common := _ } =>
      match decodeRel inv l with
      | some (AnyRel.mk s1 s1' rl) =>
          match decodeRel inv r with
          | some (AnyRel.mk s2 s2' rr) =>
              if h1 : s1 = s2 then
                if h2 : s1' = s2' then
                  some (AnyRel.mk s1 s1' (Rel.set op rl (Rel.cast2 h1 h2 rr)))
                else none
              else none
          | none => none
      | none => none
  | .set _ => none
  | .write wr =>
      match decodeRel inv wr.input with
      | some (AnyRel.mk s s' ri) =>
          match wr.tableSchema with
          | none => some (AnyRel.mk s s' (Rel.write wr.op wr.tableName none ri))
          | some ns =>
              match schemaOfFields ns.names ns.fields with
              | some sc =>
                  some (AnyRel.mk s s' (Rel.write wr.op wr.tableName (some sc) ri))
              | none => none
      | none => none
  | .extensionLeaf _ => none
  | .extensionSingle er =>
      match er.detail with
      | some d =>
          match decodeRel inv er.input with
          | some (AnyRel.mk s s' ri) =>
              some (AnyRel.mk s s' (Rel.extensionSingle d ri))
          | none => none
      | none => none
  | .extensionMulti _ => none
termination_by w => sizeOf w
decreasing_by
  all_goals (
    first
      | exact wf_filter_size _
      | exact wf_project_size _
      | exact wf_aggregate_size _
      | exact wf_sort_size _
      | exact wf_fetch_size _
      | exact (wf_join_size _).1
      | exact (wf_join_size _).2
      | exact (wf_set_size _ _ _ rfl).1
      | exact (wf_set_size _ _ _ rfl).2
      | exact wf_write_size _
      | exact wf_extensionSingle_size _)

/-- The (input, output) schema pair of a decoded rel. -/
def AnyRel.schemaPair : AnyRel → Schema × Schema
  | .mk i o _ => (i, o)

/-- The REL-level expression well-formedness: like `Expr.okS` but the field
    case pins the column DECODE exactly (`s.get? c.ordinal` resolves to the
    field's own `(name, t, n)`) — what `decodeExpr_shape`'s exact-index claim
    needs (the GADT leaves `c.ordinal` and the `HasCol` instance independent;
    the authoring surface `col` ties them). -/
def Expr.okSR (ctx : ExtCtx) (s : Schema) : {t : SType} → {n : Bool} → Expr s t n → Prop
  | _, _, .literal .. => True
  | _, _, @Expr.field _ c t n _ => s.get? c.ordinal = some (c.name, t, n)
  | _, _, .call sig args =>
      Args.okS ctx s args ∧ stOfPType (toProtoType ctx sig.ret) = some sig.ret

/-- `okSR` is strictly stronger than `okS` (the bridge the re-encode helpers
    use: their wire-level conclusions only need `okS`). -/
theorem Expr.okSR_to_okS (ctx : ExtCtx) (s : Schema) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okSR ctx s e → Expr.okS ctx s e := by
  intro t n e hok
  match e with
  | .literal .. => exact trivial
  | @Expr.field _ c _ _ _ =>
      intro hcontra
      rw [hok] at hcontra
      simp at hcontra
  | .call sig args => exact hok

/-- The expression-level well-formedness of a packaged expr (unwraps the
    package; `Expr.okSR` does the work). -/
def AnyExpr.okSR (ctx : ExtCtx) (s : Schema) (ae : AnyExpr s) : Prop :=
  match ae with
  | .mk _ _ e => Expr.okSR ctx s e

/-- The measure-level well-formedness: the output type decodes and every
    argument expression is well-formed. -/
def Measure.okS (ctx : ExtCtx) (s : Schema) (m : Measure s) : Prop :=
  stOfPType (withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable) = some m.sig.ret ∧
  ∀ ae ∈ m.args, AnyExpr.okSR ctx s ae

/-- Square-schema pinning: EVERY successful decode of `w` yields a rel whose
    input/output schemas are both `s`.  The wire erases schemas, so the typed
    GADT's square-input demand is a property of the decode, recorded here
    where the authoring surface guarantees it. -/
def SqPred (inv : FnInv) (w : Proto.Rel) (s : Schema) : Prop :=
  ∀ pkg, decodeRel inv w = some pkg → ∃ r1, pkg = AnyRel.mk s s r1

/-- Pair-schema pinning (the `project`/`join` shape). -/
def PairPred (inv : FnInv) (w : Proto.Rel) (p : Schema × Schema) : Prop :=
  ∀ pkg, decodeRel inv w = some pkg → ∃ r1, pkg = AnyRel.mk p.1 p.2 r1

/-! The rel-level well-formedness predicate — the `decodeRel_reEnc`
hypothesis, mirroring `Expr.okS`.  Beyond the per-node recursion it pins the
DECODED schemas of the children (`SqPred` / `PairPred`): the wire erases
schemas, so the typed GADT's index demands (square inputs, join condition
over the concatenated schema, set's same-schema inputs) are properties of the
decode, not of the typed term — the predicate records them where the
authoring surface guarantees them. -/
def Rel.okS (ctx : ExtCtx) (inv : FnInv) : {inS outS : Schema} → Rel inS outS → Prop
  | _, _, .read _ sc => schemaOk ctx sc
  | _, _, @Rel.filter s _ input cond =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      Expr.okSR ctx s cond
  | _, _, @Rel.project s p input outs _ =>
      Rel.okS ctx inv input ∧ PairPred inv (input.toProtoWith ctx) (s, p) ∧
      ∀ pr ∈ outs, Expr.okSR ctx p pr.expr
  | _, _, @Rel.aggregate s input grouping measures =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      (∀ ae ∈ grouping, AnyExpr.okSR ctx s ae) ∧ (∀ m ∈ measures, Measure.okS ctx s m)
  | _, _, @Rel.sort s input orderBy =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      ∀ k ∈ orderBy, s.get? k.col.ordinal ≠ none
  | _, _, @Rel.fetch s input _ _ =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s
  | _, _, @Rel.join sl sl' sr sr' _ left right cond _ =>
      Rel.okS ctx inv left ∧ Rel.okS ctx inv right ∧
      PairPred inv (left.toProtoWith ctx) (sl, sl') ∧
      PairPred inv (right.toProtoWith ctx) (sr, sr') ∧
      Expr.okSR ctx (sl' ++ sr') cond
  | _, _, @Rel.set _ _ _ left right =>
      Rel.okS ctx inv left ∧ Rel.okS ctx inv right ∧
      ∀ pkgL pkgR,
        decodeRel inv (left.toProtoWith ctx) = some pkgL →
        decodeRel inv (right.toProtoWith ctx) = some pkgR →
        pkgL.schemaPair = pkgR.schemaPair
  | _, _, @Rel.write _ _ _ _ ts input =>
      Rel.okS ctx inv input ∧
      (match ts with | none => True | some sc => schemaOk ctx sc)
  | _, _, @Rel.extensionSingle _ _ _ input => Rel.okS ctx inv input

/-! ## the rel re-encode: the decode-shape lemma and the helpers -/

/-- The re-encode skeleton, square-child slice: a decoded child whose decode
    is schema-pinned (`SqPred`) IS the square package of a rel re-lowering to
    the same wire term — the `decodeRel_reEnc` child branch (case on the
    input decode, pin the schema, rewrite the IH, transport the lowering)
    stated once. -/
theorem sqChild_of_decode (inv : FnInv) (ctx : ExtCtx) (w : Proto.Rel) (s : Schema)
    (hsq : SqPred inv w s)
    (ihc : (decodeRel inv w).map (fun a => relLower a ctx) = some w)
    {pkg : AnyRel} (hx : decodeRel inv w = some pkg) :
    ∃ r1 : Rel s s, pkg = AnyRel.mk s s r1 ∧ r1.toProtoWith ctx = w := by
  simp only [SqPred, hx] at hsq
  obtain ⟨r1, hpkg⟩ := hsq pkg rfl
  rw [hx, hpkg] at ihc
  simp only [Option.map_some, relLower, Option.some.injEq] at ihc
  exact ⟨r1, hpkg, ihc⟩

/-- The re-encode skeleton, pair-child slice (the `PairPred` twin). -/
theorem pairChild_of_decode (inv : FnInv) (ctx : ExtCtx) (w : Proto.Rel) (s1 s2 : Schema)
    (hpred : PairPred inv w (s1, s2))
    (ihc : (decodeRel inv w).map (fun a => relLower a ctx) = some w)
    {pkg : AnyRel} (hx : decodeRel inv w = some pkg) :
    ∃ r1 : Rel s1 s2, pkg = AnyRel.mk s1 s2 r1 ∧ r1.toProtoWith ctx = w := by
  simp only [PairPred, hx] at hpred
  obtain ⟨r1, hpkg⟩ := hpred pkg rfl
  rw [hx, hpkg] at ihc
  simp only [Option.map_some, relLower, Option.some.injEq] at ihc
  exact ⟨r1, hpkg, ihc⟩

/-- The re-encode skeleton, lowering transport: the map-form IH on a concrete
    package is the child's re-lowering. -/
theorem relLower_some_map {ctx : ExtCtx} {w : Proto.Rel} {s1 s2 : Schema} (r : Rel s1 s2)
    (h : (some (AnyRel.mk s1 s2 r)).map (fun a => relLower a ctx) = some w) :
    r.toProtoWith ctx = w := by
  simpa [relLower] using h

/-- The decode-shape lemma (the rel-level workhorse): a well-formed typed
    expression decodes back to a package with its EXACT `(t, n)` indices —
    what the rel GADT's constructors demand. -/
theorem decodeExpr_shape (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okSR ctx s e →
      ∃ e', decodeExpr s inv (e.toProto ctx) = some (AnyExpr.mk t n e') := by
  intro t n e
  match e with
  | .literal t' nv v =>
      intro _
      show ∃ e', decodeExpr s inv (Proto.Expression.literal
        { literalType := toProtoLiteralValue v, nullable := nv }) = some (AnyExpr.mk t' nv e')
      exact ⟨Expr.literal t' nv v, decodeLiteral_of_toProto v nv s⟩
  | @Expr.field _ c _ _ _ =>
      intro hok
      exact ⟨_, decodeExpr_field_of_get s c.ordinal c.name t n hok⟩
  | .call sig args =>
      intro hok
      have hargs : Args.okS ctx s args := hok.1
      have hret : stOfPType (toProtoType ctx sig.ret) = some sig.ret := hok.2
      have hfn' := hfn sig
      show ∃ e', decodeExpr s inv (Proto.Expression.scalarFunction
        (ctx.functionAnchor sig.urn sig.name) (args.toProto ctx)
        (withNullable (toProtoType ctx sig.ret) sig.retNullable)) =
        some (AnyExpr.mk sig.ret sig.retNullable e')
      simp only [decodeExpr, hfn']
      cases hd : decodeArgs s inv (args.toProto ctx) with
      | none =>
          have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
          rw [hd] at hinv
          simp at hinv
      | some q =>
          obtain ⟨ts', spine, hq, hlow2⟩ := decodeArgs_lower_some inv ctx hfn args hargs hd
          rw [hq]
          have hret' : stOfPType (withNullable (toProtoType ctx sig.ret) sig.retNullable) =
              some sig.ret := by
            rw [stOfPType_withNullable]
            exact hret
          rw [hret', pTypeNullable_withNullable]
          exact ⟨Expr.call (FunctionSig.mkSig sig.name sig.urn ts' sig.ret
            sig.retNullable true) spine, rfl⟩

/-- Projection-list inversion: the lowered projections decode (with
    placeholder names) and re-lower to the same wire expressions. -/
theorem decodeProjections_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (ps : List (Projection s)) (hok : ∀ pr ∈ ps, Expr.okSR ctx s pr.expr) :
    ∃ ps', decodeProjections s inv (ps.map (fun pr => pr.expr.toProto ctx)) = some ps' ∧
      ps'.map (fun pr => pr.expr.toProto ctx) = ps.map (fun pr => pr.expr.toProto ctx) := by
  induction ps with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons pr rest ih =>
      have hpr : Expr.okS ctx s pr.expr := Expr.okSR_to_okS ctx s _ (hok pr (by simp))
      have hrest : ∀ pr' ∈ rest, Expr.okSR ctx s pr'.expr := fun q hq => hok q (by simp [hq])
      obtain ⟨ps', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn pr.expr hpr
      cases hd : decodeExpr s inv (pr.expr.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          obtain ⟨t, n, ex, hpkg, hlow⟩ := decodeExpr_lower_some inv ctx hfn pr.expr hpr hd
          refine ⟨{ name := "", dtype := t, nullable := n, expr := ex } :: ps', ?_, ?_⟩
          · simp only [List.map_cons, decodeProjections, hd, hpkg, h1]
          · show ({ name := "", dtype := t, nullable := n, expr := ex } :: ps').map
                (fun pr => pr.expr.toProto ctx) =
              (pr :: rest).map (fun pr => pr.expr.toProto ctx)
            show ex.toProto ctx :: ps'.map (fun pr => pr.expr.toProto ctx) =
              pr.expr.toProto ctx :: rest.map (fun pr => pr.expr.toProto ctx)
            rw [hlow, h2]

/-- Grouping-list inversion (grouping keys; the `AnyExpr` list shape). -/
theorem decodeAnyExprs_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (xs : List (AnyExpr s)) (hok : ∀ ae ∈ xs, AnyExpr.okSR ctx s ae) :
    ∃ xs', decodeAnyExprs s inv (anyExprsLower xs ctx) = some xs' ∧
      xs'.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
        xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons ae rest ih =>
      obtain ⟨t, n, e⟩ := ae
      have hae : Expr.okS ctx s e := Expr.okSR_to_okS ctx s _ (hok (AnyExpr.mk t n e) (by simp))
      have hrest : ∀ x ∈ rest, AnyExpr.okSR ctx s x := fun y hy => hok y (by simp [hy])
      obtain ⟨xs', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn e hae
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          obtain ⟨t', n', ex, hpkg, hlow⟩ := decodeExpr_lower_some inv ctx hfn e hae hd
          refine ⟨AnyExpr.mk t' n' ex :: xs', ?_, ?_⟩
          · rw [anyExprsLower_cons]
            simp only [decodeAnyExprs, hd, hpkg, h1]
          · show (AnyExpr.mk t' n' ex :: xs').map
                (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
              (AnyExpr.mk t n e :: rest).map
                (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
            show ex.toProto ctx ::
                xs'.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
              e.toProto ctx ::
                rest.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
            rw [hlow, h2]

/-- Argument-spine inversion over a plain type-erased list: the lowered list
    decodes to a spine, and re-packing + re-lowering recovers the wire list. -/
theorem decodeArgs_anyExprs (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (xs : List (AnyExpr s)) (hok : ∀ ae ∈ xs, AnyExpr.okSR ctx s ae) :
    ∃ ts spine, decodeArgs s inv (anyExprsLower xs ctx) = some (AnyArgs.mk ts spine) ∧
      anyExprsLower (argsPack spine) ctx = anyExprsLower xs ctx := by
  induction xs with
  | nil => exact ⟨[], Args.nil, rfl, rfl⟩
  | cons ae rest ih =>
      obtain ⟨t, n, e⟩ := ae
      have hae : Expr.okS ctx s e := Expr.okSR_to_okS ctx s _ (hok (AnyExpr.mk t n e) (by simp))
      have hrest : ∀ x ∈ rest, AnyExpr.okSR ctx s x := fun y hy => hok y (by simp [hy])
      obtain ⟨ts', spine', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn e hae
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          obtain ⟨t', n', ex, hpkg, hlow⟩ := decodeExpr_lower_some inv ctx hfn e hae hd
          refine ⟨(t', n') :: ts', Args.cons t' n' ex spine', ?_, ?_⟩
          · rw [anyExprsLower_cons]
            simp only [decodeArgs, hd, hpkg, h1]
          · rw [show argsPack (Args.cons t' n' ex spine') =
              AnyExpr.mk t' n' ex :: argsPack spine' from rfl,
              anyExprsLower_cons, anyExprsLower_cons]
            show ex.toProto ctx :: anyExprsLower (argsPack spine') ctx =
              e.toProto ctx :: anyExprsLower rest ctx
            rw [hlow, h2]

/-- Measure-list inversion: the lowered measures decode and re-lower to the
    same wire measures. -/
theorem decodeMeasures_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (ms : List (Measure s)) (hok : ∀ m ∈ ms, Measure.okS ctx s m) :
    ∃ ms', decodeMeasures s inv (ms.map (measureLower ctx)) = some ms' ∧
      ms'.map (fun m =>
        ({ measure :=
            { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
              args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
              outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } } :
          Proto.AggregateMeasure)) =
      ms.map (fun m =>
        ({ measure :=
            { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
              args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
              outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } } :
          Proto.AggregateMeasure)) := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m rest ih =>
      obtain ⟨sig, marg⟩ := m
      have hm : Measure.okS ctx s { sig := sig, args := marg } := hok _ (by simp)
      obtain ⟨hret, hargs⟩ := hm
      rw [stOfPType_withNullable] at hret
      have hrest : ∀ m' ∈ rest, Measure.okS ctx s m' := fun q hq => hok q (by simp [hq])
      obtain ⟨ms', h1, h2⟩ := ih hrest
      have hfn' : fnOf inv (ctx.functionAnchor sig.urn sig.name) =
          some (sig.urn, sig.name) := hfn sig
      obtain ⟨ts, spine, hda⟩ := decodeArgs_anyExprs s inv ctx hfn marg hargs
      refine ⟨{ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                args := argsPack spine } :: ms', ?_, ?_⟩
      · show decodeMeasures s inv
          (measureLower ctx { sig := sig, args := marg } ::
            rest.map (measureLower ctx)) =
          some ({ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                  args := argsPack spine } :: ms')
        simp only [measureLower, decodeMeasures, hfn', hda, stOfPType_withNullable, hret,
          pTypeNullable_withNullable, h1, FunctionSig.mkSig]
      · have hurm : (argsPack spine).map
            (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
          marg.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) := hda.2
        show ({ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                args := argsPack spine } :: ms').map
            (fun m =>
              ({ measure :=
                  { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                    args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                    outputType := withNullable (toProtoType ctx m.sig.ret)
                      m.sig.retNullable } } : Proto.AggregateMeasure)) =
          ({ sig := sig, args := marg } :: rest).map
            (fun m =>
              ({ measure :=
                  { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                    args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                    outputType := withNullable (toProtoType ctx m.sig.ret)
                      m.sig.retNullable } } : Proto.AggregateMeasure))
        simp only [FunctionSig.mkSig, List.map_cons, hurm, h2]

/-- Sort-key-list inversion: the lowered keys decode (names re-derived from
    the schema) and re-lower to the same wire sort fields. -/
theorem decodeSortKeys_reEnc (s : Schema) (ks : List (SortKey s))
    (hok : ∀ k ∈ ks, s.get? k.col.ordinal ≠ none) :
    ∃ ks', decodeSortKeys s (ks.map sortFieldLower) = some ks' ∧
      ks'.map (fun k =>
        (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
          k.direction⟩ : Proto.SortField)) =
      ks.map (fun k =>
        (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
          k.direction⟩ : Proto.SortField)) := by
  induction ks with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons k rest ih =>
      obtain ⟨col, dir⟩ := k
      have hk : s.get? col.ordinal ≠ none :=
        hok { col := col, direction := dir } (by simp)
      have hrest : ∀ k2 ∈ rest, s.get? k2.col.ordinal ≠ none := fun k2 h2 =>
        hok k2 (by simp [h2])
      obtain ⟨ks', h1, h2⟩ := ih hrest
      cases hg : s.get? col.ordinal with
      | none => exact absurd hg hk
      | some col3 =>
          obtain ⟨nm, t3, n3⟩ := col3
          refine ⟨{ col := { name := nm, ordinal := col.ordinal }, direction := dir } :: ks',
            ?_, ?_⟩
          · simp only [List.map_cons, sortFieldLower, decodeSortKeys, hg, h1]
          · show ({ col := { name := nm, ordinal := col.ordinal }, direction := dir } :: ks').map
                (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField)) =
              ({ col := col, direction := dir } :: rest).map
                (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField))
            show ⟨Proto.Expression.field { ordinal := col.ordinal, segment := none },
                dir⟩ :: ks'.map (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField)) =
              ⟨Proto.Expression.field { ordinal := col.ordinal, segment := none },
                dir⟩ :: rest.map (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField))
            rw [h2]

/-! ## the master rel re-encode theorem -/

/- The wire-level round trip: for EVERY typed rel `r` satisfying `Rel.okS`,
   decoding `r`'s lowered form and re-lowering the decode recovers the SAME
   wire term.  This is the composition the wire consumes: anchors, ordinals,
   and schemas round-trip; names (erased by the wire) are re-derived from the
   decode. -/

/-- `squareOf` on an already-square package. -/
theorem squareOf_mk (s : Schema) (r : Rel s s) :
    squareOf (AnyRel.mk s s r) = some ⟨s, r⟩ := by
  show (if h : s = s then some (SqRel.mk s (Rel.castSq h r)) else none) = some ⟨s, r⟩
  rw [dif_pos rfl]
  rfl

/-- **THE rel re-encode theorem**: for every typed rel `r` (with its
    `Rel.okS` well-formedness — ordinal-safe columns, decodable call output
    types, decodable read schemas, and the decoded-schema pins the GADT
    demands), decoding `r`'s lowered form and re-lowering the result recovers
    the SAME wire term. -/
theorem decodeRel_reEnc (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {inS outS : Schema} (r : Rel inS outS), Rel.okS ctx inv r →
      (decodeRel inv (r.toProtoWith ctx)).map (fun a => relLower a ctx) =
        some (r.toProtoWith ctx) := by
  intro inS outS r
  induction r with
  | read table sc =>
      intro hok
      show (decodeRel inv (Proto.Rel.read
        { readType := .namedTable [table]
          baseSchema := some { fields := sc.map (toProtoColType ctx), names := sc.names }
          common := none })).map (fun a => relLower a ctx) =
        some (Proto.Rel.read
        { readType := .namedTable [table]
          baseSchema := some { fields := sc.map (toProtoColType ctx), names := sc.names }
          common := none })
      simp only [decodeRel]
      rw [schemaOfFields_of_toProto ctx sc hok]
      simp [relLower, Rel.toProtoWith]
  | @filter s _ input cond ih =>
      intro hok
      obtain ⟨hin, hsq, hcond⟩ := hok
      have ihc := ih hin
      simp only [Rel.toProtoWith, decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          obtain ⟨r1, hpkg, hlow⟩ :=
            sqChild_of_decode inv ctx (input.toProtoWith ctx) s hsq ihc hx
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨ce, hce'⟩ := decodeExpr_shape s inv ctx hfn cond hcond
          rw [hce']
          have hlowce : ce.toProto ctx = cond.toProto ctx := by
            have h2 := decodeExpr_reEnc s inv ctx hfn cond (Expr.okSR_to_okS ctx s _ hcond)
            rw [hce'] at h2
            simpa [anyLower] using h2
          simp [relLower, Rel.toProtoWith, hlowce, hlow]
  | @project s p input outs emit ih =>
      intro hok
      obtain ⟨hin, hpr, houts⟩ := hok
      have ihc := ih hin
      simp only [Rel.toProtoWith, decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          obtain ⟨r1, hpkg, hlow⟩ :=
            pairChild_of_decode inv ctx (input.toProtoWith ctx) s p hpr ihc hx
          rw [hpkg]
          obtain ⟨ps', hp1, hp2⟩ := decodeProjections_reEnc p inv ctx hfn outs houts
          simp only [hp1]
          cases emit with
          | none => simp [relLower, Rel.toProtoWith, Option.map_none, emitOf, hlow, hp2]
          | some m => simp [relLower, Rel.toProtoWith, Option.map_some, emitOf, hlow, hp2]
  | @aggregate s input grouping measures ih =>
      intro hok
      obtain ⟨hin, hsq, hg, hm⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.aggregate
        { groupingExpressions := anyExprsLower grouping ctx,
          measures := measures.map (measureLower ctx),
          input := input.toProtoWith ctx, common := none })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          obtain ⟨r1, hpkg, hlow⟩ :=
            sqChild_of_decode inv ctx (input.toProtoWith ctx) s hsq ihc hx
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨gxs, hg1, hg2⟩ := decodeAnyExprs_reEnc s inv ctx hfn grouping hg
          obtain ⟨mxs, hm1, hm2⟩ := decodeMeasures_reEnc s inv ctx hfn measures hm
          simp only [hg1, hm1]
          simp only [Option.map_some, relLower, Rel.toProtoWith]
          show some (Proto.Rel.aggregate
            { groupingExpressions :=
                gxs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx),
              measures :=
                mxs.map (fun m =>
                  ({ measure :=
                      { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                        args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                        outputType := withNullable (toProtoType ctx m.sig.ret)
                          m.sig.retNullable } } : Proto.AggregateMeasure)),
              input := r1.toProtoWith ctx, common := none }) =
            some (Proto.Rel.aggregate
              { groupingExpressions :=
                  grouping.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx),
                measures :=
                  measures.map (fun m =>
                    ({ measure :=
                        { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                          args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                          outputType := withNullable (toProtoType ctx m.sig.ret)
                            m.sig.retNullable } } : Proto.AggregateMeasure)),
                input := input.toProtoWith ctx, common := none })
          rw [hg2, hm2, hlow]
  | @sort s input orderBy ih =>
      intro hok
      obtain ⟨hin, hsq, hk⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.sort
        { sorts := orderBy.map sortFieldLower, input := input.toProtoWith ctx,
          common := none })).map (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          obtain ⟨r1, hpkg, hlow⟩ :=
            sqChild_of_decode inv ctx (input.toProtoWith ctx) s hsq ihc hx
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨ks', hk1', hk2'⟩ := decodeSortKeys_reEnc s orderBy hk
          simp only [hk1']
          simp [relLower, Rel.toProtoWith, hk2', hlow]
  | @fetch s input limit offset ih =>
      intro hok
      obtain ⟨hin, hsq⟩ := hok
      have ihc := ih hin
      simp only [Rel.toProtoWith, decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          obtain ⟨r1, hpkg, hlow⟩ :=
            sqChild_of_decode inv ctx (input.toProtoWith ctx) s hsq ihc hx
          rw [hpkg]
          simp only [squareOf_mk]
          simp [relLower, Rel.toProtoWith, hlow]
  | @join sl sl' sr sr' _ left right cond jt ihl ihr =>
      intro hok
      obtain ⟨hl, hr, hpl, hpr, hcond⟩ := hok
      have ihcL := ihl hl
      have ihcR := ihr hr
      simp only [Rel.toProtoWith, decodeRel]
      cases hx1 : decodeRel inv (left.toProtoWith ctx) with
      | none => rw [hx1] at ihcL; simp at ihcL
      | some pkgL =>
          cases hx2 : decodeRel inv (right.toProtoWith ctx) with
          | none => rw [hx2] at ihcR; simp at ihcR
          | some pkgR =>
              obtain ⟨rl, hpkgL, hlowL⟩ :=
                pairChild_of_decode inv ctx (left.toProtoWith ctx) sl sl' hpl ihcL hx1
              obtain ⟨rr, hpkgR, hlowR⟩ :=
                pairChild_of_decode inv ctx (right.toProtoWith ctx) sr sr' hpr ihcR hx2
              rw [hpkgL, hpkgR]
              show Option.map (fun a => relLower a ctx)
                  (match decodeExpr (sl' ++ sr') inv (cond.toProto ctx) with
                  | some (AnyExpr.mk .bool n ce) =>
                      some (AnyRel.mk (sl ++ sr) (sl' ++ sr') (Rel.join rl rr ce jt))
                  | _ => none) =
                some (Proto.Rel.join
                  { joinType := jt, left := left.toProtoWith ctx,
                    right := right.toProtoWith ctx, condition := cond.toProto ctx,
                    postJoinFilter := none, common := none })
              obtain ⟨ce, hce'⟩ := decodeExpr_shape (sl' ++ sr') inv ctx hfn cond hcond
              rw [hce']
              have hlowce : ce.toProto ctx = cond.toProto ctx := by
                have h2 := decodeExpr_reEnc (sl' ++ sr') inv ctx hfn cond (Expr.okSR_to_okS ctx (sl' ++ sr') _ hcond)
                rw [hce'] at h2
                simpa [anyLower] using h2
              simp [relLower, Rel.toProtoWith, hlowL, hlowR, hlowce]
  | @set s s' op left right ihl ihr =>
      intro hok
      obtain ⟨hl, hr, hpair⟩ := hok
      have ihcL := ihl hl
      have ihcR := ihr hr
      simp only [Rel.toProtoWith, decodeRel]
      cases hx1 : decodeRel inv (left.toProtoWith ctx) with
      | none => rw [hx1] at ihcL; simp at ihcL
      | some pkgL =>
          cases hx2 : decodeRel inv (right.toProtoWith ctx) with
          | none => rw [hx2] at ihcR; simp at ihcR
          | some pkgR =>
              rw [hx1] at ihcL
              rw [hx2] at ihcR
              cases pkgL with
              | mk s1 s1' rl =>
                  cases pkgR with
                  | mk s2 s2' rr =>
                      have hlowL : rl.toProtoWith ctx = left.toProtoWith ctx :=
                        relLower_some_map rl ihcL
                      have hlowR : rr.toProtoWith ctx = right.toProtoWith ctx :=
                        relLower_some_map rr ihcR
                      rw [hx1, hx2] at hpair
                      have heq : (s1, s1') = (s2, s2') := by
                        have hp := hpair (AnyRel.mk s1 s1' rl) (AnyRel.mk s2 s2' rr) rfl rfl
                        simpa [AnyRel.schemaPair] using hp
                      have h1 : s1 = s2 := congrArg Prod.fst heq
                      have h2 : s1' = s2' := congrArg Prod.snd heq
                      simp only [Option.map_some, relLower]
                      rw [dif_pos h1, dif_pos h2]
                      show some (Proto.Rel.set
                        { op := op,
                          inputs := [rl.toProtoWith ctx,
                            (Rel.cast2 h1 h2 rr).toProtoWith ctx],
                          common := none }) =
                        some (Proto.Rel.set
                          { op := op,
                            inputs := [left.toProtoWith ctx, right.toProtoWith ctx],
                            common := none })
                      rw [Rel.cast2_toProtoWith, hlowL, hlowR]
  | @write s s' op table ts input ih =>
      intro hok
      obtain ⟨hin, hts⟩ := hok
      have ihc := ih hin
      simp only [Rel.toProtoWith, decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          cases pkg with
          | mk t t' r1 =>
              have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
                simpa [relLower] using ihc
              cases ts with
              | none =>
                  show (match some (AnyRel.mk t t' r1) with
                    | some (AnyRel.mk u u' ri) =>
                        some (AnyRel.mk u u' (Rel.write op table none ri))
                    | none => none).map (fun a => relLower a ctx) = _
                  simp [relLower, Rel.toProtoWith, hlow]
              | some sc =>
                  have hsco := hts
                  show (match some (AnyRel.mk t t' r1) with
                    | some (AnyRel.mk u u' ri) =>
                        match schemaOfFields sc.names (sc.map (toProtoColType ctx)) with
                        | some sc' =>
                            some (AnyRel.mk u u' (Rel.write op table (some sc') ri))
                        | none => none
                    | none => none).map (fun a => relLower a ctx) = _
                  rw [schemaOfFields_of_toProto ctx sc hsco]
                  simp [relLower, Rel.toProtoWith, hlow]
  | @extensionSingle s s' detail input ih =>
      intro hok
      have ihc := ih hok
      simp only [Rel.toProtoWith, decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          cases pkg with
          | mk t t' r1 =>
              have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
                simpa [relLower] using ihc
              show (match some detail with
                | some d => some (AnyRel.mk t t' (Rel.extensionSingle d r1))
                | none => none).map (fun a => relLower a ctx) = _
              simp [relLower, Rel.toProtoWith, hlow]

end Substrait.Decode

end -- @[expose] public section
