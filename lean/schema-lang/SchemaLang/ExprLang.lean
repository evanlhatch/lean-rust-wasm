/-
# SchemaLang.ExprLang — the expression-language interface (W7.2)

The toolkit has several expression worlds (`VExpr` here, substrait's
`Expr`, the variant `VCase`) and consumers written per-world. This
module is the Strata `PureExpr` pattern: ONE structure packing
(Ident, Expr, Row, eval) + capability classes with LAW fields, sitting
between the GADTs (which STAY at authoring/semantics — doctrine) and
their consumers, written once against the interface.

The driving consumer (Emit.Invariant) needs per node: field refs BY
NAME (the `ref` rendering key), u64 literals, `strlen` of a string
FIELD REF (the only `.string` shape), the u64 comparisons (`>`, `==`),
and boolean `&&`/`!`. So the interface exposes exactly two views:
`U64Node` (leaves: lit / col / strlen-of-col — the cols carry the
boxed row projection so EVALUATION readings work too) and `BoolNode`
(col / gt / eq / and / not, children PRE-FOLDED — the fold shape keeps
consumer recursion structural per-instance; no well-founded plumbing
for abstract expression types).

Laws (no lawless classes): `HasU64.view_eval` ties the u64 view to the
boxed eval; `HasBool.fold_spec` ties the bool fold at the spec
algebras to the boxed eval. Strata's `tt ≠ ff` has no analogue —
VExpr has no boolean-literal ctor; the fold-spec law is the boolean
capability's law. The two EVALUATION readings (boxed `evalSpecI`, raw
0/1-word `evalRawI`) are written ONCE here; the VExpr instance proves
both agree with `evalV`/`evalB` (the "readings tie", promoted from an
executed test to theorems).

Deliberate exclusions: `Ty` is FIXED to SchemaLang's closed universe
(packing an abstract `Ty` is the substrait port's step); the variant
family (`VCase`) joins when a consumer needs it; emission algebras
live in Emit.Invariant (the consumer), not here.
-/

import SchemaLang.Validate

namespace SchemaLang

/-! ## The single-ctor payload projections -/

/-- The u64 payload projection (the `.u64` index has one ctor). -/
def Value.outU64 : Value .u64 → UInt64
  | .u64 v => v

/-- The bool payload projection. -/
def Value.outBool : Value .bool → Bool
  | .bool b => b

/-- The string payload projection. -/
def Value.outString : Value .string → String
  | .string s => s

/-- The single-ctor eta at `.u64`: the generalize-free case split (the
    indexed match's dependent motive bars `cases h :` on a scrutinee
    — the rewrite route stays). -/
theorem Value.outU64_eta : ∀ (v : Value .u64), v = .u64 v.outU64
  | .u64 _ => rfl

/-- The single-ctor eta at `.bool`. -/
theorem Value.outBool_eta : ∀ (v : Value .bool), v = .bool v.outBool
  | .bool _ => rfl

/-! ## The interface -/

/-- The expression-language interface: one structure packing what
    consumers abstract over. `Ident` is the field-ref identifier
    (String for VExpr — the emitter's rendering key); `Expr` is the
    expression family indexed by the closed boundary universe; `Row`
    is the subject expressions evaluate against; `eval` is the boxed
    (SPEC) reading — the semantics of record. -/
structure ExprLang where
  Ident : Type
  Expr : Ty → Type
  Row : Type
  eval : {t : Ty} → Expr t → Row → Value t

/-- The u64 node view: the leaves a consumer sees. The cols carry the
    boxed row projection (`get`) — the emission reading ignores it
    (the NAME is the rendering key), the evaluation readings use it
    (each reading projects its own way). `strlenCol` is strlen OF A
    FIELD REF — the only `.string`-typed expression shape VExpr has. -/
inductive U64Node (I R : Type) : Type where
  | lit (v : UInt64)
  | col (n : I) (get : R → Value .u64)
  | strlenCol (n : I) (get : R → Value .string)

/-- The bool node view with children PRE-FOLDED: `α` is the folded
    bool-child type, `γ` the folded u64-child type (the consumer picks
    both — String for emission, `R → Bool`/`R → UInt64` for
    evaluation). The fold shape is what lets ONE consumer definition
    recurse over an ABSTRACT expression type: the per-instance fold is
    structural on the GADT; consumers never recurse themselves. -/
inductive BoolNode (I R : Type) (α γ : Type) : Type where
  | col (n : I) (get : R → Value .bool)
  | gt (a b : γ)
  | eq (a b : γ)
  | and (a b : α)
  | not (a : α)

/-! ## The algebras (the two evaluation readings, written once) -/

/-- The boxed (spec) reading of a u64 node — `evalV`'s u64 arms. -/
def U64Node.eval : U64Node I R → R → Value .u64
  | .lit v, _ => .u64 v
  | .col _ g, r => g r
  | .strlenCol _ g, r => .u64 (string_len (g r).outString)

/-- The raw (0/1-word) reading of a u64 node — `evalRaw`'s u64 arms. -/
def U64Node.evalRaw : U64Node I R → R → UInt64
  | .lit v, _ => v
  | .col _ g, r => (g r).outU64
  | .strlenCol _ g, r => string_len (g r).outString

/-- The spec bool algebra over folded children (α = `R → Bool`,
    γ = `R → UInt64`) — `evalV`'s bool arms. -/
def BoolNode.evalSpec : BoolNode I R (R → Bool) (R → UInt64) → R → Bool
  | .col _ g => fun r => (g r).outBool
  | .gt a b => fun r => a r > b r
  | .eq a b => fun r => a r == b r
  | .and a b => fun r => a r && b r
  | .not a => fun r => !(a r)

/-- The raw bool algebra over folded children (α = γ = `R → UInt64`)
    — `evalRaw`'s bool arms EXACTLY (conjunction = the 0/1
    multiplication, negation = `1 - x`). -/
def BoolNode.evalRaw : BoolNode I R (R → UInt64) (R → UInt64) → R → UInt64
  | .col _ g => fun r => boolToU64 (g r).outBool
  | .gt a b => fun r => boolToU64 (a r > b r)
  | .eq a b => fun r => boolToU64 (a r == b r)
  | .and a b => fun r => a r * b r
  | .not a => fun r => 1 - a r

/-! ## The capability classes (with law fields) -/

/-- The u64 capability: the leaf view. LAW (`view_eval`): the view's
    boxed reading IS the packed eval — a consumer reading the view
    reads the expression's semantics, not a parallel syntax tree. -/
class HasU64 (L : ExprLang) where
  view : L.Expr .u64 → U64Node L.Ident L.Row
  view_eval : ∀ (e : L.Expr .u64) (r : L.Row),
    U64Node.eval (view e) r = L.eval e r

/-- The bool capability: the fold over pre-folded children (the
    consumer supplies the u64-child fold `u` and the node algebra).
    LAW (`fold_spec`): the fold at the spec algebras computes the
    boxed eval's Bool projection — the fold is a faithful READING,
    not just a syntax walk. (Strata's `tt ≠ ff` has no analogue:
    VExpr has no boolean-literal ctor.) -/
class HasBool (L : ExprLang) [HasU64 L] where
  fold : {α γ : Type} →
    (u : L.Expr .u64 → γ) → (alg : BoolNode L.Ident L.Row α γ → α) →
    L.Expr .bool → α
  fold_spec : ∀ (e : L.Expr .bool),
    fold (fun c r => (U64Node.eval (HasU64.view c) r).outU64) BoolNode.evalSpec e
      = fun r => (L.eval e r).outBool

/-! ## The two evaluation readings, written once against the interface -/

/-- Reading #1 — the BOXED reading through the fold: the spec algebras
    over the view-read u64 leaves. -/
def evalSpecI (L : ExprLang) [HasU64 L] [HasBool L] (e : L.Expr .bool) :
    L.Row → Bool :=
  HasBool.fold (fun c r => (U64Node.eval (HasU64.view c) r).outU64)
    BoolNode.evalSpec e

/-- Reading #1 agrees with the packed boxed eval — the `fold_spec`
    law, restated at the reading. -/
theorem evalSpecI_eq (L : ExprLang) [HasU64 L] [HasBool L]
    (e : L.Expr .bool) (r : L.Row) :
    evalSpecI L e r = (L.eval e r).outBool :=
  congrFun (HasBool.fold_spec e) r

/-- Reading #2 — the RAW (0/1-word) reading through the fold:
    `evalB`'s exact shape, recovered through the interface. -/
def evalRawI (L : ExprLang) [HasU64 L] [HasBool L] (e : L.Expr .bool) :
    L.Row → UInt64 :=
  HasBool.fold (fun c => U64Node.evalRaw (HasU64.view c)) BoolNode.evalRaw e

/-- The validator projection through the interface (`validates`'
    shape: the raw 0/1 word projected by `== 1`). -/
def validatesI (L : ExprLang) [HasU64 L] [HasBool L] (e : L.Expr .bool)
    (r : L.Row) : Bool :=
  evalRawI L e r == 1

/-! ## The VExpr instance -/

/-- The VExpr language over schema `s`. `@[reducible]`: consumers pass
    `VExpr s` expressions where `(vexprLang s).Expr` is expected (the
    instance-search reducibility rule). -/
@[reducible] def vexprLang (s : List Field) : ExprLang where
  Ident := String
  Expr := VExpr s
  Row := RowVals s
  eval := evalV

/-- The u64 view: the leaf data + the boxed row projections (the
    `ColPath` walk is the projection — the closure-free rule holds:
    this decl is SPEC-side, never a backend target). -/
def vexprViewU64 : VExpr s .u64 → U64Node String (RowVals s)
  | .lit v => .lit v
  | .col n p => .col n (fun r => p.get r)
  | .strlen e =>
      -- typing: the operand is a field ref (the only `.string` shape)
      match e with
      | .col n p => .strlenCol n (fun r => p.get r)

/-- The view's law: the view's boxed reading IS `evalV`. -/
theorem vexprViewU64_eval : ∀ (e : VExpr s .u64) (r : RowVals s),
    U64Node.eval (vexprViewU64 e) r = evalV e r
  | .lit _, _ => rfl
  | .col _ _, _ => rfl
  | .strlen (.col _ p), r => by
      simp only [vexprViewU64, U64Node.eval, evalV]
      cases _ : p.get r <;> rfl

/-- The bool fold: structural on the GADT (the ONE place recursion is
    proved; consumers ride the fold). -/
def vexprFoldBool {α γ : Type} (u : VExpr s .u64 → γ)
    (alg : BoolNode String (RowVals s) α γ → α) : VExpr s .bool → α
  | .col n p => alg (.col n (fun r => p.get r))
  | .gt a b => alg (.gt (u a) (u b))
  | .eq a b => alg (.eq (u a) (u b))
  | .and a b => alg (.and (vexprFoldBool u alg a) (vexprFoldBool u alg b))
  | .not a => alg (.not (vexprFoldBool u alg a))

/-- The fold's law, pointwise: at the spec algebras the fold computes
    `evalV`'s Bool projection. EQUATION-STYLE (the fixed `.bool` index
    bars the `induction` tactic — the Validate header's lesson; the
    recursion on the children is structural). -/
theorem vexprFoldBool_spec_pt : ∀ (e : VExpr s .bool) (r : RowVals s),
    vexprFoldBool (fun c r => (U64Node.eval (vexprViewU64 c) r).outU64)
        BoolNode.evalSpec e r
      = (evalV e r).outBool
  | .col _ _, _ => by
      simp only [vexprFoldBool, BoolNode.evalSpec, evalV]
  | .gt a b, r => by
      obtain ⟨x, hx⟩ : ∃ x : UInt64, evalV a r = .u64 x :=
        ⟨_, (Value.outU64_eta (evalV a r))⟩
      obtain ⟨y, hy⟩ : ∃ y : UInt64, evalV b r = .u64 y :=
        ⟨_, (Value.outU64_eta (evalV b r))⟩
      simp only [vexprFoldBool, BoolNode.evalSpec, vexprViewU64_eval, evalV,
        hx, hy, Value.outU64, Value.outBool]
  | .eq a b, r => by
      obtain ⟨x, hx⟩ : ∃ x : UInt64, evalV a r = .u64 x :=
        ⟨_, (Value.outU64_eta (evalV a r))⟩
      obtain ⟨y, hy⟩ : ∃ y : UInt64, evalV b r = .u64 y :=
        ⟨_, (Value.outU64_eta (evalV b r))⟩
      simp only [vexprFoldBool, BoolNode.evalSpec, vexprViewU64_eval, evalV,
        hx, hy, Value.outU64, Value.outBool]
  | .and a b, r => by
      obtain ⟨x, hx⟩ : ∃ x : Bool, evalV a r = .bool x :=
        ⟨_, (Value.outBool_eta (evalV a r))⟩
      obtain ⟨y, hy⟩ : ∃ y : Bool, evalV b r = .bool y :=
        ⟨_, (Value.outBool_eta (evalV b r))⟩
      simp only [vexprFoldBool, BoolNode.evalSpec, vexprFoldBool_spec_pt a r,
        vexprFoldBool_spec_pt b r, evalV, hx, hy, Value.outBool]
      cases x <;> cases y <;> rfl
  | .not a, r => by
      obtain ⟨x, hx⟩ : ∃ x : Bool, evalV a r = .bool x :=
        ⟨_, (Value.outBool_eta (evalV a r))⟩
      simp only [vexprFoldBool, BoolNode.evalSpec, vexprFoldBool_spec_pt a r,
        evalV, hx, Value.outBool]

/-- The fold's law, as the function equality the class field states. -/
theorem vexprFoldBool_spec (e : VExpr s .bool) :
    vexprFoldBool (fun c r => (U64Node.eval (vexprViewU64 c) r).outU64)
        BoolNode.evalSpec e
      = fun r => (evalV e r).outBool :=
  funext (vexprFoldBool_spec_pt e)

/-- The view's RAW coherence: the view's 0/1-word reading IS
    `evalRaw` — the lemma the raw tie theorem rewrites with. -/
theorem vexprViewU64_evalRaw : ∀ (e : VExpr s .u64) (r : RowVals s),
    U64Node.evalRaw (vexprViewU64 e) r = evalRaw e r
  | .lit _, _ => rfl
  | .col _ p, r => by
      simp only [vexprViewU64, U64Node.evalRaw, evalRaw]
      cases _ : p.get r <;> rfl
  | .strlen (.col _ p), r => by
      simp only [vexprViewU64, U64Node.evalRaw, evalRaw]
      cases _ : p.get r <;> rfl

/-- The raw tie, at the fold: the fold at the raw algebras IS
    `evalB` — the compiled reading recovered through the interface. -/
theorem vexprFoldBool_raw : ∀ (e : VExpr s .bool) (r : RowVals s),
    vexprFoldBool (fun c => U64Node.evalRaw (vexprViewU64 c))
        BoolNode.evalRaw e r
      = evalB e r
  | .col _ p, r => by
      simp only [vexprFoldBool, BoolNode.evalRaw, evalB, evalRaw]
      cases _ : p.get r <;> rfl
  | .gt _ _, _ => by
      simp only [vexprFoldBool, BoolNode.evalRaw, vexprViewU64_evalRaw,
        evalB, evalRaw]
  | .eq _ _, _ => by
      simp only [vexprFoldBool, BoolNode.evalRaw, vexprViewU64_evalRaw,
        evalB, evalRaw]
  | .and a b, r => by
      simp only [vexprFoldBool, BoolNode.evalRaw, evalB, evalRaw]
      rw [vexprFoldBool_raw a r, vexprFoldBool_raw b r]
      simp only [evalB]
  | .not a, r => by
      simp only [vexprFoldBool, BoolNode.evalRaw, evalB, evalRaw]
      rw [vexprFoldBool_raw a r]
      simp only [evalB]

instance vexprHasU64 {s : List Field} : HasU64 (vexprLang s) where
  view := vexprViewU64
  view_eval := vexprViewU64_eval

instance vexprHasBool {s : List Field} : HasBool (vexprLang s) where
  fold := vexprFoldBool
  fold_spec := vexprFoldBool_spec

/-- Reading #1 on the VExpr instance IS `evalV`'s projection. -/
theorem evalSpecI_vexpr (s : List Field) (e : VExpr s .bool) (r : RowVals s) :
    evalSpecI (vexprLang s) e r = (evalV e r).outBool :=
  evalSpecI_eq (vexprLang s) e r

/-- Reading #2 on the VExpr instance IS `evalB` — the executed
    spec≡compiled pin (Tests' `validateChecks`) promoted to a theorem. -/
theorem evalRawI_vexpr (s : List Field) (e : VExpr s .bool) (r : RowVals s) :
    evalRawI (vexprLang s) e r = evalB e r :=
  vexprFoldBool_raw e r

/-- The interface validator IS `validates` on the VExpr instance. -/
theorem validatesI_vexpr (s : List Field) (e : VExpr s .bool) (r : RowVals s) :
    validatesI (vexprLang s) e r = validates e r := by
  show (evalRawI (vexprLang s) e r == 1) = (evalB e r == 1)
  rw [evalRawI_vexpr]

end SchemaLang
