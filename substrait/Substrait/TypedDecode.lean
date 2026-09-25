/-
# Substrait.TypedDecode — the TYPED decode (the wire's read face: Proto → Typed)

Owner: the substrait wire agent (the mandate tree, `substrait/`).

THE NAMED FOLLOW-UP, LANDED (Wire.lean's header + Substrait.lean's
Phase-4 row): the decode ladder's TYPED face. The wire recovers the
Proto model exactly (`Substrait.Wire.decPlan?`); THIS module recovers
the TYPED term: `decTypedRel?` / `decTypedPlan?` turn the wire's rel
trees into `Substrait.Typed.Rel` — the schema-indexed GADT — with the
well-typedness DISCHARGED BY CONSTRUCTION: the decode produces the
typed term + its `HasCol` resolution proof in the same step (a column
reference is decoded to a `field` carrying the proof its ordinal buys
— `HasCol.at`), never a post-hoc validation of an untyped term.

THE RUNGS (each discharges its level):

- `decTypedTyCore?` / `decTypedColTy?` — the wire type → the closed
  `Ty` + the nullability bit. The refusals ARE the retarget's honest
  face, read back: `i32` has no `SchemaCore.Ty` ctor (SS0001), and the
  `unspecified` nullability is never written by the typed layer
  (SS0002). The list element's wire nullability must be `required`
  (the lowering's `toProtoType` writes exactly that face).
- `decTypedLit?` — the literal payload → `SchemaCore.Value t` (the
  GADT: a mismatched payload is unconstructible on BOTH faces).
  `i64` rides `Int64.ofInt` — the two's-complement face is total over
  `Int64.toInt` (core's `ofInt_toInt`).
- `decTypedExpr?` / `decTypedArgs?` — the mutual expression ladder:
  literal / field / call, the argument spine rebuilt WITH its type
  index. The field rung is the by-name discipline's read face: the
  ordinal looks up the schema, the miss REFUSES (SS0003 — the
  schema-mismatched reference), the hit constructs the `HasCol`.
- `decTypedSchema?` — the read's base schema: the fields × names zip
  (a length disagreement refuses — SS0006).
- `decTypedRel?` — the rel ladder: read / filter / join / aggregate /
  sort / fetch / set. The computed-output-schema discipline survives
  the read: the input schema flows DOWN the recursion, each node's
  output schema is computed exactly as `Typed`'s index computes it,
  and the refinements the GADT forces are the decode's refusals —
  a non-boolean condition (SS0004), a set whose sides disagree
  (SS0005 — the same-schema discipline, ENFORCED here because
  `Rel.set`'s type will not accept anything else). The project node
  REFUSES (SS0007): the wire's project carries no output names, so
  the typed project's computed schema is unrecoverable — the named
  gap, never a fabricated name. The `keep` node has no wire spelling
  at all (the lowering refuses it; nothing to decode).

THE LAW (the honest grade per Kit.Correspondence — the encode is
total on its domain, the decode partial on junk, so the
correspondence is the CONDITIONAL retraction):
`decTypedRel?_ok` — for every typed rel the lowering ACCEPTS and the
decode's domain condition holds (`Rel.decodable`), decode ∘ lower is
the identity AT THE TYPED LEVEL: `rel.toProto = .ok p → decTypedRel?
p = .ok (AnyRel.mk inS outS rel)`. The domain condition names the two
honest gaps: no project node (the wire carries no output names), and
every aggregate's measures carry the arity tie (`Measure.tied` — the
wire's measure shape IS the invocation, so a signature whose separate
arg list drifts from its erased args does not round-trip). The typed
plan face composes over `Rel.toPlan` (`decTypedPlan?_ok`).

THE FULL CIRCLE (the wire law lifted, pinned in SubstraitTests):
`Query.TypedBridge.qToRel` lowers a qlang query to a typed rel; the
typed rel lowers to a plan, the plan encodes to bytes, the wire decodes
the bytes to the plan (`decPlan?_encPlan`), and the typed decode
recovers the SAME typed rel — the bridge's agreement + the wire's law
composed, the query's read direction closed end to end.

The refusals ride the SS family of the persisted registry
(`notes/code-registry.txt`): SS0001–SS0011; the constants below are
the family's declaration (the code-registry gate's coverage scan ties
every spelling to its live row).

Core-only (imports Substrait.Typed — the cone rule; no byte-level
recursion here: this ladder consumes the Proto values the wire's
fuel-bounded decoders already recovered, so no fuel and no fuel
induction — the fuel discipline lives in Wire.lean).

The five questions (notes/v3/01-core.md):
- root: Crossing — the Proto plan model → the typed term families.
- carrier grade: the conditional retraction (the law above; the
  exact-image grade is meaningless while the wire accepts faces the
  typed layer cannot name — the refusals are the honest boundary).
- spine reading: Typed → Proto (the lowering) → bytes (Wire) →
  bytes → Proto (Wire) → Typed (THIS — the read direction's face).
- ladder rung: hand theorems of the small kind — the per-rung laws
  compose through the ONE rel induction (the proof-carrying-recursive-
  def pattern over the mutual GADT, Typed.lean's bridge style).
- gate row: the axiom report (Substrait is gated); SubstraitTests
  carries the typed-decode sweeps + the refusal teeth + the
  full-circle pin.
-/

import Substrait.Typed
import Kit.Diag

/- The three domain predicates the decode reads live in the TYPED
   namespace (their self-dot-recursion + the dot resolution from
   Typed's values require it; a `namespace Typed` inside Decode would
   NEST — Substrait.Decode.Typed — and strand both). -/
namespace Substrait.Typed

open SchemaCore

/-- The erased args' (type, nullability) list — the measure-arity tie's
    data side. -/
def AnyExpr.tns {s : Schema} (ae : AnyExpr s) : Ty × Bool :=
  match ae with | .mk t n _ => (t, n)

/-- The arity tie (the measure's law condition): the signature's arg
    list IS the erased args' index — the evaluator's dispatch contract.
    The wire's measure shape IS the invocation (the seed's named
    divergence), so the signature's separate arg list is not on the
    wire: a lowered measure breaking the tie does not round-trip — the
    law's named condition, never a silent gap. -/
def Measure.tied {s : Schema} (m : Measure s) : Prop :=
  m.args.map AnyExpr.tns = m.sig.args

/-- The typed decode's domain condition (the law's face): no project
    node (the wire's project carries no output names — SS0007's face),
    and every aggregate's measures carry the arity tie. -/
def Rel.decodable {inS outS : Schema} :
    Rel inS outS → Prop
  | .read _ _ => True
  | .filter i _ => i.decodable
  | .project _ _ => False
  | .keep _ _ => True
  | .join l r _ _ => l.decodable ∧ r.decodable
  | .aggregate i _ ms => (∀ m ∈ ms, m.tied) ∧ i.decodable
  | .sort i _ => i.decodable
  | .fetch i _ _ => i.decodable
  | .set _ l r => l.decodable ∧ r.decodable

end Substrait.Typed

namespace Substrait.Decode

open Substrait.Proto
open Substrait.Typed
open SchemaCore

/-! ## the SS family — the typed decode's E-codes (the persisted registry) -/

def eSS0001 : Kit.ECode := ⟨"SS0001"⟩
def eSS0002 : Kit.ECode := ⟨"SS0002"⟩
def eSS0003 : Kit.ECode := ⟨"SS0003"⟩
def eSS0004 : Kit.ECode := ⟨"SS0004"⟩
def eSS0005 : Kit.ECode := ⟨"SS0005"⟩
def eSS0006 : Kit.ECode := ⟨"SS0006"⟩
def eSS0007 : Kit.ECode := ⟨"SS0007"⟩
def eSS0008 : Kit.ECode := ⟨"SS0008"⟩
def eSS0009 : Kit.ECode := ⟨"SS0009"⟩
def eSS0010 : Kit.ECode := ⟨"SS0010"⟩
def eSS0011 : Kit.ECode := ⟨"SS0011"⟩

/-- The typed decode's refusal, in the ONE envelope (05 §4): the SS
    family's error, structured — never a bare string. -/
def ssDiag (code : Kit.ECode) (message : String) : Kit.Diag :=
  { code := code, message := message, severity := .error }

/-! ## rung 1 — the wire type → the closed Ty -/

/-- The typed layer's fragment: the `Ty`s the wire CAN name (the
    lowering's `toProtoType` domain; `u64`/`option`/… refuse at the
    emission boundary — the retarget's honest face, upstream). -/
def inTyFragment : Ty → Bool
  | .bool => true
  | .i64 => true
  | .string => true
  | .list e => inTyFragment e
  | _ => false

/-- The wire type's CORE face → the closed `Ty` (the top nullability
    bit is read by the caller — the column carries it separately; the
    list ELEMENT's wire nullability must be `required`, the lowering's
    exact face). -/
def decTypedTyCore? : Proto.PType → Except Kit.Diag Ty
  | .bool _ => .ok .bool
  | .i64 _ => .ok .i64
  | .string _ => .ok .string
  | .i32 _ => .error (ssDiag eSS0001 "typed-decode: the wire type i32 has \
      no SchemaCore.Ty face (the closed universe's slice scalars are \
      bool/u64/i64/string) — the retarget's honest refusal, read back")
  | .list e _ =>
      match e.nullability with
      | .required =>
          match decTypedTyCore? e with
          | .ok t => .ok (.list t)
          | .error d => .error d
      | _ => .error (ssDiag eSS0002 "typed-decode: the list element's wire \
          nullability is not `required` — the typed layer's lowering writes \
          exactly the required face (the canonical dialect)")

/-- The wire type's COLUMN face → (Ty, the nullability bit). -/
def decTypedColTy? (pt : Proto.PType) : Except Kit.Diag (Ty × Bool) :=
  match decTypedTyCore? pt with
  | .ok t =>
      match pt.nullability with
      | .required => .ok (t, false)
      | .nullable => .ok (t, true)
      | .unspecified => .error (ssDiag eSS0002 "typed-decode: the wire type's \
          nullability is `unspecified` — the typed layer never writes it \
          (the lowering's withNullable face)")
  | .error d => .error d

/-- The lowering's face: every wire type it writes is `required` at
    the top (the nullability bit rides `withNullable`, the caller's
    column face). -/
theorem toProtoType_ok_required (t : Ty) (p : Proto.PType)
    (h : toProtoType t = .ok p) : p.nullability = .required := by
  cases t with
  | bool => simp only [toProtoType] at h; cases h; rfl
  | i64 => simp only [toProtoType] at h; cases h; rfl
  | string => simp only [toProtoType] at h; cases h; rfl
  | list e =>
      simp only [toProtoType] at h
      cases he : toProtoType e with
      | error _ => rw [he] at h; simp at h
      | ok _ =>
          rw [he] at h
          simp only [Except.ok.injEq] at h
          subst h
          rfl
  | _ => simp [toProtoType] at h

/-- The core decode is invariant under the top nullability (the bit is
    the caller's). -/
theorem decTypedTyCore?_setNull (n : Proto.Nullability) (pt : Proto.PType) :
    decTypedTyCore? (pt.setNull n) = decTypedTyCore? pt := by
  cases pt with
  | bool _ => cases n <;> rfl
  | i32 _ => cases n <;> rfl
  | i64 _ => cases n <;> rfl
  | string _ => cases n <;> rfl
  | list e _ => cases e.nullability <;> cases n <;> rfl

/-- The core law: the lowering's face reads back (the fragment's
    induction; the list arm rides the element's `required` nullability
    — the lowering writes it). -/
theorem decTypedTyCore?_of_toProtoType (t : Ty) (p : Proto.PType)
    (h : toProtoType t = .ok p) : decTypedTyCore? p = .ok t := by
  cases t with
  | bool => simp only [toProtoType] at h; cases h; simp [decTypedTyCore?]
  | i64 => simp only [toProtoType] at h; cases h; simp [decTypedTyCore?]
  | string => simp only [toProtoType] at h; cases h; simp [decTypedTyCore?]
  | list e =>
      simp only [toProtoType] at h
      cases he : toProtoType e with
      | error _ => rw [he] at h; simp at h
      | ok p' =>
          rw [he] at h
          simp only [Except.ok.injEq] at h
          subst h
          have hreq : p'.nullability = .required :=
            toProtoType_ok_required e p' he
          simp only [decTypedTyCore?, hreq]
          rw [decTypedTyCore?_of_toProtoType e p' he]
  | _ => simp [toProtoType] at h

/-- THE PER-COLUMN LAW: the wire type the lowering produced reads back
    to exactly the typed column's (type, nullability). The type round
    trip's base rung. -/
theorem decTypedColTy?_colType (c : Col) (pt : Proto.PType)
    (h : colType c = .ok pt) : decTypedColTy? pt = .ok (c.2.1, c.2.2) := by
  obtain ⟨nm, t, n⟩ := c
  simp only [colType] at h
  cases ht : toProtoType t with
  | error _ => rw [ht] at h; simp at h
  | ok p =>
      rw [ht] at h
      simp only [Except.ok.injEq] at h
      subst h
      show decTypedColTy? (withNullable n p) = _
      cases n with
      | false =>
          show decTypedColTy? (p.setNull .required) = _
          simp only [decTypedColTy?, decTypedTyCore?_setNull,
            decTypedTyCore?_of_toProtoType t p ht, PType.setNull_nullability]
      | true =>
          show decTypedColTy? (p.setNull .nullable) = _
          simp only [decTypedColTy?, decTypedTyCore?_setNull,
            decTypedTyCore?_of_toProtoType t p ht, PType.setNull_nullability]

/-! ## rung 2 — the literal payload → the GADT value -/

/-- The packaged literal: `(t, n, Value t)` flattened (the AnyExpr
    encoding discipline — the GADT's indices ride the package). -/
inductive AnyLit : Type where
  | mk (t : Ty) (n : Bool) (v : SchemaCore.Value t)

/-- The literal payload's read face. `i64` rides `Int64.ofInt` — the
    two's-complement face is total over `Int64.toInt` (core's
    `ofInt_toInt`). `i32` refuses (SS0001 — no `Value` face). -/
def decTypedLit? : Proto.LiteralType → Bool → Except Kit.Diag AnyLit
  | .bool b, n => .ok (AnyLit.mk .bool n (SchemaCore.Value.bool b))
  | .i64 w, n => .ok (AnyLit.mk .i64 n (SchemaCore.Value.i64 (Int64.ofInt w)))
  | .string s, n => .ok (AnyLit.mk .string n (SchemaCore.Value.string s))
  | .i32 _, _ => .error (ssDiag eSS0001 "typed-decode: the wire literal i32 has \
      no SchemaCore.Value face — the retarget's honest refusal, read back")

/-- THE LITERAL LAW: the payload the lowering produced reads back to
    exactly the typed value (the i64 face rides core's `ofInt_toInt`;
    the GADT's index discipline closes the rest by cases). -/
theorem decTypedLit?_toProtoLiteral (t : Ty) (v : SchemaCore.Value t) (n : Bool)
    (lt : Proto.LiteralType) (h : toProtoLiteral t v = .ok lt) :
    decTypedLit? lt n = .ok (AnyLit.mk t n v) := by
  cases v with
  | bool b => simp only [toProtoLiteral] at h; cases h; simp [decTypedLit?]
  | i64 w => simp only [toProtoLiteral] at h; cases h; simp [decTypedLit?, Int64.ofInt_toInt]
  | string s => simp only [toProtoLiteral] at h; cases h; simp [decTypedLit?]
  | _ => simp [toProtoLiteral] at h

/-! ## rung 3 — the expression ladder (the mutual Expr/Args face) -/

/-- The packaged argument spine: the rebuilt `Args` WITH its type index
    (the index is the data the call rung's signature needs). -/
inductive AnyArgs (s : Schema) : Type where
  | mk (ts : List (Ty × Bool)) (a : Args s ts)

/-- THE HASCOL CONSTRUCTOR (the field rung's proof face): the ordinal's
    lookup hit CONSTRUCTS the resolution evidence — the instance's
    `resolves` field is the hit equation itself, the `index` is the
    ordinal. A reference without a hit has no witness (SS0003). -/
def hasColAt : (s : Schema) → (i : Nat) → (c : Col) →
    Schema.get? s i = some c → HasCol s c.1 c.2.1 c.2.2
  | [], _, _, h => absurd h (by simp [Schema.get?])
  | _ :: _, 0, _, h => by
      simp only [Schema.get?] at h
      injection h with hc
      subst hc
      exact ⟨0, rfl⟩
  | _ :: tl, i + 1, c, h => by
      simp only [Schema.get?] at h
      exact { index := i + 1, resolves := h }

/-- The constructor's read-back: applied to a REAL resolution it IS
    that resolution (structure eta + the hit equation + proof
    irrelevance on the `resolves` field). -/
theorem hasColAt_self (s : Schema) (nm : String) (t : Ty) (n : Bool)
    (hcol : HasCol s nm t n) :
    hasColAt s hcol.index (nm, t, n) hcol.resolves = hcol := by
  cases s with
  | nil =>
      cases hcol with
      | mk _ res => simp [Schema.get?] at res
  | cons c tl =>
      cases hcol with
      | mk idx res =>
          cases idx with
          | zero =>
              simp only [Schema.get?] at res
              injection res with hc
              subst hc
              rfl
          | succ i =>
              rfl

/-- The field rung (named for its law): the ordinal's lookup hit buys
    the `hasColAt` resolution; the miss is the SS0003 refusal (the
    schema-mismatched reference). -/
def decTypedField? (s : Schema) (ref : Proto.FieldReference) :
    Except Kit.Diag (AnyExpr s) :=
  match hs : Schema.get? s ref.ordinal with
  | some c =>
      .ok (AnyExpr.mk c.2.1 c.2.2
        (Expr.field c.1 c.2.1 c.2.2 (hasColAt s ref.ordinal c hs)))
  | none =>
      .error (ssDiag eSS0003
        s!"typed-decode: the field reference's ordinal {ref.ordinal} is out of \
          range of the rel's schema of width {s.length} — the schema-mismatched \
          reference refuses (the by-name discipline's read face)")

/- The typed decode's argument spine: one wire expression per spine
   element, the (type, nullability) index COMPUTED from the decoded
   elements (the signature's arg list is the data, read off the wire —
   never checked against anything). The ladder is MUTUAL with the
   expression ladder (the spine's elements are subterms). -/
mutual
def decTypedArgs? (s : Schema) : List Proto.Expression → Except Kit.Diag (AnyArgs s)
  | [] => .ok (AnyArgs.mk [] .nil)
  | e :: rest =>
      match decTypedExpr? s e, decTypedArgs? s rest with
      | .ok (AnyExpr.mk t n ex), .ok (AnyArgs.mk ts spine) =>
          .ok (AnyArgs.mk ((t, n) :: ts) (.cons t n ex spine))
      | .error d, _ => .error d
      | _, .error d => .error d

/-- The typed decode's expression ladder: the wire expression → the
    typed term, packaged (`AnyExpr`). The field rung IS the by-name
    discipline's read face — the ordinal's lookup either buys the
    `HasCol` (the proof, constructed: `HasCol.at`) or refuses (SS0003).
    The call rung rebuilds the signature from the wire (name, the
    decoded args' index, the output type) — the well-typedness is the
    construction, never a check. -/
def decTypedExpr? (s : Schema) (e : Proto.Expression) : Except Kit.Diag (AnyExpr s) :=
  match e with
  | .literal l =>
      match decTypedLit? l.literalType l.nullable with
      | .ok (AnyLit.mk t n v) => .ok (AnyExpr.mk t n (Expr.literal n v))
      | .error d => .error d
  | .field ref => decTypedField? s ref
  | .scalarFunction nm args out =>
      match decTypedArgs? s args with
      | .ok (AnyArgs.mk ts spine) =>
          match decTypedColTy? out with
          | .ok (t, n) =>
              .ok (AnyExpr.mk t n
                (Expr.call { name := nm, args := ts, ret := t, retNullable := n }
                  spine))
          | .error d => .error d
      | .error d => .error d
end

/- THE FIELD RUNG's HIT LAW: the decode at a lookup HIT is the packaged
   field term carrying the CONSTRUCTED resolution (hasColAt) — the law
   names the shape so the expression law's field arm can rewrite
   without touching the dependent match's motive. -/
theorem decTypedField?_hit (s : Schema) (i : Nat) (c : Col)
    (hs : Schema.get? s i = some c) :
    decTypedField? s { ordinal := i } = .ok (AnyExpr.mk c.2.1 c.2.2
      (Expr.field c.1 c.2.1 c.2.2 (hasColAt s i c hs))) := by
  simp only [decTypedField?]
  split
  · rename_i c' h
    have hcc : some c' = some c := h.symm.trans hs
    injection hcc with h2
    subst h2
    rfl
  · rename_i h
    rw [hs] at h
    simp at h

/- THE EXPRESSION LAW (the ladder's rung theorem, as proof-carrying
   recursive defs over the mutual GADT — Typed.lean's bridge pattern,
   read direction): for every expression the LOWERING accepts, decode
   ∘ lower is the identity at the typed level. A docstring cannot
   precede a `mutual` block (the mechanics note). -/
mutual
  def decTypedExpr?_ok : {s : Schema} → {t : Ty} → {n : Bool} →
      (e : Expr s t n) → (p : Proto.Expression) → e.toProto = .ok p →
      decTypedExpr? s p = .ok (AnyExpr.mk t n e)
    | s, t, _, .literal n v, p, hp => by
        simp only [Expr.toProto] at hp
        cases hl : toProtoLiteral t v with
        | error _ => rw [hl] at hp; simp at hp
        | ok lt =>
            rw [hl] at hp
            simp only [Except.ok.injEq] at hp
            subst hp
            simp only [decTypedExpr?]
            rw [decTypedLit?_toProtoLiteral t v n lt hl]
    | s, _, _, .field nm t' n' hcol, p, hp => by
        simp only [Expr.toProto] at hp
        simp only [Except.ok.injEq] at hp
        subst hp
        simp only [decTypedExpr?]
        rw [decTypedField?_hit s hcol.index (nm, t', n') hcol.resolves]
        rw [hasColAt_self s nm t' n' hcol]
    | s, _, _, .call sig args, p, hp => by
        simp only [Expr.toProto] at hp
        cases ha : args.toProto with
        | error _ => rw [ha] at hp; simp at hp
        | ok ps =>
            rw [ha] at hp
            cases ho : toProtoType sig.ret with
            | error _ => rw [ho] at hp; simp at hp
            | ok out =>
                rw [ho] at hp
                simp only [Except.ok.injEq] at hp
                subst hp
                have hargs := decTypedArgs?_ok args ps ha
                have hcol := decTypedColTy?_colType ("", sig.ret, sig.retNullable)
                  (withNullable sig.retNullable out) (by
                    simp only [colType, ho])
                simp only [decTypedExpr?, hargs, hcol]

  def decTypedArgs?_ok : {s : Schema} → {ts : List (Ty × Bool)} →
      (a : Args s ts) → (ps : List Proto.Expression) → a.toProto = .ok ps →
      decTypedArgs? s ps = .ok (AnyArgs.mk ts a)
    | s, _, .nil, ps, hp => by
        simp only [Args.toProto] at hp
        simp only [Except.ok.injEq] at hp
        subst hp
        simp only [decTypedArgs?]
    | s, _, .cons t n e rest, ps, hp => by
        simp only [Args.toProto] at hp
        cases he : e.toProto with
        | error _ => rw [he] at hp; simp at hp
        | ok p =>
            rw [he] at hp
            cases hr : rest.toProto with
            | error _ => rw [hr] at hp; simp at hp
            | ok ps' =>
                rw [hr] at hp
                simp only [Except.ok.injEq] at hp
                subst hp
                have h1 := decTypedExpr?_ok e p he
                have h2 := decTypedArgs?_ok rest ps' hr
                simp only [decTypedArgs?, h1, h2]
end

/-! ## rung 4 — the read's base schema (the fields × names zip) -/

/-- The base schema's read face: the fields and the names zip
    positionally; a length disagreement refuses (SS0006 — the typed
    read's schema is ONE list, written as both faces). -/
def decTypedSchema? : List Proto.PType → List String → Except Kit.Diag Schema
  | [], [] => .ok []
  | pt :: pts, nm :: nms =>
      match decTypedColTy? pt with
      | .ok (t, n) =>
          match decTypedSchema? pts nms with
          | .ok s => .ok ((nm, t, n) :: s)
          | .error d => .error d
      | .error d => .error d
  | _, _ => .error (ssDiag eSS0006 "typed-decode: the read's base schema — \
      the wire's fields and names disagree in length (the typed read's \
      schema is ONE list, written as both faces)")

/-- THE SCHEMA LAW: the base schema the lowering wrote reads back to
    exactly itself (the per-column law + the walk's shape). -/
theorem decTypedSchema?_colsToProto (s : Schema) (pts : List Proto.PType)
    (h : colsToProto s = .ok pts) : decTypedSchema? pts s.names = .ok s := by
  induction s generalizing pts with
  | nil =>
      simp only [colsToProto, walkProto, Except.ok.injEq] at h
      subst h
      rfl
  | cons c tl ih =>
      simp only [colsToProto, walkProto] at h
      cases hc : colType c with
      | error _ => rw [hc] at h; simp at h
      | ok pt =>
          rw [hc] at h
          cases hw : walkProto colType tl with
          | error _ => rw [hw] at h; simp at h
          | ok pts' =>
              rw [hw] at h
              simp only [Except.ok.injEq] at h
              subst h
              have h1 := decTypedColTy?_colType c pt hc
              have h2 := ih _ hw
              simp only [Schema.names, decTypedSchema?, h1, h2]

/-! ## rung 5 — the rel ladder -/

/-- The packaged relation: `(inS, outS, Rel inS outS)` flattened (the
    AnyExpr/AnyLit encoding discipline — the GADT's indices ride the
    package; the decode's schemas are COMPUTED data). -/
inductive AnyRel : Type where
  | mk (inS outS : Schema) (r : Rel inS outS)


/-- The schema cast the set rung needs: the sides' decoded schemas
    agree (SS0005 otherwise) — the transport is the agreement's data
    face. Also serves the ENDO rungs (aggregate/sort/fetch: the typed
    layer's input is `Rel s s`, the GADT's shape, forced — SS0011
    otherwise) via `relCast r hin rfl`. -/
def relCast {a b : Schema} (r : Rel a b) {a' b' : Schema}
    (h1 : a = a') (h2 : b = b') : Rel a' b' := by
  subst h1
  subst h2
  exact r

/-- The grouping keys, positionally. -/
def decTypedExprs? (s : Schema) : List Proto.Expression →
    Except Kit.Diag (List (AnyExpr s))
  | [] => .ok []
  | e :: rest =>
      match decTypedExpr? s e, decTypedExprs? s rest with
      | .ok ae, .ok aes => .ok (ae :: aes)
      | .error d, _ => .error d
      | _, .error d => .error d

/-- The aggregate's measures, positionally: each wire measure is the
    invocation (a scalar-function expression over the LOOSE erased-arg
    list — the seed's named divergence); the signature is rebuilt with
    the decoded args' (type, nullability) index. -/
def decTypedMeasure? (s : Schema) (e : Proto.Expression) : Except Kit.Diag (Measure s) :=
  match e with
  | .scalarFunction nm args out =>
      match decTypedExprs? s args with
      | .ok aes =>
          match decTypedColTy? out with
          | .ok (t, n) =>
              .ok { sig := { name := nm, args := aes.map AnyExpr.tns, ret := t, retNullable := n }
                  , args := aes }
          | .error d => .error d
      | .error d => .error d
  | _ =>
      .error (ssDiag eSS0010 "typed-decode: the measure is not a scalar-function \
        invocation — the wire measure's shape IS the invocation (the seed's \
        named divergence)")

/-- The measures, positionally. -/
def decTypedMeasures? (s : Schema) : List Proto.Expression →
    Except Kit.Diag (List (Measure s))
  | [] => .ok []
  | e :: rest =>
      match decTypedMeasure? s e, decTypedMeasures? s rest with
      | .ok m, .ok ms => .ok (m :: ms)
      | .error d, _ => .error d
      | _, .error d => .error d

/-- The sort keys, positionally (any typed key — the ordering face is
    type-erased; the direction rides the wire field). -/
def decTypedSortKeys? (s : Schema) : List Proto.SortField →
    Except Kit.Diag (List (SortKey s))
  | [] => .ok []
  | k :: rest =>
      match decTypedExpr? s k.expr, decTypedSortKeys? s rest with
      | .ok ae, .ok ks => .ok ({ key := ae, direction := k.direction } :: ks)
      | .error d, _ => .error d
      | _, .error d => .error d

/-- The typed decode's rel ladder: the wire rel → the typed term,
    packaged. The input schema flows DOWN the recursion; each node's
    output schema is computed exactly as the typed layer's index
    computes it. The refinements the GADT forces are the refusals:
    a non-boolean condition (SS0004), a set whose sides disagree
    (SS0005). The project node refuses outright (SS0007 — the wire
    carries no output names; the typed project's computed schema is
    unrecoverable). -/
def decTypedRel? (r : Proto.Rel) : Except Kit.Diag AnyRel :=
  match r with
  | .read rt bs =>
      match rt with
      | .namedTable nms =>
          match nms with
          | [table] =>
              match bs with
              | some ns =>
                  match decTypedSchema? ns.fields ns.names with
                  | .ok sc => .ok (AnyRel.mk sc sc (.read table sc))
                  | .error d => .error d
              | none =>
                  .error (ssDiag eSS0006 "typed-decode: the read's base schema is \
                    ABSENT — the typed read carries its schema (the lowering \
                    writes the `some` face always)")
          | _ =>
              .error (ssDiag eSS0008 "typed-decode: the named-table path is not a \
                single name — the typed read writes exactly one (the seed's \
                named narrowing)")
  | .filter c input =>
      match decTypedRel? input with
      | .ok (AnyRel.mk inS s r) =>
          match decTypedExpr? s c with
          | .ok (AnyExpr.mk .bool n ce) => .ok (AnyRel.mk inS s (.filter r ce))
          | .ok _ =>
              .error (ssDiag eSS0004 "typed-decode: the filter's condition is not \
                boolean — the typed filter's cond is `Expr s .bool n` (the GADT's \
                refinement is the refusal)")
          | .error d => .error d
      | .error d => .error d
  | .project _ _ =>
      .error (ssDiag eSS0007 "typed-decode: the wire's project node carries no \
        output names — the typed project's computed schema (projectOut) is \
        unrecoverable; the project decode lands with the names-propagation \
        face (the named gap, never a fabricated name)")
  | .join jt left right c =>
      match decTypedRel? left with
      | .ok (AnyRel.mk sl sl' l) =>
          match decTypedRel? right with
          | .ok (AnyRel.mk sr sr' r) =>
              match decTypedExpr? (sl' ++ sr') c with
              | .ok (AnyExpr.mk .bool n ce) =>
                  .ok (AnyRel.mk (sl ++ sr) (sl' ++ sr') (.join l r ce jt))
              | .ok _ =>
                  .error (ssDiag eSS0004 "typed-decode: the join's condition is not \
                    boolean — the typed join's cond is `Expr _ .bool n`")
              | .error d => .error d
          | .error d => .error d
      | .error d => .error d
  | .aggregate gs ms input =>
      match decTypedRel? input with
      | .ok (AnyRel.mk inS s r) =>
          match decTypedExprs? s gs with
          | .ok aes =>
              match decTypedMeasures? s ms with
              | .ok mes =>
                  if hin : inS = s then
                    -- the aggregate's input is ENDO (the typed layer's
                    -- shape `Rel s s` — the GADT's, forced)
                    .ok (AnyRel.mk s (aggregateOut s aes mes)
                      (.aggregate (relCast r hin rfl) aes mes))
                  else
                    .error (ssDiag eSS0011 "typed-decode: the aggregate's input \
                      is not endo — the typed aggregate's input is `Rel s s` \
                      (the GADT's shape, forced)")
              | .error d => .error d
          | .error d => .error d
      | .error d => .error d
  | .sort ks input =>
      match decTypedRel? input with
      | .ok (AnyRel.mk inS s r) =>
          match decTypedSortKeys? s ks with
          | .ok keys =>
              if hin : inS = s then
                .ok (AnyRel.mk s s (.sort (relCast r hin rfl) keys))
              else
                .error (ssDiag eSS0011 "typed-decode: the sort's input is not \
                  endo — the typed sort's input is `Rel s s` (the GADT's shape, \
                  forced)")
          | .error d => .error d
      | .error d => .error d
  | .fetch limit offset input =>
      match decTypedRel? input with
      | .ok (AnyRel.mk inS s r) =>
          if hin : inS = s then
            .ok (AnyRel.mk s s (.fetch (relCast r hin rfl) limit offset))
          else
            .error (ssDiag eSS0011 "typed-decode: the fetch's input is not endo \
              — the typed fetch's input is `Rel s s` (the GADT's shape, forced)")
      | .error d => .error d
  | .set op left right =>
      match decTypedRel? left with
      | .ok (AnyRel.mk s1 s1' l) =>
          match decTypedRel? right with
          | .ok (AnyRel.mk s2 s2' r) =>
              if h1 : s2 = s1 then
                if h2 : s2' = s1' then
                  .ok (AnyRel.mk s1 s1' (.set op l (relCast r h1 h2)))
                else
                  .error (ssDiag eSS0005 "typed-decode: the set operation's sides \
                    disagree on the OUTPUT schema — the typed layer's same-schema \
                    discipline makes two the honest arity, and `Rel.set`'s type \
                    will not accept the disagreement")
              else
                  .error (ssDiag eSS0005 "typed-decode: the set operation's sides \
                    disagree on the INPUT schema — the typed layer's same-schema \
                    discipline makes two the honest arity, and `Rel.set`'s type \
                    will not accept the disagreement")
          | .error d => .error d
      | .error d => .error d

/-- The grouping walk's law: the keys the lowering wrote read back to
    exactly themselves (the lowering is Except-valued — the law is
    conditional on its success, the encode's fragment gate). -/
theorem decTypedExprs?_ok (s : Schema) (es : List (AnyExpr s))
    (ps : List Proto.Expression) (h : anyExprListToProto es = .ok ps) :
    decTypedExprs? s ps = .ok es := by
  induction es generalizing ps with
  | nil =>
      simp only [anyExprListToProto, walkProto, Except.ok.injEq] at h
      subst h
      rfl
  | cons ae tl ih =>
      cases ae with
      | mk t n e =>
          simp only [anyExprListToProto, walkProto, AnyExpr.toProto] at h
          cases he : e.toProto with
          | error _ => rw [he] at h; simp at h
          | ok p =>
              rw [he] at h
              cases htl : walkProto AnyExpr.toProto tl with
              | error _ => rw [htl] at h; simp at h
              | ok ps' =>
                  rw [htl] at h
                  simp only [Except.ok.injEq] at h
                  subst h
                  simp only [decTypedExprs?, decTypedExpr?_ok e p he,
                    ih _ htl, Except.ok.injEq]

/-- THE MEASURE LAW: a tied measure (the arity tie above) reads back to
    exactly itself. -/
theorem decTypedMeasure?_ok (s : Schema) (m : Measure s) (e : Proto.Expression)
    (hc : m.tied) (hm : measureToProto m = .ok e) :
    decTypedMeasure? s e = .ok m := by
  obtain ⟨sig, args⟩ := m
  have hc' : args.map AnyExpr.tns = sig.args := hc
  simp only [measureToProto] at hm
  cases hg : anyExprListToProto args with
  | error _ => rw [hg] at hm; simp at hm
  | ok ps =>
      rw [hg] at hm
      cases ho : toProtoType sig.ret with
      | error _ => rw [ho] at hm; simp at hm
      | ok out =>
          rw [ho] at hm
          simp only [Except.ok.injEq] at hm
          subst hm
          have hwalk : decTypedExprs? s ps = .ok args :=
            decTypedExprs?_ok s args _ hg
          have hcol := decTypedColTy?_colType ("", sig.ret, sig.retNullable)
            (withNullable sig.retNullable out) (by
              simp only [colType, ho])
          simp only [decTypedMeasure?, hwalk, hcol, hc']

/-- The measures' walk law (the tie per element). -/
theorem decTypedMeasures?_ok (s : Schema) (ms : List (Measure s))
    (ps : List Proto.Expression) (h : measureListToProto ms = .ok ps)
    (hall : ∀ m ∈ ms, m.tied) :
    decTypedMeasures? s ps = .ok ms := by
  induction ms generalizing ps with
  | nil =>
      simp only [measureListToProto, walkProto, Except.ok.injEq] at h
      subst h
      rfl
  | cons m tl ih =>
      have hmt : m.tied := hall m (List.mem_cons_self ..)
      simp only [measureListToProto, walkProto] at h
      cases hm : measureToProto m with
      | error _ => rw [hm] at h; simp at h
      | ok e =>
          rw [hm] at h
          cases htl : walkProto measureToProto tl with
          | error _ => rw [htl] at h; simp at h
          | ok ps' =>
              rw [htl] at h
              simp only [Except.ok.injEq] at h
              subst h
              have h2 := decTypedMeasure?_ok s m e hmt hm
              have h1 := ih _ htl (fun x hx => hall x (List.mem_cons_of_mem _ hx))
              simp only [decTypedMeasures?, h2, h1, Except.ok.injEq]

/-- The sort keys' walk law. -/
theorem decTypedSortKeys?_ok (s : Schema) (ks : List (SortKey s))
    (ps : List Proto.SortField) (h : sortKeyListToProto ks = .ok ps) :
    decTypedSortKeys? s ps = .ok ks := by
  induction ks generalizing ps with
  | nil =>
      simp only [sortKeyListToProto, walkProto, Except.ok.injEq] at h
      subst h
      rfl
  | cons k tl ih =>
      cases k with
      | mk ae d =>
          cases ae with
          | mk t n e =>
              simp only [sortKeyListToProto, walkProto, sortKeyToProto,
                AnyExpr.toProto] at h
              cases he : e.toProto with
              | error _ => rw [he] at h; simp at h
              | ok p =>
                  rw [he] at h
                  cases htl : walkProto sortKeyToProto tl with
                  | error _ => rw [htl] at h; simp at h
                  | ok ps' =>
                      rw [htl] at h
                      simp only [Except.ok.injEq] at h
                      subst h
                      simp only [decTypedSortKeys?, decTypedExpr?_ok e p he,
                        ih _ htl, Except.ok.injEq]

/-- THE REL LAW (the ladder's top rung): for every typed rel the
    lowering accepts and the decode's domain condition holds, decode ∘
    lower is the identity AT THE TYPED LEVEL — the wire law lifted over
    the typed face. -/
theorem decTypedRel?_ok : ∀ {inS outS : Schema} (rel : Rel inS outS) (p : Proto.Rel),
    rel.toProto = .ok p → rel.decodable →
    decTypedRel? p = .ok (AnyRel.mk inS outS rel) := by
  intro inS outS rel
  induction rel with
  | read table schema =>
      intro p hp _
      simp only [Rel.toProto] at hp
      cases hf : colsToProto schema with
      | error _ => rw [hf] at hp; simp at hp
      | ok fields =>
          rw [hf] at hp
          simp only [Except.ok.injEq] at hp
          subst hp
          have hs := decTypedSchema?_colsToProto schema fields hf
          simp only [decTypedRel?, hs, Except.ok.injEq]
  | filter input cond ih =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hc : cond.toProto with
          | error _ => rw [hc] at hp; simp at hp
          | ok c =>
              rw [hc] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hrel := ih i hi hd
              have hcond := decTypedExpr?_ok cond c hc
              simp only [decTypedRel?, hrel, hcond, Except.ok.injEq]
  | project input outs ih =>
      intro p _ hd
      exact absurd hd (by simp [Rel.decodable])
  | keep input w ih =>
      intro p hp _
      simp only [Rel.toProto] at hp
      simp at hp
  | join left right cond jt ihl ihr =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hl : left.toProto with
      | error _ => rw [hl] at hp; simp at hp
      | ok l =>
          rw [hl] at hp
          cases hr : right.toProto with
          | error _ => rw [hr] at hp; simp at hp
          | ok r =>
              rw [hr] at hp
              cases hc : cond.toProto with
              | error _ => rw [hc] at hp; simp at hp
              | ok c =>
                  rw [hc] at hp
                  simp only [Except.ok.injEq] at hp
                  subst hp
                  have h1 := ihl l hl hd.1
                  have h2 := ihr r hr hd.2
                  have h3 := decTypedExpr?_ok cond c hc
                  simp only [decTypedRel?, h1, h2, h3, Except.ok.injEq]
  | @aggregate s input grouping measures ih =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hg : anyExprListToProto grouping with
          | error _ => rw [hg] at hp; simp at hp
          | ok gs =>
              rw [hg] at hp
              cases hm : measureListToProto measures with
              | error _ => rw [hm] at hp; simp at hp
              | ok ms =>
                  rw [hm] at hp
                  simp only [Except.ok.injEq] at hp
                  subst hp
                  have h1 := ih i hi hd.2
                  have h2 : decTypedExprs? s gs = .ok grouping :=
                    decTypedExprs?_ok _ grouping _ hg
                  have h3 : decTypedMeasures? s ms = .ok measures :=
                    decTypedMeasures?_ok _ measures _ hm hd.1
                  simp only [decTypedRel?, h1, h2, h3, Except.ok.injEq]
                  rfl
  | @sort s input keys ih =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hk : sortKeyListToProto keys with
          | error _ => rw [hk] at hp; simp at hp
          | ok ks =>
              rw [hk] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have h1 := ih i hi hd
              have h2 : decTypedSortKeys? s ks = .ok keys :=
                decTypedSortKeys?_ok _ keys _ hk
              simp only [decTypedRel?, h1, h2, Except.ok.injEq]
              rfl
  | fetch input limit offset ih =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          simp only [Except.ok.injEq] at hp
          subst hp
          have h1 := ih i hi hd
          simp only [decTypedRel?, h1, Except.ok.injEq]
          rfl
  | set op left right ihl ihr =>
      intro p hp hd
      simp only [Rel.toProto] at hp
      cases hl : left.toProto with
      | error _ => rw [hl] at hp; simp at hp
      | ok l =>
          rw [hl] at hp
          cases hr : right.toProto with
          | error _ => rw [hr] at hp; simp at hp
          | ok r =>
              rw [hr] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have h1 := ihl l hl hd.1
              have h2 := ihr r hr hd.2
              simp only [decTypedRel?, h1, h2, Except.ok.injEq]
              rfl

/-! ## rung 6 — the plan face -/

/-- The typed plan's read face: EXACTLY one top-level relation, in the
    bare-rel arm (the typed lowering's `toPlan` shape); anything else
    refuses (SS0009). -/
def decTypedPlan? (plan : Proto.Plan) : Except Kit.Diag AnyRel :=
  match plan.relations with
  | [PlanRel.rel r] => decTypedRel? r
  | _ =>
      .error (ssDiag eSS0009 "typed-decode: the plan does not carry exactly one \
        top-level bare relation — the typed lowering's toPlan shape (the \
        multi-relation face ports with the plan-composition lane)")

/-- THE PLAN LAW: the typed plan face composes over `Rel.toPlan` —
    decode ∘ (toPlan's plan) is the identity at the typed level. -/
theorem decTypedPlan?_ok : ∀ {inS outS : Schema} (rel : Rel inS outS)
    (plan : Proto.Plan), rel.toPlan = .ok plan → rel.decodable →
    decTypedPlan? plan = .ok (AnyRel.mk inS outS rel) := by
  intro inS outS rel plan hp hd
  cases hp0 : rel.toProto with
  | error _ => rw [Rel.toPlan, hp0] at hp; simp at hp
  | ok p =>
      rw [Rel.toPlan, hp0] at hp
      simp only [Except.ok.injEq] at hp
      subst hp
      simp only [decTypedPlan?]
      exact decTypedRel?_ok rel p hp0 hd

end Substrait.Decode
