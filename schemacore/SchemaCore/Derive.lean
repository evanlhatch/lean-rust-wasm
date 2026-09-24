/- # SchemaCore.Derive — the GENERIC derivation layer over the description

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/05-codegen.md §3 (the deriving protocol:
derive each capability from the description via GENERIC definitions +
GENERIC theorems — the thin wrappers per record are one-line
specializations, never per-record proofs); notes/v3/15-patterns.md #2
(the append-form codec law) + #8 (the deriving protocol) + #6 (the
dual-reading tie); notes/v3/12-construction.md §1 (`deriving WireCodec`).

## What is generic here (and what is NOT)

EVERYTHING in this module is a structural fold over `Descr` (or over
the row layer's `List Field`), with its law proved ONCE:

- `boxVList` / `boxVMap` — the index-free sibling rebuilders (the
  match column is the list alone; a GADT matcher whose index is
  `k.toTy` — a function of the key parameter — never iota-reduces, so
  the rebuilders do NOT take the key as an index column).
- `mkValue` — the native→`Value` box (the row bridge's and the codec's
  shared leaf face). The list/set/map payloads rebuild the sibling
  GADTs via `boxVList`/`boxVMap` over an element `List.map`; the
  map/set KEY positions ride `keyValue` (the scalar table). Both
  round-trip laws against `Value.eval` land here: `eval_mkValue` by
  Ty-induction, and `mkValue_eval` by the EVAL-INJECTIVITY route
  (`valueEval_inj` — the evaluator is faithful, so box∘eval = id
  follows from eval∘box = id).
- `encNat` / `decNat?` — the NATIVE face of the ONE wire:
  `encNat t v = encVal t (mkValue t v)` BY CONSTRUCTION — no second
  byte format exists to drift; the record wire IS the value wire.
- `deriveEnc` / `deriveDec` (+ the product walk `encProdOf` /
  `decProdOf?`) — the record codec: fields encoded in schema order,
  each field's bytes the value codec's.
- `deriveCodec_correct` — THE generic theorem
  (`dec (enc d v ++ rest) = some (v, rest)`, proved once over the
  description structure) + `deriveDec_eq` (the exact-image inversion).
- `deriveCodec` — the wire grade as a `Kit.Codec` value over
  `Descr.Ty d`, policy = the exact image.
- `rowTyOf` / `toRowF` / `ofRowF` + `rowBridgeIso` — the row bridge,
  generic over the field list: BOTH round-trip laws + the ONE
  `Kit.Iso` (the consolidation every per-lane bridge needs — the
  `@[row_bridge]` shape, RowVals.lean's note).

The per-record surface is the META module's (`SchemaCore.DeriveMeta`):
thin wrappers (`Example.codec := (deriveCodec Example.descr)
.transportRight Example.tupleIso`), each citing these generics.

Core-only (imports SchemaCore.Codec + RowVals + Describe — the cone
rule; no Lean import — the elaboration-time mounts live in
DeriveMeta).

The five questions (notes/v3/01-core.md):
- root: the description universe's DERIVATION face (D19's "derive via
  generic definitions + generic theorems").
- carrier: the interpretations are Type-valued dependent folds over
  the closed `Descr`/field-list structures (wrong-shape data
  unrepresentable at the leaves).
- spine reading: the derivation stage — `Descr` → capability surface
  (codec, row bridge) — consumed by the per-record thin wrappers.
- ladder rung: structural folds, kernel-visible (concrete
  descriptions reduce by `rfl`); the laws are structural inductions
  citing the atom laws (pattern #2's composition).
- gate row: SchemaTests' derive suite (the generic-theorem citation
  pins + the wire-tie known answers + the negative controls) + the
  axiom report.
-/

import Kit.Derive.Evidence
import TestingKit.Lcg
import SchemaCore.Codec
import SchemaCore.RowVals
import SchemaCore.Describe

open Kit.Varint

namespace SchemaCore

/-! ## The scalar key box (the match-lambda table) -/

/-- The scalar sub-universe's box: native key → `Value k.toTy`. The
    match-LAMBDA form: the domain type is each ctor's own reification
    (a dependent two-column match on `(k, a)` refines the domain to
    the stuck `(KeyTy.toTy k).toType` spelling, which the variable-`k`
    positions cannot consume; this form stays at `k.toType`). -/
def keyValue (k : KeyTy) : k.toType → Value k.toTy :=
  match k with
  | .bool => fun b => .bool b
  | .u64 => fun n => .u64 n
  | .i64 => fun n => .i64 n
  | .string => fun s => .string s

/-- The scalar key box's denotation round trip (per-ctor `rfl`; the
    transport is `Value.eval`'s `k.toTy`-routed index — it reduces
    away per ctor). -/
theorem keyValue_eval (k : KeyTy) (a : k.toType) :
    cast (KeyTy.toType_toTy k) (Value.eval k.toTy (keyValue k a)) = a := by
  cases k <;> rfl

/-! ## The index-free sibling rebuilders -/

/-- The list sibling's rebuild. The match column is the LIST alone —
    a GADT matcher whose index is `k.toTy` (a function of the key
    parameter) never iota-reduces (the index's cross-ctor unification
    needs the toTy-injectivity, which the matcher does not use), so
    the rebuilders take the sibling with its OWN index. -/
def boxVList {t : Ty} : List (Value t) → VList t
  | [] => .nil
  | v :: vs => .cons v (boxVList vs)

/-- The map sibling's rebuild (the same single-column discipline). -/
def boxVMap {k : KeyTy} {v : Ty} : List (Value k.toTy × Value v) → VMap k v
  | [] => .nil
  | p :: ps => .cons p.1 p.2 (boxVMap ps)

example : boxVList (t := Ty.u64) [] = VList.nil := rfl
example : boxVList (t := Ty.u64) [Value.u64 1]
    = VList.cons (Value.u64 1) VList.nil := rfl
example : boxVMap (k := KeyTy.string) (v := Ty.u64) [(Value.string "a", Value.u64 1)]
    = VMap.cons (k := KeyTy.string) (v := Ty.u64)
      (Value.string "a") (Value.u64 1) VMap.nil := rfl

/-! ## The generic box — native data → `Value` -/

/-- THE BOX: the native reification's inverse — native data → the
    typed value universe. The leaf scalars are direct; the wrappers
    recurse; the list/set/map payloads rebuild the sibling GADTs via
    `boxVList`/`boxVMap` over an element `List.map` (every recursive
    occurrence sits at a strict type-subterm — the structural shape). -/
def mkValue : (t : Ty) → t.toType → Value t
  | .bool, b => .bool b
  | .u64, n => .u64 n
  | .i64, n => .i64 n
  | .string, s => .string s
  | .option a, v =>
      match v with
      | none => .none
      | some x => .some (mkValue a x)
  | .list a, xs => .list (boxVList (xs.map (fun x => mkValue a x)))
  | .result ok err, v =>
      match v with
      | .inl x => .ok (mkValue ok x)
      | .inr x => .err (mkValue err x)
  | .map k v, xs =>
      .map (boxVMap (xs.map (fun p => (keyValue k p.1, mkValue v p.2))))
  | .set k, xs => .set (boxVList (xs.map (keyValue k)))
  | .bounded _, f => .bounded f

/-- The box's coverage pins (the kernel sees the leaves reduce). -/
example : mkValue .u64 3 = .u64 3 := rfl
example : mkValue (.option .string) none = .none := rfl
example : mkValue (.bounded 5) ⟨2, by decide⟩ = .bounded ⟨2, by decide⟩ := rfl

/-! ## The evaluator's injectivity (the box's row-side law's engine) -/

/-- The scalar-key evaluator's injectivity (per-ctor). -/
theorem keyEval_inj (k : KeyTy) (x y : Value k.toTy)
    (h : Value.eval k.toTy x = Value.eval k.toTy y) : x = y := by
  cases k <;> cases x <;> cases y <;> simp only [Value.eval] at h <;> exact congrArg _ h

mutual
/-- THE EVALUATOR IS FAITHFUL: the denotation's injectivity at every
    index — `Value.eval t v = Value.eval t w → v = w`. The GADT-family
    mutual induction (all edges strict — the sibling payloads are
    subterms); the map case transports the map arm's `Eq.rec` via
    `cases` on `KeyTy.toType_toTy k` (the index equation's own
    proof — the substitution iota-reduces both transports). -/
theorem valueEval_inj : (t : Ty) → (v w : Value t) →
    Value.eval t v = Value.eval t w → v = w
  | .bool, .bool a, .bool b, h => by simp only [Value.eval] at h; exact congrArg _ h
  | .u64, .u64 a, .u64 b, h => by simp only [Value.eval] at h; exact congrArg _ h
  | .i64, .i64 a, .i64 b, h => by simp only [Value.eval] at h; exact congrArg _ h
  | .string, .string a, .string b, h => by simp only [Value.eval] at h; exact congrArg _ h
  | .option _, .none, .none, _ => rfl
  | .option a, .some x, .some y, h => by
      simp only [Value.eval, Option.some.injEq] at h
      exact congrArg _ (valueEval_inj a x y h)
  | .list a, .list vl₁, .list vl₂, h => by
      simp only [Value.eval] at h
      exact congrArg _ (vlistEval_inj vl₁ vl₂ h)
  | .result _ _, .ok x, .ok y, h => by
      simp only [Value.eval, Sum.inl.injEq] at h
      exact congrArg _ (valueEval_inj _ x y h)
  | .result _ _, .err x, .err y, h => by
      simp only [Value.eval, Sum.inr.injEq] at h
      exact congrArg _ (valueEval_inj _ x y h)
  | .map k v, .map m₁, .map m₂, h => by
      cases k <;>
        (rw [Value.eval.eq_10, Value.eval.eq_10] at h
         exact congrArg _ (vmapEval_inj m₁ m₂ h))
  | .set k, .set vl₁, .set vl₂, h => by
      cases k <;>
        (rw [Value.eval.eq_11, Value.eval.eq_11] at h
         exact congrArg _ (vlistEval_inj vl₁ vl₂ h))
  | .bounded _, .bounded f, .bounded g, h => by
      simp only [Value.eval] at h
      exact congrArg _ h

theorem vlistEval_inj : {t : Ty} → (vl₁ vl₂ : VList t) →
    vl₁.evalList = vl₂.evalList → vl₁ = vl₂
  | _, .nil, .nil, _ => rfl
  | _, .cons x vl₁, .cons y vl₂, h => by
      simp only [VList.evalList, List.cons.injEq] at h
      have hv := valueEval_inj _ x y h.1
      have hr := vlistEval_inj vl₁ vl₂ h.2
      rw [hv, hr]

theorem vmapEval_inj : {k : KeyTy} → {v : Ty} → (m₁ m₂ : VMap k v) →
    m₁.evalMap = m₂.evalMap → m₁ = m₂
  | _, _, .nil, .nil, _ => rfl
  | _, _, .nil, .cons _ _ _, h => by exact absurd h (by simp [VMap.evalMap])
  | _, _, .cons _ _ _, .nil, h => by exact absurd h (by simp [VMap.evalMap])
  | _, _, .cons x y m₁, .cons x' y' m₂, h => by
      simp only [VMap.evalMap, List.cons.injEq, Prod.mk.injEq] at h
      have hk := keyEval_inj _ x x' h.1.1
      have hv := valueEval_inj _ y y' h.1.2
      have hr := vmapEval_inj m₁ m₂ h.2
      rw [hk, hv, hr]
end

/-! ## The box's eval face -/

/-- The rebuild face's eval: `evalList (boxVList ys)` is the pointwise
    eval (a plain-list induction — no GADT walk). -/
theorem evalList_boxVList : ∀ (t : Ty) (ys : List (Value t)),
    (boxVList ys).evalList = ys.map (Value.eval t) := by
  intro t ys
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [boxVList, VList.evalList, List.map_cons, ih]

/-- The rebuild face's eval, map edition (the evalMap output is
    `k.toTy`-typed — no cast; the cast lives in `Value.eval`'s map
    arm alone). -/
theorem evalMap_boxVMap : ∀ (k : KeyTy) (v : Ty)
    (zs : List (Value k.toTy × Value v)),
    (boxVMap zs).evalMap
      = zs.map (fun p => (Value.eval k.toTy p.1, Value.eval v p.2)) := by
  intro k v zs
  induction zs with
  | nil => rfl
  | cons p zs ih => simp only [boxVMap, VMap.evalMap, List.map_cons, ih]

/-- LAW: box then eval is the identity — the row bridge's record-side
    law's leaf face (`ofRow ∘ toRow = id`). Ty-induction; the list/
    map/set arms are nested inductions over the NATIVE lists (the
    closure per cons cites the law at the field type), with the
    map/set transports discharged per key ctor (`cases k <;> ...`). -/
theorem eval_mkValue : ∀ (t : Ty) (v : t.toType), Value.eval t (mkValue t v) = v := by
  intro t
  induction t with
  | bool => intro v; cases v <;> rfl
  | u64 => intro v; cases v <;> rfl
  | i64 => intro v; cases v <;> rfl
  | string => intro v; cases v <;> rfl
  | option a ih =>
      intro v
      cases v with
      | none => rfl
      | some x => simp only [mkValue, Value.eval, ih x]
  | list a ih =>
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ihxs =>
          simp only [mkValue, Value.eval, List.map_cons, boxVList,
            VList.evalList, ih]
          exact congrArg (List.cons x) ihxs
  | result ok err ihok iherr =>
      intro v
      cases v with
      | inl x => simp only [mkValue, Value.eval, ihok x]
      | inr x => simp only [mkValue, Value.eval, iherr x]
  | map k v ih =>
      intro xs
      cases k <;>
      induction xs with
      | nil => rfl
      | cons p xs ihxs =>
          obtain ⟨a, b⟩ := p
          simp only [mkValue]
          simp only [Value.eval]
          simp only [KeyTy.toTy, boxVMap,
            VMap.evalMap, List.map_cons, keyValue, ih]
          simp only [mkValue, Value.eval] at ihxs
          exact congrArg (List.cons (a, b)) ihxs
  | set k =>
      intro xs
      cases k <;>
      induction xs with
      | nil => rfl
      | cons x xs ihxs =>
          simp only [mkValue]
          simp only [Value.eval]
          simp only [KeyTy.toTy, boxVList,
            VList.evalList, List.map_cons, keyValue]
          simp only [mkValue, Value.eval] at ihxs
          exact congrArg (List.cons x) ihxs
  | bounded _ => intro v; cases v; rfl

/-- LAW: eval then box is the identity — the row bridge's row-side
    law's leaf face (`toRow ∘ ofRow = id`). The evaluator's
    injectivity turns `eval ∘ box ∘ eval = eval` into box ∘ eval = id:
    `mkValue t (eval t v)` has the same denotation as `v`, hence IS
    `v`. -/
theorem mkValue_eval : ∀ (t : Ty) (v : Value t), mkValue t (Value.eval t v) = v := by
  intro t v
  exact valueEval_inj t _ v (eval_mkValue t (Value.eval t v))

/-! ## The native face of the ONE wire -/

/-- THE NATIVE FACE: `encNat t v = encVal t (mkValue t v)` BY
    CONSTRUCTION — the record codec's leaf arm rides the value codec's
    bytes (no second byte format exists to drift; the dual-reading tie
    is definitional, pattern #6). -/
def encNat (t : Ty) (v : t.toType) : List UInt8 := encVal t (mkValue t v)

/-- The native face's decoder: unbox the value codec's verdict. -/
def decNat? (t : Ty) (bs : List UInt8) : Option (t.toType × List UInt8) :=
  (decVal t bs).map fun p => (Value.eval t p.1, p.2)

/-- PATTERN #2 — the native face's append-form law (the value codec's
    master law + the box's round trip, composed). -/
theorem decNat?_encNat_append (t : Ty) (v : t.toType) (rest : List UInt8) :
    decNat? t (encNat t v ++ rest) = some (v, rest) := by
  show (decVal t (encVal t (mkValue t v) ++ rest)).map _ = _
  rw [decVal_encVal_append t (mkValue t v) rest]
  simp [eval_mkValue]

/-- The native face's exact-image inversion (the value codec's
    inversion + the box's round trip, composed). -/
theorem decNat?_eq : ∀ (t : Ty) (bs : List UInt8) (v : t.toType)
    (rest : List UInt8), decNat? t bs = some (v, rest) → bs = encNat t v ++ rest := by
  intro t bs v rest h
  simp only [decNat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, hv⟩ := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj hv
  subst h2
  rw [encVal_decVal_eq t bs w.1 w.2 hw, ← h1]
  simp only [encNat, mkValue_eval]

/-! ## The record codec — the generic definitions over `Descr` -/

mutual
/-- THE RECORD ENCODER (generic over the description, 05 §3 step 2):
    the fields encoded in schema order, each field's bytes the value
    codec's (`encNat` — the native face of the ONE wire). -/
def deriveEnc : (d : Descr) → Descr.Ty d → List UInt8
  | .prim t, v => encNat t v
  | .option d, v =>
      match v with
      | none => [0]
      | some x => 1 :: deriveEnc d x
  | .list d, xs => encList (deriveEnc d) xs
  | .product _ fs, v => encProdOf fs v

/-- The product walk (the field tuple's bytes: field, then the rest). -/
def encProdOf : (fs : List (String × Descr)) → prodTyOf fs → List UInt8
  | [], _ => []
  | (_, d) :: rest, (x, xs) => deriveEnc d x ++ encProdOf rest xs

/-- THE RECORD DECODER (generic): the inverse walk, append-form. -/
def deriveDec : (d : Descr) → List UInt8 → Option (Descr.Ty d × List UInt8)
  | .prim t, bs => decNat? t bs
  | .option d, bs =>
      match decByte? bs with
      | some (b0, r) =>
          if b0 = 0 then some (none, r)
          else if b0 = 1 then (deriveDec d r).map fun p => (some p.1, p.2)
          else none
      | none => none
  | .list d, bs =>
      match decVarNat? bs with
      | some (n, r) => decManyBind? (deriveDec d) n r
      | none => none
  | .product _ fs, bs => decProdOf? fs bs

/-- The product walk's decoder (the cons arm rides `Option.bind`/`map`
    — the STANDARD lemmas fire on them; a nested GADT-match's
    equation is matcher-opaque to the rewriter). -/
def decProdOf? : (fs : List (String × Descr)) → List UInt8 →
    Option (prodTyOf fs × List UInt8)
  | [], bs => some ((), bs)
  | (_, d) :: rest, bs =>
      (deriveDec d bs).bind fun p =>
        Option.map (fun q => ((p.1, q.1), q.2)) (decProdOf? rest p.2)
end

/-- The record codec's coverage pins (kernel-visible reduction). -/
example : deriveEnc (.product "p" [("x", .prim .u64)]) ((3 : UInt64), ())
    = [3] := rfl
example : deriveEnc (.prim .u64) (300 : UInt64) = [0xAC, 0x02] := rfl
example : deriveDec (.product "p" [("x", .prim .u64)]) [3]
    = some (((3 : UInt64), ()), []) := rfl
/-- The truncation control: a dangling continuation bit refuses. -/
example : deriveDec (.prim .u64) [0x80] = none := rfl

/-! ## THE GENERIC THEOREM — proved ONCE over the description -/

mutual
/-- THE APPEND-FORM LAW over the description (15-patterns #2 at the
    record level): every description's every value decodes from its
    encoding plus ANY suffix, exactly. THE generic theorem the
    per-record thin wrappers cite (`Example.codec := (deriveCodec
    Example.descr).transportRight Example.tupleIso` — the wrapper's
    law is the Kit.Codec field, whose proof routes here). -/
theorem deriveCodec_correct : ∀ (d : Descr) (v : Descr.Ty d) (rest : List UInt8),
    deriveDec d (deriveEnc d v ++ rest) = some (v, rest)
  | .prim t, v, rest => decNat?_encNat_append t v rest
  | .option d, v, rest => by
      cases v with
      | none => simp [deriveEnc, deriveDec, decByte?_cons]
      | some x =>
          simp only [deriveEnc, deriveDec, decByte?_cons, List.cons_append,
            if_neg (by decide : ¬ ((1 : UInt8) = 0))]
          rw [deriveCodec_correct d x rest]
          simp
  | .list d, v, rest => by
      cases v with
      | nil =>
          simp [deriveEnc, deriveDec, encList, decVarNat?_encVarNat_append,
            decManyBind?]
          rfl
      | cons x xs =>
          simp only [deriveEnc, deriveDec, encList]
          rw [List.append_assoc, decVarNat?_encVarNat_append]
          simp only [decManyBind?_enc_append (deriveDec d) (deriveEnc d)
            (deriveCodec_correct d) (x :: xs) rest]
          rfl
  | .product _ fs, v, rest => decProdOf?_encProdOf_append fs v rest

/-- The product walk's append-form law (the composition discipline —
    each field rides the head law, the tail the induction). -/
theorem decProdOf?_encProdOf_append : ∀ (fs : List (String × Descr))
    (v : prodTyOf fs) (rest : List UInt8),
    decProdOf? fs (encProdOf fs v ++ rest) = some (v, rest)
  | [], v, rest => by cases v; simp [decProdOf?, encProdOf]
  | (_, d) :: fs, (x, xs), rest => by
      simp only [encProdOf, List.append_assoc]
      simp only [decProdOf?]
      rw [deriveCodec_correct d x (encProdOf fs xs ++ rest)]
      simp only [Option.bind_some]
      rw [decProdOf?_encProdOf_append fs xs rest]
      rfl
end

mutual
/-- The record decoder's exact-image inversion: a successful decode's
    input is exactly an encoding plus a suffix (the accepted-byte
    policy's content at the record level). -/
theorem deriveDec_eq : ∀ (d : Descr) (bs : List UInt8) (v : Descr.Ty d)
    (rest : List UInt8), deriveDec d bs = some (v, rest) →
    bs = deriveEnc d v ++ rest
  | .prim t, bs, v, rest, h => decNat?_eq t bs v rest h
  | .option d, bs, v, rest, h => by
      simp only [deriveDec] at h
      cases hd : decByte? bs with
      | none => rw [hd] at h; simp at h
      | some p =>
          obtain ⟨b0, r⟩ := p
          rw [hd] at h
          simp only at h
          by_cases hb0 : b0 = 0
          · rw [if_pos hb0] at h
            obtain ⟨rfl, rfl⟩ := Option.some.inj h
            rw [decByte?_eq bs b0 _ hd]
            simp [deriveEnc, hb0]
          · by_cases hb1 : b0 = 1
            · rw [if_neg hb0, if_pos hb1] at h
              obtain ⟨w, hw, hv⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
              rw [decByte?_eq bs b0 _ hd, deriveDec_eq d r w.1 w.2 hw]
              simp [deriveEnc, hb1]
            · rw [if_neg hb0, if_neg hb1] at h
              simp at h
  | .list d, bs, v, rest, h => by
      simp only [deriveDec] at h
      cases hd : decVarNat? bs with
      | none => rw [hd] at h; simp at h
      | some q =>
          obtain ⟨n, r⟩ := q
          rw [hd] at h
          simp only at h
          cases hd2 : decManyBind? (deriveDec d) n r with
          | none => rw [hd2] at h; simp at h
          | some q2 =>
              obtain ⟨xs, r'⟩ := q2
              rw [hd2] at h
              obtain ⟨rfl, rfl⟩ := Option.some.inj h
              obtain ⟨hlen, hbs⟩ := decManyBind?_eq (deriveEnc d)
                (deriveDec_eq d) n r v rest hd2
              rw [decVarNat?_encVarNat_eq bs n r hd, hbs]
              simp [deriveEnc, encList, ← hlen]
  | .product _ fs, bs, v, rest, h => decProdOf?_eq fs bs v rest h

/-- The product walk's inversion (composes the head law + the tail
    induction). -/
theorem decProdOf?_eq : ∀ (fs : List (String × Descr)) (bs : List UInt8)
    (v : prodTyOf fs) (rest : List UInt8),
    decProdOf? fs bs = some (v, rest) → bs = encProdOf fs v ++ rest
  | [], bs, _, rest, h => by
      simp only [decProdOf?, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | (_, d) :: fs, bs, (x, xs), rest, h => by
      simp only [decProdOf?] at h
      cases hd : deriveDec d bs with
      | none =>
          rw [hd] at h
          simp only [Option.bind_none] at h
          exact absurd h (by simp)
      | some q =>
          obtain ⟨x', r1⟩ := q
          rw [hd] at h
          simp only [Option.bind_some] at h
          cases hd2 : decProdOf? fs r1 with
          | none => rw [hd2] at h; simp at h
          | some q2 =>
              obtain ⟨xs', r2⟩ := q2
              rw [hd2] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              rw [deriveDec_eq d bs x' r1 hd, decProdOf?_eq fs r1 xs' r2 hd2]
              simp [encProdOf]
end

/-! ## THE WIRE GRADE — the record codec as a `Kit.Codec` value -/

/-- THE record codec of description `d` as a `Kit.Codec` (01-core §4's
    wire grade): encode/decode + the accepted-byte policy as the EXACT
    IMAGE of the encoder. Both law fields cite the generic theorems —
    `deriveCodec_correct` + `deriveDec_eq` — never a re-proof. -/
def deriveCodec (d : Descr) : Kit.Codec (List UInt8) (Descr.Ty d) where
  encode := deriveEnc d
  decode bs := (deriveDec d bs).map (·.1)
  policy bs := ∃ v rest, bs = deriveEnc d v ++ rest
  decode_encode v := by
    have h := deriveCodec_correct d v []
    rw [List.append_nil] at h
    simp [h]
  decode_some_policy bs v h := by
    cases hd : deriveDec d bs with
    | none => rw [hd] at h; simp at h
    | some p =>
        rw [hd] at h
        simp only [Option.map_some] at h
        have hv : p.1 = v := Option.some.inj h
        subst hv
        exact ⟨p.1, p.2, deriveDec_eq d bs p.1 p.2 hd⟩

/-! ## The evidence entourage's sweep face (16-surface §3, kind 3) -/

/-- The sweep's verdict (ctors, never strings — 04 §6). `pass n` =
    every one of the n drawn instances round-tripped AND discriminated;
    `failAt` names the instance + the replay seed (the LCG discipline:
    byte-identical replay from the seed). The verdict is DATA — the
    tier stays `oracleSwept`, never `provedAtElab`
    (Kit.Derive.Evidence.EvidenceKind.tier_ne_provedAtElab). -/
inductive SweepVerdict where
  | pass (n : Nat)
  | failAt (i : Nat) (seed : UInt64)
deriving Repr, BEq, Inhabited

/-- One char from a small alphabet (the drawer's leaf). -/
def drawChar (t : TestingKit.Tape) : Char × TestingKit.Tape :=
  let p := t.below 4
  ((['a', 'b', 'c', 'd'])[p.1]!, p.2)

/-- The structural repeat: draw `n` values. -/
def drawMany : Nat → (TestingKit.Tape → α × TestingKit.Tape) → TestingKit.Tape → List α × TestingKit.Tape
  | 0, _, t => ([], t)
  | n + 1, draw, t =>
      let (x, t) := draw t
      let (xs, t) := drawMany n draw t
      (x :: xs, t)

/-- The structural repeat over an OPTIONAL drawer (`none` propagates —
    the loud gap, never a silent shorter list). -/
def drawManyO : Nat → (TestingKit.Tape → Option (α × TestingKit.Tape)) → TestingKit.Tape →
    Option (List α × TestingKit.Tape)
  | 0, _, t => some ([], t)
  | n + 1, draw, t =>
      (draw t).bind fun p =>
        (drawManyO n draw p.2).map fun q => (p.1 :: q.1, q.2)

/-- A short string (length < 4) over the small alphabet. -/
def drawString (t : TestingKit.Tape) : String × TestingKit.Tape :=
  let p := t.below 4
  let (cs, t) := drawMany p.1 drawChar p.2
  (String.ofList cs, t)

/-- The key drawer (the scalar sub-universe's native values — the map
    and set positions' leaves). -/
def drawKey : (k : KeyTy) → TestingKit.Tape → k.toType × TestingKit.Tape
  | .bool, t => let p := t.below 2; ((p.1 % 2 == 1), p.2)
  | .u64, t => let p := t.below 16; (UInt64.ofNat p.1, p.2)
  | .i64, t => let p := t.below 16; (Int64.ofInt (p.1 - 8), p.2)
  | .string, t => drawString t

/-- THE INSTANCE DRAWER (the sweep's source): a native value of the
    boundary universe's type, LCG-drawn (pattern #14 — same seed,
    byte-identical replay). `none` = the drawer's LOUD gap (a type with
    no value — `bounded 0`); the sweep reports `failAt` for it, never a
    silent pass. -/
def drawTy : (t : Ty) → TestingKit.Tape → Option (t.toType × TestingKit.Tape)
  | .bool, t => let p := t.below 2; some ((p.1 % 2 == 1), p.2)
  | .u64, t => let p := t.below 16; some (UInt64.ofNat p.1, p.2)
  | .i64, t => let p := t.below 16; some (Int64.ofInt (p.1 - 8), p.2)
  | .string, t => some (drawString t)
  | .option a, t =>
      let b := t.byte
      if b.1 % 2 == 0 then some (none, b.2)
      else (drawTy a b.2).map fun p => (some p.1, p.2)
  | .list a, t =>
      let p := t.below 4
      drawManyO p.1 (drawTy a) p.2
  | .result ok err, t =>
      let b := t.byte
      if b.1 % 2 == 0 then
        (drawTy ok b.2).map fun p => (Sum.inl p.1, p.2)
      else
        (drawTy err b.2).map fun p => (Sum.inr p.1, p.2)
  | .map k v, t =>
      let p := t.below 4
      drawManyO p.1
        (fun tt => Option.bind (some (drawKey k tt)) fun kp =>
          Option.map (fun vp => ((kp.1, vp.1), vp.2)) (drawTy v kp.2)) p.2
  | .set k, t =>
      let p := t.below 4
      drawManyO p.1 (fun tt => some (drawKey k tt)) p.2
  | .bounded cap, t =>
      match cap with
      | 0 => none
      | cap + 1 =>
          let p := t.below (UInt64.ofNat (cap + 1))
          some (⟨p.1 % (cap + 1), Nat.mod_lt p.1 (Nat.succ_pos cap)⟩, p.2)

-- drawDescr and drawProdOf are MUTUAL (the product arm draws fields,
-- each field may be a product); both are STRUCTURAL — drawDescr over
-- the description, drawProdOf over the field list.
def drawDescr : (d : Descr) → TestingKit.Tape → Option (Descr.Ty d × TestingKit.Tape)
  | .prim t, tape => drawTy t tape
  | .option d, tape => (drawDescr d tape).map fun p => (some p.1, p.2)
  | .list d, tape =>
      let p := tape.below 4
      drawManyO p.1 (drawDescr d) p.2
  | .product _ fs, tape => drawProdOf fs tape
where
  /-- The product's drawer: one field value each, in schema order (the
      nested-tuple denotation). -/
  drawProdOf : (fsL : List (String × Descr)) → TestingKit.Tape →
      Option (prodTyOf fsL × TestingKit.Tape)
    | [], tape => some ((), tape)
    | (_, d) :: rest, tape =>
        (drawDescr d tape).bind fun p =>
          (drawProdOf rest p.2).map fun q => ((p.1, q.1), q.2)

/-- THE ENCODER'S INJECTIVITY (the sweep's byte-equality route's
    soundness): equal encodings are equal values — the append-form law
    pins each value through its bytes (`decode (encode v ++ []) = some
    (v, [])`), so the two `some`s agree. -/
theorem deriveEnc_inj (d : Descr) (v w : Descr.Ty d)
    (h : deriveEnc d v = deriveEnc d w) : v = w := by
  have h1 : deriveDec d (deriveEnc d v ++ []) = some (v, []) :=
    deriveCodec_correct d v []
  rw [h] at h1
  have h2 : deriveDec d (deriveEnc d w ++ []) = some (w, []) :=
    deriveCodec_correct d w []
  rw [h1] at h2
  exact Prod.mk.inj (Option.some.inj h2) |>.1

/-- THE SWEEP'S ENGINE: instance `i` draws from the tape pinned to
    seed `s`; the round trip must return the drawn value (equality via
    the RE-ENCODING — `deriveEnc_inj` makes the byte comparison EXACT,
    no `BEq` needed on the record), and the TRUNCATED encoding must not
    decode back to the same value (the mechanical truncation
    discrimination — the exact-image inversion: a decode of a strict
    prefix cannot return the same value). A failure names the instance
    + the replay seed; the LCG steps between instances. -/
def sweepStep {B : Type} (codec : Kit.Codec (List UInt8) B)
    (enc : B → List UInt8) (draw : TestingKit.Tape → Option (B × TestingKit.Tape)) (width : Nat) :
    Nat → UInt64 → SweepVerdict
  | 0, _ => .pass width
  | remaining + 1, s =>
      match draw (TestingKit.Tape.ofSeed s) with
      | none => .failAt (width - remaining - 1) s
      | some (v, _) =>
          match codec.decode (codec.encode v) with
          | none => .failAt (width - remaining - 1) s
          | some w =>
              if !(enc w == enc v) then .failAt (width - remaining - 1) s
              else
                match codec.decode ((codec.encode v).dropLast) with
                | some w2 =>
                    if enc w2 == enc v then .failAt (width - remaining - 1) s
                    else sweepStep codec enc draw width remaining (TestingKit.lcg s)
                | none => sweepStep codec enc draw width remaining (TestingKit.lcg s)

/-- THE LCG SWEEP (16-surface §3 kind 3's face): `width` instances from
    the pinned seed, the round trip + the truncation discrimination per
    instance. THE TIER HONESTY: the verdict is DATA — the sweep attests
    `oracleSwept`, never `provedAtElab`; the PROOF side of the claim is
    the generic theorem the thin wrapper cites (the entourage never
    confuses the two tiers — Evidence.tier_ne_provedAtElab). -/
def runCodecSweep {B : Type} (codec : Kit.Codec (List UInt8) B)
    (enc : B → List UInt8) (draw : TestingKit.Tape → Option (B × TestingKit.Tape))
    (width : Nat) (seed : UInt64) : SweepVerdict :=
  sweepStep codec enc draw width width seed

/-- The mechanical TRUNCATION probe (the codec control's content): a
    drawn value's truncated encoding must NOT decode back to the same
    value (byte-exact via the re-encoding). `none` (nothing drawn)
    counts as discriminating — the drawer's gap is the sweep's
    `failAt`, not this probe's. -/
def truncDiscriminates {B : Type} (codec : Kit.Codec (List UInt8) B)
    (enc : B → List UInt8) (v? : Option B) : Bool :=
  match v? with
  | none => true
  | some v =>
      match codec.decode ((codec.encode v).dropLast) with
      | none => true
      | some w => !(enc w == enc v)

/-- The mechanical EMPTY-TAPE probe: a description whose encodings are
    nonempty must refuse the empty tape (the exact-image inversion's
    face: a successful decode's input is an encoding plus a suffix, and
    the encoding is longer than empty). -/
def emptyRefused (d : Descr) : Bool :=
  match deriveDec d [] with
  | none => true
  | some _ => false

-- The mechanical BAD-TAG probe: an option-shaped description refuses
-- the unknown tag byte (2 — the tags are 0 and 1). The probe DESCENDS
-- (a record's option FIELD is where the tag byte lives); the mutual
-- pair is structural, and a description with no option anywhere
-- trivially passes (the control does not apply).
mutual
def badTagList : List (String × Descr) → Bool
  | [] => true
  | (_, d) :: rest => badTagRefused d && badTagList rest

def badTagRefused (d : Descr) : Bool :=
  match d with
  | .option _ =>
      match deriveDec d [2] with
      | none => true
      | some _ => false
  | .list d => badTagRefused d
  | .product _ fs => badTagList fs
  | _ => true
end

-- the mutual pairs are structural (Descr ⇄ its field list)
mutual
def encNonemptyList : List (String × Descr) → Bool
  | [] => false
  | (_, d) :: rest => encNonempty d || encNonemptyList rest

def encNonempty : Descr → Bool
  | .prim _ => true
  | .option _ => true
  | .list _ => true
  | .product _ fs => encNonemptyList fs
end

mutual
def hasOptionList : List (String × Descr) → Bool
  | [] => false
  | (_, d) :: rest => hasOption d || hasOptionList rest

def hasOption : Descr → Bool
  | .prim _ => false
  | .option _ => true
  | .list d => hasOption d
  | .product _ fs => hasOptionList fs
end

/-! ## The row bridge — generic over the field list -/

/-- The row shape's native tuple: one `f.ty.toType` per field, in
    schema order, `Unit`-terminated (the canonical row shape —
    Describe.lean's product denotation over the registry's fields). -/
def rowTyOf : List Field → Type
  | [] => Unit
  | f :: fs => f.ty.toType × rowTyOf fs

/-- Native → row (one `.cons` per field, boxed by the generic `mkValue`). -/
def toRowF : (fs : List Field) → rowTyOf fs → RowVals fs
  | [], _ => .nil
  | f :: fs, (x, xs) => .cons (mkValue f.ty x) (toRowF fs xs)

/-- Row → native (one `.cons` level per field, unboxed by the total
    evaluator — the row side is TOTAL because `RowVals` admits only
    well-formed rows). -/
def ofRowF : (fs : List Field) → RowVals fs → rowTyOf fs
  | [], .nil => ()
  | f :: fs, .cons v vs => (Value.eval f.ty v, ofRowF fs vs)

/-- LAW: `ofRowF fs (toRowF fs v) = v` — the record side (the box's
    round trip, per field, composed over the field list). -/
theorem ofRowF_toRowF : ∀ (fs : List Field) (v : rowTyOf fs),
    ofRowF fs (toRowF fs v) = v := by
  intro fs
  induction fs with
  | nil => intro v; cases v; rfl
  | cons f fs ih =>
      intro v
      obtain ⟨x, xs⟩ := v
      show (Value.eval f.ty (mkValue f.ty x), ofRowF fs (toRowF fs xs)) = (x, xs)
      rw [eval_mkValue, ih xs]

/-- LAW: `toRowF fs (ofRowF fs row) = row` — the row side (the box's
    other round trip, per field, composed over the field list). -/
theorem toRowF_ofRowF : ∀ (fs : List Field) (row : RowVals fs),
    toRowF fs (ofRowF fs row) = row := by
  intro fs
  induction fs with
  | nil => intro row; cases row; rfl
  | cons f fs ih =>
      intro row
      cases row with
      | cons v vs =>
          show RowVals.cons (mkValue f.ty (Value.eval f.ty v))
            (toRowF fs (ofRowF fs vs)) = .cons v vs
          rw [mkValue_eval, ih vs]

/-- THE ROW BRIDGE as a `Kit.Iso` value — both round-trip laws in the
    type (the correspondence as data, 15-patterns #11). The per-record
    row Iso composes THIS with the record's ctor↔tuple `Kit.Iso`
    (`Kit.Iso.trans` — both proved once in the kit). -/
def rowBridgeIso (fs : List Field) : Kit.Iso (rowTyOf fs) (RowVals fs) where
  to := toRowF fs
  inv := ofRowF fs
  to_inv := toRowF_ofRowF fs
  inv_to := ofRowF_toRowF fs

end SchemaCore
