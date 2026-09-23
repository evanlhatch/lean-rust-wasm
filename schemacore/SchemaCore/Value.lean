/-
# SchemaCore.Value — the typed value universe over Ty + the evaluator

Owner: the SchemaCore agent (the macht tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §1 (Universe root: closed codes
+ TOTAL DENOTATION — the (a)→(b) bridge: a `Value t` can only hold
data of type `t`, so test vectors + validators come free); notes/v3/
06-lean-rules.md §2 (the GADT sibling rule: nested `List (Value t)`
inside an indexed inductive is kernel-forbidden — the list/map shapes
are their own SIBLING inductives in the mutual block).

Provenance: mined from legacy `SchemaLang/Ty.lean` (the `Value`/`VList`/
`VMap` GADT family + the sibling rule) — ported at the SLICE's universe
size (the four scalars + option/list/result/map/set/bounded; the legacy
f32/f64/bytes/tensor/ty arms stay out with their `Ty` arms). The
evaluator is the total denotation: `Value.eval : Value t → t.toType`
(no `TySem` — the slice's `Ty` is first-order; no `.ty` refs; the
legacy tree has no evaluator — this is fresh content over mined data).

Two GADT mechanics the legacy two-column pattern style already encodes
(re-derived here, noted so they are not re-paid):

- the DEPENDENT result type generalizes the implicit index into the
  match — the index column must be given (`| .set k, .set vl => …`);
- cross-ctor arms are impossible ONLY where the indices genuinely
  conflict (`Value.bool` vs `Value.none`); `none`/`some` and `ok`/`err`
  share an `.option`/`.result` head with DIFFERENT inner indices, so
  the cross arms are POSSIBLE values and carry `false`.

The map/set arms ride the `KeyTy.toType_toTy` coherence cast (a
variable key's `toTy.toType` does not REDUCE to `toType` — the
kernel needs the named transport, not a `rfl`).

BEq/ToString discipline: structural, mutual over the sibling family —
instance search cannot run on a variable type index, so `Value.beq`/
`Value.render` match the VALUE constructors (the index follows the
ctor). The laws: `beq_refl` (each sibling), proved once in the mutual
block — the lanes' comparison surface, never re-proved per lane.

The five questions: root = Universe (data — the denotation side of the
closed codes); carrier = the GADT itself (mismatched payload
unconstructible; the `Fin cap` payload makes cap-violating `bounded`
values unconstructible too); spine reading = a value fold (the
evaluator reads the universe into Lean's native types; later lanes
compose interpretations over it, 01 §6's per-primitive preservation);
ladder rung = the evaluator + beq reduce by `rfl`/`decide` over
concrete values (structural, kernel-visible — no wf opacity); gate
row = the axiom report + SchemaTests' pins/controls.

Core-only (imports SchemaCore.Ty only — the cone rule).
-/

import SchemaCore.Ty

namespace SchemaCore

/-! ## The typed value universe — the sibling family -/

mutual
/-- A value of type `t` — a mismatched payload is UNCONSTRUCTIBLE
    (the index rides the constructor). -/
inductive Value : Ty → Type where
  | bool : Bool → Value .bool
  | u64 : UInt64 → Value .u64
  | i64 : Int64 → Value .i64
  | string : String → Value .string
  | none : {t : Ty} → Value (.option t)
  | some : {t : Ty} → Value t → Value (.option t)
  | ok : {ok err : Ty} → Value ok → Value (.result ok err)
  | err : {ok err : Ty} → Value err → Value (.result ok err)
  /-- The list payload rides the SIBLING (a nested `List (Value t)`
      inside the GADT is kernel-forbidden — 06 §2). -/
  | list : {t : Ty} → VList t → Value (.list t)
  /-- The map payload: an INSERTION-ORDERED association list over the
      SCALAR key sub-universe (duplicate keys REPRESENTABLE — order is
      payload data; canonicalization is an emitter boundary's job). -/
  | map : {k : KeyTy} → {v : Ty} → VMap k v → Value (.map k v)
  /-- The set payload: an element list over the SCALAR sub-universe
      (uniqueness a documented invariant, the legacy discipline). -/
  | set : {k : KeyTy} → VList k.toTy → Value (.set k)
  /-- The bounded payload: the cap-violating value is unconstructible —
      the `Fin cap` index IS the well-formedness (no checker pass). -/
  | bounded : {cap : Nat} → Fin cap → Value (.bounded cap)

/-- The value-list sibling (the GADT sibling rule, 06 §2). -/
inductive VList : Ty → Type where
  | nil : {t : Ty} → VList t
  | cons : {t : Ty} → Value t → VList t → VList t

/-- The map-payload sibling (an association list, not a nested
    `List (Value k.toTy × Value v)` — kernel-forbidden under the GADT). -/
inductive VMap : KeyTy → Ty → Type where
  | nil : {k : KeyTy} → {v : Ty} → VMap k v
  | cons : {k : KeyTy} → {v : Ty} → Value k.toTy → Value v → VMap k v → VMap k v
end

/-! ## The evaluator — the total denotation -/

mutual
/-- THE EVALUATOR: the closed universe's total denotation — a value
    denotes its native Lean data (structural recursion, kernel-visible:
    concrete values reduce by `rfl`). -/
def Value.eval : (t : Ty) → Value t → t.toType
  | .bool, .bool b => b
  | .u64, .u64 n => n
  | .i64, .i64 n => n
  | .string, .string s => s
  | .option _, .none => none
  | .option _, .some v => some v.eval
  | .result _ _, .ok v => .inl v.eval
  | .result _ _, .err v => .inr v.eval
  | .list _, .list vl => vl.evalList
  | .map k v, .map vm =>
      show List (KeyTy.toType k × Ty.toType v) from
        KeyTy.toType_toTy k ▸ vm.evalMap
  | .set k, .set vl =>
      show List (KeyTy.toType k) from KeyTy.toType_toTy k ▸ vl.evalList
  | .bounded _, .bounded f => f

/-- The list sibling's denotation (the native list form — the wire
    shape; richer natives are an emitter boundary's rendering). -/
def VList.evalList : {t : Ty} → VList t → List t.toType
  | _, .nil => []
  | _, .cons v vs => v.eval :: vs.evalList

/-- The map sibling's denotation: the ASSOCIATION-LIST form over the
    key's `toTy`-routed reification (the `KeyTy.toType_toTy` coherence
    transports it to the map arm's target). -/
def VMap.evalMap : {k : KeyTy} → {v : Ty} → VMap k v →
    List (k.toTy.toType × v.toType)
  | _, _, .nil => []
  | _, _, .cons k v rest => (k.eval, v.eval) :: rest.evalMap
end

/-- The evaluator's coverage pin: every family member reduces. -/
example : Value.eval .bool (.bool true) = true := rfl
example : Value.eval .u64 (.u64 7) = (7 : UInt64) := rfl
example : Value.eval .i64 (.i64 (-3)) = (-3 : Int64) := rfl
example : Value.eval .string (.string "hi") = "hi" := rfl
example : Value.eval (.option .u64) .none = (none : Option UInt64) := rfl
example : Value.eval (.option .u64) (.some (.u64 2))
    = (some (2 : UInt64)) := rfl
example : Value.eval (.result .u64 .i64) (.ok (.u64 1))
    = Sum.inl (1 : UInt64) := rfl
example : Value.eval (.result .u64 .i64) (.err (.i64 1))
    = Sum.inr (1 : Int64) := rfl
example : Value.eval (.list .u64) (.list (.cons (.u64 1) .nil))
    = [(1 : UInt64)] := rfl
example : Value.eval (.map .string .u64)
    (.map (.cons (.string "a") (.u64 1) .nil))
    = [("a", (1 : UInt64))] := rfl
example : Value.eval (.set .string) (.set (.cons (.string "a") .nil))
    = ["a"] := rfl
example : Value.eval (.bounded 3) (.bounded ⟨2, by decide⟩)
    = (2 : Fin 3) := rfl

/-! ## The BEq discipline — structural, mutual, with the refl law -/

mutual
/-- Value equality at a fixed index — structural over the sibling
    family (instance search cannot run on a variable index, so the
    VALUE constructors carry the match; the legacy two-column pattern
    style). The `none`/`some` and `ok`/`err` cross arms are POSSIBLE
    values (same `.option`/`.result` head) — they carry `false`. -/
def Value.beq : (t : Ty) → Value t → Value t → Bool
  | .bool, .bool a, .bool b => a == b
  | .u64, .u64 a, .u64 b => a == b
  | .i64, .i64 a, .i64 b => a == b
  | .string, .string a, .string b => a == b
  | .option _, .none, .none => true
  | .option _, .none, .some _ => false
  | .option _, .some _, .none => false
  | .option _, .some a, .some b => Value.beq _ a b
  | .result _ _, .ok a, .ok b => Value.beq _ a b
  | .result _ _, .ok _, .err _ => false
  | .result _ _, .err _, .ok _ => false
  | .result _ _, .err a, .err b => Value.beq _ a b
  | .list _, .list a, .list b => VList.beq a b
  | .map _ _, .map a, .map b => VMap.beq a b
  | .set _, .set a, .set b => VList.beq a b
  | .bounded _, .bounded a, .bounded b => a.val == b.val

/-- The list sibling's equality (nil vs cons are ordinary distinct
    values of `VList t` — the cross arms are live). -/
def VList.beq : {t : Ty} → VList t → VList t → Bool
  | _, .nil, .nil => true
  | _, .nil, .cons _ _ => false
  | _, .cons _ _, .nil => false
  | _, .cons a as, .cons b bs => Value.beq _ a b && VList.beq as bs

/-- The map sibling's equality (pairwise, order-sensitive — order is
    payload data). -/
def VMap.beq : {k : KeyTy} → {v : Ty} → VMap k v → VMap k v → Bool
  | _, _, .nil, .nil => true
  | _, _, .nil, .cons _ _ _ => false
  | _, _, .cons _ _ _, .nil => false
  | _, _, .cons a b as, .cons c d bs => Value.beq _ a c && Value.beq _ b d && VMap.beq as bs
end

/-- The BEq instance (the lanes' comparison surface). -/
instance {t : Ty} : BEq (Value t) := ⟨Value.beq t⟩

mutual
/-- THE BEQ LAW: reflexivity — proved once over the sibling family,
    cited by every lane (never re-proved per lane, 01 §6). Equation
    style with the inner index carried explicitly — the recursion is
    STRUCTURAL over the sibling family (no measure, no wf opacity). -/
theorem Value.beq_refl : ∀ (t : Ty) (v : Value t), Value.beq t v v = true
  | .bool, .bool b => beq_self_eq_true b
  | .u64, .u64 n => beq_self_eq_true n
  | .i64, .i64 n => beq_self_eq_true n
  | .string, .string s => beq_self_eq_true s
  | .option _, .none => rfl
  | .option t, .some a => by
      simp only [Value.beq]; exact Value.beq_refl t a
  | .result ok _, .ok a => by
      simp only [Value.beq]; exact Value.beq_refl ok a
  | .result _ err, .err a => by
      simp only [Value.beq]; exact Value.beq_refl err a
  | .list _, .list vl => by
      simp only [Value.beq]; exact VList.beq_refl vl
  | .map _ _, .map vm => by
      simp only [Value.beq]; exact VMap.beq_refl vm
  | .set _, .set vl => by
      simp only [Value.beq]; exact VList.beq_refl vl
  | .bounded _, .bounded f => beq_self_eq_true f.val

theorem VList.beq_refl : ∀ {t : Ty} (v : VList t), VList.beq v v = true
  | _, .nil => rfl
  | _, .cons a as => by
      simp [VList.beq, Value.beq_refl]
      exact VList.beq_refl as

theorem VMap.beq_refl : ∀ {k : KeyTy} {v : Ty} (m : VMap k v),
    VMap.beq m m = true
  | _, _, .nil => rfl
  | _, _, .cons a b as => by
      simp [VMap.beq, Value.beq_refl]
      exact VMap.beq_refl as
end

/-! ## The rendering discipline -/

mutual
/-- The value's rendering (test pins + diagnostics; NOT byte-tied —
    the emitter's surface is `renderTy`/`renderWit`). -/
def Value.render : (t : Ty) → Value t → String
  | .bool, .bool b => toString b
  | .u64, .u64 n => toString n
  | .i64, .i64 n => toString n
  | .string, .string s => s!"\"{s}\""
  | .option _, .none => "none"
  | .option _, .some v => s!"some {Value.render _ v}"
  | .result _ _, .ok v => s!"ok {Value.render _ v}"
  | .result _ _, .err v => s!"err {Value.render _ v}"
  | .list _, .list vl => s!"[{vl.renderList}]"
  | .map _ _, .map vm => s!"map[{vm.renderMap}]"
  | .set _, .set vl => s!"[{vl.renderList}]"
  | .bounded _, .bounded f => toString f.val

def VList.renderList : {t : Ty} → VList t → String
  | _, .nil => ""
  | _, .cons v vs =>
      match vs with
      | .nil => Value.render _ v
      | _ => s!"{Value.render _ v}, {vs.renderList}"

def VMap.renderMap : {k : KeyTy} → {v : Ty} → VMap k v → String
  | _, _, .nil => ""
  | _, _, .cons k v rest =>
      match rest with
      | .nil => s!"{Value.render _ k}={Value.render _ v}"
      | _ => s!"{Value.render _ k}={Value.render _ v}, {rest.renderMap}"
end

/-- The ToString instance (the lanes' diagnostic surface). -/
instance {t : Ty} : ToString (Value t) := ⟨Value.render t⟩

end SchemaCore
