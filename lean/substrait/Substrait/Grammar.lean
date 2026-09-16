/-
# Substrait.Grammar — the type-language grammar as DATA, not code

## The hand-rolled seam this removes

The substrait type text grammar had THREE hand-rolled consumers that could
drift against each other:

1. `Emit/Text.lean`'s `typeTextBase` — a hardcoded match printing each type's
   prefix (`"boolean"`, `"i8"`, …).
2. `Decode.lean`'s `parseType` — a hardcoded 14-branch if-chain matching those
   same prefixes and reconstructing the type.
3. The inversion proofs — each re-walking the if-chain.

This module makes the grammar **a table**. The emitter and the parser both
read the table, so they agree by construction; the round-trip proof then
quantifies over the table rather than over hardcoded cases.

## The shape

The scalar type constructors (bool, i8, …, binary — the prefix-only ones) are
a pure prefix ↔ constructor bijection: `scalarGrammar` is that table. The
parameterized constructors (decimal, list, map, struct) have a sub-grammar
(their arguments); they get a prefix entry too but their argument-parsing
stays as code (it recurses into `parseType`, which the table drives for the
scalar leaves).

`ScalarCtor` is the closed enumeration of the prefix-only constructors —
the thing that grows when substrait adds a type. Add a constructor here, one
row in `scalarGrammar`, and both directions follow.

W5.3 phase 2a extends the same pattern to the REL grammar's name tokens
(join types, set ops, sort directions) and the literal-type names: one table
per family below, emitter renderer and decoder parser both derived from it.
-/

import Substrait.Proto.Type
import Substrait.Proto.Rel

namespace Substrait.Grammar

open Substrait.Proto

/-- The prefix-only (scalar) type constructors: the closed set the grammar
    table enumerates. Growing substrait's scalar catalogue = adding a ctor
    here + a row in `scalarGrammar`. -/
inductive ScalarCtor where
  | bool | i8 | i16 | i32 | i64 | fp32 | fp64 | string | binary
deriving Repr, BEq, DecidableEq, Inhabited

/-- Build the proto type for a scalar ctor at a nullability. -/
def ScalarCtor.toPType : ScalarCtor → Proto.Nullability → Proto.PType
  | .bool, n => .bool n
  | .i8, n => .i8 n
  | .i16, n => .i16 n
  | .i32, n => .i32 n
  | .i64, n => .i64 n
  | .fp32, n => .fp32 n
  | .fp64, n => .fp64 n
  | .string, n => .string n
  | .binary, n => .binary n

/-- Recover the scalar ctor from a proto type, if it is one (the
    parameterized ctors — decimal/list/map/struct/userDefined — are not
    scalars). -/
def ScalarCtor.ofPType : Proto.PType → Option ScalarCtor
  | .bool _ => some .bool
  | .i8 _ => some .i8
  | .i16 _ => some .i16
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .fp32 _ => some .fp32
  | .fp64 _ => some .fp64
  | .string _ => some .string
  | .binary _ => some .binary
  | _ => none

/-- ofPType ∘ toPType = some: every scalar ctor round-trips through its type. -/
theorem ScalarCtor.ofPType_toPType (c : ScalarCtor) (n : Proto.Nullability) :
    ScalarCtor.ofPType (c.toPType n) = some c := by
  cases c <;> rfl

/-- toPType ∘ ofPType = id on the type (the nullability is preserved). -/
theorem ScalarCtor.toPType_ofPType (t : Proto.PType) (c : ScalarCtor)
    (h : ScalarCtor.ofPType t = some c) (n : Proto.Nullability)
    (hn : Proto.PType.nullability t = n) :
    c.toPType n = t := by
  cases t <;> simp [ScalarCtor.ofPType] at h <;> subst h
    <;> simp [ScalarCtor.toPType] <;> (try simp_all [Proto.PType.nullability])

/-- The grammar table: each scalar ctor's text prefix. The emitter and the
    parser both read this — they cannot drift. Prefixes are chosen to be
    unambiguous: no scalar prefix is a prefix of another (checked in
    `prefixes_unambiguous`). -/
def ScalarCtor.prefix : ScalarCtor → String
  | .bool => "boolean"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .fp32 => "fp32"
  | .fp64 => "fp64"
  | .string => "string"
  | .binary => "binary"

/-- The full ordered grammar table (ctor, prefix). Order matters for the
    parser: prefixes are matched longest-first to avoid `"i8"` shadowing
    nothing (they're all unambiguous, but the order documents the intent and
    keeps `"i16"/"i32"/"i64"` distinct from `"i8"`). -/
def scalarGrammar : List ScalarCtor :=
  [.bool, .i8, .i16, .i32, .i64, .fp32, .fp64, .string, .binary]

/-- Every scalar ctor is in the grammar table (the table is complete). -/
theorem scalarGrammar_complete (c : ScalarCtor) : c ∈ scalarGrammar := by
  cases c <;> simp [scalarGrammar]

/-- The table has no duplicate ctors. -/
theorem scalarGrammar_nodup : scalarGrammar.Nodup := by
  simp [scalarGrammar]

/-- **The full head-token family**: the nine prefix-only scalars plus the
    four parameterized ctors. Parsing lexes the head ONCE to a `TCtor`
    (`Decode.lexCtor`) and then dispatches on the constructor — the old
    14-branch if-chain and its per-branch complement lemmas are replaced by
    `prefix_unique` below. The string prefixes appear ONLY here and in
    `ScalarCtor.prefix`; they are the wire boundary. -/
inductive TCtor where
  | scalar (s : ScalarCtor)
  | decimal | list | map | struct
deriving Repr, BEq, DecidableEq

/-- The head keyword (for the parameterized ctors, the opening `<`
    included). The emitter writes exactly this; the lexer matches exactly
    this. -/
def TCtor.prefix : TCtor → String
  | .scalar s => ScalarCtor.prefix s
  | .decimal => "decimal<"
  | .list => "list<"
  | .map => "map<"
  | .struct => "struct<"

/-- The closed enumeration the lexer folds. Order is irrelevant
    (`prefix_unique` says at most one ctor's prefix can match any input). -/
def TCtor.all : List TCtor :=
  [.scalar .bool, .scalar .i8, .scalar .i16, .scalar .i32, .scalar .i64,
   .scalar .fp32, .scalar .fp64, .scalar .string, .scalar .binary,
   .decimal, .list, .map, .struct]

-- The head keywords as simp rules: any proof that simp-normalizes emitter
-- output sees the literal prefix, and the lexer's `lexCtor_self` rewrites
-- stay in sync automatically. The string literals live ONLY here and in
-- `ScalarCtor.prefix`.
@[simp] theorem TCtor.prefix_scalar (s : ScalarCtor) :
    TCtor.prefix (.scalar s) = ScalarCtor.prefix s := rfl
@[simp] theorem TCtor.prefix_decimal : TCtor.prefix .decimal = "decimal<" := rfl
@[simp] theorem TCtor.prefix_list : TCtor.prefix .list = "list<" := rfl
@[simp] theorem TCtor.prefix_map : TCtor.prefix .map = "map<" := rfl
@[simp] theorem TCtor.prefix_struct : TCtor.prefix .struct = "struct<" := rfl

theorem TCtor.all_complete (t : TCtor) : t ∈ all := by
  cases t with
  | scalar s => cases s <;> simp [TCtor.all]
  | _ => simp [TCtor.all]

theorem TCtor.all_nodup : all.Nodup := by simp [TCtor.all]

/-- Prefixes of a common input are prefix-comparable (the shorter is a
    prefix of the longer). Core-only: no mathlib prefix lemmas here. -/
theorem List.prefix_comparable {p₁ p₂ cs : List Char} (h1 : p₁ <+: cs)
    (h2 : p₂ <+: cs) : p₁ <+: p₂ ∨ p₂ <+: p₁ := by
  induction p₁ generalizing p₂ cs with
  | nil => left; exact ⟨p₂, rfl⟩
  | cons a as ih =>
    cases p₂ with
    | nil => right; exact ⟨a :: as, rfl⟩
    | cons b bs =>
      obtain ⟨r₁, hr₁⟩ := h1
      obtain ⟨r₂, hr₂⟩ := h2
      rw [List.cons_append] at hr₁ hr₂
      rw [← hr₂] at hr₁
      injection hr₁ with hab hrest
      subst hab
      have h1' : as <+: as ++ r₁ := ⟨r₁, rfl⟩
      have h2' : bs <+: as ++ r₁ := ⟨r₂, hrest.symm⟩
      rcases ih h1' h2' with ⟨r, hr⟩ | ⟨r, hr⟩
      · left; exact ⟨r, by simp [List.cons_append, hr]⟩
      · right; exact ⟨r, by simp [List.cons_append, hr]⟩

/-- **The lexing soundness theorem**: two ctors' prefixes cannot both match
    one input — head lexing is UNAMBIGUOUS, so the lexer never needs an
    ordered if-chain. Distinct ctors' prefixes are incompatible (checked by
    `simp` over the closed enumeration: every pair differs at a concrete
    character — no TCtor prefix is a prefix of another). -/
theorem TCtor.prefix_unique (t₁ t₂ : TCtor) (cs : List Char)
    (h1 : t₁.prefix.toList <+: cs) (h2 : t₂.prefix.toList <+: cs) :
    t₁ = t₂ := by
  -- with both prefixes comparable, incompatibility is decidable per pair
  have clash : ∀ {a b : TCtor}, a.prefix.toList <+: cs → b.prefix.toList <+: cs →
      (¬ (a.prefix.toList.isPrefixOf b.prefix.toList = true)) →
      (¬ (b.prefix.toList.isPrefixOf a.prefix.toList = true)) → a = b := by
    intro a b ha hb hab hba
    rcases List.prefix_comparable ha hb with h | h
    · exact absurd (List.isPrefixOf_iff_prefix.mpr h) hab
    · exact absurd (List.isPrefixOf_iff_prefix.mpr h) hba
  cases t₁ with
  | scalar a =>
    cases a <;> cases t₂ <;> first
      | rfl
      | exact clash h1 h2 (by decide) (by decide)
      | (rename_i b; cases b <;> first
          | rfl
          | exact clash h1 h2 (by decide) (by decide))
  | _ =>
    cases t₂ <;> first
      | rfl
      | exact clash h1 h2 (by decide) (by decide)
      | (rename_i b; cases b <;> exact clash h1 h2 (by decide) (by decide))


/-! ## The name families (W5.3 phase 2a)

The rel grammar's name tokens were FOUR hand-written tables drifting in
emitter/decoder pairs: `Emit/Text.joinTypeName` ↔ `Decode.joinTypeOfName`,
`setOpName` ↔ `setOpOfName`, `sortDirName` ↔ `sortDirOfName`, and
`literalTypeName` ↔ the literal suffix (read through `parseType`). Each
family is now ONE table here: a closed enumeration of the EMIT-ABLE
constructors (`unspecified` is excluded by construction — the emitter
rejects it, the decoder never produces it), the `name` token function, and
the row list. The emitter renders via `ofX` + `name`; the decoder
exact-matches the token via `ofName` — both read the same rows.

Discipline difference from the type heads: these decoders `scanIdent` and
then EXACT-match the token, so the side condition is name-DISTINCTNESS
(the `…_name_nodup` lemmas, by `decide`) where `TCtor` needed
`prefix_unique`. `findName_self` is the one generic lemma every family's
self-lookup rides — the exact-match analog of `lexCtor_self`. -/

/-- Exact-match self-lookup over a name table: with name-distinct rows,
    looking up a row's own name finds that row. -/
theorem findName_self {α : Type} (name : α → String) (t : List α)
    (hnodup : (t.map name).Nodup) (c : α) (hc : c ∈ t) :
    (t.find? (fun c' => name c' == name c)) = some c := by
  induction t with
  | nil => simp at hc
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hc with rfl | hin
    · rw [List.find?_cons, beq_self_eq_true]
    · have hne : (name x == name c) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        apply hnodup.1
        rw [h]
        exact List.mem_map_of_mem hin
      rw [List.find?_cons, hne]
      exact ih hnodup.2 hin

/-- The emit-able join types: the text grammar has no `Unspecified` row
    (the emitter rejects it, the decoder never produces it). Growing
    substrait's join catalogue = a ctor here + a row in `joinGrammar`. -/
inductive JoinCtor where
  | inner | outer | left | right
  | leftSemi | rightSemi | leftAnti | rightAnti
  | leftSingle | rightSingle | leftMark | rightMark
deriving Repr, BEq, DecidableEq, Inhabited

/-- Build the proto join type for a join ctor. -/
def JoinCtor.toJoinType : JoinCtor → Proto.JoinType
  | .inner => .inner | .outer => .outer | .left => .left | .right => .right
  | .leftSemi => .leftSemi | .rightSemi => .rightSemi
  | .leftAnti => .leftAnti | .rightAnti => .rightAnti
  | .leftSingle => .leftSingle | .rightSingle => .rightSingle
  | .leftMark => .leftMark | .rightMark => .rightMark

/-- Recover the join ctor from a proto join type (`unspecified` → none). -/
def JoinCtor.ofJoinType : Proto.JoinType → Option JoinCtor
  | .inner => some .inner | .outer => some .outer | .left => some .left
  | .right => some .right | .leftSemi => some .leftSemi
  | .rightSemi => some .rightSemi | .leftAnti => some .leftAnti
  | .rightAnti => some .rightAnti | .leftSingle => some .leftSingle
  | .rightSingle => some .rightSingle | .leftMark => some .leftMark
  | .rightMark => some .rightMark | .unspecified => none

/-- ofJoinType ∘ toJoinType = some. -/
theorem JoinCtor.ofJoinType_toJoinType (c : JoinCtor) :
    ofJoinType c.toJoinType = some c := by
  cases c <;> rfl

/-- toJoinType ∘ ofJoinType = id where defined. -/
theorem JoinCtor.toJoinType_ofJoinType (j : Proto.JoinType) (c : JoinCtor)
    (h : ofJoinType j = some c) : c.toJoinType = j := by
  cases j <;> simp [ofJoinType] at h <;> subst h <;> rfl

/-- The wire token of each join ctor (`&Inner`, … — the `&` is the rel
    header's, not the token's). -/
def JoinCtor.name : JoinCtor → String
  | .inner => "Inner" | .outer => "Outer" | .left => "Left" | .right => "Right"
  | .leftSemi => "LeftSemi" | .rightSemi => "RightSemi"
  | .leftAnti => "LeftAnti" | .rightAnti => "RightAnti"
  | .leftSingle => "LeftSingle" | .rightSingle => "RightSingle"
  | .leftMark => "LeftMark" | .rightMark => "RightMark"

/-- The join-name table (all rows; order irrelevant — exact match plus
    `joinGrammar_name_nodup`). -/
def joinGrammar : List JoinCtor :=
  [.inner, .outer, .left, .right, .leftSemi, .rightSemi, .leftAnti,
   .rightAnti, .leftSingle, .rightSingle, .leftMark, .rightMark]

theorem joinGrammar_complete (c : JoinCtor) : c ∈ joinGrammar := by
  cases c <;> simp [joinGrammar]

theorem joinGrammar_name_nodup : (joinGrammar.map JoinCtor.name).Nodup := by
  decide

/-- The decoder's exact-match lookup over the table. -/
def JoinCtor.ofName (s : String) : Option JoinCtor :=
  joinGrammar.find? (fun c => c.name == s)

/-- Self-lookup: a row's own name parses back to it. -/
theorem JoinCtor.ofName_self (c : JoinCtor) : ofName c.name = some c :=
  findName_self name joinGrammar joinGrammar_name_nodup c (joinGrammar_complete c)

/-- Negative control: `Unspecified` has no row, so its token does not parse. -/
theorem JoinCtor.ofName_unspecified : ofName "Unspecified" = none := by decide

/-- The emit-able set ops (no `Unspecified` row). -/
inductive SetCtor where
  | unionAll | unionDistinct
  | minusPrimary | minusPrimaryAll | minusMultiset
  | intersectionPrimary | intersectionMultiset | intersectionMultisetAll
deriving Repr, BEq, DecidableEq, Inhabited

/-- Build the proto set op for a set ctor. -/
def SetCtor.toSetOp : SetCtor → Proto.SetOp
  | .unionAll => .unionAll | .unionDistinct => .unionDistinct
  | .minusPrimary => .minusPrimary | .minusPrimaryAll => .minusPrimaryAll
  | .minusMultiset => .minusMultiset
  | .intersectionPrimary => .intersectionPrimary
  | .intersectionMultiset => .intersectionMultiset
  | .intersectionMultisetAll => .intersectionMultisetAll

/-- Recover the set ctor from a proto set op (`unspecified` → none). -/
def SetCtor.ofSetOp : Proto.SetOp → Option SetCtor
  | .unionAll => some .unionAll | .unionDistinct => some .unionDistinct
  | .minusPrimary => some .minusPrimary | .minusPrimaryAll => some .minusPrimaryAll
  | .minusMultiset => some .minusMultiset
  | .intersectionPrimary => some .intersectionPrimary
  | .intersectionMultiset => some .intersectionMultiset
  | .intersectionMultisetAll => some .intersectionMultisetAll
  | .unspecified => none

theorem SetCtor.ofSetOp_toSetOp (c : SetCtor) :
    ofSetOp c.toSetOp = some c := by
  cases c <;> rfl

theorem SetCtor.toSetOp_ofSetOp (op : Proto.SetOp) (c : SetCtor)
    (h : ofSetOp op = some c) : c.toSetOp = op := by
  cases op <;> simp [ofSetOp] at h <;> subst h <;> rfl

/-- The wire token of each set ctor (`&UnionAll`, …). -/
def SetCtor.name : SetCtor → String
  | .unionAll => "UnionAll" | .unionDistinct => "UnionDistinct"
  | .minusPrimary => "MinusPrimary" | .minusPrimaryAll => "MinusPrimaryAll"
  | .minusMultiset => "MinusMultiset"
  | .intersectionPrimary => "IntersectionPrimary"
  | .intersectionMultiset => "IntersectionMultiset"
  | .intersectionMultisetAll => "IntersectionMultisetAll"

/-- The set-op name table. -/
def setGrammar : List SetCtor :=
  [.unionAll, .unionDistinct, .minusPrimary, .minusPrimaryAll, .minusMultiset,
   .intersectionPrimary, .intersectionMultiset, .intersectionMultisetAll]

theorem setGrammar_complete (c : SetCtor) : c ∈ setGrammar := by
  cases c <;> simp [setGrammar]

theorem setGrammar_name_nodup : (setGrammar.map SetCtor.name).Nodup := by
  decide

/-- The decoder's exact-match lookup over the table. -/
def SetCtor.ofName (s : String) : Option SetCtor :=
  setGrammar.find? (fun c => c.name == s)

theorem SetCtor.ofName_self (c : SetCtor) : ofName c.name = some c :=
  findName_self name setGrammar setGrammar_name_nodup c (setGrammar_complete c)

/-- Negative control: `Unspecified` has no row, so its token does not parse. -/
theorem SetCtor.ofName_unspecified : ofName "Unspecified" = none := by decide

/-- The emit-able sort directions (no `Unspecified` row). -/
inductive SortDirCtor where
  | ascNullsFirst | ascNullsLast | descNullsFirst | descNullsLast | clustered
deriving Repr, BEq, DecidableEq, Inhabited

/-- Build the proto sort direction for a sort-dir ctor. -/
def SortDirCtor.toSortDirection : SortDirCtor → Proto.SortDirection
  | .ascNullsFirst => .ascNullsFirst | .ascNullsLast => .ascNullsLast
  | .descNullsFirst => .descNullsFirst | .descNullsLast => .descNullsLast
  | .clustered => .clustered

/-- Recover the sort-dir ctor from a proto sort direction
    (`unspecified` → none). -/
def SortDirCtor.ofSortDirection : Proto.SortDirection → Option SortDirCtor
  | .ascNullsFirst => some .ascNullsFirst | .ascNullsLast => some .ascNullsLast
  | .descNullsFirst => some .descNullsFirst | .descNullsLast => some .descNullsLast
  | .clustered => some .clustered | .unspecified => none

theorem SortDirCtor.ofSortDirection_toSortDirection (c : SortDirCtor) :
    ofSortDirection c.toSortDirection = some c := by
  cases c <;> rfl

theorem SortDirCtor.toSortDirection_of (d : Proto.SortDirection) (c : SortDirCtor)
    (h : ofSortDirection d = some c) : c.toSortDirection = d := by
  cases d <;> simp [ofSortDirection] at h <;> subst h <;> rfl

/-- `ofSortDirection` fails only at `unspecified`. -/
theorem SortDirCtor.eq_unspecified_of_ofSortDirection_none {d : Proto.SortDirection}
    (h : ofSortDirection d = none) : d = .unspecified := by
  cases d <;> simp [ofSortDirection] at h <;> rfl

/-- The wire token of each sort-dir ctor (`AscNullsFirst`, … — no `&` here;
    the sort field's `(…, &Dir)` adds it). -/
def SortDirCtor.name : SortDirCtor → String
  | .ascNullsFirst => "AscNullsFirst" | .ascNullsLast => "AscNullsLast"
  | .descNullsFirst => "DescNullsFirst" | .descNullsLast => "DescNullsLast"
  | .clustered => "Clustered"

/-- The sort-direction name table. -/
def sortDirGrammar : List SortDirCtor :=
  [.ascNullsFirst, .ascNullsLast, .descNullsFirst, .descNullsLast, .clustered]

theorem sortDirGrammar_complete (c : SortDirCtor) : c ∈ sortDirGrammar := by
  cases c <;> simp [sortDirGrammar]

theorem sortDirGrammar_name_nodup : (sortDirGrammar.map SortDirCtor.name).Nodup := by
  decide

/-- The decoder's exact-match lookup over the table. -/
def SortDirCtor.ofName (s : String) : Option SortDirCtor :=
  sortDirGrammar.find? (fun c => c.name == s)

theorem SortDirCtor.ofName_self (c : SortDirCtor) : ofName c.name = some c :=
  findName_self name sortDirGrammar sortDirGrammar_name_nodup c
    (sortDirGrammar_complete c)

/-- Negative control: `Unspecified` has no row, so its token does not parse. -/
theorem SortDirCtor.ofName_unspecified : ofName "Unspecified" = none := by decide

/-! ### The literal-type names

The literal type suffix reuses the TYPE grammar's tokens: the nine scalar
literal types carry their `ScalarCtor.prefix`; `null` is the one
literal-only token. The decode side never had a separate name table — it
reads the suffix as a full type (`scanLitSuffix` → `parseType` → `lexCtor`),
so it was already table-driven; the drift was the EMITTER's second copy
(`Emit/Text.literalTypeName`). `literalScalarCtor` + `literalTypeToken`
make the sharing explicit: the emitter's token IS the scalar's prefix. -/

/-- The scalar ctor behind a scalar literal type (`none` = the null
    literal). -/
def literalScalarCtor : Proto.LiteralType → Option ScalarCtor
  | .bool _ => some .bool
  | .i8 _ => some .i8
  | .i16 _ => some .i16
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .fp32 _ => some .fp32
  | .fp64 _ => some .fp64
  | .string _ => some .string
  | .binary _ => some .binary
  | .null _ => none

/-- The literal-type suffix token: the scalar's type prefix, `"null"` for
    the null literal. -/
def literalTypeToken (lt : Proto.LiteralType) : String :=
  match literalScalarCtor lt with
  | some c => ScalarCtor.prefix c
  | none => "null"

end Substrait.Grammar
