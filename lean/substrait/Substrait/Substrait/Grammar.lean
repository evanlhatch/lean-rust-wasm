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
-/

import Substrait.Proto.Type

namespace Substrait.Substrait

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


end Substrait.Substrait
