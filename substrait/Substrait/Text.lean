/-
# Substrait.Text — the canonical text: the token tables + the type fragment + the rel lines

Owner: the substrait port agent (the mandate tree, `substrait/`).
Provenance: the token-table content ports from
`legacy/lean/substrait/Substrait/Grammar.lean` (the scalar/type-token
tables — the legacy Grammar-tables verdict in
notes/v3/14-build-map.md's substrait row), NARROWED to the seed's
`PType` set.

THE DISCIPLINE (the honest judgment call, per piece): the scalar/token
rows are a pure prefix↔ctor BIJECTION — ONE table read by both
directions, the legacy's anti-drift shape, kept. The TYPE fragment's
emit/parse ride the TextKit DIRECT discipline (the plain `Parser`
lane). The round-trip LAW landed for the SCALAR fragment
(`parseScalarGo_typeChars` — the decode ladder's core lemma, ported as
content, proved). The RECURSIVE `list<…>` arm's round trip is
HONESTLY DEFERRED (the deferred-row discipline): the proof's shape
needs the goal's `List.drop`-argument's matcher-spelling to be
rewritten into the IH's `typeChars`-spelling — a kabstract-shape wall
(the same family as the ctor-armed recursion wall,
notes/v3/15-patterns.md #17: the compiled matcher's scrutinee terms do
not present the syntactic form the rewrite needs, and the
append-associativity crossing is propositional, not definitional). The list round trips are pinned as
VALUES in SubstraitTests; the law's full statement is the named
follow-up (its port source: `Decode/Types.lean`'s core lemma).

- the type text: `boolean`/`i32`/`i64`/`string` (+ `?` for nullable),
  `list<T>` nesting — the substrait-explain type spellings;
- `typeChars` — the char-level emitter (the proofs' surface; `typeText`
  is its String image, ONE writer);
- `parseType` — the fuel-driven total parser (plain `Parser` lane —
  positions arrive with the full line grammar, Phase 4);
- `parseScalarGo_typeChars` — THE ROUND-TRIP LAW (scalar fragment);
- `exprText` — the expression emitter (the write face for the narrow
  fragment; the parse half is the decode ladder's);
- the rel grammar's name tables + the canonical rel lines (`relText`)
  + the round-trip corollary (the slice-2 growth, above).

SLICE-2 GROWTH (the rel grammar, ported from legacy `Grammar.lean`'s
name-token tables + `Emit/Text.lean`'s line shapes, narrowed):

- the rel grammar's NAME TOKENS as tables — the sort directions, the
  set ops, the join types: ONE `name` function per family read by BOTH
  the emitter and the decoder's `ofName` exact-match, with
  `findName_self` (the generic self-lookup lemma, ported as content)
  proving the round trip and `decide`-level negative controls. The
  legacy's unspecified/ascNullsLast/descNullsLast/clustered sort rows
  and the minus/intersection set rows port with their consumers (the
  narrowed tables keep the bijection closed).
- `relLines`/`relText` — the canonical rel text (the substrait-explain
  line shapes: `Read[units => health:i64?, …]`, `Filter[… => $0, $1]`,
  `Project[$0, …]`, `Aggregate[… => …]`, `Sort[(…, &AscNullsFirst) =>
  …]`, `Fetch[limit=… => …]`, `Join[&Inner, … => …]`,
  `Set[&UnionAll => …]`), children indented 2 spaces per level. TOTAL
  over the narrow `Rel` union (no Except — the union carries no
  write/extension arms; the legacy's Ctx/anchor machinery ports with
  the extensions section).
- `parseType_typeText_scalar` — the round-trip COROLLARY (the run
  entry's face): the parse of the emit at the run's own fuel is the
  value, for every scalar ctor at a wire nullability.

The type fragment's RECURSIVE `list<…>` round-trip LAW stays the named
deferred row (below); the rel lines' parse half is the decode ladder
(Phase 4 — the legacy `Decode/*` lemmas port as content then).

MECHANICS NOTES (06's trap discipline, paid once here):
- simp does NOT reduce `String.toList` on a literal — every prefix
  decision rides the rfl CONS-FACE lemmas (`chars_*_cons`);
- the `?`-suffix check is the direct pattern check `isQHead`, NOT
  `startsWith cs "?"` (whose Char-beq symmetry fights the follow-set
  proofs);
- the length lemmas are `rfl` at the cons-chain level
  (`String.length_toList` does not reduce under simp only).

The five questions (notes/v3/01-core.md):
- root: Universe — the token tables + the type fragment's two
  directions as total functions.
- carrier grade: the round-trip law (parse ∘ emit = id at sufficient
  fuel, scalar fragment) — the byte-level content this file exists
  for; the list arm's law is the named deferred row.
- spine reading: Typed → Proto → Text (this is the text end).
- ladder rung: hand theorems of the small kind (cases over the closed
  PType + the prefix kit's concrete reductions).
- gate row: the axiom report (Substrait is gated); SubstraitTests
  carries the round-trip pins + the mandatory negative controls.
-/
module


public import Substrait.Proto
public import TextKit.Basic


@[expose] public section
namespace Substrait.Text

open Substrait.Proto
open TextKit

/-! ## the token table (the legacy Grammar tables' port, narrowed) -/

/-- The prefix-only (scalar) type constructors: the closed set the
    token table enumerates. Growing substrait's scalar catalogue =
    adding a ctor here + a `prefix` row. -/
inductive ScalarCtor where
  | bool | i32 | i64 | string
deriving Repr, BEq, DecidableEq, Inhabited

/-- Build the proto type for a scalar ctor at a nullability. -/
def ScalarCtor.toPType : ScalarCtor → Nullability → PType
  | .bool, n => .bool n
  | .i32, n => .i32 n
  | .i64, n => .i64 n
  | .string, n => .string n

/-- Recover the scalar ctor from a proto type, if it is one (the
    parameterized ctors — the seed's `list` — are not scalars). -/
def ScalarCtor.ofPType : PType → Option ScalarCtor
  | .bool _ => some .bool
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .string _ => some .string
  | _ => none

/-- ofPType ∘ toPType = some: every scalar ctor round-trips through its
    type (the legacy table's law, ported as content). -/
theorem ScalarCtor.ofPType_toPType (c : ScalarCtor) (n : Nullability) :
    ScalarCtor.ofPType (c.toPType n) = some c := by
  cases c <;> rfl

/-- toPType ∘ ofPType = id on the type (the nullability is preserved). -/
theorem ScalarCtor.toPType_ofPType (t : PType) (c : ScalarCtor)
    (h : ScalarCtor.ofPType t = some c) (n : Nullability)
    (hn : PType.nullability t = n) : c.toPType n = t := by
  cases t <;> simp [ScalarCtor.ofPType] at h <;> subst h <;>
    simp_all [ScalarCtor.toPType, PType.nullability]

/-- The token table: each scalar ctor's text token. The emitter and the
    parser both read this — they cannot drift. The tokens are
    unambiguous: no scalar token is a prefix of another (the seed's
    four are single-word; the legacy's i8/i16/i32/i64 family grew this
    note's discipline). -/
def ScalarCtor.prefix : ScalarCtor → String
  | .bool => "boolean"
  | .i32 => "i32"
  | .i64 => "i64"
  | .string => "string"

/-- The token's char face (the proofs' surface — ONE spelling: the
    String table's image, reduced by whnf at each concrete arm). -/
def ScalarCtor.chars (c : ScalarCtor) : List Char := (ScalarCtor.prefix c).toList

/-- The full ordered table (ctor order = parse order). -/
def scalarTable : List ScalarCtor := [.bool, .i32, .i64, .string]

/-- Every scalar ctor is in the table (the table is complete). -/
theorem scalarTable_complete (c : ScalarCtor) : c ∈ scalarTable := by
  cases c <;> simp [scalarTable]

/-- The tokens' cons faces (the parse's prefix decisions reduce through
    these — `rfl`, the literal's whnf; simp does NOT reduce
    `String.toList` on a literal, the probe's finding). -/
def chars_bool_cons : ScalarCtor.chars .bool = 'b' :: ['o', 'o', 'l', 'e', 'a', 'n'] := rfl

def chars_i32_cons : ScalarCtor.chars .i32 = 'i' :: ['3', '2'] := rfl

def chars_i64_cons : ScalarCtor.chars .i64 = 'i' :: ['6', '4'] := rfl

def chars_string_cons : ScalarCtor.chars .string = 's' :: ['t', 'r', 'i', 'n', 'g'] := rfl

/-- The tokens' lengths (the fuel arithmetic; `rfl`). -/
def chars_bool_length : (ScalarCtor.chars .bool).length = 7 := rfl

def chars_i32_length : (ScalarCtor.chars .i32).length = 3 := rfl

def chars_i64_length : (ScalarCtor.chars .i64).length = 3 := rfl

def chars_string_length : (ScalarCtor.chars .string).length = 6 := rfl

/-! ## the type fragment: emit (the char-level writer) -/

/-- The list tokens' + suffix's char faces (ONE spelling: the char
    lists the parse's drop arithmetic reduces through; the SCALAR
    tokens ride `ScalarCtor.chars` — the String table's image). -/
def listOpenChars : List Char := ['l', 'i', 's', 't', '<']

def listCloseChars : List Char := ['>']

def nullableChars : List Char := ['?']

/-- The tokens' lengths (the fuel arithmetic; `rfl`). -/
def listOpenChars_length : listOpenChars.length = 5 := rfl

def listCloseChars_length : listCloseChars.length = 1 := rfl

def nullableChars_length : nullableChars.length = 1 := rfl

/-- The list-open token PEELS (the parse's drop step; `rfl`-level via
    the cons chain — `simp` needs the unfold + the numeral's offset
    unification, both fine under full simp). -/
theorem drop5_listOpen (w : List Char) : List.drop 5 (listOpenChars ++ w) = w := by
  simp [listOpenChars]

/- The char-level type text: `boolean?` / `i32` / `list<i64>` /
   `list<string?>` — the substrait-explain type spellings. The proofs'
   surface (a plain List Char fold — no String-append lemma debt). -/
mutual
  def typeCharsBase : PType → List Char
    | .bool _ => ScalarCtor.chars .bool
    | .i32 _ => ScalarCtor.chars .i32
    | .i64 _ => ScalarCtor.chars .i64
    | .string _ => ScalarCtor.chars .string
    | .list e _ => listOpenChars ++ typeChars e ++ listCloseChars

  def typeChars : PType → List Char
    | t =>
        typeCharsBase t ++
          (match t.nullability with
          | .nullable => nullableChars
          | _ => [])
end

/-- The String face of the type text (the consumers' surface; ONE
    writer: the image of `typeChars`). -/
def typeText (t : PType) : String := String.ofList (typeChars t)

/-! ## the type fragment: parse (the fuel-driven reader) -/

/-- The `?`-head check (the nullability-suffix detector): the parse's
    own check — NOT `startsWith cs "?"` (whose Char-beq symmetry fights
    the follow-set proofs; the direct pattern check keeps them in
    hrest's lap). -/
def isQHead : List Char → Bool
  | '?' :: _ => true
  | _ => false

/-- The `?` head's two faces (the negative controls use these). -/
def isQHead_true : isQHead ('?' :: []) = true := rfl

def isQHead_nil : isQHead [] = false := rfl

/-- The scalar-prefix read: the table's parse side, in `scalarTable`
    order; the optional `?` nullability suffix read after the token. -/
def parseScalarGo : Parser PType :=
  fun cs =>
    if startsWith cs "boolean" then
      let cs1 := cs.drop 7
      if isQHead cs1 then some (.bool .nullable, cs1.drop 1)
      else some (.bool .required, cs1)
    else if startsWith cs "i32" then
      let cs1 := cs.drop 3
      if isQHead cs1 then some (.i32 .nullable, cs1.drop 1)
      else some (.i32 .required, cs1)
    else if startsWith cs "i64" then
      let cs1 := cs.drop 3
      if isQHead cs1 then some (.i64 .nullable, cs1.drop 1)
      else some (.i64 .required, cs1)
    else if startsWith cs "string" then
      let cs1 := cs.drop 6
      if isQHead cs1 then some (.string .nullable, cs1.drop 1)
      else some (.string .required, cs1)
    else none

/-- The type parser: fuel-driven (the `list<…>` nesting decrements; the
    fuel-0 arm is the recursion-limit refusal — the tyP precedent).
    Plain `Parser` lane (no positions — the module header's note). -/
def parseTypeGo : Nat → Parser PType :=
  fun fuel =>
    match fuel with
    | 0 => fun _ => none
    | fuel + 1 =>
        fun cs =>
          if startsWith cs "list<" then
            match parseTypeGo fuel (cs.drop 5) with
            | none => none
            | some (e, cs') =>
                if startsWith cs' ">" then
                  let cs2 := cs'.drop 1
                  if isQHead cs2 then
                    some (.list e .nullable, cs2.drop 1)
                  else
                    some (.list e .required, cs2)
                else none
          else
            parseScalarGo cs

/-- The run entry: fuel = the text's char count + 1 (always
    sufficient). -/
def parseType (t : PType) (cs : List Char) : Option (PType × List Char) :=
  parseTypeGo (cs.length + 1) cs

/-! ## the round-trip law (scalar fragment; the list arm deferred) -/

/-- The scalar text's length: the token's length + the suffix (the
    fuel-0 case's contradiction engine). -/
theorem typeChars_scalar_length (c : ScalarCtor) (n : Nullability) :
    (typeChars (c.toPType n)).length =
      (ScalarCtor.chars c).length + (match n with | .nullable => 1 | _ => 0) := by
  simp only [typeChars, typeCharsBase, ScalarCtor.toPType, PType.nullability,
    List.length_append]
  cases c <;> cases n <;>
    simp [typeCharsBase, nullableChars_length, chars_bool_length,
      chars_i32_length, chars_i64_length, chars_string_length]

/-- The FOLLOW-CLEAN predicate: the suffix text does not START with
    `?` (the follow-set discipline: the parse reads a bare `?` as the
    type's own nullability suffix — a full text's empty final suffix is
    always clean). -/
abbrev FollowClean (rest : List Char) : Prop := isQHead rest = false

/-- THE ROUND-TRIP LAW (scalar fragment — the decode ladder's core
    lemma, ported as content): the parse of the emit IS the value, at
    sufficient fuel, for every scalar ctor at a wire nullability
    ({nullable, required} — the UNSPECIFIED nullability has no text
    spelling, bare = required on the wire) and every FOLLOW-CLEAN
    suffix. -/
theorem parseScalarGo_typeChars (c : ScalarCtor) (n : Nullability)
    (rest : List Char) (fuel : Nat) (hrest : FollowClean rest)
    (hn : n ≠ Nullability.unspecified) :
    (typeChars (c.toPType n)).length ≤ fuel →
    parseTypeGo fuel ((typeChars (c.toPType n)) ++ rest) = some (c.toPType n, rest) := by
  intro hfuel
  cases fuel with
  | zero =>
      exfalso
      have h7 := typeChars_scalar_length c n
      cases c with
      | bool => exact absurd hfuel (by have := chars_bool_length; omega)
      | i32 => exact absurd hfuel (by have := chars_i32_length; omega)
      | i64 => exact absurd hfuel (by have := chars_i64_length; omega)
      | string => exact absurd hfuel (by have := chars_string_length; omega)
  | succ f =>
      cases n with
      | unspecified => exact absurd rfl hn
      | nullable =>
          cases c <;>
            simp only [ScalarCtor.toPType, PType.nullability, typeChars, typeCharsBase,
              List.cons_append, parseTypeGo, if_true] <;>
            simp [parseScalarGo, TextKit.startsWith, isQHead, nullableChars,
              chars_bool_cons, chars_i32_cons, chars_i64_cons, chars_string_cons]
      | required =>
          cases rest with
          | nil =>
              cases c <;>
                simp [ScalarCtor.toPType, PType.nullability, typeChars, typeCharsBase,
                  parseTypeGo, parseScalarGo, TextKit.startsWith, isQHead,
                  chars_bool_cons, chars_i32_cons, chars_i64_cons, chars_string_cons]
          | cons ch rest2 =>
              have h9 : isQHead (ch :: rest2) = false := hrest
              cases c <;>
                simp [ScalarCtor.toPType, PType.nullability, typeChars, typeCharsBase,
                  parseTypeGo, parseScalarGo, TextKit.startsWith, h9,
                  chars_bool_cons, chars_i32_cons, chars_i64_cons, chars_string_cons]

/- The list fragment's round trips ride the TESTS (values) — the LAW
    (the list arm of the round trip, for every WFType) is the named
    deferred row (the module header's diagnosis). Its port source:
    `Decode/Types.lean`'s core lemma. -/

/-- THE ROUND-TRIP COROLLARY (the run entry's face): the parse of the
    emit at the run's OWN fuel is the value, for every scalar ctor at a
    wire nullability. `parseType`'s fuel is the text's char count + 1 —
    always sufficient. -/
theorem parseType_typeText_scalar (c : ScalarCtor) (n : Nullability)
    (hn : n ≠ Nullability.unspecified) :
    parseType (c.toPType n) (typeChars (c.toPType n)) =
      some (c.toPType n, []) := by
  have h := parseScalarGo_typeChars c n [] ((typeChars (c.toPType n)).length + 1)
    (by simp [FollowClean, isQHead_nil]) hn (by simp)
  rw [List.append_nil] at h
  exact h

/-! ## the rel grammar's name tokens (the legacy W5.3-phase-2a tables, narrowed) -/

/-- Exact-match self-lookup over a name table: with name-distinct rows,
    looking up a row's own name finds that row (the legacy
    `Grammar.findName_self`, ported as content — the ONE generic lemma
    every family's self-lookup rides). -/
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

/-- THE NAME-TABLE BUNDLE (the legacy W5.3-phase-2a tables' shape):
    a family's display names over a closed union — the name function,
    the table, its name-distinctness, and its completeness, packed so
    the decoder's lookup is ONE generic face (self + miss) over
    `findName_self`. The three families (sortDir / setOp / joinType)
    are instances. -/
structure NameTable (α : Type) where
  name : α → String
  table : List α
  nodup : (table.map name).Nodup
  complete : ∀ x : α, x ∈ table

/-- The decoder's exact-match lookup over a bundle's table. -/
def NameTable.ofName (t : NameTable α) (s : String) : Option α :=
  t.table.find? (fun c => t.name c == s)

/-- Self-lookup: a value's own token parses back to it (the round
    trip's law, through the ONE generic lemma). -/
theorem NameTable.ofName_self (t : NameTable α) (x : α) :
    t.ofName (t.name x) = some x :=
  findName_self t.name t.table t.nodup x (t.complete x)

/-- Miss law: a token no family member spells does not parse (the
    negative controls' generic face). -/
theorem NameTable.ofName_miss (t : NameTable α) (s : String)
    (h : ∀ x, t.name x ≠ s) : t.ofName s = none := by
  simp [NameTable.ofName, List.find?_eq_none]
  intro x _hx
  exact h x

/-- The sort directions' display tokens (`AscNullsFirst`, … — no `&`
    here; the sort field's `(…, &Dir)` adds it). The emitter and the
    decoder's `ofName` both read this ONE function. -/
def sortDirName : Proto.SortDirection → String
  | .ascNullsFirst => "AscNullsFirst"
  | .descNullsFirst => "DescNullsFirst"

/-- The sort-direction bundle (ctor order irrelevant — exact match
    plus the bundle's `nodup`). -/
def sortDirTable : NameTable Proto.SortDirection where
  name := sortDirName
  table := [.ascNullsFirst, .descNullsFirst]
  nodup := by decide
  complete := by intro d; cases d <;> simp

def sortDirOfName (s : String) : Option Proto.SortDirection :=
  sortDirTable.ofName s

/-- Self-lookup: a direction's own token parses back to it. -/
theorem sortDirOfName_self (d : Proto.SortDirection) :
    sortDirOfName (sortDirName d) = some d :=
  sortDirTable.ofName_self d

/-- Negative control: a token outside the table does not parse. -/
theorem sortDirOfName_miss : sortDirOfName "Unspecified" = none :=
  sortDirTable.ofName_miss _ (by intro x; cases x <;> decide)

/-- The set ops' display tokens (`UnionAll`, …). -/
def setOpName : Proto.SetOp → String
  | .unionAll => "UnionAll"
  | .unionDistinct => "UnionDistinct"

/-- The set-op bundle. -/
def setOpTable : NameTable Proto.SetOp where
  name := setOpName
  table := [.unionAll, .unionDistinct]
  nodup := by decide
  complete := by intro op; cases op <;> simp

def setOpOfName (s : String) : Option Proto.SetOp :=
  setOpTable.ofName s

theorem setOpOfName_self (op : Proto.SetOp) :
    setOpOfName (setOpName op) = some op :=
  setOpTable.ofName_self op

theorem setOpOfName_miss : setOpOfName "Minus" = none :=
  setOpTable.ofName_miss _ (by intro x; cases x <;> decide)

/-- The write ops' display tokens (`Insert`, … — the `&` is the rel
    header's). The full closed enum — no narrowing. -/
def writeOpName : Proto.WriteOp → String
  | .insert => "Insert"
  | .delete => "Delete"
  | .update => "Update"
  | .ctas => "Ctas"

def writeOpTable : NameTable Proto.WriteOp where
  name := writeOpName
  table := [.insert, .delete, .update, .ctas]
  nodup := by decide
  complete := by intro op; cases op <;> simp

def writeOpOfName (s : String) : Option Proto.WriteOp :=
  writeOpTable.ofName s

theorem writeOpOfName_self (op : Proto.WriteOp) :
    writeOpOfName (writeOpName op) = some op :=
  writeOpTable.ofName_self op

/-- The join types' display tokens (`Inner`, … — the `&` is the rel
    header's). The narrow four cover the closed union; the legacy's
    semi/anti/single/mark rows port with their ctor set's consumers. -/
def joinTypeName : Proto.JoinType → String
  | .inner => "Inner" | .outer => "Outer" | .left => "Left" | .right => "Right"

/-- The join-name bundle. -/
def joinTypeTable : NameTable Proto.JoinType where
  name := joinTypeName
  table := [.inner, .outer, .left, .right]
  nodup := by decide
  complete := by intro jt; cases jt <;> simp

def joinTypeOfName (s : String) : Option Proto.JoinType :=
  joinTypeTable.ofName s

theorem joinTypeOfName_self (jt : Proto.JoinType) :
    joinTypeOfName (joinTypeName jt) = some jt :=
  joinTypeTable.ofName_self jt

theorem joinTypeOfName_miss : joinTypeOfName "LeftSemi" = none :=
  joinTypeTable.ofName_miss _ (by intro x; cases x <;> decide)

/-! ## the expression emitter (the write face) -/

/-- The literal's text: `true`/`false` (default-for-syntax), `42:i64`,
    `'s'` — the narrow scalar set; string literals carry no escapes
    (the escaper ports with the full grammar — the legacy
    `TextKit.Basic` escape kit's theorem content is the port source). -/
def literalText : Literal → String
  | { literalType := .bool b, nullable := false } => if b then "true" else "false"
  | { literalType := .bool b, nullable := true } =>
      (if b then "true" else "false") ++ ":boolean?"
  | { literalType := .i32 v, nullable := n } =>
      toString v ++ ":i32" ++ (if n then "?" else "")
  | { literalType := .i64 v, nullable := n } =>
      toString v ++ ":i64" ++ (if n then "?" else "")
  | { literalType := .string s, nullable := n } =>
      "'" ++ s ++ "'" ++ (if n then "?" else "")

/-- The expression's text: `$n` refs, literals, `name(args):ty` calls —
    the narrow fragment's write face (total: every arm of the narrow
    union renders; the legacy's Except face existed for userDefined
    types + subqueries, both outside the seed). -/
def exprText : Expression → String
  | .literal lit => literalText lit
  | .field f => "$" ++ toString f.ordinal
  | .scalarFunction nm args out =>
      nm ++ "(" ++ String.intercalate "," (args.map exprText) ++ "):" ++ typeText out

/-! ## the rel lines (the legacy Emit/Text line shapes, narrowed) -/

/-- The line-shape tokens (the legacy Grammar's line-shape section,
    narrowed to what the eight arms read). -/
abbrev sepTok : String := ", "

abbrev arrowTok : String := " => "

abbrev ampTok : String := "&"

abbrev sortAmpTok : String := ", &"

abbrev eqTok : String := "="

abbrev emptyGroupTok : String := "_"

abbrev colonTok : String := ":"

abbrev lparenTok : String := "("

abbrev rparenTok : String := ")"

abbrev dotTok : String := "."

abbrev indentUnit : String := "  "

abbrev kwRead : String := "Read["

abbrev kwFilter : String := "Filter["

abbrev kwProject : String := "Project["

abbrev kwAggregate : String := "Aggregate["

abbrev kwSort : String := "Sort["

abbrev kwFetch : String := "Fetch["

abbrev kwJoin : String := "Join["

abbrev kwSet : String := "Set["

abbrev kwCross : String := "Cross["

abbrev kwWrite : String := "Write["

/-- `$0, $1, …, $w-1` — the reference range's text. -/
def refRange (w : Nat) : String :=
  String.intercalate sepTok ((List.range w).map (fun i => "$" ++ toString i))

/-- The implicit output clause ` => $0, … ` over width `w`. -/
def refOutput (w : Nat) : String := arrowTok ++ refRange w

/-- Read's base-schema columns: `name:type, …` — `_` when absent (the
    legacy's empty-schema marker). -/
def readColsText : Option Proto.NamedStruct → String
  | none => emptyGroupTok
  | some s =>
      match s.fields.zip s.names with
      | [] => emptyGroupTok
      | pairs => String.intercalate sepTok
        (pairs.map (fun p => p.2 ++ colonTok ++ typeText p.1))

/-- The read's dotted table name. -/
def readTableName : Proto.ReadType → String
  | .namedTable names => String.intercalate dotTok names

/-- The canonical rel lines: the substrait-explain shapes, children
    indented 2 spaces per level. TOTAL over the `Rel` union minus the
    extension arms — every arm renders (the extension rels' `Any`
    detail has no text face — the named boundary; the legacy's
    Ctx/anchor machinery ports with the extensions section). -/
def relLines : Proto.Rel → String → List String
  | .read rt baseSchema, indent =>
      [indent ++ kwRead ++ readTableName rt ++ arrowTok ++
        readColsText baseSchema ++ "]"]
  | .filter cond input, indent =>
      (indent ++ kwFilter ++ exprText cond ++ refOutput input.width ++ "]") ::
        relLines input (indent ++ indentUnit)
  | .project exprs input, indent =>
      let shown := (List.range input.width).map (fun i => "$" ++ toString i)
        ++ exprs.map exprText
      (indent ++ kwProject ++ String.intercalate sepTok shown ++ "]") ::
        relLines input (indent ++ indentUnit)
  | .aggregate groupings measures input, indent =>
      let groupArgs := match groupings with
        | [] => [emptyGroupTok]
        | _ => groupings.map exprText
      let cols := groupings.map exprText ++ measures.map exprText
      (indent ++ kwAggregate ++ String.intercalate sepTok groupArgs ++
        arrowTok ++ String.intercalate sepTok cols ++ "]") ::
        relLines input (indent ++ indentUnit)
  | .sort keys input, indent =>
      let sortArgs := keys.map (fun k =>
        lparenTok ++ exprText k.expr ++ sortAmpTok ++ sortDirName k.direction ++
          rparenTok)
      (indent ++ kwSort ++ String.intercalate sepTok sortArgs ++
        refOutput input.width ++ "]") :: relLines input (indent ++ indentUnit)
  | .fetch limit offset input, indent =>
      let named := (limit.map (fun n => "limit" ++ eqTok ++ toString n)).toList ++
        (offset.map (fun n => "offset" ++ eqTok ++ toString n)).toList
      let argsText := match named with
        | [] => emptyGroupTok
        | _ => String.intercalate sepTok named
      (indent ++ kwFetch ++ argsText ++ refOutput input.width ++ "]") ::
        relLines input (indent ++ indentUnit)
  | .join jt left right cond, indent =>
      (indent ++ kwJoin ++ ampTok ++ joinTypeName jt ++ sepTok ++
        exprText cond ++ refOutput (jt.width left.width right.width) ++ "]") ::
        relLines left (indent ++ indentUnit) ++ relLines right (indent ++ indentUnit)
  | .set op left right, indent =>
      (indent ++ kwSet ++ ampTok ++ setOpName op ++ refOutput left.width ++ "]") ::
        relLines left (indent ++ indentUnit) ++ relLines right (indent ++ indentUnit)
  | .cross left right, indent =>
      (indent ++ kwCross ++ refOutput (left.width + right.width) ++ "]") ::
        relLines left (indent ++ indentUnit) ++ relLines right (indent ++ indentUnit)
  | .write nms op ts input, indent =>
      (indent ++ kwWrite ++ String.intercalate dotTok nms ++ ampTok ++
        writeOpName op ++ refOutput input.width ++ "]") ::
        relLines input (indent ++ indentUnit)

/-- The canonical rel text (ONE writer: the lines' image; the parse
    half is the decode ladder, Phase 4). -/
def relText (rel : Proto.Rel) : String :=
  String.intercalate "\n" (relLines rel "")

end Substrait.Text

end -- public section

