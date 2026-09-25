/-
# Wit.Parse — the total WIT parser: text → the typed AST (the grammar layer's instance)

Owner: the Wit agent (the mandate tree, `wit/`).
Driving decisions: notes/v3/05-codegen.md §1 (the two honest laws:
`parse (print x) = ok x` — everything we print parses back;
`print (parse text) = canonicalize text` — accepted text normalizes) +
notes/v3/15-patterns.md #12 (the total parser + the inversion kit) +
notes/v3/13-interfaces.md (the WIT worlds row: the host skew check
READS component types — this parser is that reading's foundation, and
`Wit.Render` is its writing half).

## Riding the grammar layer (05 §1; the CodeRegistry/Snapshot template)

The PACKAGE level IS a `TextKit.Grammar` value (`pkgGrammar` below):
the nested seq/rep spine over the lexemes — keyword literals (the
shared `constStrLex`), the name/id atoms (the shared `identAtom`), the
ty token (the guarded leaf below) — under the ONE `rel` codec
(`packageCodec`). The derived parser/printer own every loop and every
dispatch; the hand per-level climb (`tyP_ok` … `packageP_ok`, ~800
lines) and the miss lemmas are GONE except the ty token's own. THE
ROUND TRIP IS THE GENERIC THEOREM'S INSTANCE:

- `parse_print` — a `WitOk` package's rendering parses back to exactly
  it: `Grammar.run_print_fixFree` (+ the comment-strip wrapper).
- `render_parse` — accepted text IS the rendering of its result (the
  canonicalization direction): `Grammar.print_parse` (law 2) + the
  derived print's bytes ARE `Render.package`'s (`print_eq_render`) +
  `run`'s full-consumption check. LANDED HERE — the pre-grammar file
  carried it as a named follow-up; the grammar layer's law 2 pays it.
- `print_parse` (the exactness face, generic form) — the
  `Grammar.print_parse` instance at `pkgGrammar`.

## THE RECURSION'S HONEST STATE (the layered composition — notes/v3/15-patterns.md #17)

The WIT type grammar is RECURSIVE (`option`/`list`/`result`/`tuple`
nest `Ty`s). The fix-topped face (`Grammar.parse_print_fix`) covers a
fix-TOPPED grammar only, and the wall against making the Ty recursion
the fix is structural, not effort: the ctor-armed recursion wall is
pattern #17's three-point statement (verified against this format's
shapes). The LAYERED composition, per the pattern: the Ty recursion
stays the hand-riding-TextKit zone (`tyP` + its `tyP_ok`
climb — the ONE fuel-bounded induction this format keeps), presented
to the grammar as the `tyAtom` lexeme: `print = Render.ty`, `scan =
tyP` GUARDED to the canonical spelling (the consumed prefix must BE
`Render.ty` of its result — the guard makes `scan_exact` hold by pure
take/drop algebra, no canonicality theorem over `tyP` needed). The
package/interface/record/field levels ride the engine; the accepted
language is UNCHANGED (the guard never fires on `Render`'s image).

## The accepted language — the renderer's image, plus comments

The parser accepts EXACTLY the text `Wit.Render` produces (the
canonical bytes), optionally preceded by `//`-comment lines — the
committed artifact of record `gen/schema-slice.wit` carries two. The
strictness is the canonicalization law's honesty: accepted text
normalizes to its comment-stripped bytes, and those bytes are the
rendering of the parse result (`render_parse` below). Whitespace
tolerance would break normalization — it is deliberately not accepted.

The parse-time refusals keep their teeth: trailing bytes (the run
entry's full-consumption check), the maximal-munch atom refusal and
the curated ty errors (inside `tyP`), and the duplicate-field /
duplicate-record refusals (the codec's decode — the nodup checks are
decided `none`s, never silent acceptance).

Core-only (imports `Wit`, `Wit.Render`, TextKit, Kit.Correspondence —
the cone rule: Kit/TextKit are the C0 substrate).

The five questions (notes/v3/01-core.md):
- root: Crossing — the WIT text read into the typed target grammar
  (the skew check's reading half).
- carrier grade: the correspondence row `witCodec` — the round-trip
  law in the type, the accepted-byte policy a field; the retraction /
  image-iso landed (the graduation); `render_parse` pays the
  canonicalization direction as of this migration.
- spine reading: the artifact stage's inverse — the ONE parser every
  WIT-reading lane calls; `Wit.Render` is the ONE writer.
- ladder rung: rung 1-2 — the package level is the engine's; the ty
  token's law is a small fuel-bounded induction (the hand zone).
- gate row: WitTests' round-trip pins + the artifact integration pin
  (parse the committed gen/schema-slice.wit, re-render byte-identical);
  the axiom gate sweeps the Wit root.
-/

import Wit
import Wit.Render
import TextKit.Grammar
import TextKit.Grammar.Lexemes
import TextKit.Grammar.Check
import TextKit.Grammar.Laws
import Kit.Correspondence

namespace Wit.Parse

open TextKit (Cursor ParseError GParser)

/-! ## the character classes -/

/-- A name character: the ident charset plus WIT's kebab `-`. -/
def nameChar (c : Char) : Bool :=
  TextKit.isIdentChar c || c == '-'

/-- A package-id character: a name character plus WIT's `:` separator. -/
def idChar (c : Char) : Bool :=
  nameChar c || c == ':'

/-- The name discipline: an ASCII-alpha head, then charset characters.
    `WitOk` below gates the AST side; the name lexemes enforce the byte
    side — the round-trip laws ride their agreement (the bridge lemmas
    at the lexemes section). -/
def identOk (q : Char → Bool) (s : String) : Bool :=
  match s.toList with
  | c :: w => c.isAlpha && w.all q
  | [] => false

/-! ## the curated errors (the ONE construction route — the ty zone's) -/

/-- The rejected token's text: the maximal ident-ish run at the cursor
    (the `got` slot's content for token-level rejections). -/
def gotToken (cs : List Char) : String :=
  String.ofList (cs.takeWhile (fun c => TextKit.isIdentChar c || c == '-' || c == ':'))

/-- THE curated parse error: the expected set enumerated, the rejected
    token named, the did-you-mean filled by the ONE engine (05 §4's
    closed-world rule). -/
def curated (cur : Cursor) (message : String) (valid : List String) : ParseError :=
  { ParseError.base cur.off valid with
    message := message
    got := some (gotToken cur.cs)
    suggest := TextKit.suggestFor (gotToken cur.cs) valid }

/-- The literal-token refusal (tok's own error value, named). -/
def tokErr (off : Nat) (s : String) : ParseError :=
  ParseError.base off [s!"'{s}'"]

/-- The valid WIT type tokens (the closed grammar's spellings). -/
def tyValid : List String :=
  ["bool", "u64", "i64", "string", "option", "list", "result", "tuple"]

/-! ## the ty zone — THE HAND RECURSION (the layered composition's
     honest boundary; see the module header) -/

/-! ### the token scanner (the kit's inversions, consumed) -/

/-- A literal is recognized after itself (the cursor bookkeeping is
    `tok`'s own). -/
theorem tok_self (s : String) (off : Nat) (rest : List Char) :
    TextKit.tok s ⟨off, s.toList ++ rest⟩ = .ok (s, ⟨off + s.length, rest⟩) := by
  unfold TextKit.tok
  have hp : s.toList.isPrefixOf (s.toList ++ rest) = true := by
    rw [List.isPrefixOf_iff_prefix]
    exact ⟨rest, rfl⟩
  rw [if_pos hp]
  have hd : (s.toList ++ rest).drop s.length = rest := by
    have hl : s.length = s.toList.length := String.length_toList.symm
    rw [hl]
    exact List.drop_left
  simp [Cursor.advBy, hd]

/-- The token refusal, cursor-head face (the miss direction's shared
    base for the arm lemmas): a nonempty literal whose head differs
    from the cursor's head is refused, cursor offset carried. -/
theorem tok_miss (s : String) (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ s.toList.head?) (hk : s ≠ "") :
    TextKit.tok s ⟨off, cs⟩ = .error (ParseError.base off [s!"'{s}'"]) := by
  have hne' : s.toList ≠ [] := by
    intro h
    exact hk (String.toList_inj.mp h)
  unfold TextKit.tok
  cases hs : s.toList with
  | nil => rw [hs] at hne'; exact absurd rfl hne'
  | cons c0 w =>
      rw [hs] at hne
      cases cs with
      | nil => simp [List.isPrefixOf]
      | cons c rest =>
          have hc : c0 ≠ c := by
            intro hcon
            rw [hcon] at hne
            simp at hne
          simp [List.isPrefixOf, hc]

/-! ### the orElse kit -/

theorem orElse_ok_left {α : Type} {p q : GParser α} {cur : Cursor} {r : α × Cursor}
    (h : p cur = .ok r) : TextKit.orElse p q cur = .ok r := by
  simp [TextKit.orElse, h]

theorem orElse_ok_right {α : Type} {p q : GParser α} {cur : Cursor} {e : ParseError}
    {r : α × Cursor} (h1 : p cur = .error e) (h2 : q cur = .ok r) :
    TextKit.orElse p q cur = .ok r := by
  simp [TextKit.orElse, h1, h2]

theorem orElse_err_r {α : Type} {p q : GParser α} {cur : Cursor}
    (h1 : ∃ e, p cur = .error e) (h2 : ∃ e, q cur = .error e) :
    ∃ e, TextKit.orElse p q cur = .error e := by
  obtain ⟨e1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  exact ⟨ParseError.farther e1 e2, by simp [TextKit.orElse, h1, h2]⟩

/-! ### the arms (generic success + refusal) -/

/-- The maximal-munch gate's positive face: a head char passing the
    name charset is refused as an atom continuation. -/
theorem head_not_name_of_all {rest : List Char}
    (hr : rest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true) :
    ∀ c, rest.head? = some c → (TextKit.isIdentChar c || c == '-') = false := by
  intro c hc
  rw [hc] at hr
  simpa using hr

/-- One scalar atom: the keyword PLUS the maximal-munch check — the
    following character must be off the name charset (WIT spells types
    as whole words; `boolean` is not `bool` + `ean`). The refusal is
    the curated closed-world error, so a mistyped atom teaches the
    whole valid space + the did-you-mean. -/
def atomArm (kw : String) (s : Scalar) : GParser Ty := fun cur =>
  match TextKit.tok kw cur with
  | .error e => .error e
  | .ok (_, cur') =>
      match cur'.cs.head? with
      | some c =>
          if TextKit.isIdentChar c || c == '-' then
            .error (curated cur "expected a WIT type" tyValid)
          else .ok (Ty.atom s, cur')
      | none => .ok (Ty.atom s, cur')

def unaryArm (openS : String) (k : Ty → Ty) (inner : GParser Ty) : GParser Ty := fun cur =>
  match TextKit.tok openS cur with
  | .error e => .error e
  | .ok (_, c1) =>
      match inner c1 with
      | .error e => .error e
      | .ok (a, c2) =>
          match TextKit.tok ">" c2 with
          | .error e => .error e
          | .ok (_, c3) => .ok (k a, c3)

def binaryArm (openS : String) (k : Ty → Ty → Ty) (inner : GParser Ty) : GParser Ty := fun cur =>
  match TextKit.tok openS cur with
  | .error e => .error e
  | .ok (_, c1) =>
      match inner c1 with
      | .error e => .error e
      | .ok (a, c2) =>
          match TextKit.tok ", " c2 with
          | .error e => .error e
          | .ok (_, c3) =>
              match inner c3 with
              | .error e => .error e
              | .ok (b, c4) =>
                  match TextKit.tok ">" c4 with
                  | .error e => .error e
                  | .ok (_, c5) => .ok (k a b, c5)

/-- The eight ty arms over the inner parser (the chain is
    FIRST-prefix-free: the eight heads — b, u, i, s, o, l, r, t — are
    pairwise distinct, the doctrine's predictive certificate). -/
def tyArms (inner : GParser Ty) : GParser Ty :=
  TextKit.orElse (atomArm "bool" .bool) $
  TextKit.orElse (atomArm "u64" .u64) $
  TextKit.orElse (atomArm "i64" .i64) $
  TextKit.orElse (atomArm "string" .string) $
  TextKit.orElse (unaryArm "option<" .option inner) $
  TextKit.orElse (unaryArm "list<" .list inner) $
  TextKit.orElse (binaryArm "result<" .result inner) $
  TextKit.orElse (binaryArm "tuple<" .tuple inner)
    (fun cur' => .error (curated cur' "expected a WIT type" tyValid))

/-- The ty parser: fuel-bounded nesting (the invariant `fuel ≥ the
    remaining characters` — every level consumes ≥ 1 before recursing);
    fuel 0 is the loud refusal. All arms fail at the cursor ⟹ the
    curated closed-world error; a DEEPER failure (a nested ty's curated
    error) is the farther — and more teaching — error, so it
    surfaces. -/
def tyP : Nat → GParser Ty
  | 0, cur => .error (curated cur "expected a WIT type" tyValid)
  | fuel + 1, cur =>
      match tyArms (tyP fuel) cur with
      | .ok r => .ok r
      | .error e =>
          if e.pos > cur.off then .error e
          else .error (curated cur "expected a WIT type" tyValid)

/-- An atom arm succeeds on its own keyword (maximal munch: the
    following character must be off the name charset). -/
theorem atomArm_self (kw : String) (s : Scalar) (off : Nat) (rest : List Char)
    (hr : rest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true) :
    atomArm kw s ⟨off, kw.toList ++ rest⟩ = .ok (Ty.atom s, ⟨off + kw.length, rest⟩) := by
  unfold atomArm
  rw [tok_self kw off rest]
  cases rest with
  | nil => rfl
  | cons c cs =>
      have hqc : (TextKit.isIdentChar c || c == '-') = false := by
        have h := hr
        rw [List.head?_cons] at h
        simpa using h
      simp only [List.head?_cons]
      rw [if_neg (by simp [hqc])]

/-- The `">"` and `", "` literal tokens, cons-form (the normalized
    face the arm lemmas consume). -/
theorem tok_gt (off : Nat) (rest : List Char) :
    TextKit.tok ">" ⟨off, '>' :: rest⟩ = .ok (">", ⟨off + 1, rest⟩) :=
  tok_self ">" off rest

theorem tok_comma (off : Nat) (rest : List Char) :
    TextKit.tok ", " ⟨off, ',' :: ' ' :: rest⟩ = .ok (", ", ⟨off + 2, rest⟩) :=
  tok_self ", " off rest

/-- A unary arm succeeds when the inner parser is correct (the bundled
    IH: the inner reads its type's rendering off any well-fueled
    tail): exactly, cursor included. -/
theorem unaryArm_self (openS : String) (k : Ty → Ty) (a : Ty) (inner : Nat → GParser Ty)
    (fuel off : Nat) (rest : List Char)
    (hlen : (openS ++ Render.ty a ++ ">").length + rest.length ≤ fuel + 1)
    (hos : 5 ≤ openS.length)
    (hinner : ∀ (gfuel goff : Nat) (grest : List Char),
        (Render.ty a).length + grest.length ≤ gfuel →
        grest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true →
        inner gfuel ⟨goff, (Render.ty a).toList ++ grest⟩
          = .ok (a, ⟨goff + (Render.ty a).length, grest⟩)) :
    unaryArm openS k (inner fuel) ⟨off, (openS ++ Render.ty a ++ ">").toList ++ rest⟩
      = .ok (k a, ⟨off + (openS ++ Render.ty a ++ ">").length, rest⟩) := by
  have h1 : (openS ++ Render.ty a ++ ">").length
      = openS.length + (Render.ty a).length + 1 := by
    rw [String.length_append, String.length_append]
    simp [show (">" : String).length = 1 from rfl]
  have hlen1 : (Render.ty a).length + (">".toList ++ rest).length ≤ fuel := by
    have h2 : (">".toList ++ rest).length = 1 + rest.length := by simp [Nat.add_comm]
    omega
  have hr1 : (">".toList ++ rest).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  unfold unaryArm
  simp only [String.toList_append, List.append_assoc]
  simp only [tok_self]
  simp only [hinner fuel (off + openS.length) (">".toList ++ rest) hlen1 hr1]
  simp only [tok_self]
  have hoff : off + openS.length + (Render.ty a).length + ">".length
      = off + (openS ++ Render.ty a ++ ">").length := by
    rw [h1, show (">" : String).length = 1 from rfl]
    omega
  rw [hoff]

/-- A binary arm succeeds when both inner parsers are correct (the
    bundled IH): exactly, cursor included. -/
theorem binaryArm_self (openS : String) (k : Ty → Ty → Ty) (a b : Ty)
    (inner : Nat → GParser Ty) (fuel off : Nat) (rest : List Char)
    (hlen : (openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length + rest.length ≤ fuel + 1)
    (hos : 5 ≤ openS.length)
    (hinner1 : ∀ (gfuel goff : Nat) (grest : List Char),
        (Render.ty a).length + grest.length ≤ gfuel →
        grest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true →
        inner gfuel ⟨goff, (Render.ty a).toList ++ grest⟩
          = .ok (a, ⟨goff + (Render.ty a).length, grest⟩))
    (hinner2 : ∀ (gfuel goff : Nat) (grest : List Char),
        (Render.ty b).length + grest.length ≤ gfuel →
        grest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true →
        inner gfuel ⟨goff, (Render.ty b).toList ++ grest⟩
          = .ok (b, ⟨goff + (Render.ty b).length, grest⟩)) :
    binaryArm openS k (inner fuel)
      ⟨off, (openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
      = .ok (k a b,
        ⟨off + (openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length, rest⟩) := by
  have h1 : (openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length
      = openS.length + (Render.ty a).length + 2 + (Render.ty b).length + 1 := by
    rw [String.length_append, String.length_append, String.length_append,
      String.length_append]
    simp [show (">" : String).length = 1 from rfl,
      show (", " : String).length = 2 from rfl]
  have hlen1 : (Render.ty a).length
      + (',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)).length ≤ fuel := by
    have h4 : ((Render.ty b).toList ++ '>' :: rest).length
        = (Render.ty b).length + 1 + rest.length := by
      rw [List.length_append, List.length_cons, String.length_toList]
      omega
    simp only [List.length_cons, List.length_append, String.length_toList]
    omega
  have hr1 : (',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  have hlen2 : (Render.ty b).length + ('>' :: rest).length ≤ fuel := by
    have h2 : ('>' :: rest).length = rest.length + 1 := rfl
    omega
  have hr2 : ('>' :: rest).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  unfold binaryArm
  have hnorm : ((openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest)
      = openS.toList
        ++ ((Render.ty a).toList ++ ',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)) := by
    simp [String.toList_append]
  rw [hnorm]
  simp only [tok_self]
  simp only [hinner1 fuel (off + openS.length) _ hlen1 hr1]
  simp only [tok_comma (off + openS.length + (Render.ty a).length) _]
  simp only [hinner2 fuel (off + openS.length + (Render.ty a).length + 2) _ hlen2 hr2]
  simp only [tok_gt (off + openS.length + (Render.ty a).length + 2 + (Render.ty b).length) rest]
  have hoff : off + openS.length + (Render.ty a).length + 2 + (Render.ty b).length + 1
      = off + (openS ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length := by
    rw [h1]; omega
  rw [hoff]

/-- An atom arm misses when the input's head differs from its
    keyword's head (the token refusal, the curated set untouched). -/
theorem atomArm_miss (kw : String) (s : Scalar) (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ kw.toList.head?) (hk : kw ≠ "") :
    atomArm kw s ⟨off, cs⟩ = .error (tokErr off kw) := by
  unfold atomArm tokErr
  rw [tok_miss kw off cs hne hk]

/-- A unary arm misses when the input's head differs from its
    opener's head (the inner parser is never reached). -/
theorem unaryArm_miss (openS : String) (k : Ty → Ty) (inner : GParser Ty)
    (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ openS.toList.head?) (hk : openS ≠ "") :
    unaryArm openS k inner ⟨off, cs⟩ = .error (tokErr off openS) := by
  unfold unaryArm tokErr
  rw [tok_miss openS off cs hne hk]

/-- A binary arm misses when the input's head differs from its
    opener's head (the inner parser is never reached). -/
theorem binaryArm_miss (openS : String) (k : Ty → Ty → Ty) (inner : GParser Ty)
    (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ openS.toList.head?) (hk : openS ≠ "") :
    binaryArm openS k inner ⟨off, cs⟩ = .error (tokErr off openS) := by
  unfold binaryArm tokErr
  rw [tok_miss openS off cs hne hk]

/-! ### the ty zone's ok law (the lexeme's print_scan base) -/

theorem scalar_bool : Render.scalar .bool = "bool" := rfl
theorem scalar_u64 : Render.scalar .u64 = "u64" := rfl
theorem scalar_i64 : Render.scalar .i64 = "i64" := rfl
theorem scalar_string : Render.scalar .string = "string" := rfl

theorem ty_atom (s : Scalar) : Render.ty (.atom s) = Render.scalar s := rfl
theorem ty_option (a : Ty) : Render.ty (.option a) = "option<" ++ Render.ty a ++ ">" := rfl
theorem ty_list (a : Ty) : Render.ty (.list a) = "list<" ++ Render.ty a ++ ">" := rfl
theorem ty_result (a b : Ty) :
    Render.ty (.result a b) = "result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">" := rfl
theorem ty_tuple (a b : Ty) :
    Render.ty (.tuple a b) = "tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">" := rfl

/-- The ok direction for the ty parser: the rendering of any `Ty`
    parses back to exactly it, consuming exactly its bytes (the fuel
    invariant: the fuel covers the remaining characters). -/
theorem tyP_ok (t : Ty) :
    ∀ (fuel off : Nat) (rest : List Char),
      (Render.ty t).length + rest.length ≤ fuel →
      rest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true →
      tyP fuel ⟨off, (Render.ty t).toList ++ rest⟩
        = .ok (t, ⟨off + (Render.ty t).length, rest⟩) := by
  induction t with
  | atom s =>
      intro fuel off rest hlen hr
      cases fuel with
      | zero =>
          cases s with
          | bool => rw [ty_atom, scalar_bool] at hlen; simp at hlen
          | u64 => rw [ty_atom, scalar_u64] at hlen; simp at hlen
          | i64 => rw [ty_atom, scalar_i64] at hlen; simp at hlen
          | string => rw [ty_atom, scalar_string] at hlen; simp at hlen
      | succ f =>
          cases s with
          | bool =>
              rw [ty_atom, scalar_bool]
              simp only [tyP, tyArms]
              rw [orElse_ok_left (atomArm_self "bool" .bool off rest hr)]
          | u64 =>
              rw [ty_atom, scalar_u64]
              simp only [tyP, tyArms]
              have hf1 : atomArm "bool" .bool ⟨off, "u64".toList ++ rest⟩
                  = .error (tokErr off "bool") :=
                atomArm_miss "bool" .bool off _ (by simp) (by decide)
              rw [orElse_ok_right hf1
                (orElse_ok_left (atomArm_self "u64" .u64 off rest hr))]
          | i64 =>
              rw [ty_atom, scalar_i64]
              simp only [tyP, tyArms]
              have hf1 : atomArm "bool" .bool ⟨off, "i64".toList ++ rest⟩
                  = .error (tokErr off "bool") :=
                atomArm_miss "bool" .bool off _ (by simp) (by decide)
              have hf2 : atomArm "u64" .u64 ⟨off, "i64".toList ++ rest⟩
                  = .error (tokErr off "u64") :=
                atomArm_miss "u64" .u64 off _ (by simp) (by decide)
              rw [orElse_ok_right hf1 (orElse_ok_right hf2
                (orElse_ok_left (atomArm_self "i64" .i64 off rest hr)))]
          | string =>
              rw [ty_atom, scalar_string]
              simp only [tyP, tyArms]
              have hf1 : atomArm "bool" .bool ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "bool") :=
                atomArm_miss "bool" .bool off _ (by simp) (by decide)
              have hf2 : atomArm "u64" .u64 ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "u64") :=
                atomArm_miss "u64" .u64 off _ (by simp) (by decide)
              have hf3 : atomArm "i64" .i64 ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "i64") :=
                atomArm_miss "i64" .i64 off _ (by simp) (by decide)
              rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
                (orElse_ok_left (atomArm_self "string" .string off rest hr))))]
  | option a ih =>
      intro fuel off rest hlen hr
      rw [ty_option] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_left
              (unaryArm_self "option<" Ty.option a tyP f off rest hlen (by decide) ih)))))]
  | list a ih =>
      intro fuel off rest hlen hr
      rw [ty_list] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_left
              (unaryArm_self "list<" Ty.list a tyP f off rest hlen (by decide) ih))))))]
  | result a b iha ihb =>
      intro fuel off rest hlen hr
      rw [ty_result] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_left (binaryArm_self "result<" Ty.result a b tyP f off rest hlen
                (by decide) iha ihb)))))))]
  | tuple a b iha ihb =>
      intro fuel off rest hlen hr
      rw [ty_tuple] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : binaryArm "result<" Ty.result (tyP f) ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            binaryArm_miss "result<" Ty.result (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_left
                (binaryArm_self "tuple<" Ty.tuple a b tyP f off rest hlen (by decide) iha ihb))))))))]

/-! ## comments (the artifact of record's two header lines) -/

/-- Consume through the next newline (an unterminated tail consumes
    everything — the bytes are then refused downstream as a malformed
    package). Structural on the list. -/
def skipToNewline : List Char → List Char
  | '\n' :: rest => rest
  | _ :: rest => skipToNewline rest
  | [] => []

/-- Drop the leading `//` comment lines (ALL of them — the artifact
    of record carries two). Fuel-structural: each strip consumes at
    least the four bytes `//` + a line's first char + the newline, so
    `fuel = length` is always sufficient. -/
def skipCommentsGo : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, '/' :: '/' :: rest => skipCommentsGo fuel (skipToNewline rest)
  | _ + 1, cs => cs

/-- Drop the leading `//` comment lines. -/
def skipComments (cs : List Char) : List Char :=
  skipCommentsGo cs.length cs

/-- The go-loop's refusal face: a head off `/` is a comment-free tail
    (the package text's own head). -/
theorem skipCommentsGo_ne (fuel : Nat) (c : Char) (cs : List Char)
    (h : (c == '/') = false) :
    skipCommentsGo (fuel + 1) (c :: cs) = c :: cs := by
  refine skipCommentsGo.eq_3 _ _ ?_
  intro rest heq
  simp only [List.cons.injEq] at heq
  exact absurd heq.1 (fun hc => by rw [hc] at h; simp at h)

/-- The comment-stripped bytes of a text (the canonicalization law's
    byte-side function). -/
def stripComments (s : String) : String :=
  String.ofList (skipComments s.toList)

theorem L_pkg : "package ".toList
    = 'p' :: 'a' :: 'c' :: 'k' :: 'a' :: 'g' :: 'e' :: ' ' :: [] := rfl

/-- The package text is comment-free (its head is `package `, never
    `//` — the strip is the identity on the renderer's image). -/
theorem skipComments_package_sfx (sfx : List Char) :
    skipComments ("package ".toList ++ sfx) = "package ".toList ++ sfx := by
  show skipCommentsGo ("package ".toList ++ sfx).length
    ("package ".toList ++ sfx) = _
  have hl : ("package ".toList ++ sfx).length = (sfx.length + 7) + 1 := by
    rw [List.length_append, L_pkg]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hl, L_pkg, List.cons_append]
  exact skipCommentsGo_ne (sfx.length + 7) 'p' _ rfl

/-! ## the AST-side wellformedness (the round trip's side condition) -/

/-- A WIT name is identifier-shaped (the name lexeme's byte-side gate). -/
def witNameOk (s : String) : Bool := identOk nameChar s

/-- The package-id discipline. -/
def witIdOk (s : String) : Bool := identOk idChar s

/-- The AST-side wellformedness the round-trip laws ride: every name —
    the id, interface names, record names, field names — is
    identifier-shaped. The closed `Ty` grammar needs no gate (a
    malformed type shape is unconstructible). -/
def WitOk (p : Package) : Bool :=
  witIdOk p.id
    && p.interfaces.all (fun i =>
      witNameOk i.name
        && i.records.all (fun r =>
          witNameOk r.name && r.fields.all (fun f => witNameOk f.name)))

/-- The AST-side gate's membership form (the round-trip's side
    condition, unpacked). -/
theorem WitOk_spec (p : Package) (h : WitOk p = true) :
    witIdOk p.id = true
      ∧ (∀ i ∈ p.interfaces, witNameOk i.name = true
          ∧ (∀ r ∈ i.records, witNameOk r.name = true
              ∧ (∀ f ∈ r.fields, witNameOk f.name = true))) := by
  unfold WitOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hid, hinters⟩ := h
  refine ⟨hid, fun i hi => ?_⟩
  have h1 := List.all_eq_true.mp hinters i hi
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨h2, fun r hr => ?_⟩
  have h4 := List.all_eq_true.mp h3 r hr
  simp only [Bool.and_eq_true] at h4
  obtain ⟨h5, h6⟩ := h4
  exact ⟨h5, fun f hf => List.all_eq_true.mp h6 f hf⟩

/-! ## the lexemes (the shared constructors + the bridges) -/

/-- The head class rides the run class (the ident-atom's chain
    premise): WIT's names are alpha-led. -/
theorem nameChar_chain (c : Char) (h : c.isAlpha = true) : nameChar c = true := by
  simp [nameChar, TextKit.isIdentChar, h]

theorem idChar_chain (c : Char) (h : c.isAlpha = true) : idChar c = true := by
  simp [idChar, nameChar, TextKit.isIdentChar, h]

open TextKit in
/-- The keyword/separator literals (the format's hard delimiters): the
    shared const-string lexeme (TextKit.Grammar.Lexemes' `constStrLex`)
    at the format's concrete spellings — nonempty by `decide`. -/
def litAtom (s : String) (hs : s.toList ≠ []) : TextKit.Lexeme Unit :=
  TextKit.constStrLex s hs

/-- The name lexeme: the shared ident-atom over WIT's charset (the
    kebab `-` rides the run class). -/
def nameAtom : TextKit.Lexeme String :=
  TextKit.identAtom "<name>" Char.isAlpha nameChar nameChar_chain

/-- The package-id lexeme: the same atom over the id charset (`:`
    rides the run class). -/
def idAtom : TextKit.Lexeme String :=
  TextKit.identAtom "<package-id>" Char.isAlpha idChar idChar_chain

/-- The bridge: the AST-side name gate IS the name lexeme's write-side
    gate (the valueOk discipline and `WitOk` are ONE function). -/
theorem witNameOk_eq (s : String) : witNameOk s = nameAtom.pre s := by
  unfold witNameOk identOk nameAtom TextKit.identAtom TextKit.identOk
  cases hs : s.toList with
  | nil => simp [hs]
  | cons c w =>
      simp only [hs, List.isEmpty_cons, List.head?_cons, Option.all_some]
      cases hca : c.isAlpha with
      | true => simp [nameChar, TextKit.isIdentChar, hca]
      | false => simp [hca]

/-- The bridge: the id gate IS the id lexeme's write-side gate. -/
theorem witIdOk_eq (s : String) : witIdOk s = idAtom.pre s := by
  unfold witIdOk identOk idAtom TextKit.identAtom TextKit.identOk
  cases hs : s.toList with
  | nil => simp [hs]
  | cons c w =>
      simp only [hs, List.isEmpty_cons, List.head?_cons, Option.all_some]
      cases hca : c.isAlpha with
      | true => simp [idChar, nameChar, TextKit.isIdentChar, hca]
      | false => simp [hca]

/-! ## the ty-zone's head-fail kit (the ty lexeme's head_fail base) -/

/-- A token whose keyword's head passes the ident class misses any
    input whose head fails it (the eight ty arms' shared miss — THE
    CITATION: the generic kit's `TextKit.tok_miss_of_headFail`, the
    format-independent miss direction proved once in TextKit.Grammar). -/
theorem tok_miss_of_head_fail (kw : String) (off : Nat) (cs : List Char)
    (hk : kw.toList.head?.any TextKit.isIdentChar = true)
    (hh : cs.head?.all (fun c => !TextKit.isIdentChar c) = true) :
    ∃ e, TextKit.tok kw ⟨off, cs⟩ = .error e :=
  TextKit.tok_miss_of_headFail kw ⟨off, cs⟩ hk hh

/-- The ty-arms chain's failure: every arm's leading token misses, so
    the whole chain refuses (THE CITATION: the chain's spine is the
    generic kit's `TextKit.orElseChain_err` — the per-arm refusal is
    the token miss above; the nested-orElse chain IS the fold). -/
theorem tyArms_fail (inner : GParser Ty) (cur : Cursor)
    (hh : cur.cs.head?.all (fun c => !TextKit.isIdentChar c) = true) :
    ∃ e, tyArms inner cur = .error e := by
  have hkw : ∀ kw : String, kw.toList.head?.any TextKit.isIdentChar = true →
      ∃ e, TextKit.tok kw cur = .error e :=
    fun kw hk => tok_miss_of_head_fail kw cur.off cur.cs hk hh
  have harm : ∀ p ∈ [atomArm "bool" .bool, atomArm "u64" .u64,
        atomArm "i64" .i64, atomArm "string" .string,
        unaryArm "option<" .option inner, unaryArm "list<" .list inner,
        binaryArm "result<" .result inner, binaryArm "tuple<" .tuple inner],
      ∃ e, p cur = .error e := by
    intro p hp
    simp only [List.mem_cons] at hp
    obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hp := hp
    · obtain ⟨e, he⟩ := hkw "bool" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [atomArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "u64" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [atomArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "i64" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [atomArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "string" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [atomArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "option<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [unaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "list<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [unaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "result<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [binaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "tuple<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [binaryArm, he]⟩
    · exact absurd hp (by simp)
  exact TextKit.orElseChain_err _ _ cur harm
    ⟨curated cur "expected a WIT type" tyValid, rfl⟩

/-- The ty parser's head-fail face: an input whose head fails the
    ident class never parses (the tyAtom's `head_fail` base). -/
theorem tyP_head_fail (fuel : Nat) (cur : Cursor)
    (hh : cur.cs.head?.all (fun c => !TextKit.isIdentChar c) = true) :
    ∃ e, tyP fuel cur = .error e := by
  cases fuel with
  | zero => exact ⟨_, rfl⟩
  | succ f =>
      cases hb : tyArms (tyP f) cur with
      | error e =>
          by_cases hcmp : e.pos > cur.off
          · exact ⟨e, by simp only [tyP, hb, if_pos hcmp]⟩
          · exact ⟨curated cur "expected a WIT type" tyValid, by
              simp only [tyP, hb, if_neg hcmp]⟩
      | ok r =>
          exfalso
          obtain ⟨e2, he2⟩ := tyArms_fail (tyP f) cur hh
          rw [hb] at he2
          simp at he2

/-! ## the ty token — the guarded leaf (the hand recursion's grammar face) -/

/-- The ty token's rendering starts with an identifier character (the
    keyword's head letter). -/
theorem tyText_head_isIdent (t : Ty) :
    (Render.ty t).toList.head?.any TextKit.isIdentChar = true := by
  cases t with
  | atom s => cases s <;> simp [Render.ty, Render.scalar, TextKit.isIdentChar]
  | option a => simp [Render.ty, TextKit.isIdentChar]
  | list a => simp [Render.ty, TextKit.isIdentChar]
  | result a b => simp [Render.ty, TextKit.isIdentChar]
  | tuple a b => simp [Render.ty, TextKit.isIdentChar]

/-- The ty token's rendering is nonempty (every spelling is
    keyword-led). -/
theorem tyText_ne_nil (t : Ty) : (Render.ty t).toList ≠ [] := by
  intro hcon
  have hh := tyText_head_isIdent t
  rw [hcon] at hh
  simp at hh

/-- A take of a cons-list equaling a list identifies the heads (the
    scan-head's extraction). -/
theorem take_eq_head {n : Nat} {c : Char} {cs l : List Char}
    (heq : (c :: cs).take n = l) (hl : l ≠ []) :
    (c :: cs).head? = l.head? := by
  cases hn : n with
  | zero =>
      rw [hn] at heq
      have h0 : List.take 0 (c :: cs) = ([] : List Char) := rfl
      rw [h0] at heq
      exact absurd heq.symm hl
  | succ m =>
      rw [hn] at heq
      rw [show (c :: cs).take (m + 1) = c :: cs.take m from rfl] at heq
      rw [← heq]
      simp

/-- The ty token's scan: the hand `tyP` over the FULL remaining input,
    GUARDED to the canonical spelling (the consumed prefix must BE
    `Render.ty` of its result — Snapshot.lean's guarded-wrap pattern;
    the guard makes `scan_exact` hold by pure take/drop algebra, no
    canonicality theorem over `tyP` needed). The guard never fires on
    the renderer's image — the accepted language is unchanged. -/
def tyScan : GParser Ty := fun cur =>
  match tyP cur.cs.length cur with
  | .error e => .error e
  | .ok (t, _) =>
      if cur.cs.take (Render.ty t).length = (Render.ty t).toList then
        .ok (t, ⟨cur.off + (Render.ty t).length, cur.cs.drop (Render.ty t).length⟩)
      else
        .error { ParseError.base cur.off [] with
                 message := s!"non-canonical WIT type spelling — the token is not \
the canonical text of `{Render.ty t}`" }

/-- The scan's success shape (the guard's extraction): the cursor
    splits at the CANONICAL spelling's boundary. -/
theorem tyScan_ok {cur : Cursor} {t : Ty} {cur' : Cursor}
    (h : tyScan cur = .ok (t, cur')) :
    cur.cs.take (Render.ty t).length = (Render.ty t).toList ∧
    cur'.cs = cur.cs.drop (Render.ty t).length ∧
    cur'.off = cur.off + (Render.ty t).length := by
  simp only [tyScan] at h
  cases hp : tyP cur.cs.length cur with
  | error e => rw [hp] at h; simp at h
  | ok r =>
      obtain ⟨a, b⟩ := r
      simp only [hp] at h
      by_cases hguard : cur.cs.take (Render.ty a).length = (Render.ty a).toList
      · rw [if_pos hguard] at h
        obtain ⟨hab, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
        cases hab
        exact ⟨hguard, (Cursor.mk.inj hcc).2.symm, (Cursor.mk.inj hcc).1.symm⟩
      · rw [if_neg hguard] at h
        simp at h

/-- THE ty lexeme: the hand recursion as a leaf — `print` is
    `Render.ty`, the scan is the guarded `tyP`, `head` the ident-char
    class (every spelling is keyword-led), `munch` the name-char class
    (the maximal-munch boundary — a `u64` followed by `x` refuses,
    `tyP`'s own atom gate). -/
def tyAtom : TextKit.Lexeme Ty where
  scan := tyScan
  print := Render.ty
  pre := fun _ => true
  head := .cls TextKit.isIdentChar
  munch := Option.some nameChar
  scan_post := fun _ _ _ _ => rfl
  scan_exact := by
    intro cur t cur' h
    obtain ⟨h1, h2, -⟩ := tyScan_ok h
    show cur.cs = (Render.ty t).toList ++ cur'.cs
    rw [h2, ← h1, List.take_append_drop]
  scan_off := by
    intro cur t cur' h
    obtain ⟨-, -, h3⟩ := tyScan_ok h
    exact h3
  scan_head := by
    intro cur t cur' h
    obtain ⟨h1, -, -⟩ := tyScan_ok h
    show cur.cs.head?.any TextKit.isIdentChar = true
    cases hcs : cur.cs with
    | nil =>
        have h2 : (Render.ty t).toList = [] := by
          rw [← h1, hcs]
          simp
        exact absurd h2 (tyText_ne_nil t)
    | cons c cs =>
        rw [hcs] at h1
        have hhd := take_eq_head h1 (tyText_ne_nil t)
        show (c :: cs).head?.any TextKit.isIdentChar = true
        rw [hhd]
        exact tyText_head_isIdent t
  head_fail := by
    intro cur h
    have h3 : cur.cs.head?.all (fun c => !TextKit.isIdentChar c) = true := by
      cases hcs : cur.cs with
      | nil => simp
      | cons c cs =>
          have hc : TextKit.isIdentChar c = false := by
            have h4 : cur.cs.head?.any TextKit.isIdentChar = false := h
            rw [hcs] at h4
            simpa using h4
          simp [hc]
    obtain ⟨e, he⟩ := tyP_head_fail cur.cs.length cur h3
    refine ⟨e, ?_⟩
    show tyScan cur = _
    simp only [tyScan, he]
  print_scan := by
    intro k t sfx _ hmunch
    have h1 : ((Render.ty t).toList ++ sfx).length
        = (Render.ty t).length + sfx.length := by
      rw [List.length_append, String.length_toList]
    show tyScan ⟨k, (Render.ty t).toList ++ sfx⟩
      = .ok (t, ⟨k + (Render.ty t).length, sfx⟩)
    simp only [tyScan, h1,
      tyP_ok t ((Render.ty t).length + sfx.length) k sfx (by omega) hmunch]
    rw [if_pos (by rw [String.length_toList.symm]; exact List.take_left),
      String.length_toList.symm, List.drop_left]
  consumes := by
    intro cur t cur' h
    obtain ⟨h1, h2, -⟩ := tyScan_ok h
    have hsplit : cur.cs
        = cur.cs.take (Render.ty t).length ++ cur.cs.drop (Render.ty t).length :=
      (List.take_append_drop _ _).symm
    rw [h1, ← h2] at hsplit
    rw [hsplit, List.length_append, String.length_toList]
    have hl : 0 < (Render.ty t).toList.length := by
      cases hr : (Render.ty t).toList with
      | nil => exact absurd hr (tyText_ne_nil t)
      | cons c cs => simp
    have hl2 : 0 < (Render.ty t).length := by rw [String.length_toList.symm]; exact hl
    omega
  head_ne := rfl

/-! ## the raws + the codec (the ONE rel node's semantic mapping) -/

/-- A field's raw parse shape: the indent, the name, the `: `, the ty
    token, the comma (the seq-spine tuple). -/
abbrev FieldRaw := Unit × (String × (Unit × (Ty × Unit)))

/-- The fields' raw: the blank-line dam (the empty record's `\n` —
    `some` iff the record has NO fields) + the field LINES, each the
    field's bytes PLUS its trailing newline (the renderer's byte-stream:
    `fieldsJoin` separates the fields by a LEADING `\n` on the
    continuations and the record appends `"\n  }\n"` — the SAME stream
    read as trailing newlines + a `"  }\n"` closer; the trailing-
    delimiter discipline is what the engine's head-disjoint FIRST rows
    demand — the leading-`\n` reading fails WF-SEQ-1 at the fields/
    closer junction: the continuation's `\n` head collides with the
    closer's `\n` head, and the engine's `HeadSpec` FIRST sets are
    head-only). -/
abbrev FieldsRaw := Option Unit × List (FieldRaw × Unit)

/-- A record's raw: the `  record ` marker, the name, ` {\n`, the
    field block, `  }\n`. -/
abbrev RecordRaw := Unit × (String × (Unit × (FieldsRaw × Unit)))

/-- An interface's raw: the `interface ` marker, the name, ` {\n`, the
    record blocks, `}\n`. -/
abbrev InterfaceRaw := Unit × (String × (Unit × (List RecordRaw × Unit)))

/-- The package's raw: `package `, the id, `;\n\n`, the interface
    blocks. -/
abbrev PkgRaw := Unit × (String × (Unit × List InterfaceRaw))

def fieldToRaw (f : Field) : FieldRaw := ((), (f.name, ((), (f.ty, ()))))

def fieldOfRaw : FieldRaw → Field
  | (_, (n, (_, (t, _)))) => ⟨n, t⟩

def fieldsToRaw : List Field → FieldsRaw
  | [] => (Option.some (), [])
  | f :: fs => (Option.none, (fieldToRaw f, ()) :: fs.map (fun g => (fieldToRaw g, ())))

/-- The field lines' decode (every line's shape is fixed; no bits). -/
def linesOfRaws : List (FieldRaw × Unit) → Option (List Field)
  | [] => Option.some []
  | (fr, ()) :: rest => (linesOfRaws rest).map (fun l => fieldOfRaw fr :: l)

/-- The fields' decode: the dam's bit is CHECKED (the `some` dam with
    nonempty lines — the blank-line-then-field text — is refused; that
    text's `none`-dam reading is what the pre-grammar parser refused
    too, so the accepted language is unchanged). The bits carry no
    value information beyond the empty/nonempty discipline — the check
    is the `exact` law's honesty, dead at the renderer's image. -/
def fieldsOfRaws : FieldsRaw → Option (List Field)
  | (Option.none, []) => Option.none
  | (Option.none, lines) => linesOfRaws lines
  | (Option.some (), []) => Option.some []
  | (Option.some (), _ :: _) => Option.none

def recordToRaw (r : Record) : RecordRaw :=
  ((), (r.name, ((), (fieldsToRaw r.fields, ()))))

/-- A record's decode: the field names' nodup is DECIDED here — a
    duplicate field name is the loud refusal (the runtime route of the
    elaboration-level `by decide` default), never a silent
    acceptance. -/
def recordOfRaw : RecordRaw → Option Record
  | (_, (n, (_, (fr, _)))) =>
      match fieldsOfRaws fr with
      | Option.some fs =>
          if hnd : (fs.map Field.name).Nodup then
            Option.some { name := n, fields := fs, fields_nodup := hnd }
          else Option.none
      | Option.none => Option.none

def recordsToRaw (rs : List Record) : List RecordRaw := rs.map recordToRaw

def recordsOfRaws : List RecordRaw → Option (List Record)
  | [] => Option.some []
  | rr :: rest =>
      match recordOfRaw rr with
      | Option.some r => (recordsOfRaws rest).map (fun l => r :: l)
      | Option.none => Option.none

def ifaceToRaw (i : Interface) : InterfaceRaw :=
  ((), (i.name, ((), (List.map recordToRaw i.records, ()))))

/-- An interface's decode: the record names' nodup is DECIDED here
    (the record-level route, one level up). -/
def ifaceOfRaw : InterfaceRaw → Option Interface
  | (_, (n, (_, (rs, _)))) =>
      match recordsOfRaws rs with
      | Option.some rcds =>
          if hnd : (rcds.map Record.name).Nodup then
            Option.some { name := n, records := rcds, records_nodup := hnd }
          else Option.none
      | Option.none => Option.none

def ifacesToRaw (is : List Interface) : List InterfaceRaw := List.map ifaceToRaw is

def ifacesOfRaws : List InterfaceRaw → Option (List Interface)
  | [] => Option.some []
  | ir :: rest =>
      match ifaceOfRaw ir with
      | Option.some i => (ifacesOfRaws rest).map (fun l => i :: l)
      | Option.none => Option.none

def packageToRaw (p : Package) : PkgRaw :=
  ((), (p.id, ((), List.map ifaceToRaw p.interfaces)))

/-- The package's decode: the interface list has no nodup gate (the
    carrier's honest gap — `Wit`'s header), so this is a pure map. -/
def packageOfRaw : PkgRaw → Option Package
  | (_, (id, ((), is))) => (ifacesOfRaws is).map (fun l => { id := id, interfaces := l })

/-! ### the codec's laws (the rel node's decode_encode + exact fields) -/

theorem fieldOfRaw_toRaw (f : Field) : fieldOfRaw (fieldToRaw f) = f := rfl

theorem fieldToRaw_fieldOfRaw : ∀ (fr : FieldRaw), fieldToRaw (fieldOfRaw fr) = fr
  | ((), (n, ((), (t, ())))) => rfl

theorem linesOfRaws_map : ∀ (fs : List Field),
    linesOfRaws (fs.map (fun g => (fieldToRaw g, ()))) = Option.some fs
  | [] => rfl
  | g :: gs => by
      simp only [List.map_cons, linesOfRaws]
      rw [linesOfRaws_map gs, Option.map_some, fieldOfRaw_toRaw]

theorem linesOfRaws_exact : ∀ (raws : List (FieldRaw × Unit)) (fs : List Field),
    linesOfRaws raws = Option.some fs →
    fs.map (fun g => (fieldToRaw g, ())) = raws
  | [], fs, h => by
      simp only [linesOfRaws, Option.some.injEq] at h
      subst h
      rfl
  | (fr, ()) :: rest, fs, h => by
      simp only [linesOfRaws, Option.map_some, Option.some.injEq] at h
      cases hrc : linesOfRaws rest with
      | none => rw [hrc] at h; simp at h
      | some fs' =>
          rw [hrc] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h, List.map_cons, fieldToRaw_fieldOfRaw,
            linesOfRaws_exact rest fs' hrc]

theorem fieldsOfRaws_toRaw : ∀ (fs : List Field),
    fieldsOfRaws (fieldsToRaw fs) = Option.some fs
  | [] => rfl
  | f :: fs => by
      show fieldsOfRaws (Option.none, (fieldToRaw f, ()) :: List.map (fun g => (fieldToRaw g, ())) fs)
        = Option.some (f :: fs)
      simp only [fieldsOfRaws, List.map_cons, linesOfRaws, Option.map_some,
        fieldOfRaw_toRaw, linesOfRaws_map]

theorem fieldsOfRaws_exact : ∀ (fr : FieldsRaw) (fs : List Field),
    fieldsOfRaws fr = Option.some fs → fieldsToRaw fs = fr := by
  intro fr
  obtain ⟨dam, lines⟩ := fr
  cases dam with
  | none =>
      intro fs h
      simp only [fieldsOfRaws] at h
      cases lines with
      | nil => exact absurd h (by simp)
      | cons l ls =>
          obtain ⟨fr, u⟩ := l
          cases u
          simp only [fieldsOfRaws, linesOfRaws, Option.map_some, Option.some.injEq] at h
          cases hlc : linesOfRaws ls with
          | none => rw [hlc] at h; simp at h
          | some fs' =>
              rw [hlc] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              show (Option.none, (fieldToRaw (fieldOfRaw fr), ())
                    :: List.map (fun g => (fieldToRaw g, ())) fs')
                  = (Option.none, (fr, ()) :: ls)
              rw [linesOfRaws_exact ls fs' hlc, fieldToRaw_fieldOfRaw]
  | some u =>
      cases u
      intro fs h
      simp only [fieldsOfRaws] at h
      cases lines with
      | nil =>
          simp only [Option.some.injEq] at h
          subst h
          rfl
      | cons l ls => simp at h

theorem recordOfRaw_toRaw : ∀ (r : Record), recordOfRaw (recordToRaw r) = Option.some r := by
  intro r
  obtain ⟨n, fs, hnd⟩ := r
  simp only [recordToRaw, recordOfRaw, fieldsOfRaws_toRaw]
  exact dif_pos hnd

theorem recordOfRaw_exact : ∀ (rr : RecordRaw) (r : Record),
    recordOfRaw rr = Option.some r → recordToRaw r = rr := by
  intro rr
  cases rr with
  | mk u pair =>
      obtain ⟨n, pair2⟩ := pair
      obtain ⟨u2, fr, _⟩ := pair2
      cases u; cases u2
      intro r h
      simp only [recordOfRaw, Option.some.injEq] at h
      cases hf : fieldsOfRaws fr with
      | none => rw [hf] at h; simp at h
      | some fs =>
          rw [hf] at h
          simp only [Option.map_some, Option.some.injEq] at h
          by_cases hnd : (fs.map Field.name).Nodup
          · rw [dif_pos hnd] at h
            cases h
            show ((), (n, ((), (fieldsToRaw fs, ())))) = _
            rw [fieldsOfRaws_exact fr fs hf]
          · rw [dif_neg hnd] at h
            cases h

theorem recordsOfRaws_exact : ∀ (raws : List RecordRaw) (rs : List Record),
    recordsOfRaws raws = Option.some rs → rs.map recordToRaw = raws
  | [], rs, h => by
      simp only [recordsOfRaws, Option.some.injEq] at h
      subst h
      rfl
  | rr :: rest, rs, h => by
      simp only [recordsOfRaws, Option.map_some, Option.some.injEq] at h
      cases hrr : recordOfRaw rr with
      | none => rw [hrr] at h; simp at h
      | some r =>
          rw [hrr] at h
          cases hrs : recordsOfRaws rest with
          | none => rw [hrs] at h; simp at h
          | some rs' =>
              rw [hrs] at h
              simp only [Option.map_some, Option.some.injEq] at h
              rw [← h, List.map_cons, recordOfRaw_exact rr r hrr,
                recordsOfRaws_exact rest rs' hrs]

theorem recordsOfRaws_map : ∀ (rs : List Record),
    recordsOfRaws (List.map recordToRaw rs) = Option.some rs
  | [] => rfl
  | r :: rs => by
      show recordsOfRaws (recordToRaw r :: List.map recordToRaw rs) = _
      simp only [recordsOfRaws, recordOfRaw_toRaw]
      rw [recordsOfRaws_map rs, Option.map_some]

theorem ifaceOfRaw_exact : ∀ (ir : InterfaceRaw) (i : Interface),
    ifaceOfRaw ir = Option.some i → ifaceToRaw i = ir := by
  intro ir
  cases ir with
  | mk u pair =>
      obtain ⟨n, pair2⟩ := pair
      obtain ⟨u2, rs, _⟩ := pair2
      cases u; cases u2
      intro i h
      simp only [ifaceOfRaw, Option.some.injEq] at h
      cases hrs : recordsOfRaws rs with
      | none => rw [hrs] at h; simp at h
      | some rcds =>
          rw [hrs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          by_cases hnd : (rcds.map Record.name).Nodup
          · rw [dif_pos hnd] at h
            cases h
            show ((), (n, ((), (List.map recordToRaw rcds, ())))) = _
            rw [recordsOfRaws_exact rs rcds hrs]
          · rw [dif_neg hnd] at h
            cases h

theorem ifaceOfRaw_toRaw (i : Interface) : ifaceOfRaw (ifaceToRaw i) = Option.some i := by
  obtain ⟨n, rs, hnd⟩ := i
  simp only [ifaceToRaw, ifaceOfRaw, recordsOfRaws_map]
  exact dif_pos hnd

theorem ifacesOfRaws_exact : ∀ (raws : List InterfaceRaw) (is : List Interface),
    ifacesOfRaws raws = Option.some is → is.map ifaceToRaw = raws
  | [], is, h => by
      simp only [ifacesOfRaws, Option.some.injEq] at h
      subst h
      rfl
  | ir :: rest, is, h => by
      simp only [ifacesOfRaws, Option.some.injEq] at h
      cases hir : ifaceOfRaw ir with
      | none => rw [hir] at h; simp at h
      | some i =>
          rw [hir] at h
          cases hrest : ifacesOfRaws rest with
          | none => rw [hrest] at h; simp at h
          | some is' =>
              rw [hrest] at h
              simp only [Option.map_some, Option.some.injEq] at h
              rw [← h, List.map_cons, ifaceOfRaw_exact ir i hir,
                ifacesOfRaws_exact rest is' hrest]

theorem ifacesOfRaws_map : ∀ (is : List Interface),
    ifacesOfRaws (List.map ifaceToRaw is) = Option.some is
  | [] => rfl
  | i :: is => by
      show ifacesOfRaws (ifaceToRaw i :: List.map ifaceToRaw is) = _
      simp only [ifacesOfRaws, ifaceOfRaw_toRaw]
      rw [ifacesOfRaws_map is, Option.map_some]

theorem packageCodec_decode_encode (p : Package) :
    packageOfRaw (packageToRaw p) = Option.some p := by
  obtain ⟨id, is⟩ := p
  show Option.map
      (fun l => ({ id := id, interfaces := l } : Package))
      (ifacesOfRaws (List.map ifaceToRaw is)) = Option.some ⟨id, is⟩
  simp only [ifacesOfRaws_map, Option.map_some]

theorem packageToRaw_of : ∀ (raw : PkgRaw) (p : Package),
    packageOfRaw raw = Option.some p → packageToRaw p = raw := by
  intro raw
  cases raw with
  | mk u pair =>
      obtain ⟨id, pair2⟩ := pair
      obtain ⟨u2, is⟩ := pair2
      cases u; cases u2
      intro p h
      simp only [packageOfRaw, Option.map_some, Option.some.injEq] at h
      cases his : ifacesOfRaws is with
      | none => rw [his] at h; simp at h
      | some isl =>
          rw [his] at h
          simp only [Option.map_some, Option.some.injEq] at h
          cases h
          show ((), (id, ((), List.map ifaceToRaw isl))) = _
          rw [ifacesOfRaws_exact is isl his]

/-! ## the grammar + the certificate -/

open TextKit in
/-- One field's bytes: the indent, the name, `: `, the ty token, the
    comma (the renderer's `Render.field`). -/
def fieldG : TextKit.Grammar FieldRaw :=
  .seq (.atom (litAtom "    " (by decide)))
    (.seq (.atom nameAtom)
      (.seq (.atom (litAtom ": " (by decide)))
        (.seq (.atom tyAtom)
          (.atom (litAtom "," (by decide))))))

open TextKit in
/-- One field LINE: the field's bytes PLUS its trailing newline (the
    trailing-delimiter discipline — the fields' separator read at the
    line's end; see `FieldsRaw`'s note). -/
def fieldLineG : TextKit.Grammar (FieldRaw × Unit) :=
  .seq fieldG (.atom (litAtom "\n" (by decide)))

/-- The field block: the blank-line dam (the empty record's `\n`) +
    the field lines. -/
def fieldsG : TextKit.Grammar FieldsRaw :=
  .seq (.opt (.atom (litAtom "\n" (by decide))))
    (.rep fieldLineG)

open TextKit in
/-- One record block: the marker, the name, ` {\n`, the field block,
    the closer `  }\n` (the last field line's trailing newline IS the
    `\n` the renderer's `"\n  }\n"` shows — the same bytes). -/
def recordG : TextKit.Grammar RecordRaw :=
  .seq (.atom (litAtom "  record " (by decide)))
    (.seq (.atom nameAtom)
      (.seq (.atom (litAtom " {\n" (by decide)))
        (.seq fieldsG
          (.atom (litAtom "  }\n" (by decide))))))

open TextKit in
/-- One interface block: the marker, the name, ` {\n`, the record
    blocks, `}\n`. -/
def ifaceG : TextKit.Grammar InterfaceRaw :=
  .seq (.atom (litAtom "interface " (by decide)))
    (.seq (.atom nameAtom)
      (.seq (.atom (litAtom " {\n" (by decide)))
        (.seq (.rep recordG)
          (.atom (litAtom "}\n" (by decide))))))

open TextKit in
/-- The package's raw grammar: `package `, the id, `;\n\n`, the
    interface blocks. -/
def pkgRawG : TextKit.Grammar PkgRaw :=
  .seq (.atom (litAtom "package " (by decide)))
    (.seq (.atom idAtom)
      (.seq (.atom (litAtom ";\n\n" (by decide)))
        (.rep ifaceG)))

/-- THE package codec: the raw IS the seq-spine tuple; decode unmaps
    it (the nodup checks at the record/interface levels). The policy is
    HONEST: the decode really refuses (a duplicate record/interface
    name decodes to `none`), so the accepted-byte policy says so —
    `∃ q, packageOfRaw raw = some q` (the `witCodec` template below;
    never a stub `True` over a refusing decode). -/
abbrev packageCodec : Kit.Codec PkgRaw Package where
  encode := packageToRaw
  decode := packageOfRaw
  policy raw := ∃ q, packageOfRaw raw = some q
  decode_encode := packageCodec_decode_encode
  decode_some_policy := fun _ _ hq => ⟨_, hq⟩

/-- THE WIT package grammar: the nested seq/rep spine under the ONE
    `rel` codec — no `fix`, no `self` anywhere (the ty recursion is the
    guarded leaf; the module header's honest-state note). -/
def pkgGrammar : TextKit.Grammar Package :=
  .rel packageCodec (fun _ => true) (fun _ _ _ => rfl) packageToRaw_of
    "package" [] pkgRawG

/-- THE certificate discharge (06 §7's build-time check): the WF rows
    compute green (WF-REP: the line/block bodies are non-nullable and
    the ty token's name-char munch is broken by the `,`/newline
    followers; WF-SEQ: the name munches are broken by `: `, the dam's
    `\n` is disjoint from the field lines' `    `, and the trailing-
    delimiter discipline keeps every stop-position's firsts disjoint
    from the closers). -/
theorem pkgCert : TextKit.Grammar.Predictive pkgGrammar :=
  TextKit.Grammar.wfCheck_sound pkgGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere — the ty token is a
    leaf). -/
theorem pkgFixFree : TextKit.Grammar.FixFree pkgGrammar := by
  repeat constructor

/-- Law 2's coherence premise: NO `alt` node anywhere (ALL the type
    dispatch hides inside the ty leaf's scan) — the fold's branches are
    all trivial. -/
theorem pkgCoherent : TextKit.Grammar.altCoherent pkgGrammar := by
  repeat constructor

/-! ## the valueOk discipline (the WitOk bridge) -/

/-- The field's valueOk IS the name gate + the `&& true` residue (the
    spine's `&&`-chain keeps the right-`true`s definitionally — the
    `Bool.and_true` simp-lemma closes them, never defeq). -/
theorem valueOk_fieldG (f : Field) :
    TextKit.Grammar.valueOk fieldG (fieldToRaw f) = nameAtom.pre f.name := by
  simp only [fieldG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    fieldToRaw, litAtom, TextKit.constStrLex, tyAtom]
  simp [← witNameOk_eq]

theorem valueOk_fieldLineG (g : Field) (h : witNameOk g.name = true) :
    TextKit.Grammar.valueOk fieldLineG (fieldToRaw g, ()) = true := by
  show TextKit.Grammar.valueOk fieldLineG (((), (g.name, ((), (g.ty, ())))), ()) = true
  simp only [fieldLineG, fieldG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    litAtom, TextKit.constStrLex, fieldToRaw, tyAtom, ← witNameOk_eq]
  simp [h]

theorem valueOk_fields : ∀ (fs : List Field),
    (∀ f ∈ fs, witNameOk f.name = true) →
    TextKit.Grammar.valueOk fieldsG (fieldsToRaw fs) = true
  | [], _ => rfl
  | f :: fs, h => by
      have hf : witNameOk f.name = true := h f (List.mem_cons_self ..)
      have hrep : (fs.map (fun g => (fieldToRaw g, ()))).all
          (fun z => TextKit.Grammar.valueOk fieldLineG z) = true := by
        rw [List.all_eq_true]
        intro z hz
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
        show TextKit.Grammar.valueOk fieldLineG (((), (g.name, ((), (g.ty, ())))), ()) = true
        exact valueOk_fieldLineG g (h g (List.mem_cons_of_mem _ hg))
      simp only [fieldsToRaw, fieldsG, TextKit.Grammar.valueOk_seq,
        TextKit.Grammar.valueOk_opt_none, TextKit.Grammar.valueOk_rep,
        Bool.true_and, List.all_cons]
      simp [valueOk_fieldLineG f hf, hrep]

theorem valueOk_record : ∀ (r : Record),
    witNameOk r.name = true → (∀ f ∈ r.fields, witNameOk f.name = true) →
    TextKit.Grammar.valueOk recordG (recordToRaw r) = true := by
  intro r hnm hf
  simp only [recordToRaw, recordG, TextKit.Grammar.valueOk_seq,
    TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex]
  simp [valueOk_fields r.fields hf, ← witNameOk_eq, hnm]

theorem valueOk_iface : ∀ (i : Interface),
    witNameOk i.name = true →
    (∀ r ∈ i.records, witNameOk r.name = true ∧ (∀ f ∈ r.fields, witNameOk f.name = true)) →
    TextKit.Grammar.valueOk ifaceG (ifaceToRaw i) = true := by
  intro i hnm hr
  have hrep : (List.map recordToRaw i.records).all
      (fun z => TextKit.Grammar.valueOk recordG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨r, hr2, rfl⟩ := List.mem_map.mp hz
    exact valueOk_record r (hr r hr2).1 (hr r hr2).2
  simp only [ifaceToRaw, ifaceG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    TextKit.Grammar.valueOk_rep, litAtom, TextKit.constStrLex]
  simp [hrep, ← witNameOk_eq, hnm]

theorem valueOk_package (p : Package) (hok : WitOk p = true) :
    TextKit.Grammar.valueOk pkgGrammar p = true := by
  obtain ⟨hid, hn⟩ := WitOk_spec p hok
  have hrep : (List.map ifaceToRaw p.interfaces).all
      (fun z => TextKit.Grammar.valueOk ifaceG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    exact valueOk_iface i (hn i hi).1 (fun r hr => (hn i hi).2 r hr)
  simp only [pkgGrammar, TextKit.Grammar.valueOk_rel, packageCodec,
    packageToRaw, pkgRawG, TextKit.Grammar.valueOk_seq,
    TextKit.Grammar.valueOk_atom, TextKit.Grammar.valueOk_rep, litAtom,
    TextKit.constStrLex]
  simp [hrep, ← witIdOk_eq, hid]

/-! ## the print faces (the derived print's bytes ARE the renderer's) -/

/-- The `",\n"` literal vs its append-spelling (the joins' byte tie —
    the kernel reduces the adjacent literals; simp needs the named
    face, right-associated forms never expose the merge). -/
theorem append_comma_nl (x : String) : ",\n" ++ x = "," ++ ("\n" ++ x) := by
  rw [← String.append_assoc]
  rfl

theorem nameAtom_print (s : String) : nameAtom.print s = s := rfl
theorem idAtom_print (s : String) : idAtom.print s = s := rfl

theorem printG_field (f : Field) :
    TextKit.Grammar.printG fieldG (fieldToRaw f) = Render.field f := by
  simp [fieldG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    fieldToRaw, litAtom, TextKit.constStrLex, nameAtom_print, tyAtom,
    Render.field, String.append_assoc]

theorem printG_line (g : Field) :
    TextKit.Grammar.printG fieldLineG (fieldToRaw g, ()) = Render.field g ++ "\n" := by
  simp [fieldLineG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, printG_field]

theorem printG_lines : (f : Field) → (fs : List Field) →
    TextKit.Grammar.printG (.rep fieldLineG)
        ((fieldToRaw f, ()) :: fs.map (fun g => (fieldToRaw g, ())))
      = Render.fieldsJoin (f :: fs) ++ "\n"
  | f, [] => by
      show TextKit.Grammar.printG fieldLineG (fieldToRaw f, ()) ++ "" = _
      rw [printG_line]
      simp [Render.fieldsJoin, Render.fieldsTailJoin, Render.field, String.append_assoc]
  | f, g :: gs => by
      show TextKit.Grammar.printG fieldLineG (fieldToRaw f, ()) ++
        TextKit.Grammar.printG (.rep fieldLineG)
          ((fieldToRaw g, ()) :: gs.map (fun h => (fieldToRaw h, ()))) = _
      rw [printG_line, printG_lines g gs]
      simp only [Render.fieldsJoin, Render.fieldsTailJoin, Render.field,
        String.append_assoc, append_comma_nl]

theorem printG_record (r : Record) :
    TextKit.Grammar.printG recordG (recordToRaw r) = Render.record r := by
  obtain ⟨n, fs, hnd⟩ := r
  simp only [recordToRaw, recordG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, nameAtom_print]
  cases fs with
  | nil =>
      have hft : fieldsToRaw [] = (Option.some (), []) := rfl
      rw [hft]
      simp only [fieldsG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
        TextKit.Grammar.printG_opt_some, TextKit.Grammar.printG_rep, litAtom,
        TextKit.constStrLex, Render.record, Render.fieldsJoin,
        String.append_assoc, List.foldr]
      rfl
  | cons f fs' =>
      have hft : fieldsToRaw (f :: fs')
        = (Option.none, (fieldToRaw f, ()) :: List.map (fun g => (fieldToRaw g, ())) fs') := rfl
      rw [hft]
      simp only [fieldsG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
        TextKit.Grammar.printG_opt_none, litAtom, TextKit.constStrLex]
      rw [printG_lines f fs']
      simp [Render.record, Render.fieldsJoin, String.append_assoc]

theorem printG_records : ∀ (rs : List Record),
    TextKit.Grammar.printG (.rep recordG) (List.map recordToRaw rs) = Render.recordsJoin rs
  | [] => rfl
  | r :: rs => by
      show TextKit.Grammar.printG recordG (recordToRaw r) ++
        TextKit.Grammar.printG (.rep recordG) (List.map recordToRaw rs) = _
      rw [printG_record, printG_records rs]
      simp [Render.recordsJoin, String.append_assoc]

theorem printG_iface (i : Interface) :
    TextKit.Grammar.printG ifaceG (ifaceToRaw i) = Render.interface i := by
  obtain ⟨n, rs, hnd⟩ := i
  show TextKit.Grammar.printG ifaceG
    ((), (n, ((), (List.map recordToRaw rs, ())))) = _
  simp only [ifaceG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, nameAtom_print]
  rw [printG_records]
  simp [Render.interface, String.append_assoc]

theorem printG_ifaces : ∀ (is : List Interface),
    TextKit.Grammar.printG (.rep ifaceG) (List.map ifaceToRaw is) = Render.interfacesJoin is
  | [] => rfl
  | i :: is => by
      show TextKit.Grammar.printG ifaceG (ifaceToRaw i) ++
        TextKit.Grammar.printG (.rep ifaceG) (List.map ifaceToRaw is) = _
      rw [printG_iface, printG_ifaces is]
      simp [Render.interfacesJoin, String.append_assoc]

/-- The derived printer's bytes ARE the renderer's (the byte-tie's
    value face — `print_eq_render` is what makes the generic law's
    `run (print g x) = ok x` speak the RENDERER's spellings). -/
theorem print_eq_render (p : Package) :
    TextKit.Grammar.print pkgGrammar p = Render.package p := by
  obtain ⟨id, is⟩ := p
  show TextKit.Grammar.printG pkgRawG ((), (id, ((), List.map ifaceToRaw is))) = _
  simp only [pkgRawG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, idAtom_print]
  rw [printG_ifaces]
  simp [Render.package, Render.interfacesJoin, String.append_assoc]

/-! ## the entry + the laws (the generic theorems' instances) -/

/-- The total parser: text → the typed WIT package (the grammar's run
    entry over the comment-stripped bytes; every failure is a
    `ParseError` — position + expected-set — and trailing garbage is a
    loud refusal, never a silent prefix acceptance). -/
def parse (s : String) : Except ParseError Package :=
  TextKit.Grammar.run pkgGrammar (stripComments s)

/-- THE PARSE LAW (05 §1's first honest law): every well-named
    package's rendering parses back to exactly it — the
    `Grammar.run_print_fixFree` INSTANCE (the hand per-level climb of
    the pre-grammar file died here). -/
theorem parse_print (p : Package) (hok : WitOk p = true) :
    parse (Render.package p) = .ok p := by
  have hstrip : stripComments (Render.package p) = Render.package p := by
    apply String.toList_inj.mp
    show String.toList (String.ofList (skipComments (Render.package p).toList)) = _
    have h1 : (Render.package p).toList
        = "package ".toList ++ ((p.id.toList ++ ";\n\n".toList)
          ++ (Render.interfacesJoin p.interfaces).toList) := by
      simp [Render.package, String.toList_append]
    rw [String.toList_ofList, h1, skipComments_package_sfx]
  have hr : TextKit.Grammar.run pkgGrammar (TextKit.Grammar.print pkgGrammar p) = .ok p :=
    TextKit.Grammar.run_print_fixFree pkgGrammar pkgFixFree pkgCert p (valueOk_package p hok)
  rw [print_eq_render] at hr
  show TextKit.Grammar.run pkgGrammar (stripComments (Render.package p)) = _
  rw [hstrip]
  exact hr

/-- THE CANONICALIZATION LAW (05 §1's second honest law — LANDED at
    this migration, the pre-grammar file's named follow-up): accepted
    text IS the rendering of its result — `Grammar.print_parse` (law 2)
    + `print_eq_render` + the run entry's full-consumption check. -/
theorem render_parse (s : String) (p : Package) (h : parse s = .ok p) :
    Render.package p = stripComments s := by
  unfold parse at h
  simp only [TextKit.Grammar.run] at h
  split at h
  · exact absurd h (by simp)
  · rename_i x cur hrun
    split at h
    · rename_i hnil
      have hxp : x = p := Except.ok.inj h
      cases hxp
      have hpp := TextKit.Grammar.print_parse pkgGrammar
        ((stripComments s).length + 1) pkgCoherent hrun
      have h1 : (stripComments s).toList
          = (TextKit.Grammar.printG pkgGrammar p).toList := by
        rw [hnil] at hpp
        rw [List.append_nil] at hpp
        exact hpp.1
      have h2 : stripComments s = TextKit.Grammar.printG pkgGrammar p :=
        String.toList_inj.mp h1
      rw [h2]
      exact (print_eq_render p).symm
    · exact absurd h (by simp)

/-- Law 2 (the exactness direction, generic form) at the package's
    grammar: a successful derived parse consumed EXACTLY the print of
    its result (+ the parsed value is value-owned — the WitOk
    discipline). -/
theorem print_parse (fuel : Nat) (ys : Package) (cur cur' : Cursor)
    (h : TextKit.Grammar.parseG pkgGrammar fuel cur = .ok (ys, cur')) :
    cur.cs = (TextKit.Grammar.printG pkgGrammar ys).toList ++ cur'.cs ∧
    cur'.off = cur.off + (TextKit.Grammar.printG pkgGrammar ys).length ∧
    TextKit.Grammar.valueOk pkgGrammar ys = true :=
  TextKit.Grammar.print_parse pkgGrammar fuel pkgCoherent h

/-! ## the correspondence row -/

/-- The WIT codec (Kit.Correspondence's decode∘encode grade): the
    texts are the carrier, the WELL-NAMED packages the payload. The
    decode is proof-carrying — a parse result is trusted only when it
    passes `WitOk` (the gate rides the value; a parsed-then-rejected
    text decodes to `none`). `decode_encode` IS `parse_print`;
    `decode_some_policy` says a successful decode certifies acceptance.
    The image-iso upgrade (`Kit.Retraction.toImageIso`: the canonical
    texts a true `Kit.Iso` with the well-named ASTs) rides the
    retraction below. -/
def witDecode (s : String) : Option { p : Package // WitOk p } :=
  match parse s with
  | .ok p => if h : WitOk p = true then some ⟨p, h⟩ else none
  | .error _ => none

def witCodec : Kit.Codec String { p : Package // WitOk p } where
  encode q := Render.package q.1
  decode := witDecode
  policy s := ∃ q, witDecode s = some q
  decode_encode q := by
    simp only [witDecode, parse_print q.1 q.2]
    exact dif_pos q.2
  decode_some_policy := fun _ _ hq => ⟨_, hq⟩

/-! ## THE GRADUATION (16-surface §5.1, 15-patterns #11): the lossless
     fragment ≅ its image -/

/-- The default well-named package: the total inverse's off-image
    anchor (an empty package named `a`; the bytes it anchors are
    exactly the ones `witDecode` refuses — the honest gap lives on the
    `none` side, never silently). -/
def witDefault : { p : Package // WitOk p } :=
  ⟨⟨"a", []⟩, by decide⟩

/-- THE RETRACTION: the rendering embeds the well-named packages into
    the texts; the proof-carrying decode reconstructs. `inv_emb` IS
    `parse_print` (the landed top assembly) — the byte-level inverse IS
    total over the lossless fragment. Off-image texts fall back to
    `witDefault` (the retraction's inverse is total by construction;
    the honest gap — the non-image bytes — is the decode's `none`). -/
def witRetraction : Kit.Retraction { p : Package // WitOk p } String where
  emb q := Render.package q.1
  inv s := Option.getD (witDecode s) witDefault
  inv_emb q := by
    show Option.getD (witDecode (Render.package q.1)) witDefault = q
    simp only [witDecode, parse_print q.1 q.2]
    rw [dif_pos q.2]
    rfl

/-- THE GRADUATION'S VALUE (the image-iso upgrade): the renderer's
    IMAGE texts ≅ the well-named packages — a TRUE `Kit.Iso`, the
    retraction above restricted to its canonical image via
    `Retraction.toImageIso`. The image's property is the honest
    «∃ a well-named package whose rendering is exactly this text» —
    the byte-level losslessness of the fragment, both round trips
    landed (`render_parse` as of this migration). -/
def witImageIso :
    Kit.Iso (Kit.Retraction.image witRetraction) { p : Package // WitOk p } :=
  witRetraction.toImageIso

end Wit.Parse
