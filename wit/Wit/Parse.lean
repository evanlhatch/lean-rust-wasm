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

THE D2 REMAINDER LANDED: the accepted language is the renderer's
IMAGE — every ty row parses (`stream`/`future`, the one-summand
`result` faces, the `own`/`borrow` handle refs — the D2 deferred
remainder's gates dropped for the landed rows). The parser accepts
EXACTLY the text `Wit.Render` produces (the canonical bytes),
optionally preceded by `//`-comment lines — the committed artifact
of record `gen/schema-slice.wit` carries two. The
resource-declaration lines ride the engine (`resourceLineG`). The
strictness is the canonicalization law's honesty: accepted text
normalizes to its comment-stripped bytes, and those bytes are the
rendering of the parse result (`render_parse` below). Whitespace
tolerance would break normalization — it is deliberately not
accepted.

The GRADE NOTE (the D2 wall's dissolution): the D2 finisher's wall —
`Kit.Codec.decode_encode` is UNCONDITIONAL over the payload, so "gate
the round trip on the fragment" was structurally impossible for a
ty-unconstrained carrier — was a CARRIER-CHOICE mistake, not a real
wall. The payload IS `{ p : Package // WitOk p }`, and `WitOk`'s
per-field `tyPre` conjunct IS the inDomain gate (the WireTarget
`conditionalRetraction` discipline: the law's domain narrowed by the
carrier, not by a premise). Landed rows = shrink `tyPre`; every law
extends as an instance, no regrade. The fragment's residual gate is
the handle refs' NAME discipline (`tyPre (.own n) = witNameOk n` —
the maximal-munch name run's head need not be alpha).

The parse-time refusals keep their teeth: trailing bytes (the run
entry's full-consumption check), the maximal-munch atom refusal and
the curated ty errors (inside `tyP`), the malformed
stream/result/handle syntax (the arms' structural refusals — an
empty `stream<>`, a missing `>`, an empty or non-identifier handle
name — the fragment gate's last bite), and the duplicate-field /
duplicate-record / duplicate-resource refusals (the codec's decode —
the nodup checks are decided `none`s, never silent acceptance).

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
module


public import Wit
public import Wit.Render
public import TextKit.Grammar
public import TextKit.Grammar.Lexemes
public import TextKit.Grammar.Check
public import TextKit.Grammar.Laws
public import Kit.Correspondence


namespace Wit.Parse

open TextKit (Cursor ParseError GParser)

@[expose] public section

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
  ["bool", "u64", "i64", "string", "option", "list", "result", "tuple",
   "stream", "future", "own", "borrow"]

/-- A WIT name is identifier-shaped (the name lexeme's byte-side gate;
    defined here because the handle refs' fragment gate needs it). -/
def witNameOk (s : String) : Bool := identOk nameChar s

/-- The ty parser's fragment gate (the D2 remainder LANDED): every
    renderer row now parses. `stream`/`future` (the waitable wrappers),
    the one-summand `result` faces and the nested tys ride the same
    recursion; the handle refs `own`/`borrow` parse their resource NAME
    and so keep a byte-side gate — the name must be identifier-shaped
    (the scanner takes the maximal name-char run, whose head need not
    be alpha — `own<9bad>` refuses HERE, the fragment gate's last
    honest tooth). `tyPre` names the accepted fragment exactly; every
    law that speaks for the ty parser is gated on it, and the gate
    rides the `tyAtom` lexeme's `pre` (the write-side gate's home). -/
def tyPre : Ty → Bool
  | .atom _ => true
  | .option a => tyPre a
  | .list a => tyPre a
  | .result a b => tyPre a && tyPre b
  | .tuple a b => tyPre a && tyPre b
  | .stream a => tyPre a
  | .future a => tyPre a
  | .resultOk a => tyPre a
  | .resultErr a => tyPre a
  | .own n => witNameOk n
  | .borrow n => witNameOk n

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

/-- The `result<` FLEX arm: the two-summand face AND the one-summand
    `result<T>` face — ONE arm, because both faces share the `result<`
    opener (the head is not a discriminator here; the token after the
    ok-ty is). The dispatch: after `result<` + the ok-ty, `, ` means
    the two-summand face, `>` the one-summand face; the error face
    (`result<_, `) is the SEPARATE unary arm EARLIER in the chain —
    its `_` head fails the inner ty, so the flex arm never reaches the
    dispatch on error-face input. -/
def resultFlexArm (inner : GParser Ty) : GParser Ty := fun cur =>
  match TextKit.tok "result<" cur with
  | .error e => .error e
  | .ok (_, c1) =>
      match inner c1 with
      | .error e => .error e
      | .ok (a, c2) =>
          match TextKit.tok ", " c2 with
          | .ok (_, c3) =>
              match inner c3 with
              | .error e => .error e
              | .ok (b, c4) =>
                  match TextKit.tok ">" c4 with
                  | .error e => .error e
                  | .ok (_, c5) => .ok (Ty.result a b, c5)
          | .error _ =>
              match TextKit.tok ">" c2 with
              | .error e => .error e
              | .ok (_, c3) => .ok (Ty.resultOk a, c3)

/-- The handle-ref arm: `own<`/`borrow<` + the resource's name + `>`
    (the name is the maximal name-char run — whose head need not be
    alpha, so `tyPre`'s `witNameOk` gate keeps the byte-side
    discipline: `own<9bad>` refuses at the fragment gate). -/
def handleArm (kw : String) (k : String → Ty) : GParser Ty := fun cur =>
  match TextKit.tok kw cur with
  | .error e => .error e
  | .ok (_, c1) =>
      match c1.cs.takeWhile nameChar with
      | [] => .error (curated cur "expected a WIT type" tyValid)
      | nm =>
          match TextKit.tok ">" ⟨c1.off + nm.length, c1.cs.drop nm.length⟩ with
          | .error e => .error e
          | .ok (_, c2) => .ok (k (String.ofList nm), c2)

/-- The TWELVE ty arms over the inner parser (the D2 remainder's
    rows included). The heads are NOT all distinct — the four
    collisions (string/stream, option/own, bool/borrow, and the
    `result<` family's three faces) are TOKEN-discriminated: every
    arm's leading token is a full-literal check (the mismatch byte
    refuses it before any arm commits) and the chain backtracks at
    the SAME cursor, so ordering + exact tokens do the dispatch the
    head chars cannot. -/
def tyArms (inner : GParser Ty) : GParser Ty :=
  TextKit.orElse (atomArm "bool" .bool) $
  TextKit.orElse (atomArm "u64" .u64) $
  TextKit.orElse (atomArm "i64" .i64) $
  TextKit.orElse (atomArm "string" .string) $
  TextKit.orElse (unaryArm "option<" .option inner) $
  TextKit.orElse (unaryArm "list<" .list inner) $
  TextKit.orElse (unaryArm "result<_, " Ty.resultErr inner) $
  TextKit.orElse (resultFlexArm inner) $
  TextKit.orElse (binaryArm "tuple<" .tuple inner) $
  TextKit.orElse (unaryArm "stream<" .stream inner) $
  TextKit.orElse (unaryArm "future<" .future inner) $
  TextKit.orElse (handleArm "own<" Ty.own) $
  TextKit.orElse (handleArm "borrow<" Ty.borrow)
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

theorem ty_stream (a : Ty) : Render.ty (.stream a) = "stream<" ++ Render.ty a ++ ">" := rfl
theorem ty_future (a : Ty) : Render.ty (.future a) = "future<" ++ Render.ty a ++ ">" := rfl
theorem ty_resultOk (a : Ty) : Render.ty (.resultOk a) = "result<" ++ Render.ty a ++ ">" := rfl
theorem ty_resultErr (a : Ty) :
    Render.ty (.resultErr a) = "result<_, " ++ Render.ty a ++ ">" := rfl
theorem ty_own (n : String) : Render.ty (.own n) = "own<" ++ n ++ ">" := rfl
theorem ty_borrow (n : String) : Render.ty (.borrow n) = "borrow<" ++ n ++ ">" := rfl

/-- Every ty rendering's head is a lowercase letter (the keyword's
    first byte) — the dispatch's discriminator: the `_` placeholder of
    the error-result face is never a ty head, so the `result<` family's
    faces are token-distinguished. -/
theorem tyText_head_isAlpha (t : Ty) :
    ∃ c w, (Render.ty t).toList = c :: w ∧ c.isAlpha = true := by
  cases t with
  | atom s => cases s with
    | bool => rw [ty_atom, scalar_bool]; exact ⟨'b', ['o', 'o', 'l'], rfl, rfl⟩
    | u64 => rw [ty_atom, scalar_u64]; exact ⟨'u', ['6', '4'], rfl, rfl⟩
    | i64 => rw [ty_atom, scalar_i64]; exact ⟨'i', ['6', '4'], rfl, rfl⟩
    | string => rw [ty_atom, scalar_string]; exact ⟨'s', ['t', 'r', 'i', 'n', 'g'], rfl, rfl⟩
  | option a =>
      rw [ty_option]; simp only [String.toList_append]
      exact ⟨'o', _, rfl, rfl⟩
  | list a =>
      rw [ty_list]; simp only [String.toList_append]
      exact ⟨'l', _, rfl, rfl⟩
  | result a b =>
      rw [ty_result]; simp only [String.toList_append]
      exact ⟨'r', _, rfl, rfl⟩
  | tuple a b =>
      rw [ty_tuple]; simp only [String.toList_append]
      exact ⟨'t', _, rfl, rfl⟩
  | stream a =>
      rw [ty_stream]; simp only [String.toList_append]
      exact ⟨'s', _, rfl, rfl⟩
  | future a =>
      rw [ty_future]; simp only [String.toList_append]
      exact ⟨'f', _, rfl, rfl⟩
  | resultOk a =>
      rw [ty_resultOk]; simp only [String.toList_append]
      exact ⟨'r', _, rfl, rfl⟩
  | resultErr a =>
      rw [ty_resultErr]; simp only [String.toList_append]
      exact ⟨'r', _, rfl, rfl⟩
  | own n =>
      rw [ty_own]; simp only [String.toList_append]
      exact ⟨'o', _, rfl, rfl⟩
  | borrow n =>
      rw [ty_borrow]; simp only [String.toList_append]
      exact ⟨'b', _, rfl, rfl⟩

/-- An alpha char is never the `_` placeholder (the LawfulBEq face). -/
theorem beq_uscore_false_of_alpha {c : Char} (ha : c.isAlpha = true) :
    ('_' == c) = false := by
  have h : ¬ (c = '_') := by
    intro hcon; rw [hcon] at ha; simp [Char.isAlpha] at ha
  cases hcon : ('_' == c) with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hcon).symm h

/-- The token refusal by NON-prefix (the shared-head arms' miss: the
    full literal check discriminates what the head char cannot — the
    twelve-arm chain's head collisions are decided at the mismatch
    byte, never by lookahead). -/
theorem tok_miss_pfx (s : String) (off : Nat) (cs : List Char)
    (h : s.toList.isPrefixOf cs = false) :
    TextKit.tok s ⟨off, cs⟩ = .error (tokErr off s) := by
  unfold TextKit.tok tokErr
  simp [h]

/-- A unary arm misses by NON-prefix (the shared-head faces' miss —
    the full literal check discriminates what the head cannot). -/
theorem unaryArm_miss_pfx (openS : String) (k : Ty → Ty) (inner : GParser Ty)
    (off : Nat) (cs : List Char) (h : openS.toList.isPrefixOf cs = false) :
    unaryArm openS k inner ⟨off, cs⟩ = .error (tokErr off openS) := by
  unfold unaryArm tokErr
  rw [tok_miss_pfx openS off cs h]
  rfl


/-- The error-face opener never prefixes `result<` + a char list whose
    head is a letter (the ty renderings' heads are letters, never the
    `_` placeholder). -/
theorem resultErrOpener_miss (tl sfx : List Char)
    (hh : ∃ c w, tl = c :: w ∧ c.isAlpha = true) :
    "result<_, ".toList.isPrefixOf ("result<".toList ++ (tl ++ sfx)) = false := by
  obtain ⟨c, w, htl, hal⟩ := hh
  rw [htl]
  simp only [List.cons_append]
  simp [List.isPrefixOf, beq_uscore_false_of_alpha hal]

/-- The error-face arm misses on the one-summand face's text (the ok
    ty's head is a letter, never the `_` placeholder). -/
theorem resultErrArm_miss_ok (inner : GParser Ty) (a : Ty) (off : Nat) (rest : List Char) :
    unaryArm "result<_, " Ty.resultErr inner
      ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
      = .error (tokErr off "result<_, ") := by
  have hp : "result<_, ".toList.isPrefixOf
      (("result<" ++ Render.ty a ++ ">").toList ++ rest) = false := by
    rw [String.append_assoc]
    simp only [String.toList_append, List.append_assoc]
    exact resultErrOpener_miss (Render.ty a).toList (">".toList ++ rest)
      (tyText_head_isAlpha a)
  exact unaryArm_miss_pfx "result<_, " Ty.resultErr inner off _ hp

/-- The error-face arm misses on the two-summand face's text. -/
theorem resultErrArm_miss_two (inner : GParser Ty) (a b : Ty) (off : Nat) (rest : List Char) :
    unaryArm "result<_, " Ty.resultErr inner
      ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
      = .error (tokErr off "result<_, ") := by
  have hp : "result<_, ".toList.isPrefixOf
      (("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest) = false := by
    rw [String.append_assoc, String.append_assoc]
    simp only [String.toList_append, List.append_assoc]
    exact resultErrOpener_miss (Render.ty a).toList
      (", ".toList ++ ((Render.ty b).toList ++ (">".toList ++ rest)))
      (tyText_head_isAlpha a)
  exact unaryArm_miss_pfx "result<_, " Ty.resultErr inner off _ hp

/-- The shared-head misses (the maximal-munch arm kit): the full
    literal check discriminates what the head char cannot — the
    twelve-arm chain's four head collisions are decided at the
    mismatch byte, never by lookahead. -/
theorem atomArm_string_miss_stream (a : Ty) (off : Nat) (rest : List Char) :
    atomArm "string" .string ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
      = .error (tokErr off "string") := by
  unfold atomArm tokErr
  have hp : "string".toList.isPrefixOf
      (("stream<" ++ Render.ty a ++ ">").toList ++ rest) = false := by
    simp only [String.toList_append, List.append_assoc]
    simp [List.isPrefixOf]
  rw [tok_miss_pfx "string" off _ hp]
  rfl

theorem unaryArm_option_miss_own (inner : GParser Ty) (n : String) (off : Nat)
    (rest : List Char) :
    unaryArm "option<" Ty.option inner ⟨off, ("own<" ++ n ++ ">").toList ++ rest⟩
      = .error (tokErr off "option<") := by
  unfold unaryArm tokErr
  have hp : "option<".toList.isPrefixOf
      (("own<" ++ n ++ ">").toList ++ rest) = false := by
    simp only [String.toList_append, List.append_assoc]
    simp [List.isPrefixOf]
  rw [tok_miss_pfx "option<" off _ hp]
  rfl

theorem handleArm_own_miss_option (n : String) (off : Nat) (rest : List Char) :
    handleArm "own<" Ty.own ⟨off, ("option<" ++ n ++ ">").toList ++ rest⟩
      = .error (tokErr off "own<") := by
  unfold handleArm tokErr
  have hp : "own<".toList.isPrefixOf
      (("option<" ++ n ++ ">").toList ++ rest) = false := by
    simp only [String.toList_append, List.append_assoc]
    simp [List.isPrefixOf]
  rw [tok_miss_pfx "own<" off _ hp]
  rfl

theorem atomArm_bool_miss_borrow (n : String) (off : Nat) (rest : List Char) :
    atomArm "bool" .bool ⟨off, ("borrow<" ++ n ++ ">").toList ++ rest⟩
      = .error (tokErr off "bool") := by
  unfold atomArm tokErr
  have hp : "bool".toList.isPrefixOf
      (("borrow<" ++ n ++ ">").toList ++ rest) = false := by
    simp only [String.toList_append, List.append_assoc]
    simp [List.isPrefixOf]
  rw [tok_miss_pfx "bool" off _ hp]
  rfl

theorem handleArm_borrow_miss_bool (n : String) (off : Nat) (rest : List Char) :
    handleArm "borrow<" Ty.borrow ⟨off, ("bool" ++ n ++ ">").toList ++ rest⟩
      = .error (tokErr off "borrow<") := by
  unfold handleArm tokErr
  have hp : "borrow<".toList.isPrefixOf
      (("bool" ++ n ++ ">").toList ++ rest) = false := by
    simp only [String.toList_append, List.append_assoc]
    simp [List.isPrefixOf]
  rw [tok_miss_pfx "borrow<" off _ hp]
  rfl

/-- A flex arm misses when the input's head differs from `result<`'s
    (the inner parser is never reached). -/
theorem resultFlexArm_miss (inner : GParser Ty) (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ "result<".toList.head?) :
    resultFlexArm inner ⟨off, cs⟩ = .error (tokErr off "result<") := by
  unfold resultFlexArm tokErr
  rw [tok_miss "result<" off cs hne (by decide)]

/-- A handle arm misses when the input's head differs from its
    keyword's head. -/
theorem handleArm_miss (kw : String) (k : String → Ty) (off : Nat) (cs : List Char)
    (hne : cs.head? ≠ kw.toList.head?) (hk : kw ≠ "") :
    handleArm kw k ⟨off, cs⟩ = .error (tokErr off kw) := by
  unfold handleArm tokErr
  rw [tok_miss kw off cs hne hk]

/-- The takeWhile discipline: an all-pass run is taken whole before
    the `>` terminator. -/
theorem takeWhile_nameChar_all : ∀ (w rest : List Char),
    w.all nameChar = true → (w ++ '>' :: rest).takeWhile nameChar = w
  | [], rest, _ => by
      rw [show ([] ++ '>' :: rest) = ('>' :: rest) from rfl, List.takeWhile]
      have hgt : nameChar '>' = false := by
        simp [nameChar, TextKit.isIdentChar]
      rw [hgt]
  | c :: w, rest, hw => by
      rw [List.all_cons, Bool.and_eq_true] at hw
      rw [show ((c :: w) ++ '>' :: rest) = (c :: (w ++ '>' :: rest)) from rfl,
        List.takeWhile, hw.1, takeWhile_nameChar_all w rest hw.2]

/-- A handle arm succeeds on its own keyword + a well-named resource
    (exactly, cursor included). -/
theorem handleArm_self (kw : String) (k : String → Ty) (c0 : Char) (w0 : List Char)
    (off : Nat) (rest : List Char)
    (hal0 : c0.isAlpha = true) (hall : w0.all nameChar = true) :
    handleArm kw k ⟨off, (kw ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
      = .ok (k (String.ofList (c0 :: w0)),
        ⟨off + (kw ++ String.ofList (c0 :: w0) ++ ">").length, rest⟩) := by
  have hnc : nameChar c0 = true := by
    simp [nameChar, TextKit.isIdentChar, hal0]
  have htak : ((c0 :: w0) ++ ('>' :: rest)).takeWhile nameChar = c0 :: w0 := by
    rw [List.cons_append, List.takeWhile, hnc,
      takeWhile_nameChar_all w0 rest hall]
  unfold handleArm
  rw [show ((kw ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest)
      = kw.toList ++ ((c0 :: w0) ++ ('>' :: rest)) from by
    simp only [String.toList_append, String.toList_ofList, List.append_assoc,
      List.cons_append]
    rw [show (">" : String).toList = ['>'] from rfl]
    rfl]
  simp only [tok_self, htak]
  -- the takeWhile-match's scrutinee is now the cons `c0 :: w0` — iota:
  simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
    List.nil_append, List.append_nil, tok_gt (off + kw.length + (c0 :: w0).length) rest]
  have hoff : off + kw.length + (c0 :: w0).length + 1
      = off + (kw ++ String.ofList (c0 :: w0) ++ ">").length := by
    have hlen : String.length (String.ofList (c0 :: w0)) = (c0 :: w0).length := by
      rw [← String.length_toList, String.toList_ofList]
    rw [String.length_append, String.length_append, hlen, List.length_cons]
    have h1len : (">" : String).length = 1 := rfl
    omega
  rw [hoff]

/-- The flex arm's ONE-SUMMAND face: `result<T>` (exactly, cursor
    included; the bundled IH as the other arms'). -/
theorem resultFlexArm_self1 (a : Ty) (inner : Nat → GParser Ty) (fuel off : Nat)
    (rest : List Char)
    (hlen : ("result<" ++ Render.ty a ++ ">").length + rest.length ≤ fuel + 1)
    (hinner : ∀ (gfuel goff : Nat) (grest : List Char),
        (Render.ty a).length + grest.length ≤ gfuel →
        grest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true →
        inner gfuel ⟨goff, (Render.ty a).toList ++ grest⟩
          = .ok (a, ⟨goff + (Render.ty a).length, grest⟩)) :
    resultFlexArm (inner fuel)
      ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
      = .ok (Ty.resultOk a, ⟨off + ("result<" ++ Render.ty a ++ ">").length, rest⟩) := by
  have h1 : ("result<" ++ Render.ty a ++ ">").length
      = String.length ("result<" : String) + (Render.ty a).length + 1 := by
    rw [String.length_append, String.length_append]
    simp [show (">" : String).length = 1 from rfl]
  have hlen1 : (Render.ty a).length + ('>' :: rest).length ≤ fuel := by
    have h2 : ('>' :: rest).length = rest.length + 1 := rfl
    have hc7 : String.length ("result<" : String) = 7 := rfl
    omega
  have hr1 : ('>' :: rest).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  unfold resultFlexArm
  have hnorm : (("result<" ++ Render.ty a ++ ">").toList ++ rest)
      = "result<".toList ++ ((Render.ty a).toList ++ ('>' :: rest)) := by
    simp only [String.toList_append, List.append_assoc]
    rw [show (">" : String).toList = ['>'] from rfl]
    rfl
  rw [hnorm]
  simp only [tok_self, hinner fuel (off + String.length ("result<" : String)) _ hlen1 hr1]
  have hsep : TextKit.tok ", "
        ⟨off + String.length ("result<" : String) + (Render.ty a).length, ('>' :: rest)⟩
      = .error (tokErr (off + String.length ("result<" : String)
        + (Render.ty a).length) ", ") :=
    tok_miss_pfx ", " _ _ (by simp [List.isPrefixOf])
  simp only [hsep, tok_gt (off + String.length ("result<" : String)
    + (Render.ty a).length) rest]
  have hoff : off + String.length ("result<" : String) + (Render.ty a).length + 1
      = off + ("result<" ++ Render.ty a ++ ">").length := by
    rw [h1]; omega
  rw [hoff]

/-- The flex arm's TWO-SUMMAND face: `result<A, B>` (exactly, cursor
    included). -/
theorem resultFlexArm_self2 (a b : Ty) (inner : Nat → GParser Ty) (fuel off : Nat)
    (rest : List Char)
    (hlen : ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length
      + rest.length ≤ fuel + 1)
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
    resultFlexArm (inner fuel)
      ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
      = .ok (Ty.result a b,
        ⟨off + ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length, rest⟩) := by
  have h1 : ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length
      = String.length ("result<" : String) + (Render.ty a).length + 2
        + (Render.ty b).length + 1 := by
    rw [String.length_append, String.length_append, String.length_append,
      String.length_append]
    simp [show (", " : String).length = 2 from rfl,
      show (">" : String).length = 1 from rfl]
  have hlen1 : (Render.ty a).length
      + (',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)).length ≤ fuel := by
    have h4 : ((Render.ty b).toList ++ '>' :: rest).length
        = (Render.ty b).length + 1 + rest.length := by
      rw [List.length_append, List.length_cons, String.length_toList]
      omega
    have hc7 : String.length ("result<" : String) = 7 := rfl
    simp only [List.length_cons, List.length_append, String.length_toList]
    omega
  have hr1 : (',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  have hlen2 : (Render.ty b).length + ('>' :: rest).length ≤ fuel := by
    have h2 : ('>' :: rest).length = rest.length + 1 := rfl
    have hc7 : String.length ("result<" : String) = 7 := rfl
    omega
  have hr2 : ('>' :: rest).head?.all
      (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
    simp [TextKit.isIdentChar]
  unfold resultFlexArm
  have hnorm : (("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest)
      = "result<".toList
        ++ ((Render.ty a).toList ++ ',' :: ' ' :: ((Render.ty b).toList ++ '>' :: rest)) := by
    simp only [String.toList_append, List.append_assoc]
    rw [show (", " : String).toList = [',', ' '] from rfl,
      show (">" : String).toList = ['>'] from rfl]
    rfl
  rw [hnorm]
  simp only [tok_self, hinner1 fuel (off + String.length ("result<" : String)) _ hlen1 hr1]
  simp only [tok_comma (off + String.length ("result<" : String)
    + (Render.ty a).length) _]
  simp only [hinner2 fuel (off + String.length ("result<" : String)
    + (Render.ty a).length + 2) _ hlen2 hr2]
  simp only [tok_gt (off + String.length ("result<" : String)
    + (Render.ty a).length + 2 + (Render.ty b).length) rest]
  have hoff : off + String.length ("result<" : String) + (Render.ty a).length + 2
      + (Render.ty b).length + 1
      = off + ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").length := by
    rw [h1]; omega
  rw [hoff]

/-- The ok direction for the ty parser: the rendering of any `Ty`
    parses back to exactly it, consuming exactly its bytes (the fuel
    invariant: the fuel covers the remaining characters). -/
theorem tyP_ok (t : Ty) (hpre : tyPre t = true) :
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
      have hpa : tyPre a = true := hpre
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
              (unaryArm_self "option<" Ty.option a tyP f off rest hlen (by decide)
                (ih hpa))))))]
  | list a ih =>
      intro fuel off rest hlen hr
      have hpa : tyPre a = true := hpre
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
              (unaryArm_self "list<" Ty.list a tyP f off rest hlen (by decide) (ih hpa)))))))]
  | result a b iha ihb =>
      intro fuel off rest hlen hr
      have hpp : tyPre a = true ∧ tyPre b = true := by
        simp only [tyPre, Bool.and_eq_true] at hpre
        exact hpre
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
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f)
                ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            resultErrArm_miss_two (tyP f) a b off rest
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_left
                (resultFlexArm_self2 a b tyP f off rest hlen
                  (iha hpp.1) (ihb hpp.2)))))))))]
  | tuple a b iha ihb =>
      intro fuel off rest hlen hr
      have hpp : tyPre a = true ∧ tyPre b = true := by
        simp only [tyPre, Bool.and_eq_true] at hpre
        exact hpre
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
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            unaryArm_miss "result<_, " Ty.resultErr (tyP f) off _ (by simp) (by decide)
          have hf8 : resultFlexArm (tyP f) ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            resultFlexArm_miss (tyP f) off _ (by simp)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_right hf8 (orElse_ok_left
                (binaryArm_self "tuple<" Ty.tuple a b tyP f off rest hlen (by decide)
                  (iha hpp.1) (ihb hpp.2))))))))))]
  | stream a ih =>
      intro fuel off rest hlen hr
      have hpa : tyPre a = true := hpre
      rw [ty_stream] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_string_miss_stream a off rest
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            unaryArm_miss "result<_, " Ty.resultErr (tyP f) off _ (by simp) (by decide)
          have hf8 : resultFlexArm (tyP f) ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            resultFlexArm_miss (tyP f) off _ (by simp)
          have hf9 : binaryArm "tuple<" Ty.tuple (tyP f) ⟨off, ("stream<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "tuple<") :=
            binaryArm_miss "tuple<" Ty.tuple (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_right hf8 (orElse_ok_right hf9
                (orElse_ok_left (unaryArm_self "stream<" Ty.stream a tyP f off rest hlen
                  (by decide) (ih hpa)))))))))))]
  | future a ih =>
      intro fuel off rest hlen hr
      have hpa : tyPre a = true := hpre
      rw [ty_future] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            unaryArm_miss "result<_, " Ty.resultErr (tyP f) off _ (by simp) (by decide)
          have hf8 : resultFlexArm (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            resultFlexArm_miss (tyP f) off _ (by simp)
          have hf9 : binaryArm "tuple<" Ty.tuple (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "tuple<") :=
            binaryArm_miss "tuple<" Ty.tuple (tyP f) off _ (by simp) (by decide)
          have hf10 : unaryArm "stream<" Ty.stream (tyP f) ⟨off, ("future<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "stream<") :=
            unaryArm_miss "stream<" Ty.stream (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_right hf8 (orElse_ok_right hf9
                (orElse_ok_right hf10 (orElse_ok_left
                  (unaryArm_self "future<" Ty.future a tyP f off rest hlen
                    (by decide) (ih hpa))))))))))))]
  | resultOk a ih =>
      intro fuel off rest hlen hr
      have hpa : tyPre a = true := hpre
      rw [ty_resultOk] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("result<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            resultErrArm_miss_ok (tyP f) a off rest
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_left
                (resultFlexArm_self1 a tyP f off rest hlen (ih hpa)))))))))]
  | resultErr a ih =>
      intro fuel off rest hlen hr
      have hpa : tyPre a = true := hpre
      rw [ty_resultErr] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("result<_, " ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_left (unaryArm_self "result<_, " Ty.resultErr a tyP f off rest hlen
                (by decide) (ih hpa))))))))]
  | own n =>
      intro fuel off rest hlen hr
      have hnm : witNameOk n = true := hpre
      obtain ⟨c0, w0, hnl, hal0, hall⟩ : ∃ c w, n.toList = c :: w
          ∧ c.isAlpha = true ∧ w.all nameChar = true := by
        cases hn : n.toList with
        | nil =>
            unfold witNameOk identOk at hnm
            simp only [hn] at hnm
            simp at hnm
        | cons c w =>
            unfold witNameOk identOk at hnm
            simp only [hn, Bool.and_eq_true] at hnm
            refine ⟨c, w, rfl, hnm.1, hnm.2⟩
      have hns : n = String.ofList (c0 :: w0) :=
        (String.ofList_toList).symm.trans (congrArg String.ofList hnl)
      rw [hns] at hlen ⊢
      rw [ty_own] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_miss "bool" .bool off _ (by simp) (by decide)
          have hf2 : atomArm "u64" .u64 ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_option_miss_own (tyP f) (String.ofList (c0 :: w0)) off rest
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            unaryArm_miss "result<_, " Ty.resultErr (tyP f) off _ (by simp) (by decide)
          have hf8 : resultFlexArm (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            resultFlexArm_miss (tyP f) off _ (by simp)
          have hf9 : binaryArm "tuple<" Ty.tuple (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "tuple<") :=
            binaryArm_miss "tuple<" Ty.tuple (tyP f) off _ (by simp) (by decide)
          have hf10 : unaryArm "stream<" Ty.stream (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "stream<") :=
            unaryArm_miss "stream<" Ty.stream (tyP f) off _ (by simp) (by decide)
          have hf11 : unaryArm "future<" Ty.future (tyP f) ⟨off, ("own<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "future<") :=
            unaryArm_miss "future<" Ty.future (tyP f) off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_right hf8 (orElse_ok_right hf9
                (orElse_ok_right hf10 (orElse_ok_right hf11 (orElse_ok_left
                  (handleArm_self "own<" Ty.own c0 w0 off rest hal0 hall))))))))))))]
  | borrow n =>
      intro fuel off rest hlen hr
      have hnm : witNameOk n = true := hpre
      obtain ⟨c0, w0, hnl, hal0, hall⟩ : ∃ c w, n.toList = c :: w
          ∧ c.isAlpha = true ∧ w.all nameChar = true := by
        cases hn : n.toList with
        | nil =>
            unfold witNameOk identOk at hnm
            simp only [hn] at hnm
            simp at hnm
        | cons c w =>
            unfold witNameOk identOk at hnm
            simp only [hn, Bool.and_eq_true] at hnm
            refine ⟨c, w, rfl, hnm.1, hnm.2⟩
      have hns : n = String.ofList (c0 :: w0) :=
        (String.ofList_toList).symm.trans (congrArg String.ofList hnl)
      rw [hns] at hlen ⊢
      rw [ty_borrow] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") :=
            atomArm_bool_miss_borrow (String.ofList (c0 :: w0)) off rest
          have hf2 : atomArm "u64" .u64 ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") :=
            atomArm_miss "u64" .u64 off _ (by simp) (by decide)
          have hf3 : atomArm "i64" .i64 ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") :=
            atomArm_miss "i64" .i64 off _ (by simp) (by decide)
          have hf4 : atomArm "string" .string ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") :=
            atomArm_miss "string" .string off _ (by simp) (by decide)
          have hf5 : unaryArm "option<" Ty.option (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") :=
            unaryArm_miss "option<" Ty.option (tyP f) off _ (by simp) (by decide)
          have hf6 : unaryArm "list<" Ty.list (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") :=
            unaryArm_miss "list<" Ty.list (tyP f) off _ (by simp) (by decide)
          have hf7 : unaryArm "result<_, " Ty.resultErr (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<_, ") :=
            unaryArm_miss "result<_, " Ty.resultErr (tyP f) off _ (by simp) (by decide)
          have hf8 : resultFlexArm (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") :=
            resultFlexArm_miss (tyP f) off _ (by simp)
          have hf9 : binaryArm "tuple<" Ty.tuple (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "tuple<") :=
            binaryArm_miss "tuple<" Ty.tuple (tyP f) off _ (by simp) (by decide)
          have hf10 : unaryArm "stream<" Ty.stream (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "stream<") :=
            unaryArm_miss "stream<" Ty.stream (tyP f) off _ (by simp) (by decide)
          have hf11 : unaryArm "future<" Ty.future (tyP f) ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "future<") :=
            unaryArm_miss "future<" Ty.future (tyP f) off _ (by simp) (by decide)
          have hf12 : handleArm "own<" Ty.own ⟨off, ("borrow<" ++ String.ofList (c0 :: w0) ++ ">").toList ++ rest⟩
              = .error (tokErr off "own<") :=
            handleArm_miss "own<" Ty.own off _ (by simp) (by decide)
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_right hf8 (orElse_ok_right hf9
                (orElse_ok_right hf10 (orElse_ok_right hf11 (orElse_ok_right hf12
                  (orElse_ok_left (handleArm_self "borrow<" Ty.borrow c0 w0 off rest hal0 hall)))))))))))))]

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

/-- The package-id discipline (the name gate is at `tyPre` — the
    handle refs' fragment gate needs it there). -/
def witIdOk (s : String) : Bool := identOk idChar s

/-- The AST-side wellformedness the round-trip laws ride: every name —
    the id, interface names, record names, field names — is
    identifier-shaped. The closed `Ty` grammar needs no gate (a
    malformed type shape is unconstructible). -/
def WitOk (p : Package) : Bool :=
  witIdOk p.id
    && p.interfaces.all (fun i =>
      witNameOk i.name
        && i.resources.all (fun r => witNameOk r.name)
        && i.records.all (fun r =>
          witNameOk r.name && r.fields.all (fun f =>
            witNameOk f.name && tyPre f.ty)))

/-- The AST-side gate's membership form (the round-trip's side
    condition, unpacked). The `tyPre` conjunct is the fragment gate
    (the D2 remainder LANDED): every ty row now parses — the
    conjunct's residual bite is the handle refs' name discipline
    (`tyPre (.own n) = witNameOk n`) and the nested tys' recursion;
    the resource DECLARATIONS ride the engine (`resourceLineG`) and
    only gate on their names. -/
theorem WitOk_spec (p : Package) (h : WitOk p = true) :
    witIdOk p.id = true
      ∧ (∀ i ∈ p.interfaces, witNameOk i.name = true
          ∧ (∀ r ∈ i.resources, witNameOk r.name = true)
          ∧ (∀ r ∈ i.records, witNameOk r.name = true
              ∧ (∀ f ∈ r.fields, witNameOk f.name = true
                  ∧ tyPre f.ty = true))) := by
  unfold WitOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hid, hinters⟩ := h
  refine ⟨hid, fun i hi => ?_⟩
  have h1 := hinters i hi
  obtain ⟨⟨h2, h0⟩, h3⟩ := h1
  refine ⟨h2, fun r hr => h0 r hr, fun r hr => h3 r hr⟩

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
        unaryArm "result<_, " Ty.resultErr inner, resultFlexArm inner,
        binaryArm "tuple<" .tuple inner, unaryArm "stream<" .stream inner,
        unaryArm "future<" .future inner, handleArm "own<" Ty.own,
        handleArm "borrow<" Ty.borrow],
      ∃ e, p cur = .error e := by
    intro p hp
    simp only [List.mem_cons] at hp
    obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hp := hp
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
    · obtain ⟨e, he⟩ := hkw "result<_, " (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [unaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "result<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [resultFlexArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "tuple<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [binaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "stream<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [unaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "future<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [unaryArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "own<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [handleArm, he]⟩
    · obtain ⟨e, he⟩ := hkw "borrow<" (by simp [TextKit.isIdentChar])
      exact ⟨e, by simp only [handleArm, he]⟩
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
  | stream a => simp [Render.ty, TextKit.isIdentChar]
  | future a => simp [Render.ty, TextKit.isIdentChar]
  | resultOk a => simp [Render.ty, TextKit.isIdentChar]
  | resultErr b => simp [Render.ty, TextKit.isIdentChar]
  | own n => simp [Render.ty, TextKit.isIdentChar]
  | borrow n => simp [Render.ty, TextKit.isIdentChar]

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
      -- the fragment gate (the D2 remainder landed): a non-`tyPre`
      -- result is the loud refusal — the scan never returns outside
      -- the fragment (the gate's last tooth: the handle refs' name
      -- discipline — `own<9bad>`'s maximal-munch name run is not
      -- identifier-shaped)
      if !tyPre t then
        .error { ParseError.base cur.off [] with
                 message := s!"WIT type outside the parsed fragment — \
handle refs (own/borrow) need an identifier-shaped resource name" }
      else if cur.cs.take (Render.ty t).length = (Render.ty t).toList then
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
    cur'.off = cur.off + (Render.ty t).length ∧
    tyPre t = true := by
  simp only [tyScan] at h
  cases hp : tyP cur.cs.length cur with
  | error e => rw [hp] at h; simp at h
  | ok r =>
      obtain ⟨a, b⟩ := r
      simp only [hp] at h
      cases hb : tyPre a with
      | false =>
          rw [if_pos (by rw [hb]; simp)] at h
          simp at h
      | true =>
          rw [if_neg (by rw [hb]; simp)] at h
          by_cases hguard : cur.cs.take (Render.ty a).length = (Render.ty a).toList
          · rw [if_pos hguard] at h
            obtain ⟨hab, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
            cases hab
            exact ⟨hguard, (Cursor.mk.inj hcc).2.symm, (Cursor.mk.inj hcc).1.symm, hb⟩
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
  -- the write-side gate IS the fragment gate (the D2 remainder
  -- landed: the gate's residual bite is the handle refs' name
  -- discipline)
  pre := tyPre
  head := .cls TextKit.isIdentChar
  munch := Option.some nameChar
  scan_post := fun _ _ _ h => (tyScan_ok h).2.2.2
  scan_exact := by
    intro cur t cur' h
    obtain ⟨h1, h2, -, -⟩ := tyScan_ok h
    show cur.cs = (Render.ty t).toList ++ cur'.cs
    rw [h2, ← h1, List.take_append_drop]
  scan_off := by
    intro cur t cur' h
    obtain ⟨-, -, h3, -⟩ := tyScan_ok h
    exact h3
  scan_head := by
    intro cur t cur' h
    obtain ⟨h1, -, -, -⟩ := tyScan_ok h
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
    intro k t sfx hpre hmunch
    have h1 : ((Render.ty t).toList ++ sfx).length
        = (Render.ty t).length + sfx.length := by
      rw [List.length_append, String.length_toList]
    show tyScan ⟨k, (Render.ty t).toList ++ sfx⟩
      = .ok (t, ⟨k + (Render.ty t).length, sfx⟩)
    simp only [tyScan, h1,
      tyP_ok t hpre ((Render.ty t).length + sfx.length) k sfx (by omega) hmunch]
    rw [if_neg (by simp [hpre]),
      if_pos (by rw [String.length_toList.symm]; exact List.take_left),
      String.length_toList.symm, List.drop_left]
  consumes := by
    intro cur t cur' h
    obtain ⟨h1, h2, -, -⟩ := tyScan_ok h
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

/-- A resource line's raw: `resource `, the name, `;\n`. -/
abbrev ResourceRaw := Unit × (String × Unit)

/-- An interface's raw: the `interface ` marker, the name, ` {\n`, the
    resource lines, the record blocks, `}\n`. -/
abbrev InterfaceRaw :=
  Unit × (String × (Unit × (List ResourceRaw × (List RecordRaw × Unit))))

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

def resourceToRaw (r : Resource) : ResourceRaw := ((), (r.name, ()))

/-- The resource lines' decode (every line's shape is fixed; no
    bits). -/
def resourcesOfRaws : List ResourceRaw → Option (List Resource)
  | [] => Option.some []
  | ((), (n, ())) :: rest =>
      (resourcesOfRaws rest).map (fun l => { name := n } :: l)

def ifaceToRaw (i : Interface) : InterfaceRaw :=
  ((), (i.name, ((), (List.map resourceToRaw i.resources,
    (List.map recordToRaw i.records, ())))))

/-- An interface's decode: the record names' AND the resource-decl
    names' nodup are DECIDED here (the runtime route of the
    elaboration-level `by decide` defaults) — a duplicate record name
    or duplicate resource declaration is the loud refusal, never a
    silent acceptance. -/
def ifaceOfRaw : InterfaceRaw → Option Interface
  | (_, (n, (_, (rsr, (rs, _))))) =>
      match resourcesOfRaws rsr with
      | Option.some rsrc =>
          match recordsOfRaws rs with
          | Option.some rcds =>
              if hnd : (rcds.map Record.name).Nodup ∧ (rsrc.map Resource.name).Nodup then
                Option.some
                  { name := n, records := rcds, resources := rsrc,
                    records_nodup := hnd.1, resources_nodup := hnd.2 }
              else Option.none
          | Option.none => Option.none
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

/-- The resource lines' raw exactness. -/
theorem resourcesOfRaws_exact : ∀ (raws : List ResourceRaw) (rs : List Resource),
    resourcesOfRaws raws = Option.some rs → rs.map resourceToRaw = raws
  | [], rs, h => by
      simp only [resourcesOfRaws, Option.some.injEq] at h
      subst h
      rfl
  | ((), (n, ())) :: rest, rs, h => by
      simp only [resourcesOfRaws, Option.map_some, Option.some.injEq] at h
      cases hrs : resourcesOfRaws rest with
      | none => rw [hrs] at h; simp at h
      | some rs' =>
          rw [hrs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          cases h
          show List.map resourceToRaw ({ name := n } :: rs') = ((), (n, ())) :: rest
          rw [List.map_cons, resourcesOfRaws_exact rest rs' hrs]
          rfl

theorem resourcesOfRaws_map : ∀ (rs : List Resource),
    resourcesOfRaws (List.map resourceToRaw rs) = Option.some rs
  | [] => rfl
  | r :: rs => by
      show resourcesOfRaws (((), (r.name, ())) :: List.map resourceToRaw rs) = _
      simp only [resourcesOfRaws]
      rw [resourcesOfRaws_map rs]
      rfl

theorem ifaceOfRaw_exact : ∀ (ir : InterfaceRaw) (i : Interface),
    ifaceOfRaw ir = Option.some i → ifaceToRaw i = ir := by
  intro ir
  cases ir with
  | mk u pair =>
      obtain ⟨n, pair2⟩ := pair
      obtain ⟨u2, rsr, pair3⟩ := pair2
      obtain ⟨rs, u3⟩ := pair3
      cases u; cases u2; cases u3
      intro i h
      simp only [ifaceOfRaw, Option.some.injEq] at h
      cases hrsr : resourcesOfRaws rsr with
      | none => rw [hrsr] at h; simp at h
      | some rsrc =>
          rw [hrsr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          cases hrs : recordsOfRaws rs with
          | none => rw [hrs] at h; simp at h
          | some rcds =>
              rw [hrs] at h
              simp only [Option.map_some, Option.some.injEq] at h
              by_cases hnd : (rcds.map Record.name).Nodup ∧ (rsrc.map Resource.name).Nodup
              · rw [dif_pos hnd] at h
                cases h
                show ((), (n, ((), (List.map resourceToRaw rsrc,
                  (List.map recordToRaw rcds, ()))))) = _
                rw [resourcesOfRaws_exact rsr rsrc hrsr,
                  recordsOfRaws_exact rs rcds hrs]
              · rw [dif_neg hnd] at h
                cases h

theorem ifaceOfRaw_toRaw (i : Interface) : ifaceOfRaw (ifaceToRaw i) = Option.some i := by
  obtain ⟨n, rs, rsrc, hd, hrnd⟩ := i
  simp only [ifaceToRaw, ifaceOfRaw, resourcesOfRaws_map, recordsOfRaws_map]
  exact dif_pos ⟨hd, hrnd⟩

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
/-- One resource line: `resource `, the name, `;\n` (the decl's
    canonical bytes — `Render.resource`; the D2 RESOURCE rows — the
    engine-level face, unlike the deferred ty-level rows). -/
def resourceLineG : TextKit.Grammar ResourceRaw :=
  .seq (.atom (litAtom "resource " (by decide)))
    (.seq (.atom nameAtom)
      (.atom (litAtom ";\n" (by decide))))

open TextKit in
/-- One interface block: the marker, the name, ` {\n`, the resource
    lines, the record blocks, `}\n` (the renderer's canonical order —
    `Render.interface`). -/
def ifaceG : TextKit.Grammar InterfaceRaw :=
  .seq (.atom (litAtom "interface " (by decide)))
    (.seq (.atom nameAtom)
      (.seq (.atom (litAtom " {\n" (by decide)))
        (.seq (.rep resourceLineG)
          (.seq (.rep recordG)
            (.atom (litAtom "}\n" (by decide)))))))

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
    TextKit.Grammar.valueOk fieldG (fieldToRaw f)
      = (nameAtom.pre f.name && tyPre f.ty) := by
  simp only [fieldG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    fieldToRaw, litAtom, TextKit.constStrLex, tyAtom]
  simp [← witNameOk_eq]

theorem valueOk_fieldLineG (g : Field) (h : witNameOk g.name = true)
    (hty : tyPre g.ty = true) :
    TextKit.Grammar.valueOk fieldLineG (fieldToRaw g, ()) = true := by
  show TextKit.Grammar.valueOk fieldLineG (((), (g.name, ((), (g.ty, ())))), ()) = true
  simp only [fieldLineG, fieldG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    litAtom, TextKit.constStrLex, fieldToRaw, tyAtom, ← witNameOk_eq]
  simp [h, hty]

theorem valueOk_fields : ∀ (fs : List Field),
    (∀ f ∈ fs, witNameOk f.name = true ∧ tyPre f.ty = true) →
    TextKit.Grammar.valueOk fieldsG (fieldsToRaw fs) = true
  | [], _ => rfl
  | f :: fs, h => by
      obtain ⟨hf, hfty⟩ := h f (List.mem_cons_self ..)
      have hrep : (fs.map (fun g => (fieldToRaw g, ()))).all
          (fun z => TextKit.Grammar.valueOk fieldLineG z) = true := by
        rw [List.all_eq_true]
        intro z hz
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
        show TextKit.Grammar.valueOk fieldLineG (((), (g.name, ((), (g.ty, ())))), ()) = true
        have hp := h g (List.mem_cons_of_mem _ hg)
        exact valueOk_fieldLineG g hp.1 hp.2
      simp only [fieldsToRaw, fieldsG, TextKit.Grammar.valueOk_seq,
        TextKit.Grammar.valueOk_opt_none, TextKit.Grammar.valueOk_rep,
        Bool.true_and, List.all_cons]
      simp [valueOk_fieldLineG f hf hfty, hrep]

theorem valueOk_record : ∀ (r : Record),
    witNameOk r.name = true →
    (∀ f ∈ r.fields, witNameOk f.name = true ∧ tyPre f.ty = true) →
    TextKit.Grammar.valueOk recordG (recordToRaw r) = true := by
  intro r hnm hf
  simp only [recordToRaw, recordG, TextKit.Grammar.valueOk_seq,
    TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex]
  simp [valueOk_fields r.fields hf, ← witNameOk_eq, hnm]

/-- The resource line's valueOk IS the resource name's gate (the
    same `&& true` residue as the field's). -/
theorem valueOk_resourceLineG (r : Resource) (h : witNameOk r.name = true) :
    TextKit.Grammar.valueOk resourceLineG (resourceToRaw r) = true := by
  show TextKit.Grammar.valueOk resourceLineG (((), (r.name, ()))) = true
  simp only [resourceLineG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    litAtom, TextKit.constStrLex, resourceToRaw, ← witNameOk_eq]
  simp [h]

theorem valueOk_resources : ∀ (rs : List Resource),
    (∀ r ∈ rs, witNameOk r.name = true) →
    TextKit.Grammar.valueOk (.rep resourceLineG) (List.map resourceToRaw rs) = true
  | [], _ => rfl
  | r :: rs, h => by
      have hr : witNameOk r.name = true := h r (List.mem_cons_self ..)
      have hrep : (rs.map resourceToRaw).all
          (fun z => TextKit.Grammar.valueOk resourceLineG z) = true := by
        rw [List.all_eq_true]
        intro z hz
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
        exact valueOk_resourceLineG g (h g (List.mem_cons_of_mem _ hg))
      simp only [TextKit.Grammar.valueOk_rep, List.all_cons]
      simp [valueOk_resourceLineG r hr, hrep]

theorem valueOk_iface : ∀ (i : Interface),
    witNameOk i.name = true →
    (∀ r ∈ i.resources, witNameOk r.name = true) →
    (∀ r ∈ i.records, witNameOk r.name = true
      ∧ (∀ f ∈ r.fields, witNameOk f.name = true ∧ tyPre f.ty = true)) →
    TextKit.Grammar.valueOk ifaceG (ifaceToRaw i) = true := by
  intro i hnm hrs hrec
  have hres : (List.map resourceToRaw i.resources).all
      (fun z => TextKit.Grammar.valueOk resourceLineG z) = true :=
    valueOk_resources i.resources hrs
  have hrep : (List.map recordToRaw i.records).all
      (fun z => TextKit.Grammar.valueOk recordG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨r, hr2, rfl⟩ := List.mem_map.mp hz
    exact valueOk_record r (hrec r hr2).1 (hrec r hr2).2
  simp only [ifaceToRaw, ifaceG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    TextKit.Grammar.valueOk_rep, litAtom, TextKit.constStrLex]
  simp [hres, hrep, ← witNameOk_eq, hnm]

theorem valueOk_package (p : Package) (hok : WitOk p = true) :
    TextKit.Grammar.valueOk pkgGrammar p = true := by
  obtain ⟨hid, hn⟩ := WitOk_spec p hok
  have hrep : (List.map ifaceToRaw p.interfaces).all
      (fun z => TextKit.Grammar.valueOk ifaceG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    have hi3 := hn i hi
    exact valueOk_iface i hi3.1 hi3.2.1 (fun r hr => hi3.2.2 r hr)
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

/-- The resource line's derived print IS the renderer's (the
    resource rows' byte tie). -/
theorem printG_resourceLine (r : Resource) :
    TextKit.Grammar.printG resourceLineG (resourceToRaw r) = Render.resource r := by
  simp [resourceLineG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    resourceToRaw, litAtom, TextKit.constStrLex, nameAtom_print, Render.resource,
    String.append_assoc]

theorem printG_resources : ∀ (rs : List Resource),
    TextKit.Grammar.printG (.rep resourceLineG) (List.map resourceToRaw rs)
      = Render.resourcesJoin rs
  | [] => rfl
  | r :: rs => by
      show TextKit.Grammar.printG resourceLineG (resourceToRaw r) ++
        TextKit.Grammar.printG (.rep resourceLineG) (List.map resourceToRaw rs) = _
      rw [printG_resourceLine, printG_resources rs]
      simp [Render.resourcesJoin, String.append_assoc]

theorem printG_iface (i : Interface) :
    TextKit.Grammar.printG ifaceG (ifaceToRaw i) = Render.interface i := by
  obtain ⟨n, rs, rsrc, hd, hnd⟩ := i
  show TextKit.Grammar.printG ifaceG
    ((), (n, ((), (List.map resourceToRaw rsrc, (List.map recordToRaw rs, ()))))) = _
  simp only [ifaceG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, nameAtom_print]
  rw [printG_resources, printG_records]
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
    `run (print g x) = ok x` speak the RENDERER's spellings). The gate
    is the round-trip fragment: the printer drops the resource
    declarations (`ifaceToRaw` carries name + records only), so a
    resource-carrying package prints resource-free — inside `WitOk`
    the renderer emits none, and the bytes agree. -/
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

/-! ## the world face (the func-level async row's parse direction)

The world BLOCK's parse-back (the `Wit.World` header's named
follow-up, paid with the async row): `Render.world`'s image parses
under the SAME grammar-layer discipline as the package face — the
nested seq/rep/opt spine under the ONE `rel` codec, no `alt`, no
`fix` (the func/iface dispatch rides the OPTIONAL func body: an item
raw carries `Option FuncRaw`, the `none` face IS the by-name
interface form — the dispatch lives in the DECODE, never in an alt
node, so the coherence fold stays trivial). The async row's spelling
is the optional literal `"async "` before `func(` — the WIT spec's
current shape. The accepted language is `Render.world`'s image
(comment-stripped), the same honesty as the package face.

The intercalate discipline: the params' bytes are `"a: u64, b: u64"`
— the separator BETWEEN. The engine's trailing-delimiter discipline
cannot print a separator BETWEEN, so the split rides the opt-FIRST
face: `opt param, rep(", " param)` — and the decode REFUSES the
junk faces the split admits (a leading comma; a trailing comma is
refused at the GRAMMAR level: `"func(a: u64, )"`'s tail parses as
sep-then-fail and the closer's `)` never matches). -/

/-- One param's raw parse shape: the name, `: `, the ty token. -/
abbrev ParamRaw := String × (Unit × Ty)

/-- The params' raw: the opt-FIRST intercalate split — `some p`
    seeds the list, the rep carries each `", "`-led continuation; the
    empty face is `none` + the empty rep. A leading comma (the
    `none`-seed with a nonempty rep) is the decode's loud refusal. -/
abbrev ParamsRaw := Option ParamRaw × List (Unit × ParamRaw)

/-- A func body's raw: `: `, the optional `async `, `func(`, the
    params, `)`, the optional ` -> ty`. -/
abbrev FuncRaw :=
  Unit × (Option Unit × (Unit × (ParamsRaw × (Unit × Option (Unit × Ty)))))

/-- One item's raw: the direction literal, the name, the optional
    func body, `;\n` (the `none` face is the by-name interface form). -/
abbrev ItemRaw := Unit × (String × (Option FuncRaw × Unit))

/-- The world block's raw: `world `, the name, ` {\n`, the import
    lines, the export lines, `}\n`. -/
abbrev WorldRaw := Unit × (String × (Unit × (List ItemRaw × (List ItemRaw × Unit))))

def paramToRaw (p : Field) : ParamRaw := (p.name, ((), p.ty))

def paramOfRaw : ParamRaw → Field
  | (n, (_, t)) => ⟨n, t⟩

theorem paramOfRaw_toRaw (p : Field) : paramOfRaw (paramToRaw p) = p := rfl
theorem paramToRaw_ofRaw (pr : ParamRaw) : paramToRaw (paramOfRaw pr) = pr := rfl

/-- The async flag's raw: the `some` bit IS the flag (the optional
    literal `"async "`'s presence). -/
def asyncToRaw : Bool → Option Unit :=
  fun b => if b then Option.some () else Option.none

/-- The async bit's decode. -/
def asyncOfRaw : Option Unit → Bool := Option.isSome

theorem asyncOfRaw_toRaw (b : Bool) : asyncOfRaw (asyncToRaw b) = b := by
  cases b <;> rfl

theorem asyncToRaw_ofRaw (aop : Option Unit) (b : Bool)
    (h : asyncOfRaw aop = b) : asyncToRaw b = aop := by
  cases aop with
  | none => cases b with | false => rfl | true => simp [asyncOfRaw] at h
  | some u => cases u; cases b with | false => simp [asyncOfRaw] at h | true => rfl

/-- The result option's raw (the `Unit` rides the `" -> "` literal). -/
def resultToRaw : Option Ty → Option (Unit × Ty) :=
  Option.map (fun t => ((), t))

def resultOfRaw : Option (Unit × Ty) → Option Ty :=
  Option.map (fun z => z.2)

theorem resultOfRaw_toRaw (r : Option Ty) : resultOfRaw (resultToRaw r) = r := by
  cases r with | none => rfl | some t => rfl

theorem resultToRaw_ofRaw (res : Option (Unit × Ty)) (r : Option Ty)
    (h : resultOfRaw res = r) : resultToRaw r = res := by
  cases res with
  | none => cases r with | none => rfl | some t => simp [resultOfRaw] at h
  | some z =>
      obtain ⟨u, t⟩ := z
      cases u
      have h2 : resultOfRaw (some ((), t)) = some t := rfl
      rw [h2] at h
      cases h
      rfl

def paramsToRaws : List Field → ParamsRaw
  | [] => (Option.none, [])
  | p :: ps => (Option.some (paramToRaw p), ps.map (fun q => ((), paramToRaw q)))

/-- The params' decode: the leading comma's junk face (`none` seed,
    nonempty rep) is the loud refusal. -/
def paramsOfRaws : ParamsRaw → Option (List Field)
  | (Option.none, []) => Option.some []
  | (Option.some p, rest) =>
      Option.some (paramOfRaw p :: rest.map (fun z => paramOfRaw z.2))
  | (Option.none, _ :: _) => Option.none

theorem paramsOfRaws_toRaws : ∀ (ps : List Field),
    paramsOfRaws (paramsToRaws ps) = Option.some ps
  | [] => rfl
  | p :: ps => by
      show paramsOfRaws (Option.some (paramToRaw p),
        ps.map (fun q => ((), paramToRaw q))) = Option.some (p :: ps)
      have hmap : (ps.map (fun q => ((), paramToRaw q))).map
          (fun z => paramOfRaw z.2) = ps := by
        rw [List.map_map]
        exact List.map_id'' (fun q => paramOfRaw_toRaw q) ps
      simp only [paramsOfRaws, hmap, paramOfRaw_toRaw, List.cons.injEq]

/-- The params' exact face: a decoded param list re-encodes to the
    raw it came from (law 2's per-level content). -/
def paramsToRaws_of : ∀ (raw : ParamsRaw) (ps : List Field),
    paramsOfRaws raw = Option.some ps → paramsToRaws ps = raw
  | (Option.none, []), [], _ => rfl
  | (Option.some p, rest), ps, h => by
      simp only [paramsOfRaws, Option.some.injEq] at h
      subst h
      show (Option.some (paramToRaw (paramOfRaw p)),
        (rest.map (fun z => paramOfRaw z.2)).map
          (fun q => ((), paramToRaw q))) = (Option.some p, rest)
      rw [List.map_map]
      have hz : ∀ z : Unit × ParamRaw,
          ((fun q => ((), paramToRaw q)) ∘ fun z => paramOfRaw z.2) z = z := by
        intro z
        obtain ⟨u, pr⟩ := z
        cases u
        show ((), paramToRaw (paramOfRaw pr)) = ((), pr)
        rw [paramToRaw_ofRaw]
      rw [List.map_id'' hz rest, paramToRaw_ofRaw]

/-! ### the items -/

/-- The item's write-side gate (the WorldOk discipline's per-item
    face): a func's name/params/result ride the name + fragment
    gates; the by-name interface form is a REFERENCE — its decode
    carries the name alone, so the gate refuses an iface item with a
    body (the honest fragment: the body lives in the interface's own
    declaration, out of the world-row's scope). -/
def itemOk : Item → Bool
  | .func f =>
      witNameOk f.name
        && (f.params.all (fun p => witNameOk p.name && tyPre p.ty)
              && (match f.result with
                  | Option.some t => tyPre t
                  | Option.none => true))
  | .iface i =>
      i.records.isEmpty && (i.resources.isEmpty && witNameOk i.name)

/-- The func body's raw (the item's `some` face): the async bit, the
    params, the result — each through its own raw. -/
def funcBodyToRaw (f : Func) : FuncRaw :=
  ((), (asyncToRaw f.async,
    ((), (paramsToRaws f.params, ((), resultToRaw f.result)))))

def itemToRaw : Item → ItemRaw
  | .func f => ((), (f.name, (Option.some (funcBodyToRaw f), ())))
  | .iface i => ((), (i.name, (Option.none, ())))

/-- The func body's decode: the params/result/async raws decode
    through their own faces (each refusing its junk loudly). -/
def funcBodyOfRaw : FuncRaw → Option (Option Unit × (List Field × Option Ty))
  | ((), (aop, ((), (pr, ((), res))))) =>
      match paramsOfRaws pr with
      | Option.none => Option.none
      | Option.some ps => Option.some (aop, (ps, resultOfRaw res))

/-- The item's decode: the func/iface dispatch rides the OPTIONAL
    func body — `none` IS the by-name interface form. -/
def itemOfRaw : ItemRaw → Option Item
  | ((), (n, (Option.none, _))) =>
      Option.some (.iface { name := n, records := [], resources := [] })
  | ((), (n, (Option.some fb, _))) =>
      match funcBodyOfRaw fb with
      | Option.none => Option.none
      | Option.some (aop, (ps, res)) =>
          Option.some (Item.func { name := n, params := ps, result := res, async := asyncOfRaw aop })

theorem funcBodyOfRaw_toRaw (f : Func) :
    funcBodyOfRaw (funcBodyToRaw f)
      = Option.some (asyncToRaw f.async, (f.params, f.result)) := by
  show ((match paramsOfRaws (paramsToRaws f.params) with
      | Option.none => Option.none
      | Option.some ps =>
          Option.some (asyncToRaw f.async,
            (ps, resultOfRaw (resultToRaw f.result))))
    = _)
  rw [paramsOfRaws_toRaws, resultOfRaw_toRaw]

theorem itemOfRaw_toRaw : ∀ (i : Item), itemOk i = true →
    itemOfRaw (itemToRaw i) = Option.some i
  | .func f, _ => by
      show itemOfRaw ((), (f.name, (Option.some (funcBodyToRaw f), ()))) = _
      simp only [itemOfRaw]
      rw [funcBodyOfRaw_toRaw]
      simp [asyncOfRaw_toRaw]
  | .iface i, h => by
      cases i with
      | mk n rcds rsrc _ _ =>
          cases rcds <;> cases rsrc
          · simp [itemToRaw, itemOfRaw]
          · simp [itemOk] at h
          · simp [itemOk] at h
          · simp [itemOk] at h

/-- The item's exact face: a decoded item re-encodes to the raw it
    came from (law 2's per-level content). -/
def itemToRaw_of : ∀ (raw : ItemRaw) (i : Item),
    itemOfRaw raw = Option.some i → itemToRaw i = raw
  | ((), (n, (Option.none, _))), .iface i, h => by
      show ((), (i.name, (Option.none, ()))) = ((), (n, (Option.none, ())))
      simp only [itemOfRaw, Option.some.injEq, Item.iface.injEq] at h
      cases h
      rfl
  | ((), (n, (Option.some fb, _))), .func f, h => by
      obtain ⟨u1, ⟨aop, ⟨u2, ⟨pr, ⟨u3, resf⟩⟩⟩⟩⟩ := fb
      cases u1; cases u2; cases u3
      simp only [itemOfRaw, funcBodyOfRaw] at h
      cases hp : paramsOfRaws pr with
      | none => simp only [hp] at h; simp at h
      | some ps =>
          simp only [hp] at h
          simp only [Option.some.injEq, Item.func.injEq] at h
          cases h
          show ((), (n, (Option.some (funcBodyToRaw
              { name := n, params := ps, result := resultOfRaw resf,
                async := asyncOfRaw aop }), ())))
            = ((), (n, (Option.some ((), (aop, ((), (pr, ((), resf)))))), ()))
          simp only [funcBodyToRaw]
          rw [paramsToRaws_of pr ps hp,
            resultToRaw_ofRaw resf (resultOfRaw resf) rfl,
            asyncToRaw_ofRaw aop (asyncOfRaw aop) rfl]
  | ((), (n, (Option.some fb, _))), .iface _, h => by
      simp only [itemOfRaw] at h
      cases hfb : funcBodyOfRaw fb with
      | none => rw [hfb] at h; simp at h
      | some x => rw [hfb] at h; simp at h
  | ((), (n, (Option.none, _))), .func _, h => by
      simp only [itemOfRaw] at h
      simp at h

def itemsToRaws (is : List Item) : List ItemRaw := is.map itemToRaw

def itemsOfRaws : List ItemRaw → Option (List Item)
  | [] => Option.some []
  | ir :: rest =>
      match itemOfRaw ir with
      | Option.some i => (itemsOfRaws rest).map (fun l => i :: l)
      | Option.none => Option.none

/-- The items' decode_encode (the rel node's wire law), gated on the
    per-item gate — the iface-body loss is the honest fragment's
    boundary (the gate rides the SUBTYPE carrier, the `witCodec`
    pattern). -/
theorem itemsOfRaws_map : ∀ (is : List Item), (∀ i ∈ is, itemOk i = true) →
    itemsOfRaws (itemsToRaws is) = Option.some is
  | [], _ => rfl
  | i :: is, h => by
      show itemsOfRaws (itemToRaw i :: itemsToRaws is) = _
      simp only [itemsOfRaws, itemOfRaw_toRaw i (h i (List.mem_cons_self ..))]
      rw [itemsOfRaws_map is (fun j hj => h j (List.mem_cons_of_mem _ hj)),
        Option.map_some]

theorem itemsOfRaws_exact : ∀ (iraws : List ItemRaw) (is : List Item),
    itemsOfRaws iraws = Option.some is → itemsToRaws is = iraws
  | [], [], _ => rfl
  | ir :: rest, is, h => by
      show is.map itemToRaw = ir :: rest
      simp only [itemsOfRaws] at h
      cases hio : itemOfRaw ir with
      | none => simp only [hio, Option.map_none] at h; simp at h
      | some i =>
          simp only [hio] at h
          cases hrest : itemsOfRaws rest with
          | none => simp only [hrest, Option.map_none] at h; simp at h
          | some is' =>
              simp only [hrest, Option.map_some, Option.some.injEq] at h
              cases h
              show (i :: is').map itemToRaw = ir :: rest
              rw [List.map_cons, itemToRaw_of ir i hio]
              exact congrArg (fun l => ir :: l) (itemsOfRaws_exact rest is' hrest)

/-! ### the world grammar (the engine's face: no alt, no fix) -/

open TextKit in
/-- One param: the name, `: `, the ty token. -/
def paramG : TextKit.Grammar ParamRaw :=
  .seq (.atom nameAtom) (.seq (.atom (litAtom ": " (by decide))) (.atom tyAtom))


open TextKit in
/-- One `", "`-led param continuation (the intercalate's separator
    rides the CONTINUATION — the trailing comma's junk face never
    parses: after `", "` a param is mandatory). -/
def paramSepG : TextKit.Grammar (Unit × ParamRaw) :=
  .seq (.atom (litAtom ", " (by decide))) paramG

open TextKit in
def paramsG : TextKit.Grammar ParamsRaw :=
  .seq (.opt paramG) (.rep paramSepG)

open TextKit in
def funcBodyG : TextKit.Grammar FuncRaw :=
  .seq (.atom (litAtom ": " (by decide)))
    (.seq (.opt (.atom (litAtom "async " (by decide))))
      (.seq (.atom (litAtom "func(" (by decide)))
        (.seq paramsG
          (.seq (.atom (litAtom ")" (by decide)))
            (.opt (.seq (.atom (litAtom " -> " (by decide))) (.atom tyAtom)))))))

open TextKit in
/-- One item line: the direction's literal, the name, the OPTIONAL
    func body, `;\n` — the func/iface dispatch rides the option (the
    `none` face IS the by-name interface form), never an alt node. -/
def itemG (dir : String) (hdir : dir.toList ≠ []) : TextKit.Grammar ItemRaw :=
  .seq (.atom (litAtom dir hdir))
    (.seq (.atom nameAtom)
      (.seq (.opt funcBodyG)
        (.atom (litAtom ";\n" (by decide)))))

def importG : TextKit.Grammar ItemRaw := itemG "  import " (by decide)

def exportG : TextKit.Grammar ItemRaw := itemG "  export " (by decide)

open TextKit in
def worldRawG : TextKit.Grammar WorldRaw :=
  .seq (.atom (litAtom "world " (by decide)))
    (.seq (.atom nameAtom)
      (.seq (.atom (litAtom " {\n" (by decide)))
        (.seq (.rep importG)
          (.seq (.rep exportG)
            (.atom (litAtom "}\n" (by decide)))))))

def worldToRaw (w : World) : WorldRaw :=
  ((), (w.name, ((), (w.imports.map itemToRaw, (w.exports.map itemToRaw, ())))))

/-- The world block's decode: the import/export names' nodup is
    DECIDED here (the runtime route of the elaboration-level `by
    decide` defaults) — a duplicate item name is the loud refusal,
    never a silent acceptance. -/
def worldOfRaw : WorldRaw → Option World
  | ((), (n, ((), (iraws, (eraws, ()))))) =>
      match itemsOfRaws iraws with
      | Option.none => Option.none
      | Option.some is =>
          match itemsOfRaws eraws with
          | Option.none => Option.none
          | Option.some es =>
              if hnd : (is.map Item.name).Nodup ∧ (es.map Item.name).Nodup then
                Option.some { name := n, imports := is, exports := es, imports_nodup := hnd.1, exports_nodup := hnd.2 }
              else Option.none

/-- The world's AST-side gate (the round-trip's side condition): every
    name identifier-shaped, every ty in the parsed fragment, and the
    by-name iface items BODY-FREE (the decode carries the name alone
    — the honest fragment's boundary). -/
def WorldOk (w : World) : Bool :=
  witNameOk w.name && w.imports.all itemOk && w.exports.all itemOk

theorem WorldOk_spec (w : World) (h : WorldOk w = true) :
    witNameOk w.name = true
      ∧ (∀ i ∈ w.imports, itemOk i = true)
      ∧ (∀ i ∈ w.exports, itemOk i = true) := by
  unfold WorldOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The world's decode_encode (the rel node's wire law), gated on
    WorldOk — the iface-item body loss is the gate's boundary. -/
def worldOfRaw_toRaw (w : World) (hok : WorldOk w = true) :
    worldOfRaw (worldToRaw w) = Option.some w := by
  obtain ⟨hnm, himp, hexp⟩ := WorldOk_spec w hok
  obtain ⟨n, imps, exps, h1, h2⟩ := w
  show worldOfRaw ((), (n, ((), (imps.map itemToRaw, (exps.map itemToRaw, ()))))) = _
  rw [show (imps.map itemToRaw) = itemsToRaws imps from rfl,
    show (exps.map itemToRaw) = itemsToRaws exps from rfl]
  simp only [worldOfRaw, itemsOfRaws_map imps himp, itemsOfRaws_map exps hexp]
  rw [dif_pos ⟨h1, h2⟩]

/-- The world's exact face: a decoded world re-encodes to the raw it
    came from (law 2's per-level content). -/
def worldToRaw_of : ∀ (raw : WorldRaw) (w : World),
    worldOfRaw raw = Option.some w → worldToRaw w = raw := by
  intro raw
  obtain ⟨u1, ⟨n, ⟨u0, ⟨iraws, ⟨eraws, u2⟩⟩⟩⟩⟩ := raw
  cases u1; cases u0; cases u2
  intro w h
  simp only [worldOfRaw] at h
  cases hio : itemsOfRaws iraws with
  | none => simp only [hio] at h; simp at h
  | some is =>
      simp only [hio] at h
      cases heo : itemsOfRaws eraws with
      | none => simp only [heo] at h; simp at h
      | some es =>
          simp only [heo] at h
          by_cases hnd : (is.map Item.name).Nodup ∧ (es.map Item.name).Nodup
          · rw [dif_pos hnd] at h
            simp only [Option.some.injEq] at h
            cases h
            simp only [worldToRaw]
            rw [show (is.map itemToRaw) = itemsToRaws is from rfl,
              show (es.map itemToRaw) = itemsToRaws es from rfl,
              itemsOfRaws_exact iraws is hio, itemsOfRaws_exact eraws es heo]
          · rw [dif_neg hnd] at h; simp at h

/-! ### the codec + the grammar value (the subtype carrier) -/

/-- The world codec (Kit.Correspondence's decode∘encode grade): the
    payload is the WorldOk-GATED subtype — the `witCodec` pattern
    (the iface-item body loss is the honest fragment's boundary, so
    the round trip rides the gate, never an unconditional lie). -/
def worldDecode (raw : WorldRaw) : Option { w : World // WorldOk w } :=
  match worldOfRaw raw with
  | Option.some w =>
      if h : WorldOk w = true then Option.some ⟨w, h⟩ else Option.none
  | Option.none => Option.none

def worldCodec : Kit.Codec WorldRaw { w : World // WorldOk w } where
  encode q := worldToRaw q.1
  decode := worldDecode
  policy raw := ∃ q, worldDecode raw = some q
  decode_encode q := by
    simp only [worldDecode, worldOfRaw_toRaw q.1 q.2]
    exact dif_pos q.2
  decode_some_policy := fun _ _ hq => ⟨_, hq⟩

/-- The exact face at the SUBTYPE carrier (the rel node's `exact`
    slot's shape). -/
def worldToRaw_ofSub : ∀ (raw : WorldRaw) (q : { w : World // WorldOk w }),
    worldDecode raw = Option.some q → worldToRaw q.1 = raw := by
  intro raw q h
  simp only [worldDecode] at h
  cases hwo : worldOfRaw raw with
  | none => simp only [hwo] at h; simp at h
  | some w =>
      simp only [hwo] at h
      by_cases hok : WorldOk w = true
      · rw [dif_pos hok] at h
        simp only [Option.some.injEq, Subtype.mk.injEq] at h
        cases h
        exact worldToRaw_of raw w hwo
      · rw [dif_neg hok] at h; simp at h

/-- THE world grammar: the nested seq/rep/opt spine under the ONE
    `rel` codec — no `alt` (the func/iface dispatch rides the optional
    func body), no `fix` (the ty recursion is the guarded leaf). -/
def worldGrammar : TextKit.Grammar { w : World // WorldOk w } :=
  .rel worldCodec (fun _ => true) (fun _ _ _ => rfl) worldToRaw_ofSub
    "world" [] worldRawG

/-- THE certificate discharge (06 §7's build-time check). -/
def worldCert : TextKit.Grammar.Predictive worldGrammar :=
  TextKit.Grammar.wfCheck_sound worldGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere — the ty token is a
    leaf). -/
def worldFixFree : TextKit.Grammar.FixFree worldGrammar := by
  repeat constructor

/-- Law 2's coherence premise: no `alt` node anywhere. -/
def worldCoherent : TextKit.Grammar.altCoherent worldGrammar := by
  repeat constructor

/-! ### the valueOk discipline (the WorldOk bridge) -/

theorem valueOk_paramG (p : Field) :
    TextKit.Grammar.valueOk paramG (paramToRaw p)
      = (witNameOk p.name && tyPre p.ty) := by
  simp only [paramG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
    paramToRaw, litAtom, TextKit.constStrLex, ← witNameOk_eq, tyAtom]
  rfl

theorem valueOk_params : ∀ (ps : List Field),
    (∀ p ∈ ps, witNameOk p.name = true ∧ tyPre p.ty = true) →
    TextKit.Grammar.valueOk paramsG (paramsToRaws ps) = true
  | [], _ => by
      show TextKit.Grammar.valueOk paramsG (Option.none, []) = true
      simp only [paramsG, TextKit.Grammar.valueOk_seq,
        TextKit.Grammar.valueOk_opt_none, TextKit.Grammar.valueOk_rep]
      rfl
  | p :: ps, h => by
      have hrep : (ps.map (fun q => ((), paramToRaw q))).all
          (fun z => TextKit.Grammar.valueOk paramSepG z) = true := by
        rw [List.all_eq_true]
        intro z hz
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
        show TextKit.Grammar.valueOk paramSepG ((), paramToRaw q) = true
        simp only [paramSepG, TextKit.Grammar.valueOk_seq,
          TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex]
        simp only [valueOk_paramG]
        simp [h q (List.mem_cons_of_mem _ hq)]
      simp only [paramsToRaws, paramsG, TextKit.Grammar.valueOk_seq,
        TextKit.Grammar.valueOk_opt_some, TextKit.Grammar.valueOk_rep]
      simp [valueOk_paramG p, hrep, h p (List.mem_cons_self ..)]

theorem valueOk_funcBodyG (f : Func)
    (hp : ∀ p ∈ f.params, witNameOk p.name = true ∧ tyPre p.ty = true)
    (hr : ∀ t, f.result = Option.some t → tyPre t = true) :
    TextKit.Grammar.valueOk funcBodyG (funcBodyToRaw f) = true := by
  show TextKit.Grammar.valueOk funcBodyG
    ((), (asyncToRaw f.async,
      ((), (paramsToRaws f.params, ((), resultToRaw f.result))))) = _
  cases hf : f.async
  · cases hres : f.result
    · simp [funcBodyG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
        litAtom, TextKit.constStrLex, TextKit.Grammar.valueOk_opt_none,
        TextKit.Grammar.valueOk_opt_some, resultToRaw, asyncToRaw, hf, hres,
        valueOk_params f.params hp]
    · simp [funcBodyG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
        litAtom, TextKit.constStrLex, TextKit.Grammar.valueOk_opt_none,
        TextKit.Grammar.valueOk_opt_some, resultToRaw, asyncToRaw, hf, hres,
        valueOk_params f.params hp, hr _ hres, tyAtom]
  · cases hres : f.result
    · simp [funcBodyG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
        litAtom, TextKit.constStrLex, TextKit.Grammar.valueOk_opt_none,
        TextKit.Grammar.valueOk_opt_some, resultToRaw, asyncToRaw, hf, hres,
        valueOk_params f.params hp]
    · simp [funcBodyG, TextKit.Grammar.valueOk_seq, TextKit.Grammar.valueOk_atom,
        litAtom, TextKit.constStrLex, TextKit.Grammar.valueOk_opt_none,
        TextKit.Grammar.valueOk_opt_some, resultToRaw, asyncToRaw, hf, hres,
        valueOk_params f.params hp, hr _ hres, tyAtom]

theorem valueOk_itemG (dir : String) (hdir : dir.toList ≠ []) (i : Item)
    (hok : itemOk i = true) :
    TextKit.Grammar.valueOk (itemG dir hdir) (itemToRaw i) = true := by
  cases i with
  | func f =>
      simp only [itemOk, Bool.and_eq_true, List.all_eq_true] at hok
      have hr : ∀ t, f.result = Option.some t → tyPre t = true := by
        intro t ht
        rw [ht] at hok
        exact hok.2.2
      cases hf : f.async <;>
        simp [itemG, itemToRaw, TextKit.Grammar.valueOk_seq,
          TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex,
          TextKit.Grammar.valueOk_opt_none, TextKit.Grammar.valueOk_opt_some,
          asyncToRaw, hf, valueOk_funcBodyG f hok.2.1 hr, hok.1,
          ← witNameOk_eq]
  | iface i =>
      cases i with
      | mk n rcds rsrc _ _ =>
        cases rcds <;> cases rsrc
        · show (itemG dir hdir).valueOk ((), (n, (Option.none, ()))) = true
          simp only [itemG, TextKit.Grammar.valueOk_seq,
            TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex,
            TextKit.Grammar.valueOk_opt_none, ← witNameOk_eq, Bool.and_true]
          simp only [itemOk, List.isEmpty, Bool.and_eq_true, Bool.and_true] at hok
          simp [hok]
        · simp only [itemOk, List.isEmpty, Bool.and_eq_true] at hok
          simp at hok
        · simp only [itemOk, List.isEmpty, Bool.and_eq_true] at hok
          simp at hok
        · simp only [itemOk, List.isEmpty, Bool.and_eq_true] at hok
          simp at hok

theorem valueOk_items (dir : String) (hdir : dir.toList ≠ []) :
    ∀ (is : List Item), (∀ i ∈ is, itemOk i = true) →
      ∀ x ∈ is, (itemG dir hdir).valueOk (itemToRaw x) = true
  | [], _, x, hx => by simp at hx
  | i :: is, h, x, hx => by
      simp only [List.mem_cons] at hx
      cases hx with
      | inl heq => rw [heq]; exact valueOk_itemG dir hdir i (h i (List.mem_cons_self ..))
      | inr hm =>
          exact valueOk_items dir hdir is
            (fun j hj => h j (List.mem_cons_of_mem _ hj)) x hm

theorem valueOk_world (q : { w : World // WorldOk w }) :
    TextKit.Grammar.valueOk worldGrammar q = true := by
  obtain ⟨hnm, himp, hexp⟩ := WorldOk_spec q.1 q.2
  have h1 : (q.1.imports.map itemToRaw).all (fun z => importG.valueOk z) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact valueOk_items "  import " (by decide) q.1.imports himp j hj
  have h2 : (q.1.exports.map itemToRaw).all (fun z => exportG.valueOk z) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact valueOk_items "  export " (by decide) q.1.exports hexp j hj
  show TextKit.Grammar.valueOk worldRawG (worldToRaw q.1) = true
  simp only [worldRawG, worldToRaw, TextKit.Grammar.valueOk_seq,
    TextKit.Grammar.valueOk_atom, litAtom, TextKit.constStrLex,
    TextKit.Grammar.valueOk_rep, ← witNameOk_eq, hnm]
  simp [h1, h2]

/-! ### the print faces (the derived print's bytes ARE the renderer's) -/

theorem printG_param (p : Field) :
    TextKit.Grammar.printG paramG (paramToRaw p) = Render.funcParam p := by
  simp [paramG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    paramToRaw, litAtom, TextKit.constStrLex, nameAtom_print, tyAtom,
    Render.funcParam, String.append_assoc]

theorem printG_paramSepG (pr : ParamRaw) :
    TextKit.Grammar.printG paramSepG ((), pr)
      = ", " ++ TextKit.Grammar.printG paramG pr := rfl

-- The intercalate-face block below proves `rfl` over `String.intercalate`,
-- whose body is core and NOT exposed — an exported theorem may not unfold
-- it, so the exposed section closes above it and the block rides
-- module-internal visibility (no cross-module consumer; exposure does not
-- change the proof term).
end -- public section

/-- The intercalate's cons face (the byte-tie's bridge between the
    engine's foldr print and the renderer's `String.intercalate`). -/
def intercalate_cons (s a : String) : ∀ (l : List String),
    String.intercalate s (a :: l) = a ++ l.foldr (fun x acc => s ++ x ++ acc) ""
  | [] => by simp
  | b :: l => by
      rw [String.intercalate_cons_cons, intercalate_cons s b l, List.foldr_cons]
      simp [String.append_assoc]

/-- The params' fold bridge (the rep-print's foldr vs the renderer's
    intercalate fold). -/
def printG_paramsFoldr : ∀ (ps : List Field),
    List.foldr (fun z acc => TextKit.Grammar.printG paramSepG z ++ acc) ""
        (ps.map (fun q => ((), paramToRaw q)))
      = ps.foldr (fun x acc => ", " ++ Render.funcParam x ++ acc) "" := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      show TextKit.Grammar.printG paramSepG ((), paramToRaw p)
        ++ List.foldr (fun z acc => TextKit.Grammar.printG paramSepG z ++ acc) ""
          (ps.map (fun q => ((), paramToRaw q))) = _
      rw [printG_paramSepG, printG_param, ih]
      rfl

theorem printG_params : ∀ (ps : List Field),
    TextKit.Grammar.printG paramsG (paramsToRaws ps)
      = String.intercalate ", " (ps.map Render.funcParam)
  | [] => by
      -- `String.intercalate` is core and NOT exposed — a module file (kernel
      -- included) may not unfold it, so the nil face rides the core's own
      -- `intercalate_nil` theorem instead of a definitional `rfl`.
      simp only [List.map_nil, String.intercalate_nil]
      rfl
  | p :: ps => by
      show TextKit.Grammar.printG paramsG
        (Option.some (paramToRaw p), ps.map (fun q => ((), paramToRaw q))) = _
      simp only [paramsG, TextKit.Grammar.printG_seq,
        TextKit.Grammar.printG_opt_some, TextKit.Grammar.printG_rep,
        litAtom, TextKit.constStrLex]
      rw [printG_paramsFoldr, printG_param, List.map_cons,
        intercalate_cons ", " (Render.funcParam p) (ps.map Render.funcParam),
        List.foldr_map]

@[expose] public section

/-- The literal merges the byte-tie's assoc-massaging needs (the
    `append_comma_nl` pattern: the kernel reduces adjacent literals;
    simp needs the named face). -/
def merge_colon_func : ": " ++ "func(" = ": func(" := rfl

def merge_colon_async : ": " ++ "async " = ": async " := rfl

def merge_async_func : "async " ++ "func(" = "async func(" := rfl

def merge_paren_arrow : ")" ++ " -> " = ") -> " := rfl

theorem printG_funcBody (f : Func) :
    TextKit.Grammar.printG funcBodyG (funcBodyToRaw f)
      = ": " ++ ((if f.async then "async " else "") ++ ("func("
          ++ (String.intercalate ", " (f.params.map Render.funcParam)
          ++ (")" ++ (match f.result with
                | Option.some t => " -> " ++ Render.ty t
                | Option.none => ""))))) := by
  show TextKit.Grammar.printG funcBodyG
    ((), (asyncToRaw f.async,
      ((), (paramsToRaws f.params, ((), resultToRaw f.result))))) = _
  simp only [funcBodyG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
    litAtom, TextKit.constStrLex, printG_params]
  cases f.async <;> cases f.result <;>
    simp [String.append_assoc, asyncToRaw, resultToRaw, tyAtom,
      TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
      TextKit.Grammar.printG_opt_none, TextKit.Grammar.printG_opt_some,
      Option.map_none, Option.map_some, merge_colon_func, merge_colon_async,
      merge_async_func, merge_paren_arrow]

theorem printG_item (dir : String) (hdir : dir.toList ≠ []) (i : Item) :
    TextKit.Grammar.printG (itemG dir hdir) (itemToRaw i)
      = Render.itemLine dir i := by
  cases i with
  | func f =>
      show TextKit.Grammar.printG (itemG dir hdir)
        ((), (f.name, (Option.some (funcBodyToRaw f), ()))) = _
      simp only [itemG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
        litAtom, TextKit.constStrLex, nameAtom_print]
      simp only [TextKit.Grammar.printG_opt_some, printG_funcBody]
      simp [Render.itemLine, Render.func, String.append_assoc]
      rfl
  | iface i =>
      show TextKit.Grammar.printG (itemG dir hdir)
        ((), (i.name, (Option.none, ()))) = _
      simp only [itemG, TextKit.Grammar.printG_seq, TextKit.Grammar.printG_atom,
        litAtom, TextKit.constStrLex, nameAtom_print]
      simp only [TextKit.Grammar.printG_opt_none]
      simp [Render.itemLine, String.append_assoc]

theorem printG_items (dir : String) (hdir : dir.toList ≠ []) :
    ∀ (is : List Item),
    List.foldr (fun z acc => (itemG dir hdir).printG z ++ acc) "" (is.map itemToRaw)
      = Render.itemsJoin (Render.itemLine dir) is
  | [] => rfl
  | i :: is => by
      show (itemG dir hdir).printG (itemToRaw i)
        ++ List.foldr (fun z acc => (itemG dir hdir).printG z ++ acc) ""
          (is.map itemToRaw) = _
      rw [printG_item dir hdir i, printG_items dir hdir is]
      simp [Render.itemsJoin, String.append_assoc]

/-- The derived printer's bytes ARE the renderer's (the world face's
    byte tie — the parse laws speak the RENDERER's spellings). -/
def printG_world (q : { w : World // WorldOk w }) :
    TextKit.Grammar.print worldGrammar q = Render.world q.1 := by
  show TextKit.Grammar.printG worldRawG (worldToRaw q.1) = _
  simp only [worldRawG, worldToRaw, TextKit.Grammar.printG_seq,
    TextKit.Grammar.printG_atom, litAtom, TextKit.constStrLex, nameAtom_print,
    TextKit.Grammar.printG_rep, importG, exportG]
  rw [printG_items "  import " (by decide) q.1.imports,
    printG_items "  export " (by decide) q.1.exports]
  simp [Render.world, Render.itemsJoin, String.append_assoc]
  rfl

/-! ### the entry + the laws (the generic theorems' instances) -/

theorem L_world : "world ".toList = 'w' :: "orld ".toList := rfl

/-- The world-block text is comment-free (its head is `world `, never
    `//` — the strip is the identity on the renderer's image). -/
def skipComments_world_sfx (sfx : List Char) :
    skipComments ("world ".toList ++ sfx) = "world ".toList ++ sfx := by
  show skipCommentsGo ("world ".toList ++ sfx).length
    ("world ".toList ++ sfx) = _
  have hl : ("world ".toList ++ sfx).length = (sfx.length + 5) + 1 := by
    rw [List.length_append, String.length_toList]
    have h6 : "world ".length = 6 := rfl
    omega
  rw [hl, L_world, List.cons_append]
  exact skipCommentsGo_ne (sfx.length + 5) 'w' _ rfl

/-- The total world-block parser: text → the WorldOk-gated world (the
    grammar's run entry over the comment-stripped bytes; every failure
    is a structured `ParseError` — position + expected set — and
    trailing garbage is a loud refusal). -/
def parseWorld (s : String) : Except ParseError { w : World // WorldOk w } :=
  TextKit.Grammar.run worldGrammar (stripComments s)

/-- THE WORLD PARSE LAW (05 §1's first honest law): every gated
    world's rendering parses back to exactly it — the
    `Grammar.run_print_fixFree` INSTANCE (the async row's round
    trip). -/
def parseWorld_print (w : World) (hok : WorldOk w = true) :
    parseWorld (Render.world w) = .ok ⟨w, hok⟩ := by
  have hstrip : stripComments (Render.world w) = Render.world w := by
    apply String.toList_inj.mp
    show String.toList (String.ofList (skipComments (Render.world w).toList)) = _
    rw [String.toList_ofList]
    have h1 : (Render.world w).toList
        = "world ".toList ++ (((w.name ++ " {\n"
            ++ (Render.itemsJoin Render.importItem w.imports
                ++ (Render.itemsJoin Render.exportItem w.exports ++ "}\n")))).toList) := by
      simp [Render.world, String.toList_append]
    rw [h1, skipComments_world_sfx]
  have hr : TextKit.Grammar.run worldGrammar (TextKit.Grammar.print worldGrammar ⟨w, hok⟩)
      = .ok ⟨w, hok⟩ :=
    TextKit.Grammar.run_print_fixFree worldGrammar worldFixFree worldCert ⟨w, hok⟩
      (valueOk_world ⟨w, hok⟩)
  rw [printG_world] at hr
  show TextKit.Grammar.run worldGrammar (stripComments (Render.world w)) = _
  rw [hstrip]
  exact hr

/-- THE WORLD CANONICALIZATION LAW (05 §1's second honest law, at the
    world face): accepted text IS the rendering of its result. -/
def renderWorld_parse (s : String) (q : { w : World // WorldOk w })
    (h : parseWorld s = .ok q) :
    Render.world q.1 = stripComments s := by
  unfold parseWorld at h
  simp only [TextKit.Grammar.run] at h
  split at h
  · exact absurd h (by simp)
  · rename_i x cur hrun
    split at h
    · rename_i hnil
      have hxp : x = q := Except.ok.inj h
      cases hxp
      have hpp := TextKit.Grammar.print_parse worldGrammar
        ((stripComments s).length + 1) worldCoherent hrun
      have h1 : (stripComments s).toList
          = (TextKit.Grammar.printG worldGrammar q).toList := by
        rw [hnil] at hpp
        rw [List.append_nil] at hpp
        exact hpp.1
      have h2 : stripComments s = TextKit.Grammar.printG worldGrammar q :=
        String.toList_inj.mp h1
      rw [h2]
      rw [← printG_world]
      rfl
    · exact absurd h (by simp)

end -- public section

end Wit.Parse

