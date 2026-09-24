/- 
# Wit.Parse — the total WIT parser: text → the typed AST

Owner: the Wit agent (the mandate tree, `wit/`).
Driving decisions: notes/v3/05-codegen.md §1 (the two honest laws:
`parse (print x) = ok x` — everything we print parses back;
`print (parse text) = canonicalize text` — accepted text normalizes) +
notes/v3/15-patterns.md #12 (the total parser + the inversion kit) +
notes/v3/13-interfaces.md (the WIT worlds row: the host skew check
READS component types — this parser is that reading's foundation, and
`Wit.Render` is its writing half).

## The accepted language — the renderer's image, plus comments

The parser accepts EXACTLY the text `Wit.Render` produces (the
canonical bytes), optionally preceded by `//`-comment lines — the
committed artifact of record `gen/schema-slice.wit` carries two. The
strictness is the canonicalization law's honesty: accepted text
normalizes to its comment-stripped bytes, and those bytes are the
rendering of the parse result (`render_parse` below). Whitespace
tolerance would break normalization — it is deliberately not accepted
(the accepted-byte-policy discipline: the policy rides the Codec row).

## The shape

TextKit combinators all the way (`tok`/`satisfy`/`many`/`orElse` over
`GParser`); errors are the converged `ParseError` (the Diag envelope
with position — never `none`, never a bare string). The closed-world
rejections enumerate the valid space + fill the did-you-mean from the
ONE engine (`TextKit.suggestFor`) — `curated` is this module's ONE
construction route for them.

TOTALITY: every definition is a plain structural match — the ty
recursion and the list loops ride a fuel `Nat` (one unit per nesting
step; the invariant `fuel ≥ remaining characters` holds at every entry
with the top-level fuel = the input length, because every level
consumes at least one character before recursing). This is 05 §1's
rep-progress discipline at the carrier TextKit fixes: `many` (used
inside the name scanner) already stops at zero progress; the block
loops use the explicit fuel because their bodies consume
variable-length words (the SchemaCore.Snapshot precedent: the loop
fuel is the genuine recursion measure, not hand-rolled plumbing).

## The laws

PROVED (below): the full per-level climb — `tyP_ok`, `fieldsGo_ok`,
`fieldsP_ok`, `recordCore_ok`, `recordsP_ok`, `interfaceP_ok`,
`interfacesP_ok`, `packageP_ok` — each level inverting the renderer's
join exactly, cursor included, under the `WitOk` side condition (the
AST carries names as plain strings; a name the scanner cannot rescan
has no parse — `WitOk` gates exactly that).

ASSEMBLED (landed after the per-level climb):

- `parse_print` (line ~1568) — the top assembly over `packageP_ok`.
- `witCodec` / `witRetraction` / `witImageIso` — the correspondence
  chain: the Codec row, the retraction (`inv_emb` = `parse_print`),
  and the image-iso upgrade (the renderer's image texts ≅ the
  well-named packages).

NAMED, NOT PROVED (the follow-up):

- `render_parse` : accepted text normalizes — `∀ s p, parse s = .ok p
  → Render.package p = stripComments s`. This is the inversion
  (soundness) direction: it needs the scanners' maximality + the loops'
  predictive-dispatch completeness — a full second proof effort, not
  begun. The artifact pin (WitTests reads `gen/schema-slice.wit`, parses,
  re-renders byte-identical) re-derives the bytes at the value level
  instead, as the snapshot lane did for its own canonicalization half.
- `witRetraction` / the image-iso upgrade (`toImageIso`): gated on
  `render_parse` — the retraction's `inv`-leg is exactly the
  canonicalization direction.

Core-only (imports `Wit`, `Wit.Render`, TextKit, Kit.Correspondence —
the cone rule: Kit/TextKit are the C0 substrate).

The five questions (notes/v3/01-core.md):
- root: Crossing — the WIT text read into the typed target grammar
  (the skew check's reading half).
- carrier grade: the correspondence row `witCodec` — the round-trip
  law in the type, the accepted-byte policy a field; the retraction /
  image-iso upgrade land with `render_parse`.
- spine reading: the artifact stage's inverse — the ONE parser every
  WIT-reading lane calls; `Wit.Render` is the ONE writer.
- ladder rung: rung 1-2 — total fuel-structural folds + small
  inductions (the inversion kit).
- gate row: WitTests' round-trip pins + the artifact integration pin
  (parse the committed gen/schema-slice.wit, re-render byte-identical);
  the axiom gate sweeps the Wit root.
-/

import Wit
import Wit.Render
import TextKit.Combinators
import TextKit.Lemmas
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
    `WitOk` below gates the AST side; `identP` enforces the byte side —
    the round-trip laws ride their agreement. -/
def identOk (q : Char → Bool) (s : String) : Bool :=
  match s.toList with
  | c :: w => c.isAlpha && w.all q
  | [] => false

/-! ## the curated errors (the ONE construction route) -/

/-- The rejected token's text: the maximal ident-ish run at the cursor
    (the `got` slot's content for token-level rejections). -/
def gotToken (cs : List Char) : String :=
  String.ofList (cs.takeWhile (fun c => TextKit.isIdentChar c || c == '-' || c == ':'))

/-- THE curated parse error: the expected set enumerated, the rejected
    token named, the did-you-mean filled by the ONE engine (05 §4's
    closed-world rule — this module's rejections all route here). -/
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

/-! ## the name scanner (TextKit's satisfy + many) -/

/-- An identifier: alpha head, then a maximal run of `q` characters
    (the `many` zero-progress stop ends the run — the delimiter's
    refusal). Total; never silent. -/
def identP (q : Char → Bool) : GParser String := fun cur =>
  match TextKit.satisfy "an identifier start" Char.isAlpha cur with
  | .error e => .error e
  | .ok (c, c1) =>
      match TextKit.many (TextKit.satisfy "an identifier character" q) c1 with
      | .ok (w, c2) => .ok (String.ofList (c :: w), c2)
      | .error e => .error e

/-! ## the type grammar (predictive: the eight heads are prefix-free) -/

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

/-! ## the record fields -/

/-- A field line's text (the renderer's `Render.field` — proved equal
    below). -/
def fieldText (f : Field) : String :=
  "    " ++ f.name ++ ": " ++ Render.ty f.ty ++ ","

/-- A field's core: `name: ty,` (the indent consumed by the caller). -/
def fieldCore (fuel : Nat) : GParser Field := fun cur =>
  match identP nameChar cur with
  | .error e => .error e
  | .ok (n, c1) =>
      match TextKit.tok ": " c1 with
      | .error e => .error e
      | .ok (_, c2) =>
          match tyP fuel c2 with
          | .error e => .error e
          | .ok (t, c3) =>
              match TextKit.tok "," c3 with
              | .error e => .error e
              | .ok (_, c4) => .ok (({ name := n, ty := t } : Field), c4)

/-- The rendered continuation block: each further field rides its
    preceding newline (the renderer's join). -/
def fieldsSepText : List Field → String := Render.fieldsTailJoin

/-- The rendered field block (the renderer's join). -/
def fieldsText : List Field → String := Render.fieldsJoin

/-- The fields' continuation loop: `("\n    " core)*`, dispatched
    predictively (the doctrine's FIRST-dispatch certificate, explicit):
    a continuation line starts `\n` + four spaces; the closing form
    `\n  }` shares the first three characters, so the dispatch looks
    four deep. The committed choice never swallows a deep failure —
    a typo inside a field surfaces at its own position. Total (fuel
    structural; each iteration consumes ≥ 5 characters). -/
def fieldsGo : Nat → GParser (List Field)
  | 0, cur => .error (curated cur "expected a field line or the record's closing brace"
    ["a field line (\"    <name>: <type>,\")", "the record's closing brace (\"  }\")"])
  | fuel + 1, cur =>
      match cur.cs with
      | '\n' :: ' ' :: ' ' :: ' ' :: _ =>
          match TextKit.tok "\n    " cur with
          | .error e => .error e
          | .ok (_, c1) =>
              match fieldCore fuel c1 with
              | .error e => .error e
              | .ok (f, c2) =>
                  match fieldsGo fuel c2 with
                  | .error e => .error e
                  | .ok (fs, c3) => .ok (f :: fs, c3)
      | _ => .ok ([], cur)

/-- The fields block: `"    " core` then the continuation loop,
    dispatched predictively on the head character (a field starts four
    spaces; a blank line / the closer starts `\n`). The committed
    choice never swallows a deep failure. -/
def fieldsP : Nat → GParser (List Field)
  | 0, cur => .error (curated cur "expected a field line or the record's closing brace"
    ["a field line (\"    <name>: <type>,\")", "the record's closing brace (\"  }\")"])
  | fuel + 1, cur =>
      match cur.cs.head? with
      | some ' ' =>
          match TextKit.tok "    " cur with
          | .error e => .error e
          | .ok (_, c1) =>
              match fieldCore fuel c1 with
              | .error e => .error e
              | .ok (f, c2) =>
                  match fieldsGo fuel c2 with
                  | .error e => .error e
                  | .ok (fs, c3) => .ok (f :: fs, c3)
      | _ => .ok ([], cur)

/-! ## the records + the interface -/

/-- A record block's text (the renderer's `Render.record`). -/
def recordText (r : Record) : String :=
  "  record " ++ r.name ++ " {\n" ++ fieldsText r.fields ++ "\n  }\n"

/-- The rendered record-block concatenation (the renderer's join). -/
def recordsText : List Record → String := Render.recordsJoin

/-- A record block: name, the field block, the closing brace. The
    record's nodup-in-type is DECIDED at construction: a duplicate
    field name is the loud refusal (the runtime route of the
    elaboration-level `by decide` default), never a silent
    acceptance. -/
def recordCore (fuel : Nat) : GParser Record := fun cur =>
  match identP nameChar cur with
  | .error e => .error e
  | .ok (n, c1) =>
      match TextKit.tok " {\n" c1 with
      | .error e => .error e
      | .ok (_, c2) =>
          match fieldsP fuel c2 with
          | .error e => .error e
          | .ok (fs, c3) =>
              match TextKit.tok "\n  }\n" c3 with
              | .error e => .error e
              | .ok (_, c4) =>
                  if hnd : (fs.map Field.name).Nodup then
                    .ok (({ name := n, fields := fs, fields_nodup := hnd } : Record), c4)
                  else
                    .error (curated cur
                      "duplicate field names — WIT rejects a record with a repeated field name"
                      ["distinct field names"])

/-- The record-block concatenation loop, dispatched predictively on
    the head character (a block starts `"  record "`; the interface's
    closing brace starts `}`). Total (fuel structural; each block
    consumes ≥ 12 characters). -/
def recordsP : Nat → GParser (List Record)
  | 0, cur => .error (curated cur "expected a record block or the interface's closing brace"
    ["a record block (\"  record <name> { ... }\")", "the interface's closing brace (\"}\")"])
  | fuel + 1, cur =>
      match cur.cs.head? with
      | some ' ' =>
          match TextKit.tok "  record " cur with
          | .error e => .error e
          | .ok (_, c1) =>
              match recordCore fuel c1 with
              | .error e => .error e
              | .ok (r, c2) =>
                  match recordsP fuel c2 with
                  | .error e => .error e
                  | .ok (rs, c3) => .ok (r :: rs, c3)
      | _ => .ok ([], cur)

/-- An interface block's text (the renderer's `Render.interface`). -/
def interfaceText (i : Interface) : String :=
  "interface " ++ i.name ++ " {\n" ++ recordsText i.records ++ "}\n"

/-- The rendered interface-block concatenation (the renderer's join). -/
def interfacesText : List Interface → String := Render.interfacesJoin

/-- An interface block: name, the record blocks, the closing brace.
    The interface's nodup-in-type is DECIDED at construction (the
    record-level route, one level up). -/
def interfaceP (fuel : Nat) : GParser Interface := fun cur =>
  match identP nameChar cur with
  | .error e => .error e
  | .ok (n, c1) =>
      match TextKit.tok " {\n" c1 with
      | .error e => .error e
      | .ok (_, c2) =>
          match recordsP fuel c2 with
          | .error e => .error e
          | .ok (rs, c3) =>
              match TextKit.tok "}\n" c3 with
              | .error e => .error e
              | .ok (_, c4) =>
                  if hnd : (rs.map Record.name).Nodup then
                    .ok (({ name := n, records := rs, records_nodup := hnd } : Interface), c4)
                  else
                    .error (curated cur
                      "duplicate record names — WIT rejects an interface with a repeated record name"
                      ["distinct record names"])

/-- The interface-block concatenation loop, dispatched predictively on
    the head character (a block starts `interface `; the package ends
    at the cursor otherwise). Total (fuel structural). -/
def interfacesP : Nat → GParser (List Interface)
  | 0, cur => .error (curated cur "expected an interface block"
    ["an interface block (\"interface <name> { ... }\")"])
  | fuel + 1, cur =>
      match cur.cs.head? with
      | some 'i' =>
          match TextKit.tok "interface " cur with
          | .error e => .error e
          | .ok (_, c1) =>
              match interfaceP fuel c1 with
              | .error e => .error e
              | .ok (i, c2) =>
                  match interfacesP fuel c2 with
                  | .error e => .error e
                  | .ok (is, c3) => .ok (i :: is, c3)
      | _ => .ok ([], cur)

/-! ## the package -/

/-- The whole-package text (the renderer's `Render.package`). -/
def packageText (p : Package) : String :=
  "package " ++ p.id ++ ";\n\n" ++ interfacesText p.interfaces

/-- A package block: the id line, then the interface blocks. -/
def packageP (fuel : Nat) : GParser Package := fun cur =>
  match TextKit.tok "package " cur with
  | .error e => .error e
  | .ok (_, c1) =>
      match identP idChar c1 with
      | .error e => .error e
      | .ok (i, c2) =>
          match TextKit.tok ";\n\n" c2 with
          | .error e => .error e
          | .ok (_, c3) =>
              match interfacesP fuel c3 with
              | .error e => .error e
              | .ok (is, c4) => .ok (({ id := i, interfaces := is } : Package), c4)

/-! ## comments (the artifact of record's two header lines) -/

/-- Consume through the next newline (an unterminated tail consumes
    everything — the bytes are then refused downstream as a malformed
    package). Structural on the list. -/
def skipToNewline : List Char → List Char
  | '\n' :: rest => rest
  | _ :: rest => skipToNewline rest
  | [] => []

/-- Drop the leading `//` comment lines (ALL of them — the artifact
    of record carries two). Fuel-structural (the house's no-wf-opacity
    discipline): each strip consumes at least the four bytes
    `//` + a line's first char + the newline, so `fuel = length` is
    always sufficient. -/
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

/-! ## the entry -/

/-- The total parser: text → the typed WIT package. Every failure is a
    curated `ParseError` (position + expected-set + did-you-mean);
    trailing garbage after the last `}` is a loud refusal, never a
    silent prefix acceptance. -/
def parse (s : String) : Except ParseError Package :=
  match packageP s.length ⟨0, skipComments s.toList⟩ with
  | .ok (p, cur) =>
      match cur.cs with
      | [] => .ok p
      | _ => .error (curated cur
          "trailing bytes after the package's last interface"
          ["the end of the package text"])
  | .error e => .error e

/-! ## the AST-side wellformedness (the round trip's side condition) -/

/-- A WIT name is identifier-shaped (the scanner's byte-side gate). -/
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

/-! ## the laws — the two honest directions (05 §1) -/

/-! ### the renderer's spelling, as equations -/

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

theorem field_eq (f : Field) : Render.field f = fieldText f := rfl

/-- The render face: the renderer's texts ARE the parse-side texts
    (the folds are shared — `rfl` bridges every level). -/
theorem record_eq (r : Record) : Render.record r = recordText r := rfl
theorem interface_eq (i : Interface) : Render.interface i = interfaceText i := rfl
theorem package_eq (p : Package) : Render.package p = packageText p := rfl

/-! ### the token + name scanners (the kit's inversions, consumed) -/

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

/-- A literal whose head differs from the input's head is refused (the
    error value is `tok`'s own). -/
theorem tok_ne (s : String) (off : Nat) (c0 : Char) (w : List Char) (c : Char)
    (rest : List Char) (hc : s.toList = c0 :: w) (hne : c0 ≠ c) :
    TextKit.tok s ⟨off, c :: rest⟩ = .error (ParseError.base off [s!"'{s}'"]) := by
  unfold TextKit.tok
  rw [hc]
  simp [hne]

/-! ### the name scanner (TextKit's satisfy + many, exactly) -/

/-- The maximal `satisfy`-run's exactness on the accept side: a run of
    `q` characters followed by a non-`q` character scans back exactly
    (the round-trip face). -/
theorem manySatisfy_self (nm : String) (q : Char → Bool) :
    ∀ (off : Nat) (w rest : List Char), w.all q = true →
      rest.head?.all (fun c => !q c) = true →
      TextKit.many (TextKit.satisfy nm q) ⟨off, w ++ rest⟩
        = .ok (w, ⟨off + w.length, rest⟩) := by
  intro off w
  induction w generalizing off with
  | nil =>
      intro rest _ hr
      show TextKit.manyGo (TextKit.satisfy nm q) (rest.length + 1) ⟨off, rest⟩ = _
      cases rest with
      | nil => simp [TextKit.manyGo, TextKit.satisfy]
      | cons c cs =>
          have hqc : q c = false := by simpa using hr
          simp [TextKit.manyGo, TextKit.satisfy, hqc]
  | cons c w ih =>
      intro rest hw hr
      have hcq : q c = true := List.all_eq_true.mp hw c (by simp)
      have hsucc : TextKit.satisfy nm q ⟨off, (c :: w) ++ rest⟩
          = .ok (c, ⟨off + 1, w ++ rest⟩) := by
        simp [TextKit.satisfy, hcq, Cursor.adv]
      have hw' : w.all q = true := by
        refine List.all_eq_true.mpr fun x hx => ?_
        exact List.all_eq_true.mp hw x (by simp [hx])
      have hlen : ((c :: w) ++ rest).length = (w ++ rest).length + 1 := by simp
      rw [show TextKit.many (TextKit.satisfy nm q) ⟨off, (c :: w) ++ rest⟩
            = TextKit.manyGo (TextKit.satisfy nm q)
                (((c :: w) ++ rest).length + 1) ⟨off, (c :: w) ++ rest⟩ from rfl,
        hlen]
      rw [TextKit.manyGo.eq_2]
      simp only [hsucc]
      rw [if_pos (by simp)]
      rw [← show TextKit.many (TextKit.satisfy nm q) ⟨off + 1, w ++ rest⟩
            = TextKit.manyGo (TextKit.satisfy nm q)
                ((w ++ rest).length + 1) ⟨off + 1, w ++ rest⟩ from rfl]
      simp only [ih (off + 1) rest hw' hr]
      simp only [List.length_cons]
      simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq]
      simp only [true_and, and_true]
      omega

/-- The name scanner recognizes a well-formed identifier followed by a
    non-identifier character (or end of input): exactly, cursor
    included. -/
theorem identP_self (q : Char → Bool) (s : String) (off : Nat) (rest : List Char)
    (hok : identOk q s = true)
    (hr : rest.head?.all (fun c => !q c) = true) :
    identP q ⟨off, s.toList ++ rest⟩ = .ok (s, ⟨off + s.length, rest⟩) := by
  unfold identOk at hok
  cases hs : s.toList with
  | nil => rw [hs] at hok; simp at hok
  | cons c w =>
      simp only [hs] at hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hc, hw⟩ := hok
      have hscan : TextKit.satisfy "an identifier start" Char.isAlpha
          ⟨off, (c :: w) ++ rest⟩ = .ok (c, ⟨off + 1, w ++ rest⟩) := by
        simp [TextKit.satisfy, hc, Cursor.adv]
      have hmany := manySatisfy_self "an identifier character" q (off + 1) w rest hw hr
      have hval : String.ofList (c :: w) = s := by rw [← hs]; exact String.ofList_toList
      have hlen : s.length = w.length + 1 := by
        rw [← String.length_toList, hs]
        rfl
      unfold identP
      simp only [hscan]
      simp only [hmany]
      rw [hval, hlen]
      simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq]
      simp only [true_and, and_true]
      omega

/-! ### the orElse kit -/

theorem orElse_ok_left {α : Type} {p q : GParser α} {cur : Cursor} {r : α × Cursor}
    (h : p cur = .ok r) : TextKit.orElse p q cur = .ok r := by
  simp [TextKit.orElse, h]

theorem orElse_ok_right {α : Type} {p q : GParser α} {cur : Cursor} {e : ParseError}
    {r : α × Cursor} (h1 : p cur = .error e) (h2 : q cur = .ok r) :
    TextKit.orElse p q cur = .ok r := by
  simp [TextKit.orElse, h1, h2]

theorem orElse_inv {α : Type} {p q : GParser α} {cur : Cursor} {r : α × Cursor}
    (h : TextKit.orElse p q cur = .ok r) :
    p cur = .ok r ∨ ∃ e, p cur = .error e ∧ q cur = .ok r := by
  unfold TextKit.orElse at h
  generalize hp : p cur = pv at h
  cases pv with
  | ok x =>
      left
      have h2 : Except.ok x = .ok r := h
      have hx : x = r := by injection h2
      exact by rw [hx]
  | error e =>
      right
      generalize hq : q cur = qv at h
      cases qv with
      | ok x =>
          have h2 : Except.ok x = .ok r := h
          exact ⟨e, rfl, h2⟩
      | error e' =>
          have h2 : Except.error (ParseError.farther e e') = .ok r := h
          exact absurd h2 (by simp)

/-! ### the arms (generic success + refusal) -/

/-- The maximal-munch gate's positive face: a head char passing the
    name charset is refused as an atom continuation. -/
theorem head_not_name_of_all {rest : List Char}
    (hr : rest.head?.all (fun c => !(TextKit.isIdentChar c || c == '-')) = true) :
    ∀ c, rest.head? = some c → (TextKit.isIdentChar c || c == '-') = false := by
  intro c hc
  rw [hc] at hr
  simpa using hr

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

/-- The dispatch-adjacent literals, cons-form (the dispatch's char-normalized face). -/
theorem tok_nlsp4 (off : Nat) (rest : List Char) :
    TextKit.tok "\n    " ⟨off, '\n' :: ' ' :: ' ' :: ' ' :: ' ' :: rest⟩
      = .ok ("\n    ", ⟨off + "\n    ".length, rest⟩) :=
  tok_self "\n    " off rest

theorem tok_sp4 (off : Nat) (rest : List Char) :
    TextKit.tok "    " ⟨off, ' ' :: ' ' :: ' ' :: ' ' :: rest⟩
      = .ok ("    ", ⟨off + "    ".length, rest⟩) :=
  tok_self "    " off rest

theorem tok_rec2 (off : Nat) (rest : List Char) :
    TextKit.tok "  record "
        ⟨off, ' ' :: ' ' :: 'r' :: 'e' :: 'c' :: 'o' :: 'r' :: 'd' :: ' ' :: rest⟩
      = .ok ("  record ", ⟨off + "  record ".length, rest⟩) :=
  tok_self "  record " off rest

theorem tok_iface (off : Nat) (rest : List Char) :
    TextKit.tok "interface "
        ⟨off, 'i' :: 'n' :: 't' :: 'e' :: 'r' :: 'f' :: 'a' :: 'c' :: 'e' :: ' ' :: rest⟩
      = .ok ("interface ", ⟨off + "interface ".length, rest⟩) :=
  tok_self "interface " off rest

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


theorem ty_i64_list : (Render.ty (.atom .i64)).toList = ['i', '6', '4'] := rfl
theorem ty_string_list : (Render.ty (.atom .string)).toList = ['s', 't', 'r', 'i', 'n', 'g'] := rfl

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
                  = .error (tokErr off "bool") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              rw [orElse_ok_right hf1
                (orElse_ok_left (atomArm_self "u64" .u64 off rest hr))]
          | i64 =>
              rw [ty_atom, scalar_i64]
              simp only [tyP, tyArms]
              have hf1 : atomArm "bool" .bool ⟨off, "i64".toList ++ rest⟩
                  = .error (tokErr off "bool") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              have hf2 : atomArm "u64" .u64 ⟨off, "i64".toList ++ rest⟩
                  = .error (tokErr off "u64") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              rw [orElse_ok_right hf1 (orElse_ok_right hf2
                (orElse_ok_left (atomArm_self "i64" .i64 off rest hr)))]
          | string =>
              rw [ty_atom, scalar_string]
              simp only [tyP, tyArms]
              have hf1 : atomArm "bool" .bool ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "bool") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              have hf2 : atomArm "u64" .u64 ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "u64") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              have hf3 : atomArm "i64" .i64 ⟨off, "string".toList ++ rest⟩
                  = .error (tokErr off "i64") := by
                  unfold atomArm tokErr
                  simp [TextKit.tok]
              rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
                (orElse_ok_left (atomArm_self "string" .string off rest hr))))]
  | option a ih =>
      intro fuel off rest hlen hr
      rw [ty_option] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [tyP, tyArms]
          have hf1 : atomArm "bool" .bool
              ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf2 : atomArm "u64" .u64
              ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf3 : atomArm "i64" .i64
              ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf4 : atomArm "string" .string
              ⟨off, ("option<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
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
          have hf1 : atomArm "bool" .bool
              ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf2 : atomArm "u64" .u64
              ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf3 : atomArm "i64" .i64
              ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf4 : atomArm "string" .string
              ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf5 : unaryArm "option<" Ty.option (tyP f)
              ⟨off, ("list<" ++ Render.ty a ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") := by
              unfold unaryArm tokErr
              simp [TextKit.tok]
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
          have hf1 : atomArm "bool" .bool
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf2 : atomArm "u64" .u64
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf3 : atomArm "i64" .i64
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf4 : atomArm "string" .string
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf5 : unaryArm "option<" Ty.option (tyP f)
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") := by
              unfold unaryArm tokErr
              simp [TextKit.tok]
          have hf6 : unaryArm "list<" Ty.list (tyP f)
              ⟨off, ("result<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") := by
              unfold unaryArm tokErr
              simp [TextKit.tok]
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
          have hf1 : atomArm "bool" .bool
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "bool") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf2 : atomArm "u64" .u64
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "u64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf3 : atomArm "i64" .i64
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "i64") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf4 : atomArm "string" .string
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "string") := by
              unfold atomArm tokErr
              simp [TextKit.tok]
          have hf5 : unaryArm "option<" Ty.option (tyP f)
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "option<") := by
              unfold unaryArm tokErr
              simp [TextKit.tok]
          have hf6 : unaryArm "list<" Ty.list (tyP f)
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "list<") := by
              unfold unaryArm tokErr
              simp [TextKit.tok]
          have hf7 : binaryArm "result<" Ty.result (tyP f)
              ⟨off, ("tuple<" ++ Render.ty a ++ ", " ++ Render.ty b ++ ">").toList ++ rest⟩
              = .error (tokErr off "result<") := by
              unfold binaryArm tokErr
              simp [TextKit.tok]
          rw [orElse_ok_right hf1 (orElse_ok_right hf2 (orElse_ok_right hf3
            (orElse_ok_right hf4 (orElse_ok_right hf5 (orElse_ok_right hf6
              (orElse_ok_right hf7 (orElse_ok_left
                (binaryArm_self "tuple<" Ty.tuple a b tyP f off rest hlen (by decide) iha ihb))))))))]




/-! ## the round-trip kit — the render→parse direction (05 §1's first law) -/

/-! ### the literal charlists (the tiny local rfl family: one per
    literal, the snapshot lane's `lparen` precedent) -/

theorem L_nl : "\n".toList = ['\n'] := rfl
theorem L_nlsp4 : "\n    ".toList = '\n' :: "    ".toList := rfl
theorem L_sp : " ".toList = [' '] := rfl
theorem L_sp4 : "    ".toList = [' ', ' ', ' ', ' '] := rfl
theorem L_colsp : ": ".toList = ':' :: " ".toList := rfl
theorem L_comma : ",".toList = [','] := rfl
theorem L_ob : " {\n".toList = ' ' :: '{' :: '\n' :: [] := rfl
theorem L_cb : "\n  }\n".toList = '\n' :: ' ' :: ' ' :: '}' :: '\n' :: [] := rfl
theorem L_rbnl : "}\n".toList = '}' :: '\n' :: [] := rfl
theorem L_semi2 : ";\n\n".toList = ';' :: '\n' :: '\n' :: [] := rfl
theorem L_pkg : "package ".toList
    = 'p' :: 'a' :: 'c' :: 'k' :: 'a' :: 'g' :: 'e' :: ' ' :: [] := rfl
theorem L_iface : "interface ".toList
    = 'i' :: 'n' :: 't' :: 'e' :: 'r' :: 'f' :: 'a' :: 'c' :: 'e' :: ' ' :: [] := rfl
theorem L_rec : "  record ".toList
    = ' ' :: ' ' :: 'r' :: 'e' :: 'c' :: 'o' :: 'r' :: 'd' :: ' ' :: [] := rfl

/-! ### the literal lengths (the fuel arithmetic's decided facts) -/

theorem lenNl : "\n".length = 1 := by decide
theorem lenSp4 : "    ".length = 4 := by decide
theorem lenNlSp4 : "\n    ".length = 5 := by decide
theorem lenColSp : ": ".length = 2 := by decide
theorem lenComma : ",".length = 1 := by decide
theorem lenOb : " {\n".length = 3 := by decide
theorem lenCb : "\n  }\n".length = 5 := by decide
theorem lenRbnl : "}\n".length = 2 := by decide
theorem lenSemi2 : ";\n\n".length = 3 := by decide
theorem lenPkg : "package ".length = 8 := by decide
theorem lenIface : "interface ".length = 10 := by decide
theorem lenRec : "  record ".length = 9 := by decide

/-! ### the tail discipline — what may follow a rendered fragment at a
    loop's stop position: not a field continuation (`\n` + three
    spaces), not a record block's leading space, not an interface's
    leading `i`. Every delimiter the renderer emits after a block
    (`}`, EOF, `\n  }`) satisfies it. -/

def tailOk : List Char → Bool
  | [] => true
  | '\n' :: ' ' :: ' ' :: ' ' :: _ => false
  | ' ' :: _ => false
  | 'i' :: _ => false
  | _ => true

theorem tailOk_cons (c : Char) (cs : List Char) (h : tailOk (c :: cs) = true) :
    c ≠ ' ' ∧ c ≠ 'i' := by
  unfold tailOk at h
  split at h
  · rename_i heq; exact absurd heq (by simp)
  · simp at h
  · simp at h
  · simp at h
  · rename_i e0 e1 e2 e3 e4
    exact ⟨fun hc => e3 cs (by simp [hc]), fun hc => e4 cs (by simp [hc])⟩

theorem tailOk_ne_space (sfx : List Char) (h : tailOk sfx = true) :
    sfx.head? ≠ some ' ' := by
  cases sfx with
  | nil => intro hc; simp at hc
  | cons c cs =>
      obtain ⟨h1, _⟩ := tailOk_cons c cs h
      intro hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      exact h1 hc

theorem tailOk_ne_i (sfx : List Char) (h : tailOk sfx = true) :
    sfx.head? ≠ some 'i' := by
  cases sfx with
  | nil => intro hc; simp at hc
  | cons c cs =>
      obtain ⟨_, h2⟩ := tailOk_cons c cs h
      intro hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      exact h2 hc

/-! ### the renderer's lengths (the fuel arithmetic's spine) -/

theorem field_len (f : Field) :
    (Render.field f).length = 7 + f.name.length + (Render.ty f.ty).length := by
  simp [Render.field, String.length_append, lenSp4, lenColSp, lenComma]
  omega

theorem fieldsTailJoin_len (f : Field) (fs : List Field) :
    (Render.fieldsTailJoin (f :: fs)).length
      = 1 + (Render.field f).length + (Render.fieldsTailJoin fs).length := by
  simp [Render.fieldsTailJoin, String.length_append, lenNl]

theorem fieldsJoin_len (f : Field) (fs : List Field) :
    (Render.fieldsJoin (f :: fs)).length
      = (Render.field f).length + (Render.fieldsTailJoin fs).length := by
  simp [Render.fieldsJoin, String.length_append]

theorem record_len (r : Record) :
    (Render.record r).length
      = 17 + r.name.length + (Render.fieldsJoin r.fields).length := by
  simp [Render.record, String.length_append, lenRec, lenOb, lenCb]
  omega

theorem recordsJoin_len (r : Record) (rs : List Record) :
    (Render.recordsJoin (r :: rs)).length
      = (Render.record r).length + (Render.recordsJoin rs).length := by
  simp [Render.recordsJoin, String.length_append]

theorem interface_len (i : Interface) :
    (Render.interface i).length
      = 15 + i.name.length + (Render.recordsJoin i.records).length := by
  simp [Render.interface, String.length_append, lenIface, lenOb, lenRbnl]
  omega

theorem interfacesJoin_len (i : Interface) (is : List Interface) :
    (Render.interfacesJoin (i :: is)).length
      = (Render.interface i).length + (Render.interfacesJoin is).length := by
  simp [Render.interfacesJoin, String.length_append]

theorem package_len (p : Package) :
    (Render.package p).length
      = 11 + p.id.length + (Render.interfacesJoin p.interfaces).length := by
  simp [Render.package, String.length_append, lenPkg, lenSemi2]
  omega

/-! ### the loops + the blocks (each level inverts the renderer's join) -/

theorem tailOk_after_fields (sfx : List Char) :
    tailOk ("\n  }\n".toList ++ sfx) = true := by
  simp [tailOk, L_cb]

theorem tailOk_after_records (sfx : List Char) :
    tailOk ("}\n".toList ++ sfx) = true := by
  simp [tailOk, L_rbnl]

/-- THE FIELDS' CONTINUATION LAW: the renderer's continuation join
    scans back to exactly the fields, consuming exactly its bytes. -/
theorem fieldsGo_ok (fs : List Field) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → tailOk sfx = true →
      (∀ f ∈ fs, witNameOk f.name) →
      (Render.fieldsTailJoin fs).length + sfx.length ≤ fuel + 1 →
      fieldsGo fuel ⟨off, (Render.fieldsTailJoin fs).toList ++ sfx⟩
        = .ok (fs, ⟨off + (Render.fieldsTailJoin fs).length, sfx⟩) := by
  induction fs with
  | nil =>
      intro fuel off sfx hguard ht _ _
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [Render.fieldsTailJoin]
          simp only [String.toList_empty, List.nil_append, fieldsGo]
          split
          · exfalso
            simp [tailOk] at ht
          · rfl
  | cons f fs ih =>
      intro fuel off sfx hguard ht hn hlen
      cases fuel with
      | zero =>
          exfalso
          have h2 := field_len f
          rw [fieldsTailJoin_len] at hlen
          omega
      | succ fuel =>
          have hfl : (Render.field f).length + (Render.fieldsTailJoin fs).length
              + sfx.length ≤ fuel + 1 := by
            rw [fieldsTailJoin_len] at hlen
            have h2 := field_len f
            omega
          simp only [Render.fieldsTailJoin, Render.field, String.toList_append,
            List.cons_append, List.nil_append, List.append_assoc,
            L_nl, L_sp4, fieldsGo, tok_nlsp4, fieldCore]
          rw [identP_self nameChar f.name (off + "\n    ".length)
              (": ".toList ++ ((Render.ty f.ty).toList
                ++ (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx))))
              (hn f (List.mem_cons_self))
              (by simp [nameChar, L_colsp, TextKit.isIdentChar])]
          simp only [tok_self]
          have hr' : (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx)).head?.all
              (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
            simp [L_comma, TextKit.isIdentChar]
          rw [tyP_ok f.ty fuel
              (off + "\n    ".length + f.name.length + ": ".length)
              (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx))
              (by
                have h3 := field_len f
                have h4 : (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx)).length
                    = 1 + (Render.fieldsTailJoin fs).length + sfx.length := by
                  rw [List.length_append, L_comma, List.length_append,
                    String.length_toList, List.length_cons, List.length_nil]
                  omega
                omega)
              hr']
          simp only [tok_self]
          have hihr := ih fuel
              (off + "\n    ".length + f.name.length + ": ".length
                + (Render.ty f.ty).length + ",".length) sfx
              (by have h2 := field_len f; omega)
              ht (fun g hg => hn g (List.mem_cons_of_mem _ hg))
                (by have h2 := field_len f; omega)
          rw [hihr]
          simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq,
            String.length_append,
            lenSp4, lenNlSp4, lenColSp, lenComma, lenNl]
          try simp only [true_and, and_true]
          omega

/-- THE FIELDS LAW: the renderer's field block scans back to exactly
    the fields (the first line rides `"    "`, the rest the
    continuation law). -/
theorem fieldsP_ok (fs : List Field) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → tailOk sfx = true →
      (∀ f ∈ fs, witNameOk f.name) →
      (Render.fieldsJoin fs).length + sfx.length ≤ fuel →
      fieldsP fuel ⟨off, (Render.fieldsJoin fs).toList ++ sfx⟩
        = .ok (fs, ⟨off + (Render.fieldsJoin fs).length, sfx⟩) := by
  induction fs with
  | nil =>
      intro fuel off sfx hguard ht _ _
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [Render.fieldsJoin]
          simp only [String.toList_empty, List.nil_append, fieldsP]
          have hne := tailOk_ne_space sfx ht
          split
          · rename_i heq; exact absurd heq hne
          · rfl
  | cons f fs ih =>
      intro fuel off sfx hguard ht hn hlen
      cases fuel with
      | zero =>
          exfalso
          have h2 := field_len f
          rw [fieldsJoin_len] at hlen
          omega
      | succ fuel =>
          have hfg : (Render.fieldsTailJoin fs).length + sfx.length ≤ fuel + 1 := by
            rw [fieldsJoin_len] at hlen
            omega
          simp only [Render.fieldsJoin, Render.field, String.toList_append,
            List.cons_append, List.nil_append, List.append_assoc,
            L_sp4, fieldsP, tok_sp4, fieldCore, List.head?_cons]
          rw [identP_self nameChar f.name (off + "    ".length)
              (": ".toList ++ ((Render.ty f.ty).toList
                ++ (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx))))
              (hn f (List.mem_cons_self))
              (by simp [nameChar, L_colsp, TextKit.isIdentChar])]
          simp only [tok_self]
          have hr' : (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx)).head?.all
              (fun c => !(TextKit.isIdentChar c || c == '-')) = true := by
            simp [L_comma, TextKit.isIdentChar]
          rw [tyP_ok f.ty fuel
              (off + "    ".length + f.name.length + ": ".length)
              (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx))
              (by
                have h3 := field_len f
                have h5 := fieldsJoin_len f fs
                have h4 : (",".toList ++ ((Render.fieldsTailJoin fs).toList ++ sfx)).length
                    = 1 + (Render.fieldsTailJoin fs).length + sfx.length := by
                  rw [List.length_append, L_comma, List.length_append,
                    String.length_toList, List.length_cons, List.length_nil]
                  omega
                omega)
              hr']
          simp only [tok_self]
          have hihr := fieldsGo_ok fs fuel
              (off + "    ".length + f.name.length + ": ".length
                + (Render.ty f.ty).length + ",".length) sfx
              (by have h1 := fieldsJoin_len f fs; have h2 := field_len f; omega)
              ht (fun g hg => hn g (List.mem_cons_of_mem _ hg)) hfg
          rw [hihr]
          simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq,
            String.length_append,
            lenSp4, lenColSp, lenComma]
          try simp only [true_and, and_true]
          omega


/-! ### the blocks: records, interfaces, the package -/

/-- THE RECORD-BLOCK LAW: the record block's body (post
    `"  record "`) scans back to exactly the record. The nodup gate is
    decided at construction (`dif_pos` with the AST's own proof). -/
theorem recordCore_ok (r : Record) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → witNameOk r.name = true → (∀ f ∈ r.fields, witNameOk f.name) →
      (Render.fieldsJoin r.fields).length + ("\n  }\n".toList ++ sfx).length ≤ fuel →
      recordCore fuel ⟨off, r.name.toList ++ (" {\n".toList
          ++ ((Render.fieldsJoin r.fields).toList ++ ("\n  }\n".toList ++ sfx)))⟩
        = .ok (r, ⟨off + r.name.length + 3 + (Render.fieldsJoin r.fields).length + 5, sfx⟩) := by
  obtain ⟨rn, rfs, rhnd⟩ := r
  intro fuel off sfx hguard hnm hnf hlen
  unfold recordCore
  rw [identP_self nameChar rn off
    (" {\n".toList ++ ((Render.fieldsJoin rfs).toList ++ ("\n  }\n".toList ++ sfx)))
    hnm (by simp [nameChar, L_ob, TextKit.isIdentChar])]
  simp only [tok_self]
  rw [fieldsP_ok rfs fuel (off + rn.length + " {\n".length) ("\n  }\n".toList ++ sfx)
    hguard (tailOk_after_fields sfx) hnf hlen]
  simp only [tok_self]
  rw [dif_pos rhnd]
  simp only [
    lenOb, lenCb]

/-- THE RECORDS LAW: the renderer's record-block concatenation scans
    back to exactly the records. -/
theorem recordsP_ok (rs : List Record) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → tailOk sfx = true →
      (∀ r ∈ rs, witNameOk r.name ∧ (∀ f ∈ r.fields, witNameOk f.name)) →
      (Render.recordsJoin rs).length + sfx.length ≤ fuel →
      recordsP fuel ⟨off, (Render.recordsJoin rs).toList ++ sfx⟩
        = .ok (rs, ⟨off + (Render.recordsJoin rs).length, sfx⟩) := by
  induction rs with
  | nil =>
      intro fuel off sfx hguard ht _ _
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [Render.recordsJoin]
          simp only [String.toList_empty, List.nil_append, recordsP]
          have hne := tailOk_ne_space sfx ht
          split
          · rename_i heq; exact absurd heq hne
          · rfl
  | cons r rs ih =>
      obtain ⟨rn, rfs, rhnd⟩ := r
      intro fuel off sfx hguard ht hn hlen
      cases fuel with
      | zero =>
          exfalso
          have h1 := recordsJoin_len ⟨rn, rfs, rhnd⟩ rs
          have h2 := record_len ⟨rn, rfs, rhnd⟩
          rw [recordsJoin_len ⟨rn, rfs, rhnd⟩ rs] at hlen
          omega
      | succ fuel =>
          have hguard2 : 1 ≤ fuel := by
            have h1 := recordsJoin_len ⟨rn, rfs, rhnd⟩ rs
            have h2 := record_len ⟨rn, rfs, rhnd⟩
            omega
          simp only [Render.recordsJoin, Render.record, String.toList_append,
            List.cons_append, List.nil_append, List.append_assoc,
            L_rec, recordsP, tok_rec2, List.head?_cons]
          rw [recordCore_ok ⟨rn, rfs, rhnd⟩ fuel (off + "  record ".length)
            ((Render.recordsJoin rs).toList ++ sfx)
            hguard2 (hn ⟨rn, rfs, rhnd⟩ (List.mem_cons_self)).1
            (hn ⟨rn, rfs, rhnd⟩ (List.mem_cons_self)).2
            (by
              have h1 := recordsJoin_len ⟨rn, rfs, rhnd⟩ rs
              have h2 := record_len ⟨rn, rfs, rhnd⟩
              have h3 : ("\n  }\n".toList ++ ((Render.recordsJoin rs).toList ++ sfx)).length
                  = 5 + (Render.recordsJoin rs).length + sfx.length := by
                simp [L_cb, String.length_toList, List.length_append]
                omega
              omega)]
          simp only []
          rw [ih fuel (off + "  record ".length
            + (Record.mk rn rfs rhnd).name.length + 3
            + (Render.fieldsJoin (Record.mk rn rfs rhnd).fields).length
            + 5) sfx
            hguard2 ht (fun g hg => hn g (List.mem_cons_of_mem _ hg))
            (by
              have h1 := recordsJoin_len ⟨rn, rfs, rhnd⟩ rs
              have h2 := record_len ⟨rn, rfs, rhnd⟩
              omega)]
          simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq,
            
            String.length_append, lenRec, lenOb, lenCb,
            ]
          try simp only [true_and, and_true]
          omega

theorem interfaceP_ok (i : Interface) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → witNameOk i.name = true →
      (∀ r ∈ i.records, witNameOk r.name ∧ (∀ f ∈ r.fields, witNameOk f.name)) →
      (Render.recordsJoin i.records).length + ("}\n".toList ++ sfx).length ≤ fuel →
      interfaceP fuel ⟨off, i.name.toList ++ (" {\n".toList
          ++ ((Render.recordsJoin i.records).toList ++ ("}\n".toList ++ sfx)))⟩
        = .ok (i, ⟨off + i.name.length + 3 + (Render.recordsJoin i.records).length + 2, sfx⟩) := by
  obtain ⟨nm, rs, rhnd⟩ := i
  intro fuel off sfx hguard hnm hn hlen
  unfold interfaceP
  rw [identP_self nameChar nm off
    (" {\n".toList ++ ((Render.recordsJoin rs).toList ++ ("}\n".toList ++ sfx)))
    hnm (by simp [nameChar, L_ob, TextKit.isIdentChar])]
  simp only [tok_self]
  rw [recordsP_ok rs fuel (off + nm.length + " {\n".length) ("}\n".toList ++ sfx)
    hguard (tailOk_after_records sfx) hn hlen]
  simp only [tok_self]
  rw [dif_pos rhnd]
  simp only [
    lenOb, lenRbnl]

/-- THE INTERFACES LAW: the renderer's interface-block concatenation
    scans back to exactly the interfaces. -/
theorem interfacesP_ok (is : List Interface) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → tailOk sfx = true →
      (∀ i ∈ is, witNameOk i.name
        ∧ (∀ r ∈ i.records, witNameOk r.name ∧ (∀ f ∈ r.fields, witNameOk f.name))) →
      (Render.interfacesJoin is).length + sfx.length ≤ fuel →
      interfacesP fuel ⟨off, (Render.interfacesJoin is).toList ++ sfx⟩
        = .ok (is, ⟨off + (Render.interfacesJoin is).length, sfx⟩) := by
  induction is with
  | nil =>
      intro fuel off sfx hguard ht _ _
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [Render.interfacesJoin]
          simp only [String.toList_empty, List.nil_append, interfacesP]
          have hne := tailOk_ne_i sfx ht
          split
          · rename_i heq; exact absurd heq hne
          · rfl
  | cons i is ih =>
      obtain ⟨nm, rs, rhnd⟩ := i
      intro fuel off sfx hguard ht hn hlen
      cases fuel with
      | zero =>
          exfalso
          have h1 := interfacesJoin_len (Interface.mk nm rs rhnd) is
          have h2 := interface_len (Interface.mk nm rs rhnd)
          rw [interfacesJoin_len (Interface.mk nm rs rhnd) is] at hlen
          omega
      | succ fuel =>
          have hguard2 : 1 ≤ fuel := by
            have h1 := interfacesJoin_len (Interface.mk nm rs rhnd) is
            have h2 := interface_len (Interface.mk nm rs rhnd)
            omega
          have hifp : (Render.recordsJoin (Interface.mk nm rs rhnd).records).length
              + ("}\n".toList ++ ((Render.interfacesJoin is).toList ++ sfx)).length ≤ fuel := by
            have h1 := interfacesJoin_len (Interface.mk nm rs rhnd) is
            have h2 := interface_len (Interface.mk nm rs rhnd)
            have h3 : ("}\n".toList ++ ((Render.interfacesJoin is).toList ++ sfx)).length
                = 2 + (Render.interfacesJoin is).length + sfx.length := by
              simp [L_rbnl, String.length_toList, List.length_append]
              omega
            rw [interfacesJoin_len (Interface.mk nm rs rhnd) is] at hlen
            omega
          simp only [Render.interfacesJoin, Render.interface, String.toList_append,
            List.cons_append, List.nil_append, List.append_assoc,
            L_iface, interfacesP, tok_iface, List.head?_cons]
          rw [interfaceP_ok (Interface.mk nm rs rhnd) fuel
            (off + "interface ".length)
            ((Render.interfacesJoin is).toList ++ sfx)
            hguard2 (hn (Interface.mk nm rs rhnd) (List.mem_cons_self)).1
            (hn (Interface.mk nm rs rhnd) (List.mem_cons_self)).2 hifp]
          simp only []
          rw [ih fuel (off + "interface ".length
            + (Interface.mk nm rs rhnd).name.length + 3
            + (Render.recordsJoin (Interface.mk nm rs rhnd).records).length
            + 2) sfx
            hguard2 ht (fun g hg => hn g (List.mem_cons_of_mem _ hg))
            (by
              have h1 := interfacesJoin_len (Interface.mk nm rs rhnd) is
              have h2 := interface_len (Interface.mk nm rs rhnd)
              omega)]
          simp only [Except.ok.injEq, Prod.mk.injEq, Cursor.mk.injEq,
            
            String.length_append, lenIface, lenOb, lenRbnl,
            ]
          try simp only [true_and, and_true]
          omega

theorem packageP_ok (p : Package) :
    ∀ (fuel off : Nat) (sfx : List Char),
      1 ≤ fuel → tailOk sfx = true → witIdOk p.id = true →
      (∀ i ∈ p.interfaces, witNameOk i.name
        ∧ (∀ r ∈ i.records, witNameOk r.name ∧ (∀ f ∈ r.fields, witNameOk f.name))) →
      (Render.interfacesJoin p.interfaces).length + sfx.length ≤ fuel →
      packageP fuel ⟨off, "package ".toList ++ (p.id.toList ++ (";\n\n".toList
          ++ ((Render.interfacesJoin p.interfaces).toList ++ sfx)))⟩
        = .ok (p, ⟨off + "package ".length + p.id.length + 3 + (Render.interfacesJoin p.interfaces).length, sfx⟩) := by
  intro fuel off sfx hguard ht hid hn hlen
  unfold packageP
  simp only [tok_self]
  rw [identP_self idChar p.id (off + "package ".length)
    (";\n\n".toList ++ ((Render.interfacesJoin p.interfaces).toList ++ sfx))
    hid (by simp [idChar, nameChar, L_semi2, TextKit.isIdentChar])]
  simp only [tok_self]
  rw [interfacesP_ok p.interfaces fuel (off + "package ".length + p.id.length + ";\n\n".length) sfx
    hguard ht hn hlen]
  simp only []
  simp only [
    lenPkg, lenSemi2]

/-! ### the two honest laws (05 §1) -/

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

/-- THE PARSE LAW (05 §1's first honest law): every well-named
    package's rendering parses back to exactly it — `parse (print x) =
    ok x` on the `WitOk` fragment. -/
theorem parse_print (p : Package) (hok : WitOk p = true) :
    parse (Render.package p) = .ok p := by
  obtain ⟨hid, hn⟩ := WitOk_spec p hok
  have hcursor : (Render.package p).toList
      = "package ".toList ++ (p.id.toList ++ (";\n\n".toList
        ++ ((Render.interfacesJoin p.interfaces).toList ++ []))) := by
    simp [Render.package, String.toList_append, List.append_assoc]
  have hstrip : ∀ (sfx : List Char),
      skipComments ("package ".toList ++ sfx) = "package ".toList ++ sfx := by
    intro sfx
    show skipCommentsGo ("package ".toList ++ sfx).length
      ("package ".toList ++ sfx) = _
    have hl : ("package ".toList ++ sfx).length = (sfx.length + 7) + 1 := by
      rw [List.length_append, L_pkg]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [hl, L_pkg, List.cons_append]
    exact skipCommentsGo_ne (sfx.length + 7) 'p' _ rfl
  simp only [parse, hcursor]
  rw [hstrip (p.id.toList ++ (";\n\n".toList ++ ((Render.interfacesJoin p.interfaces).toList ++ [])))]
  rw [packageP_ok p (Render.package p).length 0 []
    (by have h1 := package_len p; omega)
    (by simp [tailOk])
    hid hn
    (by have h1 := package_len p; simp only [List.length_nil]; omega)]

/-! ### the correspondence row -/

/-- The WIT codec (Kit.Correspondence's decode∘encode grade): the
    texts are the carrier, the WELL-NAMED packages the payload. The
    decode is proof-carrying — a parse result is trusted only when it
    passes `WitOk` (the gate rides the value; a parsed-then-rejected
    text decodes to `none`). `decode_encode` IS `parse_print`;
    `decode_some_policy` says a successful decode certifies acceptance.
    The image-iso upgrade (`Kit.Retraction.toImageIso`: the canonical
    texts a true `Kit.Iso` with the well-named ASTs) is the
    canonicalization direction — `render_parse` — the named follow-up
    (see the module header). -/
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
    landed. -/
def witImageIso :
    Kit.Iso (Kit.Retraction.image witRetraction) { p : Package // WitOk p } :=
  witRetraction.toImageIso

end Wit.Parse
