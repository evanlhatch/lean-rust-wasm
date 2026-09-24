/-
# SchemaCore.Snapshot — the registry-state serialization (the universe snapshot)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §7 (the snapshot is the
substrate the committed delta checks against — the breaking gate reads
THIS file's format); notes/v3/09-gates-ops.md §3-4 (the committed
baseline is the spec of record; the artifact ledger's demand-set
honesty); notes/v3/15-patterns.md #7 (the env extension as the event
log — registration = append, replay = the materialization, THE SNAPSHOT
= THE INTEGRAL); notes/v3/13-interfaces.md ("the universe snapshot"
row: this module is the ONE writer; lossless by design — the WIT view
is the lossy one, never this baseline).

## The format (canonical, one item per line)

    item <name> field <fname> <tytext> field <fname> <tytext> ...

- one LINE per item (the line IS the block); lines sorted by item name
  — the CANONICAL form is the point: `print` sorts, so printing a
  reordered-but-equal registry state is byte-identical;
- `<tytext>` is `tyText`'s paren encoding (`option(u64)`,
  `result(u64,string)`, `bounded(42)`) — NO spaces, so the space is a
  reliable separator;
- names (`<name>`, `<fname>`) are space/newline-free (`nameOk` — the
  write-side gate, the emitter's law);
- LF line endings, every line newline-terminated, the empty file IS
  the empty universe.

## Riding TextKit (the 10-sequencing rule: no second parser plumbing)

The parser's plumbing is TextKit's, not hand-rolled:
- the token scans (ty keywords, item/field names) are
  `TextKit.Parser.takeWhile` — ONE maximal-prefix scan returning token
  + rest, with `TextKit.takeWhile_stop`/`TextKit.takeDrop_head` as the
  inversion lemmas (TextKit.Lemmas owns them); the file carries NO
  local takeWhile/dropWhile pair or its lemmas;
- the literal prefixes (`item `, `field `) are `TextKit.expect` (the
  kit's `expect_self` is the round-trip face — no local copy);
- the bounded cap's digits are `TextKit.scanNat`.

HONEST RESIDUE (the local machinery that stays):
- the carrier is `Except String` (the loud refusal messages ARE the
  format's contract), so the delimiter discipline (the paren/comma/
  space structure inside `parseTy`, the newline arm of `parseFields`)
  is structural matching, not TextKit combinators — moving it onto
  GParser would re-key the errors and change the laws' statements;
- the line/item loop fuel stays: it is the genuine recursion measure
  (one unit per field/item), not an artifact of hand-rolled plumbing;
  TextKit's `many` covers a different carrier;
- `natText` (the cap's renderer) is format content — its OWN encoding,
  proved round-trip below — not parsing plumbing.

## The laws (honest, at this size)

- PROVED: `parse_print` — `parse (print items) = .ok (canonical items)`
  for `nameOk` registries. The state is finite data over a closed `Ty`,
  so the decode-after-encode direction is a plain induction (the ty
  recursion is fuel-bounded, the fuel discipline is `tyDepth`, the
  line/item folds mirror `renderFields`/`printItems` structurally).
- NOTED, NOT PROVED: the print∘parse direction — `print (parse s) = s`
  for canonical `s` — is the CANONICALIZATION claim (parse then re-sort
  must reproduce the canonical bytes). It needs the sort's permutation
  + stability theory on top of the round trip, and the legacy paid
  three failed attempts at the full round-trip law (notes/v3/
  14-build-map.md's deferred-laws record). The gate re-derives the
  bytes instead (the code-registry-check precedent: the committed file
  is compared against the fresh canonical render — no second encoding),
  and `parse_print` IS the half the differential twin needs. This is a
  header note, not a stub: zero `sorry`, zero `axiom`.

Mining: `legacy/lean/schema-lang/SchemaLang/Snapshot.lean` — the
FORMAT's intent (the stable line-based text encoding, the write-side
name gate, loud parse refusals, the committed universe baseline).
Written fresh: the legacy Item carried variants/funcs/resources — the
slice's universe is the record-of-fields `Item`; and the legacy
preserved registry order where this format sorts (the canonical form is
the point here; the breaking diff is order-insensitive over names in
both trees).

Core-only (imports Kit-riding SchemaCore only — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Universe content — the registry's items (finite data), the
  snapshot = the integral of the registration event log (15 #7).
- carrier grade: first-order over String/List Char; the round-trip law
  is a THEOREM over the closed universe (`parse_print`), the
  canonicalization direction is the noted honest gap.
- spine reading: the Interpretation stage's OTHER face — registry →
  baseline text; the breaking gate (the forward consumer) reads it.
- ladder rung: rung 1-2 — total folds, fuel-bounded recursion, the
  proved direction is small inductions.
- gate row: `gates snapshot-check` (the byte-tie over
  notes/universe.snapshot; the snapshot's ONE tie — never also
  gen-check's, one tie per artifact).
-/

import Kit.Diag
import SchemaCore.Item
import SchemaCore.Register
import TextKit.Lemmas

namespace SchemaCore

open Kit

/-! ## the refusal envelope (05 §4: the failure KINDS as registry codes) -/

/-- The SN family — the snapshot lane's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    declaration, the code-registry gate's coverage scan ties the
    spellings to the live rows. -/
def eSN0001 : Kit.ECode := ⟨"SN0001"⟩
def eSN0002 : Kit.ECode := ⟨"SN0002"⟩
def eSN0003 : Kit.ECode := ⟨"SN0003"⟩
def eSN0004 : Kit.ECode := ⟨"SN0004"⟩
def eSN0005 : Kit.ECode := ⟨"SN0005"⟩
def eSN0006 : Kit.ECode := ⟨"SN0006"⟩
def eSN0007 : Kit.ECode := ⟨"SN0007"⟩
def eSN0008 : Kit.ECode := ⟨"SN0008"⟩
def eSN0009 : Kit.ECode := ⟨"SN0009"⟩
def eSN0010 : Kit.ECode := ⟨"SN0010"⟩
def eSN0011 : Kit.ECode := ⟨"SN0011"⟩
def eSN0012 : Kit.ECode := ⟨"SN0012"⟩
def eSN0013 : Kit.ECode := ⟨"SN0013"⟩
def eSN0014 : Kit.ECode := ⟨"SN0014"⟩
def eSN0015 : Kit.ECode := ⟨"SN0015"⟩
def eSN0016 : Kit.ECode := ⟨"SN0016"⟩
def eSN0017 : Kit.ECode := ⟨"SN0017"⟩
def eSN0018 : Kit.ECode := ⟨"SN0018"⟩
def eSN0019 : Kit.ECode := ⟨"SN0019"⟩
def eSN0020 : Kit.ECode := ⟨"SN0020"⟩
def eSN0021 : Kit.ECode := ⟨"SN0021"⟩
def eSN0022 : Kit.ECode := ⟨"SN0022"⟩
def eSN0023 : Kit.ECode := ⟨"SN0023"⟩
def eSN0024 : Kit.ECode := ⟨"SN0024"⟩
def eSN0025 : Kit.ECode := ⟨"SN0025"⟩
def eSN0026 : Kit.ECode := ⟨"SN0026"⟩
def eSN0027 : Kit.ECode := ⟨"SN0027"⟩

/-- The snapshot's refusal, in the ONE envelope's rendering: the failure
    kind rides the registry's SN row, the text keeps the `snapshot:`
    channel prefix. The parser's refusals are positional/structural (no
    single `got` to enumerate a valid space over), so the literal Diag
    is the honest shape; the closed-world refusal (the unknown type
    token) constructs through `Kit.Diag.closedWorld` directly. -/
def snapshotDiag (code : Kit.ECode) (message : String) : String :=
  Kit.Diag.toString { code := code, message := s!"snapshot: {message}" }

/-! ## the encoding -/

/-- The name charset's parse face: everything but the two separators
    (space, LF). -/
def sepOk (c : Char) : Bool := c != ' ' && c != '\n'

/-- The cap's canonical decimal text. OWN renderer (not `Nat.toString`):
    its round trip through the parser is PROVED below (`scanNat_natText`)
    — core ships no `Nat.toString` round-trip lemma, and the snapshot
    law is only as strong as its weakest token. -/
def natDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9' | _ => '?'

def natText (n : Nat) : String :=
  if n < 10 then String.singleton (natDigit n)
  else natText (n / 10) ++ String.singleton (natDigit (n % 10))
decreasing_by
  simp_wf
  omega

/-- The snapshot spelling's ALGEBRA (the foldTy row set — the ONE
    walk's snapshot face). The literal apps are split (`"option" ++ "("`)
    so the char-level proofs see every separator — the VALUE is
    byte-identical to the fused spelling (the legacy `Ty.toSnapshot`'s
    discipline, over the slice's universe). The map/set rows consume
    the KEY directly (`renderKeyTy` — no `Ty` re-entry, Ty.lean's
    scalar-sub-universe discipline). -/
def snapshotAlg : TyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "string"
  option a := "option" ++ "(" ++ a ++ ")"
  list a := "list" ++ "(" ++ a ++ ")"
  result a b := "result" ++ "(" ++ a ++ "," ++ b ++ ")"
  map k v := "map" ++ "(" ++ renderKeyTy k ++ "," ++ v ++ ")"
  set k := "set" ++ "(" ++ renderKeyTy k ++ ")"
  bounded n := "bounded" ++ "(" ++ natText n ++ ")"

/-- The snapshot spelling of a `Ty` = the fold over `snapshotAlg` (the
    migration: ONE walk, the emitter's rows as data — a new `Ty` ctor
    refuses to compile until this algebra grows its row). -/
def tyText : Ty → String := foldTy snapshotAlg

/-- The fold's equations in the char-proof-facing form (each `rfl`:
    the fold's structural reduction + the algebra row — `parseTy_tyText`
    and its dependents consume THESE). -/
theorem tyText_bool : tyText .bool = "bool" := rfl
theorem tyText_u64 : tyText .u64 = "u64" := rfl
theorem tyText_i64 : tyText .i64 = "i64" := rfl
theorem tyText_string : tyText .string = "string" := rfl
theorem tyText_option (t : Ty) :
    tyText (.option t) = "option" ++ "(" ++ tyText t ++ ")" := rfl
theorem tyText_list (t : Ty) :
    tyText (.list t) = "list" ++ "(" ++ tyText t ++ ")" := rfl
theorem tyText_result (a b : Ty) :
    tyText (.result a b) = "result" ++ "(" ++ tyText a ++ "," ++ tyText b ++ ")" := rfl
theorem tyText_map (k : KeyTy) (v : Ty) :
    tyText (.map k v) = "map" ++ "(" ++ renderKeyTy k ++ "," ++ tyText v ++ ")" := rfl
theorem tyText_set (k : KeyTy) :
    tyText (.set k) = "set" ++ "(" ++ renderKeyTy k ++ ")" := rfl
theorem tyText_bounded (n : Nat) :
    tyText (.bounded n) = "bounded" ++ "(" ++ natText n ++ ")" := rfl

/-- The field run of one line: ` field <fname> <tytext>` per field
    (structural — the round-trip proof mirrors it fold for fold).
    The literal apps are split (`" " ++ "field "`) for the same
    proof reason; the VALUE is byte-identical to the fused spelling. -/
def renderFields : List Field → String
  | [] => ""
  | f :: fs => " " ++ "field " ++ f.name ++ " " ++ tyText f.ty ++ renderFields fs

/-- One item → one canonical line. -/
def renderLine (it : Item) : String :=
  "item " ++ it.name ++ renderFields it.fields

/-- The item lines, each newline-terminated (the last one too; the
    empty universe prints empty). -/
def printItems : List Item → String
  | [] => ""
  | it :: its => renderLine it ++ "\n" ++ printItems its

/-- Insert by item name (the rows stay sorted; the registry's nodup
    makes the order total). -/
def insertItem : Item → List Item → List Item
  | it, [] => [it]
  | it, row :: rows => if it.name < row.name then it :: row :: rows
      else row :: insertItem it rows

/-- Canonical order: sorted by item name. `print` sorts; `parse` does
    not need to (the canonical form is the print's job). -/
def canonical : List Item → List Item
  | [] => []
  | it :: its => insertItem it (canonical its)

/-- The whole universe as snapshot text (canonical bytes: sorted, one
    line per item, each newline-terminated; the empty universe prints
    EMPTY — `parse "" = .ok []` is the same zero). -/
def print (items : List Item) : String :=
  printItems (canonical items)

/-- The write-side name gate: every name the format must encode — item
    names AND field names — survives the space-separated line grammar.
    `print`-side refusals ride the emitter's law; parse failures are
    always corruption, never writer drift (the legacy
    `namesEncodable` discipline). -/
def nameOk (s : String) : Bool :=
  !s.isEmpty && s.toList.all sepOk

/-- Every name in the item list passes `nameOk`. -/
def namesOk (items : List Item) : Bool :=
  items.all (fun it => nameOk it.name && it.fields.all (fun f => nameOk f.name))

/-! ## the fuel discipline -/

/-- The ty recursion's depth measure: each `parseTy` nesting consumes
    one unit of fuel; the round-trip law's hypotheses are stated in it. -/
def tyDepth : Ty → Nat
  | .bool => 1 | .u64 => 1 | .i64 => 1 | .string => 1
  | .option t => 1 + tyDepth t
  | .list t => 1 + tyDepth t
  | .result a b => 1 + max (tyDepth a) (tyDepth b)
  | .map _k v => 1 + tyDepth v
  | .set _k => 2
  | .bounded _ => 2

/-! ## the parser -/

/-- A `Ty` → `KeyTy` re-gate (the legacy `Ty.toKeyTy?` discipline: the
    key position is parsed as a ty then GATED back into the scalar
    sub-universe — a non-scalar key is unrepresentable in the type, and
    the parse refuses it loudly). -/
def keyOfTy : Ty → Option KeyTy
  | .bool => some .bool
  | .u64 => some .u64
  | .i64 => some .i64
  | .string => some .string
  | _ => none

/-- The ty token parser (fuel-bounded; the legacy `parseTy`'s shape over
    the slice's universe). Total: `0` fuel is the loud refusal; every
    recursive call consumes at least one character, so fuel = the input
    length is strictly sufficient (the caller passes exactly that). -/
def parseTy : Nat → List Char → Except String (Ty × List Char)
  | 0, _ => .error (snapshotDiag eSN0001 "parse fuel exhausted (malformed ty nesting)")
  | fuel + 1, cs =>
      -- the token scan rides TextKit: ONE maximal-prefix scan returning
      -- the token + the rest (`TextKit.takeWhile_stop` is its round-trip
      -- inversion). The scan is total, so the none arm is the monad
      -- carrier's shape, never a live path.
      match TextKit.Parser.takeWhile Char.isAlphanum cs with
      | none => .error (snapshotDiag eSN0002 "the token scan failed")
      | some (kw, rest) =>
        let one (k : Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (t, ')' :: r2) => .ok (k t, r2)
              | .ok (_, _) => .error (snapshotDiag eSN0003 "expected ')' after the ty argument")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        let two (k : Ty → Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (a, ',' :: r2) =>
                  match parseTy fuel r2 with
                  | .ok (b, ')' :: r3) => .ok (k a b, r3)
                  | .ok (_, _) => .error (snapshotDiag eSN0005 "expected ')' after the second ty argument")
                  | .error e => .error e
              | .ok (_, _) => .error (snapshotDiag eSN0006 "expected ',' between the ty arguments")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        let key (k : KeyTy → Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (kt, ',' :: r2) =>
                  match keyOfTy kt with
                  | none => .error (snapshotDiag eSN0007 "the map key is not a scalar key type")
                  | some kk =>
                      match parseTy fuel r2 with
                      | .ok (v, ')' :: r3) => .ok (k kk v, r3)
                      | .ok (_, _) => .error (snapshotDiag eSN0008 "expected ')' after the map's value type")
                      | .error e => .error e
              | .ok (_, _) => .error (snapshotDiag eSN0009 "expected ',' between the map's key and value")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        match kw with
        | "bool" => .ok (.bool, rest)
        | "u64" => .ok (.u64, rest)
        | "i64" => .ok (.i64, rest)
        | "string" => .ok (.string, rest)
        | "option" => one .option
        | "list" => one .list
        | "result" => two (fun a b => .result a b)
        | "map" => key (fun kk v => .map kk v)
        | "set" =>
            -- the scalar-key gate at the boundary (the legacy `set` arm):
            -- parse the element as a ty, re-gate into `KeyTy`
            match rest with
            | '(' :: r =>
                match parseTy fuel r with
                | .ok (kt, ')' :: r2) =>
                    match keyOfTy kt with
                    | none => .error (snapshotDiag eSN0010 "the set element is not a scalar key type")
                    | some kk => .ok (.set kk, r2)
                | .ok (_, _) => .error (snapshotDiag eSN0011 "expected ')' after the set element")
                | .error e => .error e
            | _ => .error (snapshotDiag eSN0012 "expected '(' after `set`")
        | "bounded" =>
            match rest with
            | '(' :: r =>
                match TextKit.scanNat r with
                | some (n, ')' :: r2) => .ok (.bounded n, r2)
                | some (_, _) => .error (snapshotDiag eSN0013 "expected ')' after the bounded cap")
                | none => .error (snapshotDiag eSN0014 "expected the bounded cap's digits")
            | _ => .error (snapshotDiag eSN0015 "expected '(' after `bounded`")
        | other =>
            -- the closed-world discipline: the legal space enumerated +
            -- the did-you-mean — the ONE engine (`Kit.suggestFor`) fills
            -- the envelope's `suggest` via `closedWorld`; the rendering
            -- carries the valid list + the suggestion suffix
            .error (Kit.Diag.toString (Kit.Diag.closedWorld eSN0016
              s!"snapshot: unknown type token `{other}`" .error other
              ["bool", "u64", "i64", "string", "option", "list", "result",
                "map", "set", "bounded"]))

/-- The field run: zero or more ` field <fname> <tytext>` segments,
    terminated by the item line's newline (consumed — the item loop owns
    the line discipline) or EOF. TWO budgets: `tyFuel` for the ty
    recursion (CONSTANT across the run) and the loop fuel (one unit per
    field). -/
def parseFields : Nat → Nat → List Char → Except String (List Field × List Char)
  | _, _, [] => .ok ([], [])
  | _, _, '\n' :: r => .ok ([], r)
  | _, 0, _ => .error (snapshotDiag eSN0017 "parse fuel exhausted (the field run)")
  | tyFuel, loop + 1, ' ' :: r =>
      match TextKit.expect "field " r with
      | none => .error (snapshotDiag eSN0018 "expected `field `")
      | some r1 =>
        -- the name scan rides TextKit (ONE maximal sep-free run: the
        -- name + the rest; the scan is total, so the none arm is the
        -- monad carrier's shape, never a live path)
        match TextKit.Parser.takeWhile sepOk r1 with
        | none => .error (snapshotDiag eSN0019 "the name scan failed")
        | some (fn, r2) =>
          if fn = "" then .error (snapshotDiag eSN0020 "empty field name")
          else match r2 with
            | ' ' :: r3 =>
                match parseTy tyFuel r3 with
                | .error e => .error e
                | .ok (t, r4) =>
                    match parseFields tyFuel loop r4 with
                    | .error e => .error e
                    | .ok (more, r5) => .ok ({ name := fn, ty := t } :: more, r5)
            | _ => .error (snapshotDiag eSN0021 "expected ' ' between the field name and its type")
  | _, _, _ => .error (snapshotDiag eSN0022 "expected ` field`, newline, or EOF")

/-- One item's block: `item <name>` + its field run. The field run's
    loop fuel reuses the ty budget (both are bounded by the input
    length; the conditions stay CONSTANT per item). -/
def parseItem (tyFuel : Nat) (cs : List Char) : Except String (Item × List Char) :=
  match TextKit.expect "item " cs with
  | none => .error (snapshotDiag eSN0023 "expected `item `")
  | some r =>
      -- the name scan rides TextKit (the maximal sep-free run; total,
      -- so the none arm is the monad carrier's shape, never a live path)
      match TextKit.Parser.takeWhile sepOk r with
      | none => .error (snapshotDiag eSN0019 "the name scan failed")
      | some (nm, r1) =>
        if nm = "" then .error (snapshotDiag eSN0024 "empty item name")
        else
          match parseFields tyFuel tyFuel r1 with
          | .error e => .error e
          | .ok (fs, r2) => .ok ({ name := nm, fields := fs }, r2)

/-- The item loop: one item per line; `parseItem` CONSUMES the line's
    newline (parseFields owns it), so the next iteration starts directly
    at the next `item ` (or EOF). Two fuel budgets: `tyFuel` (shared by
    the ty/field recursions — CONSTANT across items) and the loop fuel
    (one unit per item). Total over List Char. -/
def parseItems : Nat → Nat → List Char → Except String (List Item × List Char)
  | _, _, [] => .ok ([], [])
  | _, 0, _ => .error "snapshot: parse fuel exhausted (the item run)"
  | tyFuel, loop + 1, cs =>
      match parseItem tyFuel cs with
      | .error e => .error e
      | .ok (it, r) =>
          match parseItems tyFuel loop r with
          | .error e => .error e
          | .ok (its, r3) => .ok (it :: its, r3)

theorem parseItems_cons (tyFuel : Nat) (loop : Nat) (cs : List Char)
    (hne : cs ≠ []) :
    parseItems tyFuel (loop + 1) cs
      = match parseItem tyFuel cs with
        | .error e => .error e
        | .ok (it, r) =>
            match parseItems tyFuel loop r with
            | .error e => .error e
            | .ok (its, r3) => .ok (it :: its, r3) := by
  simp only [parseItems]

theorem append_cons_ne_nil (l : List Char) (a : Char) (y : List Char) :
    (l ++ a :: y) ≠ [] := by simp

/-- Parse snapshot text back to the universe. Total over String; every
    failure is LOUD (a snapshot that doesn't parse is a gate refusal,
    never a skip). The empty text is the empty universe. -/
def parse (s : String) : Except String (List Item) :=
  match parseItems s.length s.length s.toList with
  | .ok (its, []) => .ok its
  | .ok (_, _) => .error (snapshotDiag eSN0025 "trailing garbage after the last item line")
  | .error e => .error e

/-! ## the round-trip proofs -/

theorem tyDepth_pos (t : Ty) : 1 ≤ tyDepth t := by
  -- kept a simp walk: the option/list cases leave the CHILD variable
  -- in the goal (not closed), so rung-3 decide cannot take them whole
  cases t <;> simp [tyDepth]

/-- A well-formed ty text always ends against a break char (one of the
    four the grammar puts after a ty token) or EOF. -/
def tyBreakOk : List Char → Prop :=
  fun sfx => match sfx.head? with
    | some c => c = ')' ∨ c = ',' ∨ c = ' ' ∨ c = '\n'
    | none => true

/-- A line's remainder: EOF or a newline-headed run (the parseFields
    side of the line-end discipline). -/
def suffixOk (suffix : List Char) : Prop :=
  suffix = [] ∨ suffix.head? = some '\n'

theorem lparen : "(".toList = ['('] := rfl
theorem rparen : ")".toList = [')'] := rfl
theorem lcomma : ",".toList = [','] := rfl
theorem lspace : " ".toList = [' '] := rfl
theorem rnewline : "\n".toList = ['\n'] := rfl

/-! The takeWhile/dropWhile scan family (takeDrop_head/takeDrop_stop/
takeWhile_stop/dropWhile_stop) is TextKit.Lemmas' — the kit owns the
maximal-scan inversion; the parser above cites TextKit.takeWhile_stop
and TextKit.takeDrop_head. -/

theorem ofList_ne_nil {L : List Char} (h : L ≠ []) : String.ofList L ≠ "" := by
  intro hcon
  have h2 := congrArg String.toList hcon
  simp [String.toList_ofList] at h2
  exact h h2

/-- The digit char's two faces agree with its value. -/
theorem natDigit_spec : ∀ m : Nat, m < 10 →
    (natDigit m).isDigit ∧ ((natDigit m).toNat - '0'.toNat) = m
  | 0, _ => ⟨rfl, rfl⟩
  | 1, _ => ⟨rfl, rfl⟩
  | 2, _ => ⟨rfl, rfl⟩
  | 3, _ => ⟨rfl, rfl⟩
  | 4, _ => ⟨rfl, rfl⟩
  | 5, _ => ⟨rfl, rfl⟩
  | 6, _ => ⟨rfl, rfl⟩
  | 7, _ => ⟨rfl, rfl⟩
  | 8, _ => ⟨rfl, rfl⟩
  | 9, _ => ⟨rfl, rfl⟩
  | n + 10, h => absurd h (by omega)

theorem all_natText (n : Nat) : (natText n).toList.all Char.isDigit := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natText.eq_1, if_pos h]
      simp [String.toList_singleton, (natDigit_spec n h).1]
    · rw [natText.eq_1, if_neg h]
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      simp only [String.toList_append, List.all_append]
      exact Bool.and_eq_true_iff.mpr ⟨ih (n / 10) hlt,
        by simp [String.toList_singleton,
          (natDigit_spec (n % 10) (Nat.mod_lt n (by omega))).1]⟩

theorem natText_ne (n : Nat) : (natText n).toList ≠ [] := by
  by_cases h : n < 10
  · rw [natText.eq_1, if_pos h]
    simp
  · rw [natText.eq_1, if_neg h]
    simp

theorem foldl_natText (n : Nat) :
    (natText n).toList.foldl
      (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natText.eq_1, if_pos h]
      have h0 : ('0' : Char).toNat = 48 := rfl
      have hv := (natDigit_spec n h).2
      simp only [String.toList_singleton, List.foldl_cons, List.foldl_nil]
      omega
    · rw [natText.eq_1, if_neg h]
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hv := (natDigit_spec (n % 10) (Nat.mod_lt n (by omega))).2
      have h0 : ('0' : Char).toNat = 48 := rfl
      simp only [String.toList_append, String.toList_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) hlt]
      omega

/-- The cap's canonical decimal text scans back to the cap — the
    bounded lane's token round trip. -/
theorem scanNat_natText (n : Nat) (r : List Char)
    (hr : r.head?.all (fun c => !c.isDigit)) :
    TextKit.scanNat ((natText n).toList ++ r) = some (n, r) := by
  have hall := all_natText n
  have htw : ((natText n).toList ++ r).takeWhile Char.isDigit
      = (natText n).toList := by
    rw [List.takeWhile_append_of_pos (List.all_eq_true.mp hall)]
    simp [(TextKit.takeDrop_head hr).1]
  have hdr : ((natText n).toList ++ r).dropWhile Char.isDigit = r := by
    rw [List.dropWhile_append_of_pos (List.all_eq_true.mp hall)]
    exact (TextKit.takeDrop_head hr).2
  simp only [TextKit.scanNat, htw, hdr]
  rw [if_neg (ofList_ne_nil (natText_ne n)), String.ofList_toList,
    foldl_natText]

theorem headOk_break (sfx : List Char) (h : tyBreakOk sfx) :
    sfx.head?.all (fun c => !c.isAlphanum)
    ∧ sfx.head?.all (fun c => !c.isDigit) := by
  cases sfx with
  | nil => simp []
  | cons c X =>
      have hc := h
      simp only [tyBreakOk, List.head?_cons] at hc
      simp only [List.head?_cons, Option.all_some]
      rcases hc with hc | hc | hc | hc
      · simp [hc]
      · simp [hc]
      · simp [hc]
      · simp [hc]

theorem nameOk_all (s : String) (h : nameOk s) : s.toList.all sepOk := by
  have h2 := Bool.and_eq_true_iff.mp h
  exact h2.2

theorem nameOk_ne_str (s : String) (h : nameOk s) : s ≠ "" := by
  intro hcon
  rw [hcon] at h
  simp [nameOk] at h

/-- The head conditions for the ty/field scans' `r` sides (term lemmas —
    the `r` is inferred, so a tactic block there would meet a
    metavariable). -/
theorem headOk_lparen (X : List Char) :
    ('(' :: X).head?.all (fun c => !c.isAlphanum) := by simp

theorem headOk_lparen_d (X : List Char) :
    ('(' :: X).head?.all (fun c => !c.isDigit) := by simp

theorem headOk_rparen_d (X : List Char) :
    (')' :: X).head?.all (fun c => !c.isDigit) := by simp

theorem headOk_space_sep (X : List Char) :
    (' ' :: X).head?.all (fun c => !sepOk c) := by simp [sepOk]

/-- The name head condition after a field run (a space) or at a line end
    (newline / EOF). -/
theorem headOk_renderFields (fs : List Field) (suffix : List Char)
    (h : suffixOk suffix) :
    ((renderFields fs).toList ++ suffix).head?.all (fun c => !sepOk c) := by
  cases fs with
  | nil =>
      simp only [renderFields, String.toList_empty,
        List.nil_append]
      rcases h with h | h
      · rw [h]; simp
      · rw [h]; simp [sepOk]
  | cons f fs =>
      simp only [renderFields, String.toList_append, List.cons_append, lspace,
        List.head?_cons, Option.all_some]
      simp [sepOk]

/-- The ty break condition after a field run (a space) or at a line end. -/
theorem tyBreakOk_renderFields (fs : List Field) (suffix : List Char)
    (h : suffixOk suffix) :
    tyBreakOk ((renderFields fs).toList ++ suffix) := by
  cases fs with
  | nil =>
      rcases h with h | h
      · rw [h]
        simp [tyBreakOk, renderFields, 
          String.toList_empty, List.append_nil]
      · simp only [renderFields, String.toList_empty,
          List.nil_append, tyBreakOk]
        rw [h]
        simp
  | cons f fs =>
      simp only [renderFields, String.toList_append, List.cons_append, lspace,
        ]
      simp [tyBreakOk]

/-- The key scalar's snapshot text scans back to the injected ty (the
    key positions parse as tys, then re-gate). -/
theorem parseTy_keyText (k : KeyTy) (fuel : Nat) (sfx : List Char)
    (h1 : 1 ≤ fuel) (h2 : tyBreakOk sfx) :
    parseTy fuel ((renderKeyTy k).toList ++ sfx) = .ok (k.toTy, sfx) := by
  have h2' := (headOk_break sfx h2).1
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases k with
      | bool =>
          simp only [renderKeyTy, 
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bool".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | u64 =>
          simp only [renderKeyTy, 
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "u64".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | i64 =>
          simp only [renderKeyTy, 
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "i64".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | string =>
          simp only [renderKeyTy, 
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "string".toList) (by decide) h2']
          simp [KeyTy.toTy]

theorem keyOfTy_toTy (k : KeyTy) : keyOfTy k.toTy = some k := by
  cases k <;> rfl

/-- THE TY LAW: a ty's snapshot text scans back to the ty. Fuel is the
    budget the caller passes (the input length suffices — every
    recursion consumes a character). -/
theorem parseTy_tyText (t : Ty) : ∀ (fuel : Nat) (sfx : List Char),
    tyDepth t ≤ fuel → tyBreakOk sfx →
    parseTy fuel ((tyText t).toList ++ sfx) = .ok (t, sfx) := by
  induction t with
  | bool =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_bool, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bool".toList) (by decide) h2']
          simp
  | u64 =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_u64, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "u64".toList) (by decide) h2']
          simp
  | i64 =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_i64, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "i64".toList) (by decide) h2']
          simp
  | string =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_string, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "string".toList) (by decide) h2']
          simp
  | option t ih =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_option, String.toList_append, List.cons_append, lparen,
            rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "option".toList) (by decide) (headOk_lparen _)]
          simp
          rw [ih fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | list t ih =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_list, String.toList_append, List.cons_append, lparen,
            rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "list".toList) (by decide) (headOk_lparen _)]
          simp
          rw [ih fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | result a b iha ihb =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_result, String.toList_append, List.cons_append, lparen,
            rparen, lcomma, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "result".toList) (by decide) (headOk_lparen _)]
          simp
          rw [iha fuel (',' :: ((tyText b).toList ++ (')' :: sfx)))
            (by omega) (by simp [tyBreakOk])]
          simp
          rw [ihb fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | map k v ihv =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_map, String.toList_append, List.cons_append, lparen,
            rparen, lcomma, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "map".toList) (by decide) (headOk_lparen _)]
          simp
          rw [parseTy_keyText k fuel
            (',' :: ((tyText v).toList ++ (')' :: sfx)))
            (by have := tyDepth_pos v; omega) (by simp [tyBreakOk])]
          simp
          rw [keyOfTy_toTy k]
          simp
          rw [ihv fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | set k =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_set, String.toList_append, List.cons_append, lparen,
            rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "set".toList) (by decide) (headOk_lparen _)]
          simp
          rw [parseTy_keyText k fuel (')' :: sfx) (by omega)
            (by simp [tyBreakOk])]
          simp
          rw [keyOfTy_toTy k]
  | bounded n =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_bounded, String.toList_append, List.cons_append, lparen,
            rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bounded".toList) (by decide) (headOk_lparen _)]
          simp
          rw [scanNat_natText n (')' :: sfx) (headOk_rparen_d sfx)]
          simp

/-- THE FIELDS LAW: a field run's snapshot text scans back to the
    fields. `parseFields` CONSUMES the line's newline, so the rest is
    the suffix after it (`suffix.drop 1`). -/
theorem parseFields_render (fs : List Field) : ∀ (tyFuel loop : Nat) (suffix : List Char),
    suffixOk suffix →
    (∀ f ∈ fs, nameOk f.name) → (∀ f ∈ fs, tyDepth f.ty ≤ tyFuel) →
    fs.length ≤ loop →
    parseFields tyFuel loop ((renderFields fs).toList ++ suffix)
      = .ok (fs, suffix.drop 1) := by
  induction fs with
  | nil =>
      intro tyFuel loop suffix h0 _ _ _
      rcases h0 with h0 | h0
      · rw [h0]
        simp [parseFields, renderFields, 
          String.toList_empty, List.append_nil]
      · cases hs : suffix with
        | nil => rw [hs] at h0; simp at h0
        | cons c cs =>
            rw [hs] at h0
            simp at h0
            subst h0
            simp [parseFields, renderFields, 
              String.toList_empty, List.nil_append]
  | cons f fs ih =>
      intro tyFuel loop suffix h0 h1 h2 h3
      simp only [List.length_cons] at h3
      cases loop with
      | zero => omega
      | succ loop =>
          have hfn := nameOk_all f.name (h1 f (List.mem_cons_self))
          have hne := nameOk_ne_str f.name (h1 f (List.mem_cons_self))
          simp only [renderFields, String.toList_append, List.cons_append,
            List.nil_append, List.append_assoc, lspace, parseFields,
            TextKit.expect_self,
            TextKit.takeWhile_stop (p := sepOk) (w := f.name.toList) hfn
              (headOk_space_sep _),
            String.ofList_toList,
            if_neg hne]
          rw [parseTy_tyText f.ty tyFuel ((renderFields fs).toList ++ suffix)
            (h2 f (List.mem_cons_self)) (tyBreakOk_renderFields fs suffix h0)]
          simp
          rw [ih tyFuel loop suffix h0
            (fun g hg => h1 g (List.mem_cons_of_mem _ hg))
            (fun g hg => h2 g (List.mem_cons_of_mem _ hg))
            (by omega)]
          simp

/-- THE ITEM LAW: one item's block (through its newline) scans back to
    the item. The suffix (EOF or the rest after the newline) passes
    through. -/
theorem parseItem_render (it : Item) (tyFuel : Nat) (suffix : List Char)
    (h0 : suffixOk suffix)
    (h1 : nameOk it.name) (h2 : ∀ f ∈ it.fields, nameOk f.name)
    (h3 : ∀ f ∈ it.fields, tyDepth f.ty ≤ tyFuel)
    (h4 : it.fields.length ≤ tyFuel) :
    parseItem tyFuel ((renderLine it).toList ++ suffix) = .ok (it, suffix.drop 1) := by
  simp only [renderLine, String.toList_append, 
    List.append_assoc, parseItem, TextKit.expect_self,
    TextKit.takeWhile_stop (p := sepOk) (w := it.name.toList)
      (nameOk_all it.name h1) (headOk_renderFields it.fields suffix h0),
    String.ofList_toList,
    nameOk_ne_str it.name h1]
  rw [parseFields_render it.fields tyFuel tyFuel suffix h0 h2 h3 h4]
  simp

/-- THE ITEMS LAW: the canonical line run scans back to the items. -/
theorem parseItems_printItems (its : List Item) : ∀ (tyFuel loop : Nat),
    (∀ it ∈ its, nameOk it.name ∧ (∀ f ∈ it.fields, nameOk f.name)
      ∧ (∀ f ∈ it.fields, tyDepth f.ty ≤ tyFuel)
      ∧ it.fields.length ≤ tyFuel) →
    its.length ≤ loop →
    parseItems tyFuel loop (printItems its).toList = .ok (its, []) := by
  induction its with
  | nil =>
      intro _tyFuel _loop _ _
      simp [parseItems, printItems, String.toList_empty]
  | cons it its ih =>
      intro tyFuel loop hmem hlen
      simp only [List.length_cons] at hlen
      cases loop with
      | zero => omega
      | succ loop =>
          obtain ⟨h1, h2, h3, h4⟩ := hmem it (List.mem_cons_self)
          simp only [printItems, String.toList_append, List.cons_append,
            List.nil_append, List.append_assoc, rnewline]
          rw [parseItems_cons tyFuel loop _
            (append_cons_ne_nil (renderLine it).toList '\n'
              (printItems its).toList),
            parseItem_render it tyFuel ('\n' :: (printItems its).toList)
              (by simp [suffixOk]) h1 h2 h3 h4]
          simp
          rw [ih tyFuel loop
            (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) (by omega)]

/-! ## the length/depth plumbing (the fuel's sufficiency) -/

theorem lenB : "bool".length = 4 := by decide
theorem lenU : "u64".length = 3 := by decide
theorem lenI : "i64".length = 3 := by decide
theorem lenS : "string".length = 6 := by decide
theorem lenO : "option".length = 6 := by decide
theorem lenL : "list".length = 4 := by decide
theorem lenR : "result".length = 6 := by decide
theorem lenM : "map".length = 3 := by decide
theorem lenT : "set".length = 3 := by decide
theorem lenBd : "bounded".length = 7 := by decide
theorem lenPl : "(".length = 1 := by decide
theorem lenPr : ")".length = 1 := by decide
theorem lenCm : ",".length = 1 := by decide

theorem renderKeyTy_pos (k : KeyTy) : 1 ≤ (renderKeyTy k).length := by
  cases k <;> simp only [renderKeyTy] <;> decide

theorem tyDepth_le_tyText (t : Ty) : tyDepth t ≤ (tyText t).length := by
  induction t with
  | bool => simp [tyDepth, tyText_bool, lenB]
  | u64 => simp [tyDepth, tyText_u64, lenU]
  | i64 => simp [tyDepth, tyText_i64, lenI]
  | string => simp [tyDepth, tyText_string, lenS]
  | option t ih =>
      simp [tyDepth, tyText_option, String.length_append, lenPr]; omega
  | list t ih =>
      simp [tyDepth, tyText_list, String.length_append, lenPr]; omega
  | result a b iha ihb =>
      simp [tyDepth, tyText_result, String.length_append, lenPr, lenCm]
      omega
  | map k v ihv =>
      have hk := renderKeyTy_pos k
      simp only [tyDepth, tyText_map, String.length_append, lenM, lenPl, lenPr,
        lenCm]
      omega
  | set k =>
      have hk := renderKeyTy_pos k
      simp only [tyDepth, tyText_set, String.length_append, lenT, lenPl, lenPr]
      omega
  | bounded n =>
      have h1 : 1 ≤ (natText n).toList.length := by
        cases hl : (natText n).toList with
        | nil => exact absurd hl (natText_ne n)
        | cons c cs => simp
      have h2 : (natText n).length = (natText n).toList.length :=
        (String.length_toList (s := natText n)).symm
      simp only [tyDepth, tyText_bounded, String.length_append, lenBd, lenPl, lenPr]
      rw [h2]
      omega

theorem tyText_le_renderFields (f : Field) (fs : List Field) (h : f ∈ fs) :
    (tyText f.ty).length ≤ (renderFields fs).length := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      simp only [renderFields, String.length_append]
      rcases List.mem_cons.mp h with rfl | hm
      · omega
      · have h2 := ih hm; omega

theorem fields_le_renderFields (fs : List Field) :
    fs.length ≤ (renderFields fs).length := by
  induction fs with
  | nil => simp [renderFields]
  | cons f fs ih =>
      have h1 : 1 ≤ (tyText f.ty).length := by
        have h2 := tyDepth_pos f.ty
        have h3 := tyDepth_le_tyText f.ty
        omega
      simp only [renderFields, String.length_append, List.length_cons]
      omega

theorem renderLine_len_pos (it : Item) : 1 ≤ (renderLine it).length := by
  have h5 : "item ".length = 5 := by decide
  simp only [renderLine, String.length_append]
  omega

theorem renderFields_le_renderLine (it : Item) :
    (renderFields it.fields).length ≤ (renderLine it).length := by
  simp [renderLine, String.length_append]

theorem renderLine_le_printItems (it : Item) (its : List Item) (h : it ∈ its) :
    (renderLine it).length ≤ (printItems its).length := by
  induction its with
  | nil => cases h
  | cons g gs ih =>
      simp only [printItems, String.length_append]
      rcases List.mem_cons.mp h with rfl | hm
      · omega
      · have h2 := ih hm; omega

theorem printItems_ge (its : List Item) :
    its.length ≤ (printItems its).length := by
  induction its with
  | nil => simp [printItems]
  | cons it its ih =>
      have h1 := renderLine_len_pos it
      simp only [printItems, String.length_append, List.length_cons]
      omega

/-! ## the sort's members (the canonical form's data) -/

theorem insertItem_mem (y : Item) (l : List Item) (x : Item) :
    x ∈ insertItem y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertItem]
  | cons z zs ih =>
      simp only [insertItem]
      split
      · simp []
      · constructor
        · intro h
          rcases List.mem_cons.mp h with hx | h
          · simp [hx]
          · rcases ih.mp h with hx | hx
            · exact Or.inl hx
            · simp [hx]
        · intro h
          rcases h with hx | h
          · simp [ih.mpr (Or.inl hx)]
          · rcases List.mem_cons.mp h with hx | hx
            · simp [hx]
            · simp [ih.mpr (Or.inr hx)]

theorem canonical_mem (l : List Item) (x : Item) :
    x ∈ canonical l ↔ x ∈ l := by
  induction l with
  | nil => simp [canonical]
  | cons y ys ih => simp [canonical, insertItem_mem y (canonical ys) x, ih]

theorem insertItem_length (y : Item) (l : List Item) :
    (insertItem y l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertItem]
  | cons z zs ih =>
      simp only [insertItem]
      split
      · simp
      · simp [ih]

theorem canonical_length (l : List Item) :
    (canonical l).length = l.length := by
  induction l with
  | nil => simp [canonical]
  | cons y ys ih => simp [canonical, insertItem_length, ih]

theorem namesOk_spec (items : List Item) (h : namesOk items) :
    ∀ x ∈ items, nameOk x.name ∧ (∀ f ∈ x.fields, nameOk f.name) := by
  intro x hx
  have h2 := List.all_eq_true.mp h x hx
  have h3 := Bool.and_eq_true_iff.mp h2
  exact ⟨h3.1, List.all_eq_true.mp h3.2⟩

/-- THE SNAPSHOT LAW: the universe's snapshot text parses back to the
    CANONICAL form of the universe — `print` sorts, `parse` reads, and
    the round trip is exact. (The converse — `print (parse s) = s` for
    canonical `s` — is the canonicalization direction, NOTED in the
    module header, not proved: the sort's permutation theory on top of
    this; the legacy paid three failed attempts.) -/
theorem parse_print (items : List Item) (hok : namesOk items) :
    parse (print items) = .ok (canonical items) := by
  have hmem : ∀ x ∈ canonical items, x ∈ items :=
    fun x hx => (canonical_mem items x).mp hx
  have hok' := namesOk_spec items hok
  have hnameOk : ∀ x ∈ canonical items, nameOk x.name
      ∧ (∀ f ∈ x.fields, nameOk f.name) :=
    fun x hx => hok' x (hmem x hx)
  cases hc : canonical items with
  | nil =>
      simp only [print, hc, printItems]
      simp [parse, parseItems]
  | cons c0 cs =>
      rw [hc] at hmem hnameOk
      have hge := printItems_ge (c0 :: cs)
      have hconds : ∀ x ∈ c0 :: cs, nameOk x.name
          ∧ (∀ f ∈ x.fields, nameOk f.name)
          ∧ (∀ f ∈ x.fields, tyDepth f.ty ≤ (printItems (c0 :: cs)).length)
          ∧ x.fields.length ≤ (printItems (c0 :: cs)).length := by
        intro x hx
        have hd : ∀ f ∈ x.fields, tyDepth f.ty
            ≤ (printItems (c0 :: cs)).length := by
          intro f hf
          have h1 := tyDepth_le_tyText f.ty
          have h2 := tyText_le_renderFields f x.fields hf
          have h3 := renderFields_le_renderLine x
          have h4 := renderLine_le_printItems x (c0 :: cs) hx
          omega
        have hfl : x.fields.length ≤ (printItems (c0 :: cs)).length := by
          have h1 := fields_le_renderFields x.fields
          have h3 := renderFields_le_renderLine x
          have h4 := renderLine_le_printItems x (c0 :: cs) hx
          omega
        exact ⟨(hnameOk x hx).1, (hnameOk x hx).2, hd, hfl⟩
      simp only [print, hc, parse]
      rw [parseItems_printItems (c0 :: cs) _ _ hconds hge]

/-! ## the emitter row + the gate's ONE reading -/

/-- The snapshot's emitter row (15 #10): the declared output + the law.
    The artifact is a HEADER-FREE canonical data file (the
    code-registry precedent): the bytes are `print`'s canonical output —
    the gate (`gates snapshot-check`) is the artifact's ONE tie (never
    also gen-check's — one tie per artifact); the `style` field is
    unused here (no GENERATED header is prepended — the canonical bytes
    ARE the file). -/
def snapshotEmitter : Kit.Emit.Emitter (DataRegistry Item) where
  name := "schema-snapshot"
  style := .lean
  specSource := "SchemaCore.Slice"
  outputs := ["notes/universe.snapshot"]
  run reg := [{ path := "notes/universe.snapshot", contents := print reg.items }]
  law := some fun reg => namesOk reg.items

/-- The certified write path: the snapshot is unemittable without the
    discharged naming precondition. -/
def snapshotFiles (reg : DataRegistry Item) (h : namesOk reg.items) :
    List Kit.Emit.GeneratedFile :=
  snapshotEmitter.runCertified reg h

/-- The gate's ONE reading: replay the registry, render the canonical
    bytes. Shared by the writer and the check — never re-encoded. -/
def snapshotOfEnv (env : Lean.Environment) : Except String String := do
  let reg ← registryOfItems (schemaExt.getState env)
  if h : namesOk reg.items = true then
    match snapshotFiles reg h with
    | [] => .error (snapshotDiag eSN0026 "the emitter produced nothing")
    | f :: _ => .ok f.contents
  else
    .error (snapshotDiag eSN0027 "a registered name is not encodable \
      (space/newline in an item or field name) — the write-side gate refuses")

end SchemaCore

/-! ## the module's law-summary (the honest ledger)

PROVED: `parseTy_tyText` (every ty token), `parseFields_render`,
`parseItem_render`, `parseItems_printItems`, `parse_print` — the
decode-after-encode direction, for `nameOk` registries, exactly —
over the TextKit base (the scans ride `TextKit.Parser.takeWhile`,
`TextKit.expect`, `TextKit.scanNat`; the inversions cite
TextKit.Lemmas, no local scan-lemma copies).
NOTED, NOT PROVED: the canonicalization direction (`print (parse s) = s`
for canonical `s`) — the sort's permutation theory on top; the gate
re-derives the bytes instead. NO `sorry`, NO `axiom` anywhere above.
-/
