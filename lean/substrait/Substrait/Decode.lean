/-
# Substrait.Decode — the text decoder (the emitter's inverse)

lean-v3 step 8 / D6: the parser shares the emitter's skeleton factorization
and `parse ∘ emit = id` is the theorem. Hand-rolled recursive descent over
`List Char` (D15) — structural prefix scanners for the leaves (proved) and
fuel-bounded recursion for the grammar layers (the project's fuel
discipline), rather than Parsec's `partial` combinators (proof-hostile).

Proved layer so far:
- `unescape_escape`: unescaping inverts `Emit.Text.escape`.
- `scanQuotedRaw_escChars`/`scanQuotedRaw_escape`: the raw quoted scanner
  recovers escape text (pairs never misread as the closing quote).
- `scanIdent_of_identifier`, `scanName_quoted`, `scanName_name`: the name
  inversion (`Emit.Text.name` scans back to the name, both branches).
- the TYPED wire decode: `decodeExpr`/`decodeArgs` + `decodeExpr_reEnc`/
  `decodeArgs_reEnc` (decode → lower recovers the wire term), and
  `decodeRel` + `decodeRel_reEnc` (the full `Typed.Rel` grammar: read /
  filter / project / aggregate / sort / fetch / join / set / write /
  extensionSingle; wire-side rejections for cross/extensionLeaf/
  extensionMulti).  `Rel.okS` is the hypothesis predicate (per-node
  recursion plus the decoded-schema pins the GADT demands — see its
  comment).

The full-plan round trip is executable-witnessed in Tests (decode-emit = id
on the golden plan; emit-decode byte-identical on the golden text).

Wire-decode notes (the rel layer):
- the mutual-block `Proto.Rel` defeats structural recursion, its derived
  `sizeOf` simproc disagrees with the instance funs, and `sizeOf` in a
  definition body hits an LCNF codegen failure — `decodeRel` is therefore
  well-founded on the actual `sizeOf` instance with hand-proved decreasing
  goals (`wf*_size`, from the instance funs, simproc-free);
- schema equality for the square/set checks is a hand-rolled
  `DecidableEq SType` (mutual inductives are refused by the deriving
  handlers; `Schema.lean` ships none by design);
- the master theorem compares at the WIRE level (decode → `relLower` = id):
  the decoded rel's projection names are placeholders (`""`) and its
  `FunctionSig.deterministic`/`sessionDependent` are re-derived defaults —
  both are erased by the wire, so the wire-level statement is the honest
  strongest form (the same convention as `decodeExpr_reEnc`).

Documented lossiness (the format, not the decoder): `RelCommon.direct` vs
absent emit kinds print identically (canonicalized to `none` on parse);
`advancedExtension` never prints; extension declarations print in
(anchor, kind) order; explicit-emit `Project`s (mapping baked into args)
are not invertible and rejected.

Substrait stays core-only: nothing here imports the engine model.
-/
import Substrait.Emit.Text
import Substrait.Grammar
import Substrait.Typed

namespace Substrait.Decode

/-! ## the parser monad -/

/-- The rest-threading parser monad: over `List Char`, returning the value
    and the unconsumed rest. `Parser` is an `abbrev` (reducible), so every
    public entry keeps its plain `List Char → Option (α × List Char)`
    signature; the `do`-blocks live in `where`-clause helpers typed
    `… → Parser α` (the notation's monad inference needs the `Parser` head). -/
abbrev Parser (α : Type) : Type := List Char → Option (α × List Char)

namespace Parser

@[simp] def result (a : α) : Parser α := fun cs => some (a, cs)

@[simp] def bind {α β} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun cs => match p cs with | none => none | some (a, rest) => f a rest

instance : Monad Parser where
  pure := Parser.result
  bind := Parser.bind

@[simp] def fail : Parser α := fun _ => none

/-- Look at (but do not consume) the next character. -/
@[simp] def peek : Parser Char :=
  fun cs => match cs with | c :: _ => some (c, cs) | [] => none

/-- The input as it stands (position capture — do-block branches that need
    the unconsumed text, e.g. fuel lengths and rest-shape tests). -/
@[simp] def rest : Parser (List Char) := fun cs => some (cs, cs)

/-- Rewind to an earlier captured position (position-reset jumps). -/
@[simp] def jump (tgt : List Char) : Parser Unit := fun _ => some ((), tgt)

/-- Consume one specific character (the leaf scanners' quote consumption). -/
@[simp] def consumeChar (c : Char) : Parser Unit :=
  fun cs => match cs with | c' :: rest => if c' == c then some ((), rest) else none | [] => none

/-- Consume the maximal prefix matching `p` — the leaf scanners' core. -/
@[simp] def takeWhile (p : Char → Bool) : Parser String :=
  fun cs => some (String.ofList (cs.takeWhile p), cs.dropWhile p)

/-- `do`-notation's `>>=` at an applied position reduces to the bind's
    `match` (the class-instance glue is otherwise opaque to `simp`). -/
@[simp] theorem bind_apply (p : Parser α) (f : α → Parser β) (cs : List Char) :
    (p >>= f) cs = (Parser.bind p f) cs := by rfl

/-- `consumeChar` at a matching literal head. -/
@[simp] theorem consumeChar_self (c : Char) (rest : List Char) :
    consumeChar c (c :: rest) = some ((), rest) := by
  unfold consumeChar
  simp

/-- `pure` at an applied position (the instance glue unfolds here). -/
@[simp] theorem pure_apply (a : α) (cs : List Char) :
    (pure a : Parser α) cs = some (a, cs) := rfl

end Parser

/-- `(toString c).toList = [c]` — core never proves it; the chain is
    `Char.toString = String.singleton` + `singleton_eq_ofList`. -/
theorem toString_char_toList (c : Char) : (toString c).toList = [c] := by
  show (Char.toString c).toList = [c]
  rw [Char.toString, String.singleton_eq_ofList, String.toList_ofList]

/-- The character text `Emit.Text.escape` writes for one character, as a
    list (the proof-side reading of the emitter's match table). -/
def escChars : Char → List Char
  | '\n' => ['\\', 'n'] | '\t' => ['\\', 't'] | '\r' => ['\\', 'r']
  | '\\' => ['\\', '\\'] | '"' => ['\\', '"'] | '\'' => ['\\', '\'']
  | c => [c]

/-- The emitter's escape arm IS `String.ofList (escChars ·)` (arm-for-arm;
    the default arm is `toString_char_toList`). -/
theorem escapeArm_eq (c : Char) :
    (match c with
      | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | '\\' => "\\\\" | '"' => "\\\"" | '\'' => "\\'"
      | c => toString c) = String.ofList (escChars c) := by
  split
  case h_1 => rfl
  case h_2 => rfl
  case h_3 => rfl
  case h_4 => rfl
  case h_5 => rfl
  case h_6 => rfl
  case h_7 =>
    rw [escChars.eq_7 _ (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)]
    calc toString _ = String.ofList (toString _).toList := String.ofList_toList.symm
      _ = String.ofList [_] := by rw [toString_char_toList]

/-- The emitter's escape, as a list fold over `escChars`. -/
theorem escape_toList (s : String) :
    (Emit.Text.escape s).toList = s.toList.flatMap escChars := by
  have foldFlat : ∀ (l : List Char) (init : List Char),
      l.foldl (fun acc c => acc ++ escChars c) init = init ++ l.flatMap escChars := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons c rest ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (init ++ escChars c), List.flatMap_cons, List.append_assoc]
  have foldString : ∀ (init : String) (l : List Char),
      (l.foldl (fun (acc : String) c => acc ++ (match c with
          | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
          | '\\' => "\\\\" | '"' => "\\\"" | '\'' => "\\'"
          | c => toString c)) init).toList =
        init.toList ++ l.foldl (fun acc c => acc ++ escChars c) [] := by
    intro init l
    induction l generalizing init with
    | nil => simp
    | cons c rest ih =>
      simp only [List.foldl_cons, List.nil_append]
      rw [escapeArm_eq]
      rw [ih (init ++ String.ofList (escChars c))]
      rw [String.toList_append, String.toList_ofList, List.append_assoc]
      rw [foldFlat rest (escChars c), foldFlat rest []]
      simp
  unfold Emit.Text.escape
  refine (foldString "" s.toList).trans ?_
  rw [foldFlat s.toList []]
  simp

/-- Unescape: the structural inverse of escape (fails on a bare backslash —
    `escape` never writes one). -/
def unescapeGo : List Char → List Char → Option (List Char)
  | acc, [] => some acc.reverse
  | acc, '\\' :: 'n' :: rest => unescapeGo ('\n' :: acc) rest
  | acc, '\\' :: 't' :: rest => unescapeGo ('\t' :: acc) rest
  | acc, '\\' :: 'r' :: rest => unescapeGo ('\r' :: acc) rest
  | acc, '\\' :: '\\' :: rest => unescapeGo ('\\' :: acc) rest
  | acc, '\\' :: '"' :: rest => unescapeGo ('"' :: acc) rest
  | acc, '\\' :: '\'' :: rest => unescapeGo ('\'' :: acc) rest
  | _, '\\' :: _ => none
  | acc, c :: rest => unescapeGo (c :: acc) rest

def unescape (s : String) : Option String :=
  (unescapeGo [] s.toList).map String.ofList

/-- Per-character step of the unescaper: consuming `escChars c` prepends `c`. -/
theorem unescapeGo_escChars (acc rest : List Char) (c : Char) :
    unescapeGo acc (escChars c ++ rest) = unescapeGo (c :: acc) rest := by
  by_cases h1 : c = '\n'; · subst h1; rw [escChars.eq_1]; rfl
  by_cases h2 : c = '\t'; · subst h2; rw [escChars.eq_2]; rfl
  by_cases h3 : c = '\r'; · subst h3; rw [escChars.eq_3]; rfl
  by_cases h4 : c = '\\'; · subst h4; rw [escChars.eq_4]; rfl
  by_cases h5 : c = '"'; · subst h5; rw [escChars.eq_5]; rfl
  by_cases h6 : c = '\''; · subst h6; rw [escChars.eq_6]; rfl
  have hesc : escChars c = [c] := escChars.eq_7 c h1 h2 h3 h4 h5 h6
  rw [hesc]
  show unescapeGo acc (c :: rest) = unescapeGo (c :: acc) rest
  rw [unescapeGo.eq_9 acc c rest
    (fun _ hcontra _ => absurd hcontra h4) (fun _ hcontra _ => absurd hcontra h4)
    (fun _ hcontra _ => absurd hcontra h4) (fun _ hcontra _ => absurd hcontra h4)
    (fun _ hcontra _ => absurd hcontra h4) (fun _ hcontra _ => absurd hcontra h4) h4]

/-- **The escape inversion**: unescaping inverts escaping. -/
theorem unescape_escape (s : String) : unescape (Emit.Text.escape s) = some s := by
  have key : ∀ (l acc : List Char),
      unescapeGo acc (l.flatMap escChars) = some (l.reverse ++ acc).reverse := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons c rest ih =>
      intro acc
      rw [List.flatMap_cons, unescapeGo_escChars, ih (c :: acc),
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  rw [unescape, escape_toList, key s.toList []]
  simp [Option.map_some, String.ofList_toList]

-- ── names ─────────────────────────────────────────────────────────────────

/-- Scan a bare identifier: ASCII alpha, then ident-chars. Returns the name
    and the unconsumed rest. -/
def scanIdent : List Char → Option (String × List Char) := scanIdentGo
where
  scanIdentGo : Parser String := do
    let h ← Parser.peek
    if h.isAlpha then Parser.takeWhile Emit.Text.isIdentChar
    else Parser.fail

/-- Scan raw quoted content (escape pairs kept raw, in order) up to the
    closing `q`. -/
def scanQuotedRaw (q : Char) : List Char → List Char → Option (List Char × List Char)
  | acc, c :: rest =>
    if c == q then some (acc.reverse, rest)
    else if c == '\\' then
      match rest with
      | c2 :: rest2 => scanQuotedRaw q (c2 :: '\\' :: acc) rest2
      | [] => none
    else scanQuotedRaw q (c :: acc) rest
  | _, [] => none

/-- Per-character step of the raw quoted scanner over escape text: the
    escape pair is consumed as a pair (never misread as a closing quote). -/
theorem scanQuotedRaw_escChars (q : Char) (acc rest : List Char) (c : Char)
    (hq : q = '"' ∨ q = '\'') :
    scanQuotedRaw q acc (escChars c ++ rest) = scanQuotedRaw q ((escChars c).reverse ++ acc) rest := by
  rcases hq with rfl | rfl
  · by_cases h1 : c = '\n'; · subst h1; rw [escChars.eq_1]; show scanQuotedRaw '"' acc ('\\' :: 'n' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h2 : c = '\t'; · subst h2; rw [escChars.eq_2]; show scanQuotedRaw '"' acc ('\\' :: 't' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h3 : c = '\r'; · subst h3; rw [escChars.eq_3]; show scanQuotedRaw '"' acc ('\\' :: 'r' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h4 : c = '\\'; · subst h4; rw [escChars.eq_4]; show scanQuotedRaw '"' acc ('\\' :: '\\' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h5 : c = '"'; · subst h5; rw [escChars.eq_5]; show scanQuotedRaw '"' acc ('\\' :: '"' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h6 : c = '\''; · subst h6; rw [escChars.eq_6]; show scanQuotedRaw '"' acc ('\\' :: '\'' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    have hesc : escChars c = [c] := escChars.eq_7 c h1 h2 h3 h4 h5 h6
    rw [hesc]
    show scanQuotedRaw '"' acc (c :: rest) = _
    cases rest with
    | nil => rw [scanQuotedRaw.eq_2]; simp [h4, h5]
    | cons c2 rest2 => rw [scanQuotedRaw.eq_1]; simp [h4, h5]
  · by_cases h1 : c = '\n'; · subst h1; rw [escChars.eq_1]; show scanQuotedRaw '\'' acc ('\\' :: 'n' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h2 : c = '\t'; · subst h2; rw [escChars.eq_2]; show scanQuotedRaw '\'' acc ('\\' :: 't' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h3 : c = '\r'; · subst h3; rw [escChars.eq_3]; show scanQuotedRaw '\'' acc ('\\' :: 'r' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h4 : c = '\\'; · subst h4; rw [escChars.eq_4]; show scanQuotedRaw '\'' acc ('\\' :: '\\' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h5 : c = '"'; · subst h5; rw [escChars.eq_5]; show scanQuotedRaw '\'' acc ('\\' :: '"' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    by_cases h6 : c = '\''; · subst h6; rw [escChars.eq_6]; show scanQuotedRaw '\'' acc ('\\' :: '\'' :: rest) = _; rw [scanQuotedRaw.eq_1]; simp
    have hesc : escChars c = [c] := escChars.eq_7 c h1 h2 h3 h4 h5 h6
    rw [hesc]
    show scanQuotedRaw '\'' acc (c :: rest) = _
    cases rest with
    | nil => rw [scanQuotedRaw.eq_2]; simp [h4, h6]
    | cons c2 rest2 => rw [scanQuotedRaw.eq_1]; simp [h4, h6]

/-- Scanning raw quoted content recovers the escape text up to the closing
    quote (the go prepends, the closing arm reverses). -/
theorem scanQuotedRaw_escape (q : Char) (l acc : List Char) (rest : List Char)
    (hq : q = '"' ∨ q = '\'') :
    scanQuotedRaw q acc (l.flatMap escChars ++ q :: rest) =
      some (acc.reverse ++ l.flatMap escChars, rest) := by
  rcases hq with rfl | rfl
  · induction l generalizing acc with
    | nil =>
      rw [List.flatMap_nil, List.nil_append]
      cases rest with
      | nil =>
        rw [scanQuotedRaw.eq_2]
        simp
      | cons c2 rest2 =>
        rw [scanQuotedRaw.eq_1]
        simp
    | cons c rest' ih =>
      rw [List.flatMap_cons, List.append_assoc]
      rw [scanQuotedRaw_escChars '"' acc (rest'.flatMap escChars ++ '"' :: rest) c (Or.inl rfl)]
      rw [ih]
      rw [List.reverse_append, List.reverse_reverse, ← List.append_assoc]
  · induction l generalizing acc with
    | nil =>
      rw [List.flatMap_nil, List.nil_append]
      cases rest with
      | nil =>
        rw [scanQuotedRaw.eq_2]
        simp
      | cons c2 rest2 =>
        rw [scanQuotedRaw.eq_1]
        simp
    | cons c rest' ih =>
      rw [List.flatMap_cons, List.append_assoc]
      rw [scanQuotedRaw_escChars '\'' acc (rest'.flatMap escChars ++ '\'' :: rest) c (Or.inr rfl)]
      rw [ih]
      rw [List.reverse_append, List.reverse_reverse, ← List.append_assoc]

/-- Scan a name: quoted (content unescaped) or bare. -/
def scanName : List Char → Option (String × List Char) := scanNameGo
where
  scanNameGo : Parser String := do
    let cs ← Parser.rest
    match cs with
    | '"' :: _ => do
        let _ ← Parser.consumeChar '"'
        let raw ← scanQuotedRaw '"' []
        match unescape (String.ofList raw) with
        | some n => pure n
        | none => Parser.fail
    | _ => scanIdent

/-- Bare-name inversion: an identifier scans back to itself, provided the
    following text starts with a non-identifier character (the emitter
    always follows names with a delimiter). -/
theorem scanIdent_of_identifier (n : String) (h : Emit.Text.isIdentifier n = true)
    (rest : List Char)
    (hsep : rest = [] ∨ ∃ c0 rest0, rest = c0 :: rest0 ∧ Emit.Text.isIdentChar c0 = false) :
    scanIdent (n.toList ++ rest) = some (n, rest) := by
  unfold Emit.Text.isIdentifier at h
  cases hn : n.toList with
  | nil => rw [hn] at h; simp at h
  | cons c tail =>
    rw [hn] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hc, htail⟩ := h
    have hall : ∀ a ∈ tail, Emit.Text.isIdentChar a := List.all_eq_true.mp htail
    show scanIdent (c :: (tail ++ rest)) = _
    unfold scanIdent
    rw [show scanIdent.scanIdentGo (c :: (tail ++ rest)) =
        Parser.takeWhile Emit.Text.isIdentChar (c :: (tail ++ rest)) by
      unfold scanIdent.scanIdentGo
      simp only [Parser.bind_apply, Parser.bind, Parser.peek, Parser.result]
      simp [hc]]
    rw [Parser.takeWhile]
    have hic : Emit.Text.isIdentChar c = true := by
      unfold Emit.Text.isIdentChar
      rw [hc]
      rfl
    rw [List.takeWhile_cons_of_pos hic]
    rw [List.takeWhile_append_of_pos hall]
    rw [List.dropWhile_cons_of_pos hic]
    rw [List.dropWhile_append_of_pos hall]
    cases hsep with
    | inl hr =>
      subst hr
      rw [List.takeWhile_nil, List.dropWhile_nil, List.append_nil, ← hn, String.ofList_toList]
    | inr hr =>
      obtain ⟨c0, rest0, hr, h0⟩ := hr
      subst hr
      have h0' : ¬ (Emit.Text.isIdentChar c0 = true) := by simp [h0]
      rw [List.takeWhile_cons_of_neg h0', List.dropWhile_cons_of_neg h0',
        List.append_nil, ← hn, String.ofList_toList]

/-- Quoted-name inversion. -/
theorem scanName_quoted (n : String) (rest : List Char) :
    scanName ('"' :: (Emit.Text.escape n).toList ++ '"' :: rest) = some (n, rest) := by
  unfold scanName scanName.scanNameGo
  let X : List Char := (Emit.Text.escape n).toList ++ '"' :: rest
  simp [Parser.bind_apply, Parser.bind, Parser.rest, Parser.result, Parser.consumeChar]
  rw [escape_toList, scanQuotedRaw_escape (q := '"') (acc := []) (rest := rest) (hq := Or.inl rfl)]
  rw [List.reverse_nil, List.nil_append]
  simp [Parser.bind_apply, Parser.bind, Parser.result]
  rw [← escape_toList, String.ofList_toList, unescape_escape]
  rfl

/-- **The name inversion**: `Emit.Text.name` scans back to the name. -/
theorem scanName_name (n : String) (rest : List Char)
    (hsep : rest = [] ∨ ∃ c0 rest0, rest = c0 :: rest0 ∧ Emit.Text.isIdentChar c0 = false) :
    scanName ((Emit.Text.name n).toList ++ rest) = some (n, rest) := by
  unfold Emit.Text.name
  by_cases hi : Emit.Text.isIdentifier n = true
  · rw [if_pos hi]
    show scanName (n.toList ++ rest) = _
    cases hn : n.toList with
    | nil =>
      unfold Emit.Text.isIdentifier at hi
      rw [hn] at hi
      simp at hi
    | cons c tail =>
      have hcq : c ≠ '"' := by
        unfold Emit.Text.isIdentifier at hi
        rw [hn] at hi
        simp only [Bool.and_eq_true] at hi
        intro hcontra
        rw [hcontra] at hi
        simp [Char.isAlpha] at hi
      show scanName (c :: (tail ++ rest)) = _
      rw [show scanName (c :: (tail ++ rest)) = scanIdent (c :: (tail ++ rest)) by
        unfold scanName scanName.scanNameGo
        simp only [Parser.bind_apply, Parser.bind, Parser.rest, Parser.result]
        simp [hcq]]
      have hsc := scanIdent_of_identifier n hi rest hsep
      rw [hn] at hsc
      exact hsc
  · rw [if_neg hi]
    have hl : ("\"" ++ Emit.Text.escape n ++ "\"").toList =
        '"' :: ((Emit.Text.escape n).toList ++ ['"']) := by
      rw [String.toList_append, String.toList_append]
      rfl
    rw [hl, List.cons_append, List.append_assoc]
    show scanName ('"' :: ((Emit.Text.escape n).toList ++ '"' :: rest)) = _
    exact scanName_quoted n rest

-- ── scanner kit (grammar layer) ─────────────────────────────────────────────

/-- Is `p` a literal prefix of `cs`? -/
def startsWith (cs : List Char) (p : String) : Bool := p.toList.isPrefixOf cs

/-- Consume the literal prefix. -/
def expect (p : String) (cs : List Char) : Option (List Char) :=
  if startsWith cs p then some (cs.drop p.length) else none

/-- Scan a decimal natural. -/
def scanNat : List Char → Option (Nat × List Char) := scanNatGo
where
  scanNatGo : Parser Nat := do
    let ds ← Parser.takeWhile Char.isDigit
    if ds == "" then Parser.fail
    else
      let n := ds.toList.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
      pure n

/-- Scan a decimal integer (optional leading `-`). -/
def scanInt : List Char → Option (Int × List Char)
  | '-' :: rest => (do let n ← scanNat; pure (-(n : Int)) : Parser Int) rest
  | cs => (do let n ← scanNat; pure (n : Int) : Parser Int) cs

/-- The prefix kit: a literal prefix is recognized (inversion proofs). -/
theorem startsWith_self (p : String) (rest : List Char) :
    startsWith (p.toList ++ rest) p = true := by
  unfold startsWith
  rw [List.isPrefixOf_iff_prefix]
  exact ⟨rest, rfl⟩

/-- The prefix kit: a literal prefix is consumed by `expect`. -/
theorem expect_self (p : String) (rest : List Char) : expect p (p.toList ++ rest) = some rest := by
  unfold expect
  rw [if_pos (startsWith_self p rest)]
  have h : p.length = p.toList.length := rfl
  rw [h, List.drop_left]


-- ── types ──────────────────────────────────────────────────────────────────

/-- The nullability-suffix consumer, top-level so equation lemmas exist
    (inversion proofs reduce it via `withNull.eq_1`/`withNull.eq_2`). -/
def withNull (mk : Proto.Nullability → Proto.PType) (rest : List Char) :
    Option (Proto.PType × List Char) :=
  match rest with
  | '?' :: rest' => some (mk .nullable, rest')
  | _ => some (mk .required, rest)

/-- The suffix lemma: no leading `?` → required. -/
theorem withNull_required (mk : Proto.Nullability → Proto.PType) (rest : List Char)
    (h : rest.head? ≠ some '?') :
    withNull mk rest = some (mk .required, rest) := by
  rw [withNull.eq_2]
  intro rest' hr
  subst hr
  exact h rfl

/-- The suffix lemma: leading `?` → nullable. -/
theorem withNull_nullable (mk : Proto.Nullability → Proto.PType) (rest : List Char) :
    withNull mk ('?' :: rest) = some (mk .nullable, rest) := withNull.eq_1 mk rest

/-- **Head lexing**: fold the closed `TCtor` table for the prefix match.
    The match is UNIQUE by `TCtor.prefix_unique`, so the fold order is
    irrelevant — this replaces the ordered 14-branch if-chain. Structural
    `go` (not `findSome?`) for the same whnf reason as `parseScalarType`.
    Fuel-free: lexing never recurses, which is what makes the new
    `parseType_mono` a per-ctor case split with no `by_cases` chains. -/
def lexCtorGo : List Substrait.Grammar.TCtor → List Char → Option Substrait.Grammar.TCtor
  | [], _ => none
  | t :: ts, cs => if startsWith cs t.prefix then some t else lexCtorGo ts cs

def lexCtor (cs : List Char) : Option Substrait.Grammar.TCtor :=
  lexCtorGo Substrait.Grammar.TCtor.all cs

/-- The fold finds the matching row; uniqueness (`prefix_unique`) forces
    the found row to BE `t` whenever `t`'s prefix matches. -/
theorem lexCtorGo_eq_of_startsWith (ts : List Substrait.Grammar.TCtor) (cs : List Char)
    (t : Substrait.Grammar.TCtor) (hmem : t ∈ ts) (hsw : startsWith cs t.prefix = true) :
    lexCtorGo ts cs = some t := by
  induction ts with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [lexCtorGo]
    by_cases hx : startsWith cs x.prefix = true
    · rw [if_pos hx]
      have hxeq : x = t := Substrait.Grammar.TCtor.prefix_unique x t cs
        (List.isPrefixOf_iff_prefix.mp hx) (List.isPrefixOf_iff_prefix.mp hsw)
      rw [hxeq]
    · rw [if_neg hx]
      rcases List.mem_cons.mp hmem with htx | hin
      · subst htx; exact absurd hsw hx
      · exact ih hin

/-- Lexing succeeds on exactly the ctors whose prefix matches. -/
theorem lexCtor_eq_some (t : Substrait.Grammar.TCtor) (cs : List Char)
    (hsw : startsWith cs t.prefix = true) : lexCtor cs = some t :=
  lexCtorGo_eq_of_startsWith _ _ _ (Substrait.Grammar.TCtor.all_complete t) hsw

/-- Self-lexing: a ctor's own text lexes to it. ONE lemma for all 13 ctors —
    the round-trip proofs' per-branch prefix skips collapse into this. -/
theorem lexCtor_self (t : Substrait.Grammar.TCtor) (rest : List Char) :
    lexCtor (t.prefix.toList ++ rest) = some t :=
  lexCtor_eq_some _ _ (startsWith_self _ _)

mutual

/-- `", "`-separated type list (struct fields); structural on `lfuel`. -/
def parseTypeList : Nat → Nat → List Char → Option (List Proto.PType × List Char)
  | 0, _, _ => none
  | lfuel + 1, tfuel, cs =>
    match parseType tfuel cs with
    | none => none
    | some (t, r1) =>
      match expect ", " r1 with
      | some r2 => match parseTypeList lfuel tfuel r2 with
        | some (ts, r3) => some (t :: ts, r3)
        | none => none
      | none => some ([t], r1)

/-- Parse a type: lex the head ctor (`lexCtor`, unique by
    `TCtor.prefix_unique`), then dispatch on the CONSTRUCTOR — no prefix
    if-chain. `fuel` bounds nesting depth (list/map/struct). -/
def parseType : Nat → List Char → Option (Proto.PType × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match lexCtor cs with
    | none => none
    | some (.scalar c) =>
      withNull (Substrait.Grammar.ScalarCtor.toPType c)
        (cs.drop (Substrait.Grammar.ScalarCtor.prefix c).length)
    | some .decimal =>
      match scanNat (cs.drop 8) with
      | some (p, r1) =>
        match expect "," r1 with
        | some r2 => match scanNat r2 with
          | some (s, r3) => match expect ">" r3 with
            | some r4 => withNull (.decimal p s) r4
            | none => none
          | none => none
        | none => none
      | none => none
    | some .list =>
      match parseType fuel (cs.drop 5) with
      | some (e, r1) => match expect ">" r1 with
        | some r2 => withNull (.list e) r2
        | none => none
      | none => none
    | some .map =>
      match parseType fuel (cs.drop 4) with
      | some (k, r1) => match expect ", " r1 with
        | some r2 => match parseType fuel r2 with
          | some (v, r3) => match expect ">" r3 with
            | some r4 => withNull (.map k v) r4
            | none => none
          | none => none
        | none => none
      | none => none
    | some .struct =>
      -- the emitter prints `struct<>` for the empty field list; parseTypeList
      -- needs ≥1 element, so the empty case is peeled off here
      match expect ">" (cs.drop 7) with
      | some r2 => withNull (.struct []) r2
      | none =>
        match parseTypeList (cs.length + 1) fuel (cs.drop 7) with
        | some (fs, r1) => match expect ">" r1 with
          | some r2 => withNull (.struct fs) r2
          | none => none
        | none => none

end

/-- Type nesting depth — the fuel a parse of `t`'s text needs. The fuel is
    a technicality of the termination proof; every successful parse at fuel
    f also succeeds at any larger fuel (`parseType_mono`). -/
def typeDepth : Proto.PType → Nat
  | .bool _ | .i8 _ | .i16 _ | .i32 _ | .i64 _ | .fp32 _ | .fp64 _
  | .string _ | .binary _ | .decimal _ _ _ | .userDefined _ _ _ => 1
  | .list e _ => typeDepth e + 1
  | .map k v _ => typeDepth k + typeDepth v + 1
  | .struct fs _ => fs.foldl (fun m t => max m (typeDepth t)) 0 + 1

/-- **Fuel monotonicity (+1)**: one more unit of fuel never breaks a
    successful parse. The proof peels the 14-branch if-chain (conditions
    depend on cs only, so both sides agree); the list/map recursive branches
    discharge by the fuel-`f` IH; the struct branch uses the nested
    `hlist_mono` (an lfuel-induction with the fuel-`f` IH available — the
    mutual knot dissolved by nesting, not by a `mutual` block). -/
theorem parseType_mono (fuel : Nat) (cs : List Char) (r : Proto.PType × List Char) :
    parseType fuel cs = some r → parseType (fuel + 1) cs = some r := by
  induction fuel generalizing cs r with
  | zero => simp [parseType]
  | succ f ih =>
    have hlist_mono : ∀ (lf : Nat) (cs' : List Char) (r' : List Proto.PType × List Char),
        parseTypeList lf f cs' = some r' → parseTypeList lf (f + 1) cs' = some r' := by
      intro lf
      induction lf with
      | zero => intro cs' r' h; simp [parseTypeList] at h
      | succ lf ihl =>
        intro cs' r' h
        rw [parseTypeList] at h ⊢
        cases hx : parseType f cs' with
        | none => simp_all
        | some p =>
          have hpt := ih _ _ hx
          cases h2 : expect ", " p.2 with
          | none => simp_all
          | some r2 =>
            cases hy : parseTypeList lf f r2 with
            | none => simp_all
            | some q =>
              have hlist := ihl _ _ hy
              simp_all
    intro h
    unfold parseType at h ⊢
    -- lexing is fuel-free: both sides dispatch on the same ctor. The old
    -- four `by_cases` prefix chains are now ONE case split on the lexed
    -- head — per ctor, only the recursion sites need the IH.
    cases hlex : lexCtor cs with
    | none => simp_all
    | some t =>
      simp only [hlex] at h ⊢
      cases t with
      | scalar c => exact h
      | decimal => exact h
      | list =>
        cases he : parseType f (cs.drop 5) with
        | none => simp_all
        | some x =>
          cases hgt : expect ">" x.2 with
          | none => simp_all
          | some r2 =>
            have hih := ih _ _ he
            simp_all
      | map =>
        cases hk : parseType f (cs.drop 4) with
        | none => simp_all
        | some x =>
          cases hsep : expect ", " x.2 with
          | none => simp_all
          | some r2 =>
            cases hv : parseType f r2 with
            | none => simp_all
            | some y =>
              have ihk := ih _ _ hk
              have ihv := ih _ _ hv
              simp_all
      | struct =>
        cases he0 : expect ">" (cs.drop 7) with
        | some r2 =>
          cases r2 with
          | nil => simp_all
          | cons c cs' => simp_all
        | none =>
          cases hlist : parseTypeList (cs.length + 1) f (cs.drop 7) with
          | none => simp_all
          | some x =>
            cases hgt : expect ">" x.2 with
            | none => simp_all
            | some r2 =>
              have hlm := hlist_mono (cs.length + 1) _ _ hlist
              simp_all

/-- **Fuel monotonicity (k steps)**: any extra fuel preserves a successful
    parse. The form inversion proofs consume. -/
theorem parseType_mono_of_le (f k : Nat) (cs : List Char) (r : Proto.PType × List Char) :
    parseType f cs = some r → parseType (f + k) cs = some r := by
  intro h
  induction k with
  | zero => exact h
  | succ k ihk => rw [Nat.add_succ]; exact parseType_mono _ _ _ ihk

/-- The depth-bounded form: a parse at fuel `typeDepth t` succeeds at any
    larger fuel. -/
theorem parseType_at_depth (t : Proto.PType) (cs : List Char) (r : Proto.PType × List Char)
    (h : parseType (typeDepth t) cs = some r) : ∀ k, parseType (typeDepth t + k) cs = some r :=
  fun _k => parseType_mono_of_le _ _ _ _ h

-- ── types: the inversion theorems ─────────────────────────────────────────

/-- The parseType form: a scalar's text parses at fuel 1. -/
theorem parseType_scalar (c : Substrait.Grammar.ScalarCtor) (rest : List Char)
    (hrest : rest.head? ≠ some '?') :
    parseType 1 ((Substrait.Grammar.ScalarCtor.prefix c).toList ++ rest) =
      some (Substrait.Grammar.ScalarCtor.toPType c .required, rest) := by
  rw [show (Substrait.Grammar.ScalarCtor.prefix c) =
      Substrait.Grammar.TCtor.prefix (.scalar c) from rfl]
  unfold parseType
  rw [lexCtor_self]
  -- the match on `some (.scalar c)` is constructor-headed: reduce it, then
  -- the drop peels the prefix
  show withNull (Substrait.Grammar.ScalarCtor.toPType c)
      (((Substrait.Grammar.TCtor.prefix (.scalar c)).toList ++ rest).drop
        (Substrait.Grammar.ScalarCtor.prefix c).length) =
    some (Substrait.Grammar.ScalarCtor.toPType c .required, rest)
  rw [show (Substrait.Grammar.ScalarCtor.prefix c).length =
      (Substrait.Grammar.TCtor.prefix (.scalar c)).toList.length from rfl,
    List.drop_left]
  exact withNull_required _ rest hrest

/-- The `(p ++ "?")` text as a char list: the prefix, then the `?`. -/
private theorem toList_append_question (p : String) (rest : List Char) :
    (p ++ "?").toList ++ rest = p.toList ++ ('?' :: rest) := by
  rw [String.toList_append, show ("?".toList) = ['?'] from by decide]
  simp [List.append_assoc]

/-- The nullable-suffix form of `parseType_scalar`: `<prefix>?` parses at
    `.nullable`. ONE lemma for all nine scalar ctors — the nine nullable
    round-trip sites collapse onto it. -/
theorem parseType_scalar_nullable (c : Substrait.Grammar.ScalarCtor) (rest : List Char) :
    parseType 1 ((Substrait.Grammar.ScalarCtor.prefix c).toList ++ '?' :: rest) =
      some (Substrait.Grammar.ScalarCtor.toPType c .nullable, rest) := by
  rw [show (Substrait.Grammar.ScalarCtor.prefix c) =
      Substrait.Grammar.TCtor.prefix (.scalar c) from rfl]
  unfold parseType
  rw [lexCtor_self]
  show withNull (Substrait.Grammar.ScalarCtor.toPType c)
      (((Substrait.Grammar.TCtor.prefix (.scalar c)).toList ++ '?' :: rest).drop
        (Substrait.Grammar.ScalarCtor.prefix c).length) =
    some (Substrait.Grammar.ScalarCtor.toPType c .nullable, rest)
  rw [show (Substrait.Grammar.ScalarCtor.prefix c).length =
      (Substrait.Grammar.TCtor.prefix (.scalar c)).toList.length from rfl,
    List.drop_left]
  exact withNull_nullable _ rest



/-- `expect ">"` on a literal `>` head. -/
private theorem expect_gt_cons (rest : List Char) : expect ">" ('>' :: rest) = some rest := by
  unfold expect startsWith
  have hpre : ">".toList.isPrefixOf ('>' :: rest) = true := by rfl
  rw [if_pos hpre]
  rfl

/-- `expect ", "` on a literal `, ` head. -/
private theorem expect_comma_sp (rest : List Char) : expect ", " (',' :: ' ' :: rest) = some rest := by
  unfold expect startsWith
  have hpre : ", ".toList.isPrefixOf (',' :: ' ' :: rest) = true := by rfl
  rw [if_pos hpre]
  rfl

/-- `(p ++ s).toList ++ tail = p.toList ++ (s.toList ++ tail)` — the prefix
    split the if-chain rewrites consume. -/
private theorem toList_head_eq (p s : String) (tail : List Char) :
    (p ++ s).toList ++ tail = p.toList ++ (s.toList ++ tail) := by
  rw [String.toList_append]
  rw [List.append_assoc]

/-- `(a ++ b ++ c).toList` split fully. -/
private theorem toList_append3 (a b c : String) :
    (a ++ b ++ c).toList = a.toList ++ b.toList ++ c.toList := by
  rw [String.toList_append, String.toList_append]

-- the `Except`-monad reductions the emitter `do` blocks need (the emitter's
-- hard-error paths never produce a value; these make `simp` see it)

@[simp]
private theorem error_map_reduce {ε α β : Type} (e : ε) (f : α → β) :
    f <$> (Except.error e : Except ε α) = (Except.error e : Except ε β) := by rfl

@[simp]
private theorem ok_map_reduce {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = (Except.ok (f a) : Except ε β) := by rfl

@[simp]
private theorem error_bind_reduce {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = Except.error e := by rfl

@[simp]
private theorem ok_bind_reduce {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := by rfl

@[simp]
private theorem pure_ok_reduce {ε α : Type} (a : α) :
    (pure a : Except ε α) = Except.ok a := by rfl

@[simp]
private theorem throw_reduce {ε α : Type} (e : ε) :
    (throw e : Except ε α) = Except.error e := by rfl

/-- The scanNat stopping condition: empty, or a first char that isn't a digit. -/
private def notDigitHead (rest : List Char) : Prop :=
  rest.head? = none ∨ ∃ c cs0, rest = c :: cs0 ∧ c.isDigit = false

private theorem scanNat_takeWhile_nil (rest : List Char) (hstop : notDigitHead rest) :
    rest.takeWhile Char.isDigit = [] := by
  cases rest with
  | nil => rfl
  | cons c cs0 =>
    rcases hstop with hnone | ⟨c0, cs1, hr, hnd⟩
    · simp at hnone
    · cases hr
      exact List.takeWhile_cons_of_neg (by simp [hnd])

private theorem scanNat_dropWhile_self (rest : List Char) (hstop : notDigitHead rest) :
    rest.dropWhile Char.isDigit = rest := by
  cases rest with
  | nil => rfl
  | cons c cs0 =>
    rcases hstop with hnone | ⟨c0, cs1, hr, hnd⟩
    · simp at hnone
    · cases hr
      exact List.dropWhile_cons_of_neg (by simp [hnd])

/-- `,` vs `",".toList` — the expect's literal head. -/
private theorem comma_prepend (rest : List Char) : ',' :: rest = ",".toList ++ rest := by
  rw [show ",".toList = [','] by decide]
  rfl

/-- `>` vs `">".toList` — the expect's literal head. -/
private theorem gt_prepend (rest : List Char) : '>' :: rest = ">".toList ++ rest := by
  rw [show ">".toList = ['>'] by decide]
  rfl

/-- `(toString n).toList` is never empty. -/
private theorem toString_toList_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
  rw [hdig]
  exact Nat.toDigits_ne_nil

/-- The head char of a Nat's decimal text is a digit. -/
private theorem toString_head_isDigit (n : Nat) (c : Char) (cs : List Char)
    (hn : (toString n).toList = c :: cs) : c.isDigit = true := by
  have hm : c ∈ Nat.toDigits 10 n := by
    have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
    rw [← hdig, hn]
    simp
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hm

/-- **The decimal-scan inversion**: a `ToString` number reads back to itself,
    provided the following text stops at a non-digit. -/
private theorem scanNat_of_toString (n : Nat) (rest : List Char) (hstop : notDigitHead rest) :
    scanNat ((toString n).toList ++ rest) = some (n, rest) := by
  let f : Nat → Char → Nat := fun a d => a * 10 + (d.toNat - '0'.toNat)
  have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
  rw [hdig]
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  cases hd : Nat.toDigits 10 n with
  | nil => exact (hne hd).elim
  | cons c cs =>
    change scanNat (c :: (cs ++ rest)) = some (n, rest)
    have hc : c.isDigit = true := by
      have hmc : c ∈ Nat.toDigits 10 n := by rw [hd]; simp
      exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hmc
    have hcs : ∀ a ∈ cs, a.isDigit = true := by
      intro a ha
      exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
        (by rw [hd]; simp [ha])
    simp [scanNat, scanNat.scanNatGo, Parser.bind_apply, Parser.bind, Parser.takeWhile]
    rw [List.takeWhile_cons_of_pos hc]
    rw [List.takeWhile_append_of_pos hcs]
    rw [scanNat_takeWhile_nil rest hstop]
    rw [List.dropWhile_cons_of_pos hc]
    rw [List.dropWhile_append_of_pos hcs]
    rw [scanNat_dropWhile_self rest hstop]
    have hfold : List.foldl f (c.toNat - '0'.toNat) cs = n := by
      have hf0 : f 0 c = c.toNat - '0'.toNat := by simp [f]
      rw [← hf0]
      rw [← List.foldl_cons]
      rw [← hd]
      simpa [f, Nat.ofDigitChars_eq_foldl, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.ofDigitChars_ten_toDigits : Nat.ofDigitChars 10 (Nat.toDigits 10 n) 0 = n)
    by_cases hz : c :: (cs ++ rest) = []
    · exact False.elim (by simp at hz)
    · simp [hz]
      change List.foldl f (c.toNat - '0'.toNat) cs = n
      exact hfold

-- ── the per-constructor helpers (full type text: base + `?`) ──────────────

/-- **The scalar inversion, ctor-generic**: the emitter's text for a
    scalar type parses back to it. The nine scalar cases are ONE proof via
    the grammar table. The ctor match must come first: `ScalarCtor.toPType`
    is ctor-indexed, so the emitter equation lemmas only reduce at a concrete
    ctor. -/
theorem scalarT (c : Substrait.Grammar.ScalarCtor) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText (Substrait.Grammar.ScalarCtor.toPType c n) = .ok b) :
    parseType 1 (b.toList ++ rest) = some (Substrait.Grammar.ScalarCtor.toPType c n, rest) := by
  cases n with
  | required =>
      cases c <;> (
        rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
        simp [Emit.Text.nullSuffix, Substrait.Grammar.ScalarCtor.toPType,
          Proto.PType.nullability] at hemit
        rw [show b = Substrait.Grammar.ScalarCtor.prefix _ from hemit.symm]
        exact parseType_scalar _ rest hrest)
  | nullable =>
      -- ctor-generic: the base IS the table's prefix (`typeTextBase_scalar`),
      -- the nullability is `.nullable`, so `b = prefix c ++ "?"`
      have hn : Proto.PType.nullability (Substrait.Grammar.ScalarCtor.toPType c .nullable) =
          .nullable := by
        cases c <;> rfl
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase_scalar, hn] at hemit
      have hb : b = Substrait.Grammar.ScalarCtor.prefix c ++ "?" :=
        Except.ok.inj (hemit.symm : Except.ok b =
          Except.ok (Substrait.Grammar.ScalarCtor.prefix c ++ "?"))
      rw [hb, toList_append_question]
      exact parseType_scalar_nullable c rest
  | unspecified =>
      cases c <;> (
        rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
        simp [Emit.Text.nullSuffix, Substrait.Grammar.ScalarCtor.toPType,
          Proto.PType.nullability] at hemit)

/-- The decimal inversion: `decimal<P,S>` scans back (both nullabilities). -/
private theorem decimalT (p s : Nat) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText (.decimal p s n) = .ok b) :
    parseType (typeDepth (.decimal p s n)) (b.toList ++ rest) = some (.decimal p s n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    have hb : b = "decimal<" ++ toString p ++ "," ++ toString s ++ ">" := hemit.symm
    rw [hb]
    unfold parseType
    simp
    have hA : notDigitHead (',' :: (Nat.toDigits 10 s ++ '>' :: rest)) := by
      right
      exact ⟨',', Nat.toDigits 10 s ++ '>' :: rest, rfl, by decide⟩
    have hp : scanNat (Nat.toDigits 10 p ++ ',' :: (Nat.toDigits 10 s ++ '>' :: rest)) =
        some (p, ',' :: (Nat.toDigits 10 s ++ '>' :: rest)) := by
      simpa using (scanNat_of_toString p (',' :: (Nat.toDigits 10 s ++ '>' :: rest)) hA)
    rw [hp]
    simp
    rw [comma_prepend (Nat.toDigits 10 s ++ '>' :: rest)]
    rw [expect_self "," (Nat.toDigits 10 s ++ '>' :: rest)]
    simp
    have hB : notDigitHead ('>' :: rest) := by
      right
      exact ⟨'>', rest, rfl, by decide⟩
    have hs : scanNat (Nat.toDigits 10 s ++ '>' :: rest) = some (s, '>' :: rest) := by
      simpa using (scanNat_of_toString s ('>' :: rest) hB)
    rw [hs]
    simp
    rw [gt_prepend rest]
    rw [expect_self ">" rest]
    exact withNull_required (.decimal p s) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    have hb : b = "decimal<" ++ toString p ++ "," ++ toString s ++ ">" ++ "?" := hemit.symm
    rw [hb]
    unfold parseType
    simp
    have hA : notDigitHead (',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) := by
      right
      exact ⟨',', Nat.toDigits 10 s ++ '>' :: '?' :: rest, rfl, by decide⟩
    have hp : scanNat (Nat.toDigits 10 p ++ ',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) =
        some (p, ',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) := by
      simpa using (scanNat_of_toString p (',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) hA)
    rw [hp]
    simp
    rw [comma_prepend (Nat.toDigits 10 s ++ '>' :: '?' :: rest)]
    rw [expect_self "," (Nat.toDigits 10 s ++ '>' :: '?' :: rest)]
    simp
    have hB : notDigitHead ('>' :: '?' :: rest) := by
      right
      exact ⟨'>', '?' :: rest, rfl, by decide⟩
    have hs : scanNat (Nat.toDigits 10 s ++ '>' :: '?' :: rest) = some (s, '>' :: '?' :: rest) := by
      simpa using (scanNat_of_toString s ('>' :: '?' :: rest) hB)
    rw [hs]
    simp
    rw [gt_prepend ('?' :: rest)]
    rw [expect_self ">" ('?' :: rest)]
    simp
    exact withNull_nullable (.decimal p s) rest
  | unspecified =>
    simp [Emit.Text.typeText, Emit.Text.typeTextBase, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The list inversion: `list<T>` scans back. The element hypothesis
    `hie` is the master theorem restricted to `e` (depth-bounded). -/
private theorem listT (e : Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hie : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText e = .ok b' → parseType (typeDepth e) (b'.toList ++ rest') = some (e, rest'))
    (hemit : Emit.Text.typeText (.list e n) = .ok b) :
    parseType (typeDepth (.list e n)) (b.toList ++ rest) = some (.list e n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he] at hemit
      have hb : b = "list<" ++ es ++ ">" := hemit.symm
      rw [hb]
      unfold parseType
      -- the lexer folds the closed ctor table; `list<…` self-lexes
      have hcv : (("list<" ++ es ++ ">").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 5
          ((Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">").toList ++ rest)) =
          (es ++ ">").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      have hcomb : parseType (typeDepth e) ((es ++ ">").toList ++ rest) =
          some (e, '>' :: rest) := by
        have h0 := hie es ('>' :: rest) (by simp) he
        rw [String.toList_append]
        simp [List.append_assoc]
        exact h0
      rw [hcomb]
      dsimp
      rw [expect_gt_cons rest]
      dsimp
      exact withNull_required (.list e) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he] at hemit
      have hb : b = "list<" ++ es ++ ">" ++ "?" := hemit.symm
      rw [hb]
      unfold parseType
      -- the scalar table-fold skips `list<…` (conversion to the literal char
      -- form + the param-prefix complement lemma), then the only preceding
      -- parameterized check (`decimal<`) is skipped by prefix mismatch
      have hcv : (("list<" ++ es ++ ">" ++ "?").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">" ++ "?").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 5
          ((Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">" ++ "?").toList ++ rest)) =
          (es ++ ">" ++ "?").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      have hcomb : parseType (typeDepth e) ((es ++ ">" ++ "?").toList ++ rest) =
          some (e, '>' :: '?' :: rest) := by
        have h0 := hie es ('>' :: '?' :: rest) (by simp) he
        rw [String.toList_append, String.toList_append]
        simp [List.append_assoc]
        exact h0
      rw [hcomb]
      dsimp
      rw [expect_gt_cons ('?' :: rest)]
      dsimp
      exact withNull_nullable (.list e) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The map inversion: `map<K, V>` scans back (both nullabilities). -/
private theorem mapT (k v : Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hik : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText k = .ok b' → parseType (typeDepth k) (b'.toList ++ rest') = some (k, rest'))
    (hiv : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText v = .ok b' → parseType (typeDepth v) (b'.toList ++ rest') = some (v, rest'))
    (hemit : Emit.Text.typeText (.map k v n) = .ok b) :
    parseType (typeDepth (.map k v n)) (b.toList ++ rest) = some (.map k v n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2] at hemit
        have hb : b = "map<" ++ ks ++ ", " ++ vs ++ ">" := hemit.symm
        rw [hb]
        unfold parseType
        have hcv : (("map<" ++ ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            (Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">").toList ++ rest) := by
          simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
        rw [hcv, lexCtor_self]
        have hdrop : List.drop 4
            ((Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">").toList ++ rest)) =
            (ks ++ ", " ++ vs ++ ">").toList ++ rest := by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
        rw [hdrop]
        have hkey : parseType (typeDepth k) ((ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: rest))) := by
          have h0 := hik ks (',' :: ' ' :: (vs.toList ++ ('>' :: rest))) (by simp) he
          rw [String.toList_append, String.toList_append, String.toList_append]
          simp [List.append_assoc]
          exact h0
        have hkeyF : parseType (typeDepth k + typeDepth v) ((ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: rest))) := by
          exact parseType_mono_of_le (typeDepth k) (typeDepth v) _ _ hkey
        rw [hkeyF]
        dsimp
        rw [expect_comma_sp (vs.toList ++ '>' :: rest)]
        dsimp
        have hval : parseType (typeDepth v) (vs.toList ++ ('>' :: rest)) =
            some (v, '>' :: rest) := by
          exact hiv vs ('>' :: rest) (by simp) he2
        have hvalF : parseType (typeDepth k + typeDepth v) (vs.toList ++ ('>' :: rest)) =
            some (v, '>' :: rest) := by
          simpa [Nat.add_comm] using (parseType_mono_of_le (typeDepth v) (typeDepth k) _ _ hval)
        rw [hvalF]
        dsimp
        rw [expect_gt_cons rest]
        dsimp
        exact withNull_required (.map k v) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2] at hemit
        have hb : b = "map<" ++ ks ++ ", " ++ vs ++ ">" ++ "?" := hemit.symm
        rw [hb]
        unfold parseType
        have hcv : (("map<" ++ ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            (Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) := by
          simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
        rw [hcv, lexCtor_self]
        have hdrop : List.drop 4
            ((Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest)) =
            (ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest := by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
        rw [hdrop]
        have hkey : parseType (typeDepth k) ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) := by
          have h0 := hik ks (',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) (by simp) he
          rw [String.toList_append, String.toList_append, String.toList_append]
          simp [List.append_assoc]
          exact h0
        have hkeyF : parseType (typeDepth k + typeDepth v) ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) := by
          exact parseType_mono_of_le (typeDepth k) (typeDepth v) _ _ hkey
        rw [hkeyF]
        dsimp
        rw [expect_comma_sp (vs.toList ++ '>' :: '?' :: rest)]
        dsimp
        have hval : parseType (typeDepth v) (vs.toList ++ ('>' :: '?' :: rest)) =
            some (v, '>' :: '?' :: rest) := by
          exact hiv vs ('>' :: '?' :: rest) (by simp) he2
        have hvalF : parseType (typeDepth k + typeDepth v) (vs.toList ++ ('>' :: '?' :: rest)) =
            some (v, '>' :: '?' :: rest) := by
          simpa [Nat.add_comm] using (parseType_mono_of_le (typeDepth v) (typeDepth k) _ _ hval)
        rw [hvalF]
        dsimp
        rw [expect_gt_cons ('?' :: rest)]
        dsimp
        exact withNull_nullable (.map k v) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

-- ── the struct-field machinery (parseTypeList inversion) ────────────────

private theorem foldl_max_init_le (l : List Proto.PType) (init : Nat) :
    init ≤ l.foldl (fun m x => max m (typeDepth x)) init := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init (typeDepth a))
      (ih (max init (typeDepth a)))

private theorem foldl_max_mono_l (l : List Proto.PType) (i j : Nat) (hij : i ≤ j) :
    l.foldl (fun m x => max m (typeDepth x)) i ≤
      l.foldl (fun m x => max m (typeDepth x)) j := by
  induction l generalizing i j with
  | nil => simpa using hij
  | cons a rest ih =>
    simp [List.foldl_cons]
    exact ih (max i (typeDepth a)) (max j (typeDepth a))
      (Nat.max_le.mpr ⟨Nat.le_trans hij (Nat.le_max_left j (typeDepth a)),
        Nat.le_max_right j (typeDepth a)⟩)

private theorem typeDepth_le_foldl_max {l : List Proto.PType} {t : Proto.PType} (h : t ∈ l) :
    typeDepth t ≤ l.foldl (fun m x => max m (typeDepth x)) 0 := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
    simp [List.foldl_cons]
    by_cases hca : t = a
    · subst t
      exact foldl_max_init_le rest (typeDepth a)
    · exact Nat.le_trans (ih (by simp [hca] at h; exact h))
        (foldl_max_mono_l rest 0 (typeDepth a) (Nat.zero_le _))

private theorem mapM_length {α β ε : Type} (l : List α) (f : α → Except ε β) (ts : List β)
    (h : l.mapM f = Except.ok ts) : ts.length = l.length := by
  induction l generalizing ts with
  | nil =>
    have hpm : [].mapM f = Except.ok ([] : List β) := by simp [List.mapM_nil]
    have hts : ts = [] := (Except.ok.inj (h.symm.trans hpm))
    rw [hts]
    simp
  | cons a rest ih =>
    cases hf : f a with
    | error e => simp [hf] at h
    | ok b =>
      cases hr : rest.mapM f with
      | error e => simp [hf, hr] at h
      | ok bs =>
        simp [hf, hr] at h
        have hts : ts = b :: bs := h.symm
        rw [hts]
        simp [ih bs hr]

private theorem mapM_cons_ok {α β ε : Type} (a : α) (rest : List α)
    (f : α → Except ε β) (ts : List β)
    (h : (a :: rest).mapM f = Except.ok ts) :
    ∃ tb tsr, f a = Except.ok tb ∧ rest.mapM f = Except.ok tsr ∧ ts = tb :: tsr := by
  cases hf : f a with
  | error e => simp [hf] at h
  | ok tb =>
    cases hr : rest.mapM f with
    | error e => simp [hf, hr] at h
    | ok tsr =>
      simp [hf, hr] at h
      exact ⟨tb, tsr, rfl, rfl, h.symm⟩

private theorem app_ne_prefix (pre tail : String) (hp : pre.toList ≠ []) :
    pre ++ tail ≠ "" := by
  intro hz
  have h' : (pre ++ tail).toList = [] := by simp [hz]
  have htl : pre.toList ++ tail.toList = [] := by simpa [String.toList_append] using h'
  exact hp ((List.append_eq_nil_iff.mp htl).1)

private theorem typeTextBase_nonempty (t : Proto.PType) (b0 : String)
    (h : Emit.Text.typeTextBase t = .ok b0) : b0 ≠ "" := by
  cases t with
  | userDefined a ps n =>
    rw [Emit.Text.typeTextBase.eq_def] at h
    simp at h
  | bool n =>
    simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h
    intro hz
    exact (by decide : "boolean".toList ≠ []) (by simpa [h] using hz)
  | i8 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i16 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | string n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | binary n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | decimal p s n =>
    simp [Emit.Text.typeTextBase] at h
    rw [h.symm]
    exact app_ne_prefix "decimal<" (toString p ++ "," ++ toString s ++ ">") (by decide)
  | list e n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact app_ne_prefix "list<" (es ++ ">") (by decide)
  | map k v n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at h
    | ok es =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at h
      | ok es2 =>
        simp [he, he2] at h
        rw [h.symm]
        exact app_ne_prefix "map<" (es ++ ", " ++ es2 ++ ">") (by decide)
  | struct fs n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact app_ne_prefix "struct<" (Emit.Text.sep ", " es ++ ">") (by decide)

private theorem typeText_nonempty (t : Proto.PType) (s : String) (h : Emit.Text.typeText t = .ok s) : s ≠ "" := by
  rw [Emit.Text.typeText.eq_def] at h
  cases hb : Emit.Text.typeTextBase t with
  | error em => simp [hb] at h
  | ok b0 =>
    simp [hb] at h
    cases hn : Emit.Text.nullSuffix (Proto.PType.nullability t) with
    | error em => simp [hn] at h
    | ok ns =>
      simp [hn] at h
      intro hz
      have hne0 : b0 ≠ "" := typeTextBase_nonempty t b0 hb
      exact hne0 (by
        have hbs : b0 ++ ns = "" := h.trans hz
        have h' : (b0 ++ ns).toList = [] := by simp [hbs]
        have htl : b0.toList ++ ns.toList = [] := by simpa [String.toList_append] using h'
        have hpl : b0.toList = [] := (List.append_eq_nil_iff.mp htl).1
        exact String.toList_inj.mp (by simpa using hpl))

private theorem mapM_ok_mem (l : List Proto.PType) (ts : List String)
    (h : l.mapM Emit.Text.typeText = .ok ts) (s : String) (hs : s ∈ ts) : s ≠ "" := by
  induction l generalizing ts with
  | nil =>
    have hts : ts = [] := (Except.ok.inj
      (h.symm.trans (by simp [List.mapM_nil])))
    rw [hts] at hs
    simp at hs
  | cons x rest ih =>
    cases hx : Emit.Text.typeText x with
    | error e => simp [hx] at h
    | ok tx =>
      cases hr : rest.mapM Emit.Text.typeText with
      | error e => simp [hx, hr] at h
      | ok tsr =>
        simp [hx, hr] at h
        -- h : ts = tx :: tsr after the simp; hs : s ∈ ts. Rewrite hs.
        have hts : ts = tx :: tsr := h.symm
        rw [hts] at hs
        rcases List.mem_cons.mp hs with htx | ht
        · exact htx ▸ typeText_nonempty x tx hx
        · exact ih tsr hr ht

private theorem sep_cons {l : List String} (d s : String) (hl : l ≠ []) :
    Emit.Text.sep d (s :: l) = s ++ d ++ Emit.Text.sep d l :=
  String.intercalate_cons_of_ne_nil hl

private theorem sep_len_ge (l : List String) (hl : l ≠ [])
    (he : ∀ s ∈ l, s ≠ "") : l.length ≤ (Emit.Text.sep ", " l).toList.length := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons s rest ih =>
    cases rest with
    | nil =>
      have hs' : 1 ≤ s.toList.length := by
        have : 0 < s.toList.length := List.length_pos_iff.mpr (by
          intro hz
          exact he s (by simp) (String.toList_inj.mp hz))
        omega
      simp [Emit.Text.sep]
      exact hs'
    | cons s2 rest2 =>
      have hssep : Emit.Text.sep ", " (s :: s2 :: rest2) =
          s ++ ", " ++ Emit.Text.sep ", " (s2 :: rest2) := by
        simp [Emit.Text.sep]
      have ih' : (s2 :: rest2).length ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length :=
        ih (by simp) (by intro x hx; exact he x (by simp [hx]))
      calc
        (s :: s2 :: rest2).length = (s2 :: rest2).length + 1 := by simp
        _ ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length + 1 := by
          have h1 : (s2 :: rest2).length ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length := ih'
          omega
        _ ≤ s.toList.length + 2 + (Emit.Text.sep ", " (s2 :: rest2)).toList.length := by
          have h1 : 1 ≤ s.toList.length := by
            have : 0 < s.toList.length := List.length_pos_iff.mpr (by
              intro hz
              exact he s (by simp) (String.toList_inj.mp hz))
            omega
          omega
        _ = (Emit.Text.sep ", " (s :: s2 :: rest2)).toList.length := by
          rw [hssep]
          rw [String.toList_append, String.toList_append]
          simp [List.length_append, List.length_cons]
          omega

private theorem expect_fail (p : String) (rest : List Char) (hp : p ≠ "")
    (hh : rest.head? ≠ p.toList.head?) : expect p rest = none := by
  unfold expect
  have hs : startsWith rest p = false := by
    unfold startsWith
    cases hp' : p.toList with
    | nil => exact (hp (String.toList_inj.mp hp')).elim
    | cons c cs =>
      cases hr : rest with
      | nil => simp [List.isPrefixOf]
      | cons c0 rest0 =>
        have hh0 : some c0 ≠ some c := by
          intro hc
          exact hh (by simp [hp', hr, hc])
        have hc0 : c0 ≠ c := by
          intro hcc
          exact hh0 (by rw [hcc])
        simp [List.isPrefixOf, hc0.symm]
  simp [hs]

private theorem expect_comma_fail (rest : List Char) (hh : rest.head? ≠ some ',') :
    expect ", " rest = none := by
  have hh' : rest.head? ≠ ", ".toList.head? := by simpa using hh
  exact expect_fail ", " rest (by decide) hh'

/-- The separator text starts with its first element (char-wise). -/
private theorem sep_toList_head (s : String) (l : List String) (hs : s.toList ≠ []) :
    (Emit.Text.sep ", " (s :: l)).toList.head? = s.toList.head? := by
  cases l with
  | nil => simp [Emit.Text.sep]
  | cons x xs =>
    have hsep : Emit.Text.sep ", " (s :: x :: xs) =
        s ++ ", " ++ Emit.Text.sep ", " (x :: xs) := by
      simp [Emit.Text.sep]
    rw [hsep]
    rw [String.toList_append]
    rw [String.toList_append]
    cases hs' : s.toList with
    | nil => exact (hs hs').elim
    | cons c cs => rfl

/-- The head of a nonempty append is the head of the prefix. -/
private theorem head_append_ne (l l' : List Char) (hl : l ≠ []) :
    (l ++ l').head? = l.head? := by
  cases hl' : l with
  | nil => exact (hl hl').elim
  | cons c cs => rfl

/-- The separator text is nonempty and does not start with `>`. -/
private theorem sep_toList_ne_gt (s : String) (l : List String)
    (hs : s.toList ≠ [] ∧ s.toList.head? ≠ some '>') :
    (Emit.Text.sep ", " (s :: l)).toList ≠ [] ∧ (Emit.Text.sep ", " (s :: l)).toList.head? ≠ some '>' := by
  constructor
  · intro hz
    have h0 := sep_toList_head s l hs.1
    cases hmt : s.toList with
    | nil => exact (hs.1 hmt).elim
    | cons c cs =>
      have hh : (Emit.Text.sep ", " (s :: l)).toList.head? = some c :=
        h0.trans (by rw [hmt]; rfl)
      rw [hz] at hh
      simp at hh
  · have h0 := sep_toList_head s l hs.1
    intro hz
    exact hs.2 (h0.symm.trans hz)

private theorem expect_gt_fail_char (c : Char) (rest : List Char) (hc : c ≠ '>') :
    expect ">" (c :: rest) = none := by
  unfold expect
  cases hc0 : c == '>' with
  | true =>
    have hce : c = '>' := beq_iff_eq.mp hc0
    exact (hc hce).elim
  | false =>
    have hpre : startsWith (c :: rest) ">" = false := by
      unfold startsWith
      have hl : (">" : String).toList = ['>'] := by decide
      rw [hl]
      simp [List.isPrefixOf]
      exact fun hz : '>' = c => hc hz.symm
    rw [if_neg (by intro hz; rw [hpre] at hz; simp at hz)]

private theorem expect_gt_fail_head (cs : List Char) (hh : cs ≠ [] ∧ cs.head? ≠ some '>') :
    expect ">" cs = none := by
  cases cs with
  | nil => exact (hh.1 rfl).elim
  | cons c cs0 =>
    have hc : c ≠ '>' := by
      intro hcc
      exact hh.2 (by simp [hcc])
    exact expect_gt_fail_char c cs0 hc

private theorem parseTypeList_invert (l : List Proto.PType) (fuel0 : Nat) (after : List Char)
    (hafter : after.head? ≠ some '?' ∧ after.head? ≠ some ',')
    (hall : ∀ f ∈ l, typeDepth f ≤ fuel0)
    (hfield : ∀ (f : Proto.PType), f ∈ l →
        ∀ (tf : String), Emit.Text.typeText f = .ok tf →
        ∀ (rf : List Char), rf.head? ≠ some '?' →
        parseType (typeDepth f) (tf.toList ++ rf) = some (f, rf)) :
    ∀ (ts : List String), l.mapM Emit.Text.typeText = .ok ts → l ≠ [] →
    ∀ lf, lf ≥ l.length →
    parseTypeList (lf + 1) fuel0 ((Emit.Text.sep ", " ts).toList ++ after) = some (l, after)
  := by
  induction l generalizing fuel0 after with
  | nil => intro ts hmap hne; exact (hne rfl).elim
  | cons f fs' ih =>
    intro ts hmap hne lf hlf
    rcases (mapM_cons_ok f fs' Emit.Text.typeText ts hmap) with ⟨tf, ts'', hf, hr, hts⟩
    subst ts
    cases fs' with
    | nil =>
      have ht0 : ts'' = [] := by
        have hpm : [].mapM Emit.Text.typeText = Except.ok ([] : List String) := by
          simp [List.mapM_nil]
        exact (Except.ok.inj (hr.symm.trans hpm))
      subst ts''
      have hsep1 : Emit.Text.sep ", " [tf] = tf := by simp [Emit.Text.sep]
      rw [hsep1]
      rw [parseTypeList.eq_2]
      have hfld := hfield f (by simp) tf hf after hafter.1
      have hb := hall f (by simp)
      have hm : parseType (fuel0 - typeDepth f + typeDepth f) (tf.toList ++ after) = some (f, after) := by
        have hm0 : parseType (typeDepth f + (fuel0 - typeDepth f)) (tf.toList ++ after) = some (f, after) := by
          exact parseType_mono_of_le (typeDepth f) (fuel0 - typeDepth f) _ _ hfld
        simpa [Nat.add_comm] using hm0
      rw [← Nat.sub_add_cancel hb]
      rw [hm]
      simp
      rw [expect_comma_fail after hafter.2]
    | cons f2 fs2 =>
      rcases (mapM_cons_ok f2 fs2 Emit.Text.typeText ts'' hr) with ⟨tf2, ts2, hf2, hr2, hts2⟩
      subst ts''
      let cont : List Char := ", ".toList ++ (Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after
      have hinput : ((Emit.Text.sep ", " (tf :: tf2 :: ts2)).toList ++ after) = tf.toList ++ cont := by
        have hc := sep_cons (l := (tf2 :: ts2)) ", " tf (by simp)
        have hsept : Emit.Text.sep ", " (tf :: tf2 :: ts2) = tf ++ ", " ++ Emit.Text.sep ", " (tf2 :: ts2) := by
          simp [Emit.Text.sep]
        rw [hsept, toList_append3]
        simp [cont, List.append_assoc]
      rw [hinput]
      rw [parseTypeList.eq_2]
      have hcontQ : cont.head? ≠ some '?' := by
        simp [cont]
      have hfld := hfield f (by simp) tf hf cont hcontQ
      have hb := hall f (by simp)
      have hm : parseType (fuel0 - typeDepth f + typeDepth f) (tf.toList ++ cont) = some (f, cont) := by
        have hm0 : parseType (typeDepth f + (fuel0 - typeDepth f)) (tf.toList ++ cont) = some (f, cont) := by
          exact parseType_mono_of_le (typeDepth f) (fuel0 - typeDepth f) _ _ hfld
        simpa [Nat.add_comm] using hm0
      rw [← Nat.sub_add_cancel hb]
      rw [hm]
      simp
      rw [show expect ", " cont = some ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) by
        have hlist : ", ".toList ++ ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) = cont := by
          simp [cont, List.append_assoc]
        rw [← hlist]
        exact expect_self ", " ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after)]
      have hlen' : (f :: f2 :: fs2).length = (f2 :: fs2).length + 1 := by simp
      have hlf1 : 1 ≤ lf := by
        have hlen2 : 2 ≤ (f :: f2 :: fs2).length := by simp
        have : (f :: f2 :: fs2).length ≤ lf := hlf
        omega
      have hfield' : ∀ (x : Proto.PType), x ∈ f2 :: fs2 →
          ∀ (tx : String), Emit.Text.typeText x = .ok tx →
          ∀ (rx : List Char), rx.head? ≠ some '?' →
          parseType (typeDepth x) (tx.toList ++ rx) = some (x, rx) := by
        intro x hx tx htx rx hrx
        exact hfield x (by simp [hx]) tx htx rx hrx
      have hall' : ∀ x ∈ f2 :: fs2, typeDepth x ≤ fuel0 := by
        intro x hx
        exact hall x (by simp [hx])
      have hlf' : lf - 1 ≥ (f2 :: fs2).length := by
        have : (f2 :: fs2).length + 1 ≤ lf := by simpa [hlen'] using hlf
        omega
      have hfuel : fuel0 - typeDepth f + typeDepth f = fuel0 := Nat.sub_add_cancel hb
      rw [hfuel]
      have hrec : parseTypeList lf fuel0 ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) =
          some (f2 :: fs2, after) := by
        simpa [Nat.sub_add_cancel hlf1] using
          (ih fuel0 after hafter hall' hfield' (tf2 :: ts2) hr (by simp) (lf - 1) hlf')
      show (match parseTypeList lf fuel0 ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) with
        | some (ts, r3) => some (f :: ts, r3) | none => none) = some (f :: f2 :: fs2, after)
      rw [hrec]

private theorem cons_head_append (c : Char) (cs tail : List Char) :
    (c :: cs ++ tail).head? = some c := rfl

private theorem prefix_head (pre : String) (c : Char) (pre_rest : List Char) (tail : String)
    (hc : c ≠ '>') (hp : pre.toList = c :: pre_rest) :
    (pre ++ tail).toList ≠ [] ∧ (pre ++ tail).toList.head? ≠ some '>' := by
  rw [String.toList_append, hp]
  constructor
  · simp
  · rw [cons_head_append]
    intro hz
    exact hc (Option.some.inj hz)

private theorem typeText_base_head (t : Proto.PType) (b0 : String)
    (h : Emit.Text.typeTextBase t = .ok b0) : b0.toList ≠ [] ∧ b0.toList.head? ≠ some '>' := by
  cases t with
  | userDefined a ps n =>
    rw [Emit.Text.typeTextBase.eq_def] at h
    simp at h
  | bool n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i8 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i16 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | string n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | binary n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | decimal p s n =>
    simp [Emit.Text.typeTextBase] at h
    rw [h.symm]
    exact prefix_head "decimal<" 'd' "ecimal<".toList (toString p ++ "," ++ toString s ++ ">") (by decide)
      (by decide : "decimal<".toList = 'd' :: "ecimal<".toList)
  | list e n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact prefix_head "list<" 'l' "ist<".toList (es ++ ">") (by decide)
        (by decide : "list<".toList = 'l' :: "ist<".toList)
  | map k v n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at h
    | ok es =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at h
      | ok es2 =>
        simp [he, he2] at h
        rw [h.symm]
        exact prefix_head "map<" 'm' "ap<".toList (es ++ ", " ++ es2 ++ ">") (by decide)
          (by decide : "map<".toList = 'm' :: "ap<".toList)
  | struct fs n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact prefix_head "struct<" 's' "truct<".toList (Emit.Text.sep ", " es ++ ">") (by decide)
        (by decide : "struct<".toList = 's' :: "truct<".toList)

private theorem typeText_head (t : Proto.PType) (s : String) (h : Emit.Text.typeText t = .ok s) :
    s.toList ≠ [] ∧ s.toList.head? ≠ some '>' := by
  rw [Emit.Text.typeText.eq_def] at h
  cases hb : Emit.Text.typeTextBase t with
  | error em => simp [hb] at h
  | ok b0 =>
    simp [hb] at h
    cases hn : Emit.Text.nullSuffix (Proto.PType.nullability t) with
    | error em => simp [hn] at h
    | ok ns =>
      simp [hn] at h
      have hsp : s = b0 ++ ns := h.symm
      rw [hsp]
      rw [String.toList_append]
      have hk := typeText_base_head t b0 hb
      constructor
      · exact fun hz => hk.1 ((List.append_eq_nil_iff.mp hz).1)
      · intro hz
        cases hb' : b0.toList with
        | nil => exact (hk.1 hb').elim
        | cons c cs =>
          have hhh : (b0.toList ++ ns.toList).head? = some c := by
            rw [hb', cons_head_append]
          have hc : some c = some '>' := hhh.symm.trans hz
          have hcd : c = '>' := Option.some.inj hc
          have hb0h : b0.toList.head? = some c := by rw [hb']; rfl
          have hb0gt : b0.toList.head? = some '>' := by rw [hb0h, hcd]
          exact hk.2 hb0gt

/-- The struct inversion: `struct<T,…>` (and the empty `struct<>`) scans back. -/
private theorem structT (fs : List Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hif : ∀ (f : Proto.PType), f ∈ fs → ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText f = .ok b' → parseType (typeDepth f) (b'.toList ++ rest') = some (f, rest'))
    (hemit : Emit.Text.typeText (.struct fs n) = .ok b) :
    parseType (typeDepth (.struct fs n)) (b.toList ++ rest) = some (.struct fs n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he] at hemit
      have hb : b = "struct<" ++ Emit.Text.sep ", " ts ++ ">" := hemit.symm
      rw [hb]
      unfold parseType
      have hcv : (("struct<" ++ Emit.Text.sep ", " ts ++ ">").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 7
          ((Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">").toList ++ rest)) =
          (Emit.Text.sep ", " ts ++ ">").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      -- the parseTypeList lfuel counts the input length; restore the
      -- string-append form the downstream lemmas are stated against
      rw [show ((Substrait.Grammar.TCtor.prefix .struct).toList ++
              ((Emit.Text.sep ", " ts ++ ">").toList ++ rest)).length =
            (("struct<" ++ Emit.Text.sep ", " ts ++ ">").toList ++ rest).length from by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]]
      cases ts with
      | nil =>
        have hfs : fs = [] := by
          have hl := mapM_length fs Emit.Text.typeText [] he
          cases fs with
          | nil => rfl
          | cons x xs => simp at hl
        subst fs
        simp [Emit.Text.sep]
        rw [gt_prepend rest]
        rw [expect_self ">" rest]
        simp
        exact withNull_required (.struct []) rest hrest
      | cons t ts' =>
        cases fs with
        | nil => simp at he
        | cons f fs0 =>
          rcases (mapM_cons_ok f fs0 Emit.Text.typeText (t :: ts') he) with ⟨tb, tsr, hft, hfr, hts⟩
          have ht : t = tb := (List.cons.inj hts).1
          have htsr : ts' = tsr := (List.cons.inj hts).2
          rw [ht, htsr] at he
          rw [ht, htsr]
          have hth := typeText_head f tb hft
          have hsn := sep_toList_ne_gt tb tsr hth
          have hargne : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) ≠ [] := by
            intro hz
            -- hz : (sep ++ ">").toList ++ rest = [] → both components are []
            have h2 := (List.append_eq_nil_iff.mp hz).1
            -- h2 : (sep ++ ">").toList = [] → sep's toList = []
            rw [String.toList_append] at h2
            have h3 := (List.append_eq_nil_iff.mp h2).1
            exact hsn.1 h3
          have harghead : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).head? ≠ some '>' := by
            -- the combined text starts with sep's head (sep is nonempty), which ≠ '>'
            have hne : (Emit.Text.sep ", " (tb :: tsr)).toList ≠ [] := hsn.1
            have hhd : (Emit.Text.sep ", " (tb :: tsr)).toList.head? ≠ some '>' := hsn.2
            have hx : (Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest =
                (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest) := by
              rw [String.toList_append, List.append_assoc]
            rw [hx]
            cases hsep : (Emit.Text.sep ", " (tb :: tsr)).toList with
            | nil => exact absurd hsep hne
            | cons c cs => simp_all
          have htgt : expect ">" ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) = none := by
            exact expect_gt_fail_head ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) ⟨hargne, harghead⟩
          rw [htgt]
          dsimp
          -- parseTypeList inversion: sep text + ">" + rest
          have hinput : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) =
              (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest) := by
            rw [String.toList_append]
            rw [List.append_assoc]
          rw [hinput]
          have hinpLen : (f :: fs0).length ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length := by
            have hm : (f :: fs0).length = (tb :: tsr).length := by
              simpa using (mapM_length (f :: fs0) Emit.Text.typeText (tb :: tsr) he).symm
            have hsepl := sep_len_ge (tb :: tsr) (by simp) (fun s hs => mapM_ok_mem (f :: fs0) (tb :: tsr) he s hs)
            calc
              (f :: fs0).length = (tb :: tsr).length := hm
              _ ≤ (Emit.Text.sep ", " (tb :: tsr)).toList.length := hsepl
              _ ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length := by
                rw [String.toList_append, String.toList_append]
                simp only [List.length_append]
                have hc8 : (("struct<".toList).length) ≥ 7 := by decide
                omega
          have hall : ∀ x ∈ f :: fs0, typeDepth x ≤ (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 := by
            intro x hx
            exact typeDepth_le_foldl_max hx
          have hafterRest : (">".toList ++ rest).head? ≠ some '?' ∧ (">".toList ++ rest).head? ≠ some ',' := by
            simp
          -- the parser's tfuel for the struct branch is the OUTER fuel =
          -- foldl over (f :: fs0) from 0 = foldl over fs0 from (max 0 (typeDepth f))
          have hfold : (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 =
              fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)) := rfl
          have hplt : parseTypeList ((( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length + 1)
                (fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)))
                ((Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest)) =
              some (f :: fs0, ">".toList ++ rest) := by
            have h := parseTypeList_invert (f :: fs0)
              ((f :: fs0).foldl (fun m x => max m (typeDepth x)) 0)
              (">".toList ++ rest)
              hafterRest hall
              (fun x hx tx htx rx hrx => hif x hx tx rx hrx htx)
              (tb :: tsr) he (by simp)
              (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length
              hinpLen
            rw [hfold] at h
            exact h
          rw [hplt]
          dsimp
          rw [gt_prepend rest]
          rw [expect_self ">" rest]
          dsimp
          exact withNull_required (.struct (f :: fs0)) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he] at hemit
      have hb : b = "struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?" := hemit.symm
      rw [hb]
      unfold parseType
      have hcv : (("struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 7
          ((Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest)) =
          (Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      rw [show ((Substrait.Grammar.TCtor.prefix .struct).toList ++
              ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest)).length =
            (("struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest).length from by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]]
      cases ts with
      | nil =>
        have hfs : fs = [] := by
          have hl := mapM_length fs Emit.Text.typeText [] he
          cases fs with
          | nil => rfl
          | cons x xs => simp at hl
        subst fs
        simp [Emit.Text.sep]
        rw [gt_prepend ('?' :: rest)]
        rw [expect_self ">" ('?' :: rest)]
        simp
        exact withNull_nullable (.struct []) rest
      | cons t ts' =>
        cases fs with
        | nil => simp at he
        | cons f fs0 =>
          rcases (mapM_cons_ok f fs0 Emit.Text.typeText (t :: ts') he) with ⟨tb, tsr, hft, hfr, hts⟩
          have ht : t = tb := (List.cons.inj hts).1
          have htsr : ts' = tsr := (List.cons.inj hts).2
          rw [ht, htsr] at he
          rw [ht, htsr]
          have hth := typeText_head f tb hft
          have hsn := sep_toList_ne_gt tb tsr hth
          have hargne : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) ≠ [] := by
            intro hz
            have h2 := (List.append_eq_nil_iff.mp hz).1
            rw [String.toList_append] at h2
            have h3 := (List.append_eq_nil_iff.mp h2).1
            rw [String.toList_append] at h3
            have h4 := (List.append_eq_nil_iff.mp h3).1
            exact hsn.1 h4
          have harghead : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).head? ≠ some '>' := by
            have hne : (Emit.Text.sep ", " (tb :: tsr)).toList ≠ [] := hsn.1
            have hhd : (Emit.Text.sep ", " (tb :: tsr)).toList.head? ≠ some '>' := hsn.2
            have hx : (Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest =
                (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest) := by
              rw [String.toList_append, String.toList_append]
              simp [List.append_assoc]
            rw [hx]
            cases hsep : (Emit.Text.sep ", " (tb :: tsr)).toList with
            | nil => exact absurd hsep hne
            | cons c cs => simp_all
          have htgt : expect ">" ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) = none := by
            exact expect_gt_fail_head ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) ⟨hargne, harghead⟩
          rw [htgt]
          dsimp
          have hinput : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) =
              (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest) := by
            rw [String.toList_append, String.toList_append]
            simp [List.append_assoc]
          rw [hinput]
          have hinpLen : (f :: fs0).length ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length := by
            have hm : (f :: fs0).length = (tb :: tsr).length := by
              simpa using (mapM_length (f :: fs0) Emit.Text.typeText (tb :: tsr) he).symm
            have hsepl := sep_len_ge (tb :: tsr) (by simp) (fun s hs => mapM_ok_mem (f :: fs0) (tb :: tsr) he s hs)
            calc
              (f :: fs0).length = (tb :: tsr).length := hm
              _ ≤ (Emit.Text.sep ", " (tb :: tsr)).toList.length := hsepl
              _ ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length := by
                have h1 : (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length =
                    "struct<".toList.length + (Emit.Text.sep ", " (tb :: tsr)).toList.length +
                    ">".toList.length + "?".toList.length + rest.length := by
                  rw [String.toList_append, String.toList_append, String.toList_append]
                  simp [List.length_append]
                  omega
                have hc8 : "struct<".toList.length ≥ 7 := by decide
                omega
          have hall : ∀ x ∈ f :: fs0, typeDepth x ≤ (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 := by
            intro x hx
            exact typeDepth_le_foldl_max hx
          have hafterRest : (">".toList ++ "?".toList ++ rest).head? ≠ some '?' ∧
              (">".toList ++ "?".toList ++ rest).head? ≠ some ',' := by
            simp
          have hfold : (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 =
              fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)) := rfl
          have hplt : parseTypeList ((( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length + 1)
                (fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)))
                ((Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest)) =
              some (f :: fs0, ">".toList ++ "?".toList ++ rest) := by
            have h := parseTypeList_invert (f :: fs0)
              ((f :: fs0).foldl (fun m x => max m (typeDepth x)) 0)
              (">".toList ++ "?".toList ++ rest)
              hafterRest hall
              (fun x hx tx htx rx hrx => hif x hx tx rx hrx htx)
              (tb :: tsr) he (by simp)
              (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length
              hinpLen
            rw [hfold] at h
            exact h
          rw [hplt]
          dsimp
          rw [gt_prepend ('?' :: rest)]
          rw [expect_self ">" ('?' :: rest)]
          exact withNull_nullable (.struct (f :: fs0)) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The mutual `Proto.PType` recursor driven on a `PType → Prop` motive:
    the `PParam` minors are trivial (`True`), the `List PType` minor is the
    membership induction.  The shared skeleton of `parseType_typeText` and
    `typeDepth_le_len` (`induction` refuses `Proto.PType` — it lives in a
    mutual block with `PParam` — so the recursor is driven directly). -/
private theorem ptypeRec (motive : Proto.PType → Prop)
    (hbool : ∀ n, motive (.bool n)) (hi8 : ∀ n, motive (.i8 n))
    (hi16 : ∀ n, motive (.i16 n)) (hi32 : ∀ n, motive (.i32 n))
    (hi64 : ∀ n, motive (.i64 n)) (hfp32 : ∀ n, motive (.fp32 n))
    (hfp64 : ∀ n, motive (.fp64 n)) (hstring : ∀ n, motive (.string n))
    (hbinary : ∀ n, motive (.binary n))
    (hdecimal : ∀ p s n, motive (.decimal p s n))
    (hlist : ∀ e n, motive e → motive (.list e n))
    (hmap : ∀ k v n, motive k → motive v → motive (.map k v n))
    (hstruct : ∀ fs n, (∀ f, f ∈ fs → motive f) → motive (.struct fs n))
    (huser : ∀ a ps n, True → motive (.userDefined a ps n))
    (t : Proto.PType) : motive t := by
  have hnil : ∀ f, f ∈ ([] : List Proto.PType) → motive f := by
    intro f hf
    simp at hf
  have hcons : ∀ (hd : Proto.PType) (tl : List Proto.PType),
      motive hd → (∀ f, f ∈ tl → motive f) → ∀ f, f ∈ hd :: tl → motive f := by
    intro hd tl ihd iht f hf
    rw [List.mem_cons] at hf
    rcases hf with hfe | hft
    · subst hfe; exact ihd
    · exact iht f hft
  refine @Proto.PType.rec motive (fun _ => True)
    (fun (l : List Proto.PType) => ∀ f, f ∈ l → motive f) (fun _ => True)
    hbool hi8 hi16 hi32 hi64 hfp32 hfp64 hstring hbinary hdecimal
    hlist hmap hstruct huser
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial)
    hnil hcons trivial (fun _ _ _ _ => trivial) t

/-- ***Master type-inversion theorem***: `parseType` at fuel `typeDepth t`
    inverts `Emit.Text.typeText` on the whole emit-able fragment (all
    constructors except `userDefined`, which the emitter hard-errors on and
    the `hemit` hypothesis rules out).  The induction is a thin unwrapping:
    every per-constructor helper (`boolT`…`binaryT`, `decimalT`, `listT`,
    `mapT`, `structT`) is stated *exactly* at this theorem's shape, so each
    recursive case preinstantiates the induction hypothesis on its subterms.
    The nullable suffix is inside the helpers (withNull_required /
    withNull_nullable), so no case re-derives the `?` scan.
    `Proto.PType` lives in a mutual block with `PParam`, so the `induction`
    tactic refuses it; the mutual recursor is driven directly, with the
    `PParam` motives `True` (the emitter hard-errors before `PParam` values
    can matter here) and the `List PType` motive the struct membership
    induction. -/
theorem parseType_typeText (t : Proto.PType) (b : String) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText t = .ok b) :
    parseType (typeDepth t) (b.toList ++ rest) = some (t, rest) := by
  let motive : Proto.PType → Prop :=
    fun t => ∀ (b : String) (rest : List Char), rest.head? ≠ some '?' →
      Emit.Text.typeText t = .ok b → parseType (typeDepth t) (b.toList ++ rest) = some (t, rest)
  have hscalar : ∀ (c : Substrait.Grammar.ScalarCtor) n,
      motive (Substrait.Grammar.ScalarCtor.toPType c n) := by
    intro c n b rest hrest hemit
    rw [show typeDepth (Substrait.Grammar.ScalarCtor.toPType c n) = 1 from by
      cases c <;> simp [typeDepth, Substrait.Grammar.ScalarCtor.toPType]]
    exact scalarT c n rest hrest hemit
  have hbool   : ∀ n, motive (.bool n)   := hscalar .bool
  have hi8     : ∀ n, motive (.i8 n)     := hscalar .i8
  have hi16    : ∀ n, motive (.i16 n)    := hscalar .i16
  have hi32    : ∀ n, motive (.i32 n)    := hscalar .i32
  have hi64    : ∀ n, motive (.i64 n)    := hscalar .i64
  have hfp32   : ∀ n, motive (.fp32 n)   := hscalar .fp32
  have hfp64   : ∀ n, motive (.fp64 n)   := hscalar .fp64
  have hstring : ∀ n, motive (.string n) := hscalar .string
  have hbinary : ∀ n, motive (.binary n) := hscalar .binary
  have hdecimal : ∀ p s n, motive (.decimal p s n) :=
    fun p s n b rest hrest hemit => decimalT p s n rest hrest hemit
  have hlist : ∀ e n, motive e → motive (.list e n) := by
    intro e n ih b rest hrest hemit
    exact listT e n rest hrest (fun b' rest' hr' he' => ih b' rest' hr' he') hemit
  have hmap : ∀ k v n, motive k → motive v → motive (.map k v n) := by
    intro k v n ihk ihv b rest hrest hemit
    exact mapT k v n rest hrest
      (fun b' rest' hr' he' => ihk b' rest' hr' he')
      (fun b' rest' hr' he' => ihv b' rest' hr' he') hemit
  have hstruct : ∀ fs n, (∀ f, f ∈ fs → motive f) → motive (.struct fs n) := by
    intro fs n ih b rest hrest hemit
    exact structT fs n rest hrest
      (fun f hf b' rest' hr' he' => ih f hf b' rest' hr' he') hemit
  have huser : ∀ a ps n, True → motive (.userDefined a ps n) := by
    intro a ps n _ b rest hrest hemit
    simp [Emit.Text.typeText, Emit.Text.typeTextBase] at hemit
  exact ptypeRec motive hbool hi8 hi16 hi32 hi64 hfp32 hfp64 hstring hbinary
    hdecimal hlist hmap hstruct huser t b rest hrest hemit

/-- The nullability marker. Delegates to `Proto.PType.nullability` (one
    accessor, not two — the parallel fold was dead duplication). -/
abbrev nullabilityOf (t : Proto.PType) : Proto.Nullability := t.nullability

-- ── literals + expressions ──────────────────────────────────────────────────

/-- The name→anchor context (from the parsed extensions section). -/
abbrev FnCtx := List (String × Nat)

/-- The `:type?` literal suffix: `some t` when present. -/
def scanLitSuffix : List Char → Option (Option Proto.PType × List Char)
  | ':' :: rest => (parseType (rest.length + 1) rest).map (fun (t, r) => (some t, r))
  | cs => some (none, cs)

/-- Nullability from the suffix (absent = non-null). -/
def suffixNullable : Option Proto.PType → Bool
  | some t => nullabilityOf t == .nullable
  | none => false

/-- Int literal with the suffix's integer kind (default i64; a non-integer
    suffix is a parse error). -/
def intLitOf (v : Int) : Option Proto.PType → Option Proto.LiteralType
  | none => some (.i64 v)
  | some t => match t with
    | .i8 _ => some (.i8 v) | .i16 _ => some (.i16 v)
    | .i32 _ => some (.i32 v) | .i64 _ => some (.i64 v)
    | _ => none

/-- Attach a scanned literal SUFFIX (`?`/`!`) to a literal, deriving the
    nullability — the repeated tail of `parseLiteral`'s arms. `abbrev`
    (reducible): the proof-rewrites in this module must see through it
    to the underlying `scanLitSuffix` shape. -/
abbrev litWithSuffix (lt : Proto.LiteralType) (rest : List Char) :
    Option (Proto.Literal × List Char) :=
  (scanLitSuffix rest).map fun (sfx, r) =>
    ({ literalType := lt, nullable := suffixNullable sfx }, r)

/-- The int arm's tail: the suffix scan after a scanned integer — the
    only parseLiteral arm that does not COMPUTE the literal type up
    front (`intLitOf` decides the integer kind from the suffix). -/
def intLitTail (v : Int) (r1 : List Char) : Option (Proto.Literal × List Char) :=
  match scanLitSuffix r1 with
  | some (sfx, r) => (intLitOf v sfx).map (fun lt =>
      ({ literalType := lt, nullable := suffixNullable sfx }, r))
  | none => none

/-- Parse a literal (the emitter's `literal` forms). -/
def parseLiteral : List Char → Option (Proto.Literal × List Char)
  | 'n' :: 'u' :: 'l' :: 'l' :: ':' :: rest =>
    (parseType (rest.length + 1) rest).map (fun (t, r) =>
      ({ literalType := .null t, nullable := true }, r))
  | 't' :: 'r' :: 'u' :: 'e' :: rest => litWithSuffix (.bool true) rest
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => litWithSuffix (.bool false) rest
  | '\'' :: rest =>
    (scanQuotedRaw '\'' [] rest).bind fun (raw, r1) =>
      (unescape (String.ofList raw)).bind fun s => litWithSuffix (.string s) r1
  | cs =>
    if startsWith cs "{{binary}}" then litWithSuffix (.binary []) (cs.drop 10)
    else match scanInt cs with
      | some (v, r1) => intLitTail v r1
      | none => none

mutual

/-- `", "`-separated expression list inside a call; structural on `lfuel`. -/
def parseExprList : Nat → Nat → FnCtx → List Char → Option (List Proto.Expression × List Char)
  | 0, _, _, _ => none
  | lfuel + 1, efuel, ctx, cs =>
    match parseExpr efuel ctx cs with
    | none => none
    | some (e, r1) =>
      match expect ", " r1 with
      | some r2 => match parseExprList lfuel efuel ctx r2 with
        | some (es, r3) => some (e :: es, r3)
        | none => none
      | none => some ([e], r1)

/-- The if_then argument list: `_ -> else` or `cond -> value, ` + more. -/
def parseIfPairs : Nat → Nat → FnCtx → List Char →
    Option (List (Proto.Expression × Proto.Expression) × Proto.Expression × List Char)
  | 0, _, _, _ => none
  | lfuel + 1, efuel, ctx, cs =>
    if startsWith cs "_ -> " then
      match parseExpr efuel ctx (cs.drop 5) with
      | some (e, r1) => match expect ")" r1 with
        | some r2 => some ([], e, r2)
        | none => none
      | none => none
    else match parseExpr efuel ctx cs with
      | some (c, r1) =>
        match expect " -> " r1 with
        | some r2 => match parseExpr efuel ctx r2 with
          | some (v, r3) =>
            match expect ", " r3 with
            | some r4 => match parseIfPairs lfuel efuel ctx r4 with
              | some (rest', els, r5) => some ((c, v) :: rest', els, r5)
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none

/-- Parse an expression (the emitter's `expr` forms). `fuel` bounds call
    nesting depth. -/
def parseExpr : Nat → FnCtx → List Char → Option (Proto.Expression × List Char)
  | 0, _, _ => none
  | fuel + 1, ctx, cs =>
    -- cast: `(expr)::?type` / `(expr)::!type` / `(expr)::type`
    if startsWith cs "(" then
      match parseExpr fuel ctx (cs.drop 1) with
      | some (e, r1) =>
        match expect ")" r1 with
        | some r2 =>
          match expect "::" r2 with
          | some r3 =>
            let (fb, r4) := match r3 with
              | '?' :: rr => (Proto.CastFailureBehavior.returnNull, rr)
              | '!' :: rr => (Proto.CastFailureBehavior.throwException, rr)
              | rr => (Proto.CastFailureBehavior.unspecified, rr)
            match parseType (r4.length + 1) r4 with
            | some (t, r5) =>
              -- Unspecified behavior cannot be emitted; parse it back as
              -- returnNull only when the emitter wrote '?', etc. The bare
              -- form `(e)::type` is NOT emitted (unspecified throws), so
              -- reject it here:
              match fb with
              | .unspecified => none
              | _ => some (.cast e t fb, r5)
            | none => none
          | none => none
        | none => none
      | none => none
    -- if_then(...)
    else if startsWith cs "if_then(" then
      match parseIfPairs (cs.length + 1) fuel ctx (cs.drop 8) with
      | some (ifs, els, r) => some (.ifThen ifs els, r)
      | none => none
    else if startsWith cs "$" then
      match scanNat (cs.drop 1) with
      | some (n, r) => some (.field { ordinal := n, segment := none }, r)
      | none => none
    else match scanIdent cs with
    | some (fn, r1) =>
      match expect "(" r1 with
      | some r2 =>
        match parseExprList (r2.length + 1) fuel ctx r2 with
        | some (args, r3) =>
          match expect ")" r3 with
          | some r4 =>
            match expect ":" r4 with
            | some r5 =>
              match parseType (r5.length + 1) r5 with
              | some (outTy, r6) =>
                match ctx.lookup fn with
                | some anchor => some (.scalarFunction anchor args outTy, r6)
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | none =>
        -- not a call: identifier-lexing literals (true/false/null) land here
        match parseLiteral cs with
        | some (lit, r) => some (.literal lit, r)
        | none => none
    | none => match parseLiteral cs with
      | some (lit, r) => some (.literal lit, r)
      | none => none

end

-- ── expressions: the inversion theorems ────────────────────────────────────

/-- `expect "("` rejects when the head isn't `(`. -/
private theorem expect_paren_fail (rest : List Char) (hh : rest.head? ≠ some '(') :
    expect "(" rest = none := by
  have hh' : rest.head? ≠ "(".toList.head? := by
    have hl : "(".toList = ['('] := by decide
    rw [hl]
    exact hh
  exact expect_fail "(" rest (by decide) hh'

/-- No `:` head → the literal type suffix is absent. -/
private theorem scanLitSuffix_none (rest : List Char) (h : rest.head? ≠ some ':') :
    scanLitSuffix rest = some (none, rest) := by
  cases hr : rest with
  | nil =>
    rw [scanLitSuffix.eq_2 ([] : List Char) (by intro rest' h'; cases h')]
  | cons c cs0 =>
    have hc : c ≠ ':' := by
      intro hcc
      exact h (by simp [hr, hcc])
    rw [scanLitSuffix.eq_2 (c :: cs0)
      (by intro rest' h'; injection h' with hcc _; exact hc hcc)]

/-- The `scanInt` inversion for nonneg values: a Nat's decimal text scans back
    (the sign-less arm). -/
private theorem scanInt_of_nat (n : Nat) (rest : List Char) (hstop : notDigitHead rest) :
    scanInt ((toString n).toList ++ rest) = some ((n : Int), rest) := by
  have hdash : ∀ rest0, ¬ (toString n).toList ++ rest = '-' :: rest0 := by
    intro rest0 h'
    cases hd : (toString n).toList with
    | nil => exact (toString_toList_ne_nil n hd).elim
    | cons c cs =>
      rw [hd] at h'
      rw [List.cons_append] at h'
      injection h' with hcc _
      have hdigc : c.isDigit = true := toString_head_isDigit n c cs hd
      rw [hcc] at hdigc
      have hnd : Char.isDigit '-' = false := by decide
      rw [hnd] at hdigc
      simp at hdigc
  rw [scanInt.eq_2 ((toString n).toList ++ rest) hdash]
  rw [Parser.bind_apply, Parser.bind]
  rw [scanNat_of_toString n rest hstop]
  simp

/-- The `scanInt` inversion for negative values: `-` + the Nat text of the
    magnitude scans back to the negative Int. -/
private theorem scanInt_of_neg (n : Nat) (rest : List Char) (hstop : notDigitHead rest) :
    scanInt ('-' :: (toString n).toList ++ rest) = some (-(n : Int), rest) := by
  rw [List.cons_append]
  rw [scanInt.eq_1 ((toString n).toList ++ rest)]
  rw [Parser.bind_apply, Parser.bind]
  rw [scanNat_of_toString n rest hstop]
  simp [Parser.bind, Parser.result]

/-- The `field` inversion: `$n` scans back to the field reference (the
    emitter writes the ordinal only; the segment is always `none`). -/
theorem parseExpr_field (fuel n : Nat) (ctx : FnCtx) (rest : List Char)
    (hstop : notDigitHead rest) :
    parseExpr (fuel + 1) ctx ((Emit.Text.fieldRef n).toList ++ rest) =
      some (.field { ordinal := n, segment := none }, rest) := by
  unfold Emit.Text.fieldRef
  have hshape : ("$" ++ toString n).toList ++ rest = '$' :: ((toString n).toList ++ rest) := by
    rw [String.toList_append]
    have hd : "$".toList = ['$'] := by decide
    rw [hd]
    rfl
  rw [hshape]
  unfold parseExpr
  have hnot1 : ¬ startsWith ('$' :: ((toString n).toList ++ rest)) "(" = true := by
    unfold startsWith
    simp [List.isPrefixOf]
  rw [if_neg hnot1]
  have hnot2 : ¬ startsWith ('$' :: ((toString n).toList ++ rest)) "if_then(" = true := by
    unfold startsWith
    simp [List.isPrefixOf]
  rw [if_neg hnot2]
  have hdollar : startsWith ('$' :: ((toString n).toList ++ rest)) "$" = true := by
    unfold startsWith
    simp [List.isPrefixOf]
  rw [if_pos hdollar]
  change (match scanNat ((toString n).toList ++ rest) with
    | some (n, r) => some (Proto.Expression.field { ordinal := n, segment := none }, r)
    | none => none) =
      some (Proto.Expression.field { ordinal := n, segment := none }, rest)
  rw [scanNat_of_toString n rest hstop]

-- ── expressions: the literal machinery ─────────────────────────────────────

/-- The digit-value range (Nat-view) of a `Char.isDigit` character. -/
private theorem Char_isDigit_toNat_bounds {c : Char} (hc : c.isDigit = true) :
    '0'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ '9'.val.toNat := by
  unfold Char.isDigit at hc
  rw [Bool.and_eq_true] at hc
  have hu : c.val ≥ '0'.val ∧ c.val ≤ '9'.val := by simpa using hc
  rw [UInt32.le_iff_toNat_le] at hu
  exact hu

/-- A digit character is not an ASCII letter (the value ranges are disjoint). -/
private theorem Char_isAlpha_of_digit {c : Char} (hc : c.isDigit = true) : c.isAlpha = false := by
  unfold Char.isAlpha
  cases hup : c.isUpper with
  | true =>
    have hv : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val := by
      unfold Char.isUpper at hup
      simpa using hup
    have hvt : 'A'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'Z'.val.toNat := by
      rw [UInt32.le_iff_toNat_le] at hv
      exact hv
    have hd := Char_isDigit_toNat_bounds hc
    have hA : 'A'.val.toNat = 65 := by decide
    have hZ : 'Z'.val.toNat = 90 := by decide
    have h0 : '0'.val.toNat = 48 := by decide
    have h9 : '9'.val.toNat = 57 := by decide
    rw [hA, hZ] at hvt
    rw [h0, h9] at hd
    have hbad : False := by omega
    exact hbad.elim
  | false =>
    cases hlo : c.isLower with
    | true =>
      have hv : c.val ≥ 'a'.val ∧ c.val ≤ 'z'.val := by
        unfold Char.isLower at hlo
        simpa using hlo
      have hvt : 'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat := by
        rw [UInt32.le_iff_toNat_le] at hv
        exact hv
      have hd := Char_isDigit_toNat_bounds hc
      have ha : 'a'.val.toNat = 97 := by decide
      have hz : 'z'.val.toNat = 122 := by decide
      have h0 : '0'.val.toNat = 48 := by decide
      have h9 : '9'.val.toNat = 57 := by decide
      rw [ha, hz] at hvt
      rw [h0, h9] at hd
      have hbad : False := by omega
      exact hbad.elim
    | false => rfl

/-- A digit-headed text is not an identifier. -/
private theorem scanIdent_digit_head (c : Char) (cs : List Char) (hc : c.isDigit = true) :
    scanIdent (c :: cs) = none := by
  unfold scanIdent scanIdent.scanIdentGo
  simp [Parser.bind_apply, Parser.bind, Parser.peek, Parser.fail, Char_isAlpha_of_digit hc]

/-- `startsWith p` on a cons-headed text is false when the head char differs
    from the literal `p`'s head (one lemma for every literal prefix the
    grammar tests). -/
private theorem startsWith_neg_of_head (c : Char) (cs : List Char) (p : String)
    (h0 : Char) (hp : p.toList.head? = some h0) (hc : c ≠ h0) :
    startsWith (c :: cs) p = false := by
  unfold startsWith
  cases hl : p.toList with
  | nil => simp [hl] at hp
  | cons h' t =>
    simp [hl] at hp
    subst hp
    cases hc0 : c == h' with
    | true => exact (hc (beq_iff_eq.mp hc0)).elim
    | false =>
      simp [List.isPrefixOf]
      intro hz
      exact (hc hz.symm).elim

/-- The prefix-peeled parseExpr body for a non-call text reduces to the
    literal parse: `scanIdent` is either `none` or its remainder doesn't
    start with `(`. -/
private theorem parseExpr_literal_fallback (fuel : Nat) (ctx : FnCtx) (cs : List Char)
    (hnot1 : ¬ startsWith cs "(" = true)
    (hnot2 : ¬ startsWith cs "if_then(" = true)
    (hnot3 : ¬ startsWith cs "$" = true)
    (hnocall : ∀ (fn : String) (r1 : List Char), scanIdent cs = some (fn, r1) →
      expect "(" r1 = none) :
    parseExpr (fuel + 1) ctx cs =
      (match parseLiteral cs with
        | some (lit, r) => some (.literal lit, r)
        | none => none) := by
  unfold parseExpr
  rw [if_neg hnot1, if_neg hnot2, if_neg hnot3]
  cases hs : scanIdent cs with
  | none => rfl
  | some p =>
    rcases p with ⟨fn, r1⟩
    dsimp only
    cases he : expect "(" r1 with
    | none => rfl
    | some r2 => exact (by cases (he.symm.trans (hnocall fn r1 hs)))

/-- The word-parameterized bool-literal inversion (the shared body of the
    `true`/`false` twins): an identifier word `word` heading `c :: cs` that
    `parseLiteral` scans back to the `.bool b` literal parses as that literal
    expression.  The caller discharges the literal scan (the only branch-
    specific part: `parseLiteral.eq_2` for `true`, `eq_3` for `false`). -/
private theorem parseExpr_lit_word (fuel : Nat) (ctx : FnCtx) (word : String) (b : Bool)
    (c : Char) (cs rest : List Char)
    (hword : word.toList = c :: cs)
    (hident : Emit.Text.isIdentifier word = true)
    (hsep : rest = [] ∨ ∃ c0 rest0, rest = c0 :: rest0 ∧ Emit.Text.isIdentChar c0 = false)
    (hnotparen : rest.head? ≠ some '(')
    (hnot1 : ¬ startsWith (c :: (cs ++ rest)) "(" = true)
    (hnot2 : ¬ startsWith (c :: (cs ++ rest)) "if_then(" = true)
    (hnot3 : ¬ startsWith (c :: (cs ++ rest)) "$" = true)
    (hlit : (match parseLiteral (word.toList ++ rest) with
              | some (lit, r) => some (Proto.Expression.literal lit, r)
              | none => none) =
            some (Proto.Expression.literal { literalType := Proto.LiteralType.bool b,
                                             nullable := false }, rest)) :
    parseExpr (fuel + 1) ctx (word.toList ++ rest) =
      some (Proto.Expression.literal { literalType := Proto.LiteralType.bool b,
                                       nullable := false }, rest) := by
  rw [hword, List.cons_append]
  have hsc : scanIdent (c :: (cs ++ rest)) = some (word, rest) := by
    rw [← List.cons_append, ← hword]
    exact scanIdent_of_identifier word hident rest hsep
  have hnocall : ∀ (fn : String) (r1 : List Char),
      scanIdent (c :: (cs ++ rest)) = some (fn, r1) → expect "(" r1 = none := by
    intro fn r1 h'
    rw [hsc] at h'
    have hpair : (word, rest) = (fn, r1) := Option.some.inj h'
    have hr : r1 = rest := (congrArg Prod.snd hpair).symm
    rw [hr]
    exact expect_paren_fail rest hnotparen
  rw [parseExpr_literal_fallback fuel ctx (c :: (cs ++ rest)) hnot1 hnot2 hnot3 hnocall]
  rw [← List.cons_append, ← hword]
  exact hlit

/-- `true`/`false` (no suffix) scans back to the required bool literal. -/
theorem parseExpr_lit_bool (fuel : Nat) (ctx : FnCtx) (b : Bool) (rest : List Char)
    (hsep : rest = [] ∨ ∃ c0 rest0, rest = c0 :: rest0 ∧ Emit.Text.isIdentChar c0 = false)
    (hnotcolon : rest.head? ≠ some ':')
    (hnotparen : rest.head? ≠ some '(') :
    parseExpr (fuel + 1) ctx ((if b then "true" else "false").toList ++ rest) =
      some (.literal { literalType := .bool b, nullable := false }, rest) := by
  cases b
  · -- `false` (Bool's first constructor)
    have hred : (if false = true then ("true" : String) else "false") = "false" := by decide
    rw [hred]
    exact parseExpr_lit_word fuel ctx "false" false 'f' ['a', 'l', 's', 'e'] rest
      (by decide) (by decide) hsep hnotparen
      (by simpa using (startsWith_neg_of_head 'f' (['a', 'l', 's', 'e'] ++ rest) "(" '(' (by decide) (by decide)))
      (by simpa using (startsWith_neg_of_head 'f' (['a', 'l', 's', 'e'] ++ rest) "if_then(" 'i' (by decide) (by decide)))
      (by simpa using (startsWith_neg_of_head 'f' (['a', 'l', 's', 'e'] ++ rest) "$" '$' (by decide) (by decide)))
      (by have hshape : (("false" : String).toList ++ rest) = 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest := by
            have ht : "false".toList = ['f', 'a', 'l', 's', 'e'] := by decide
            rw [ht]; rfl
          rw [hshape, parseLiteral.eq_3, litWithSuffix, scanLitSuffix_none rest hnotcolon]; simp [suffixNullable])
  · -- `true`
    have hred : (if true = true then ("true" : String) else "false") = "true" := by decide
    rw [hred]
    exact parseExpr_lit_word fuel ctx "true" true 't' ['r', 'u', 'e'] rest
      (by decide) (by decide) hsep hnotparen
      (by simpa using (startsWith_neg_of_head 't' (['r', 'u', 'e'] ++ rest) "(" '(' (by decide) (by decide)))
      (by simpa using (startsWith_neg_of_head 't' (['r', 'u', 'e'] ++ rest) "if_then(" 'i' (by decide) (by decide)))
      (by simpa using (startsWith_neg_of_head 't' (['r', 'u', 'e'] ++ rest) "$" '$' (by decide) (by decide)))
      (by have hshape : (("true" : String).toList ++ rest) = 't' :: 'r' :: 'u' :: 'e' :: rest := by
            have ht : "true".toList = ['t', 'r', 'u', 'e'] := by decide
            rw [ht]; rfl
          rw [hshape, parseLiteral.eq_2, litWithSuffix, scanLitSuffix_none rest hnotcolon]; simp [suffixNullable])

-- ── expressions: numeric/string/null literals ──────────────────────────────

/-- A digit character differs from any non-digit character. -/
private theorem char_ne_digit {c l : Char} (hc : c.isDigit = true) (hl : l.isDigit = false) : c ≠ l := by
  intro hcc
  rw [hcc] at hc
  rw [hl] at hc
  simp at hc

/-- The int-literal text's parseExpr prefix conditions (digit head: no
    cast/if_then/field prefix; not an identifier). -/
private theorem parseExpr_int_prefix (n : Nat) (rest : List Char) :
    ¬ startsWith ((toString n).toList ++ rest) "(" = true ∧
    ¬ startsWith ((toString n).toList ++ rest) "if_then(" = true ∧
    ¬ startsWith ((toString n).toList ++ rest) "$" = true ∧
    scanIdent ((toString n).toList ++ rest) = none := by
  cases hn : (toString n).toList with
  | nil => exact (toString_toList_ne_nil n hn).elim
  | cons c cs =>
    have hdim : c.isDigit = true := toString_head_isDigit n c cs hn
    constructor
    · rw [List.cons_append]
      exact (by simpa using (startsWith_neg_of_head c (cs ++ rest) "(" '(' (by decide)
        (char_ne_digit hdim (by decide : '('.isDigit = false))))
    · constructor
      · rw [List.cons_append]
        exact (by simpa using (startsWith_neg_of_head c (cs ++ rest) "if_then(" 'i' (by decide)
          (char_ne_digit hdim (by decide : 'i'.isDigit = false))))
      · constructor
        · rw [List.cons_append]
          exact (by simpa using (startsWith_neg_of_head c (cs ++ rest) "$" '$' (by decide)
            (char_ne_digit hdim (by decide : '$'.isDigit = false))))
        · rw [List.cons_append]
          exact scanIdent_digit_head c (cs ++ rest) hdim

/-- The `i64` literal (the syntax-default integer): `42` scans back. -/
private theorem parseLiteral_i64 (n : Nat) (rest : List Char)
    (hstop : notDigitHead rest) (hnotcolon : rest.head? ≠ some ':') :
    parseLiteral ((toString n).toList ++ rest) =
      some ({ literalType := .i64 (n : Int), nullable := false }, rest) := by
  cases hn : (toString n).toList with
  | nil => exact (toString_toList_ne_nil n hn).elim
  | cons c cs =>
    have hdim : c.isDigit = true := toString_head_isDigit n c cs hn
    rw [List.cons_append]
    have hbin : startsWith (c :: (cs ++ rest)) "{{binary}}" = false :=
      startsWith_neg_of_head c (cs ++ rest) "{{binary}}" '{' (by decide)
        (char_ne_digit hdim (by decide : '{'.isDigit = false))
    have hneg : c ≠ '-' := char_ne_digit hdim (by decide : '-'.isDigit = false)
    have hsc := scanNat_of_toString n rest hstop
    rw [hn] at hsc
    rw [List.cons_append] at hsc
    have hsc' : scanInt (c :: (cs ++ rest)) = some ((n : Int), rest) := by
      rw [scanInt.eq_2 (c :: (cs ++ rest)) (by intro rest' h'; injection h' with hcc _; exact hneg hcc)]
      rw [Parser.bind_apply, Parser.bind]
      rw [hsc]
      simp
    simp [parseLiteral,
      char_ne_digit hdim (by decide : 'n'.isDigit = false),
      char_ne_digit hdim (by decide : 't'.isDigit = false),
      char_ne_digit hdim (by decide : 'f'.isDigit = false),
      char_ne_digit hdim (by decide : ('\'' : Char).isDigit = false),
      hbin, hsc', intLitTail, scanLitSuffix_none rest hnotcolon, intLitOf, suffixNullable]



-- ── expressions: the type-suffix kit ───────────────────────────────────────

/-- `foldl max` never exceeds the running sum of the accumulated values. -/
private theorem foldl_max_le_acc_sum {α : Type} (l : List α) (f : α → Nat) (acc : Nat) :
    l.foldl (fun m x => max m (f x)) acc ≤ acc + (l.map f).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    calc
      tl.foldl (fun m x => max m (f x)) (max acc (f hd)) ≤ max acc (f hd) + (tl.map f).sum :=
          ih (max acc (f hd))
      _ ≤ acc + f hd + (tl.map f).sum := by omega
      _ = acc + ((hd :: tl).map f).sum := by
        simp [List.map_cons, List.sum_cons]
        omega

/-- The list `sep` text is at least as long as the sum of its items. -/
private theorem sep_len_ge_sum (ts : List String) :
    (ts.map (fun s => s.toList.length)).sum ≤ (Emit.Text.sep ", " ts).toList.length := by
  induction ts with
  | nil => simp [Emit.Text.sep]
  | cons t rest ih =>
    cases rest with
    | nil => simp [Emit.Text.sep]
    | cons t2 rest2 =>
      have hs : Emit.Text.sep ", " (t :: t2 :: rest2) =
          t ++ ", " ++ Emit.Text.sep ", " (t2 :: rest2) := by
        have hc := sep_cons (l := t2 :: rest2) ", " t (by simp)
        exact hc
      rw [hs]
      calc
        ((t :: t2 :: rest2).map (fun s => s.toList.length)).sum
            = t.toList.length + ((t2 :: rest2).map (fun s => s.toList.length)).sum := by
              simp [List.map_cons, List.sum_cons]
        _ ≤ t.toList.length + (Emit.Text.sep ", " (t2 :: rest2)).toList.length := by omega
        _ ≤ t.toList.length + 2 + (Emit.Text.sep ", " (t2 :: rest2)).toList.length := by omega
        _ = (t ++ ", " ++ Emit.Text.sep ", " (t2 :: rest2)).toList.length := by
          rw [toList_append3]
          simp [List.length_append]
          omega

/-- The sum of the field depths is at most the sum of the emitted field texts
    (the mapM pairing is positional — carried through by list induction). -/
private theorem typeDepth_sum_le_len_sum (fs : List Proto.PType) (ts : List String)
    (hmap : fs.mapM Emit.Text.typeText = .ok ts)
    (hif : ∀ f ∈ fs, ∀ b, Emit.Text.typeText f = .ok b → typeDepth f ≤ b.toList.length) :
    (fs.map typeDepth).sum ≤ (ts.map (fun s => s.toList.length)).sum := by
  induction fs generalizing ts with
  | nil =>
    cases ts with
    | nil => simp
    | cons t rest =>
      have hl := mapM_length ([] : List Proto.PType) Emit.Text.typeText (t :: rest) hmap
      simp at hl
  | cons f fs' ih =>
    rcases mapM_cons_ok f fs' Emit.Text.typeText ts hmap with ⟨tf, ts', hf, hr, hts⟩
    subst ts
    have hll := hif f (by simp) tf hf
    have hsum := ih ts' hr (fun x hx b hb => hif x (by simp [hx]) b hb)
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    omega

/-- The struct-field foldl (max over the depths) is bounded by the separator
    text length: foldl ≤ depth-sum ≤ text-length-sum ≤ sep length. -/
private theorem typeDepth_foldl_le_sep (fs : List Proto.PType) (ts : List String)
    (hmap : fs.mapM Emit.Text.typeText = .ok ts)
    (hif : ∀ f ∈ fs, ∀ b, Emit.Text.typeText f = .ok b → typeDepth f ≤ b.toList.length) :
    fs.foldl (fun m x => max m (typeDepth x)) 0 ≤ (Emit.Text.sep ", " ts).toList.length := by
  have h1 := foldl_max_le_acc_sum fs typeDepth 0
  have h2 := typeDepth_sum_le_len_sum fs ts hmap hif
  have h3 := sep_len_ge_sum ts
  omega

/-- A depth-1 type's text (any emitted spelling) has length ≥ 1. -/
private theorem typeDepth_one_le_len {t : Proto.PType} (_hd : typeDepth t = 1) (b : String)
    (hemit : Emit.Text.typeText t = .ok b) : 1 ≤ b.toList.length := by
  have hne := typeText_nonempty t b hemit
  have hpos : 0 < b.toList.length := by
    rw [List.length_pos_iff]
    intro hz
    exact hne (String.toList_inj.mp hz)
  omega

/-- A successful `typeText` requires the base spelling to have succeeded. -/
private theorem typeText_base_ok (t : Proto.PType) (b : String)
    (h : Emit.Text.typeText t = .ok b) : ∃ b0, Emit.Text.typeTextBase t = .ok b0 := by
  rw [Emit.Text.typeText.eq_def] at h
  match he : Emit.Text.typeTextBase t with
  | .error em =>
    rw [he] at h
    simp at h
  | .ok b0 => exact ⟨b0, rfl⟩

/-- **The depth/length bound**: a type's text is always at least as long as
    its depth — the master type-inversion theorem re-uses the recursor
    skeleton (`motive` base + recursion hypotheses per constructor). -/
private theorem typeDepth_le_len (t : Proto.PType) (b : String)
    (hemit : Emit.Text.typeText t = .ok b) : typeDepth t ≤ b.toList.length := by
  let motive : Proto.PType → Prop :=
    fun t => ∀ (b : String), Emit.Text.typeText t = .ok b → typeDepth t ≤ b.toList.length
  let baseMotive (tm : Proto.PType) (hd : typeDepth tm = 1)
      (b : String) (he : Emit.Text.typeText tm = .ok b) : typeDepth tm ≤ b.toList.length := by
    rw [hd]
    exact typeDepth_one_le_len (t := tm) hd b he
  have hbool : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.bool n) = .ok b' → typeDepth (.bool n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.bool n) (by simp [typeDepth]) b' he
  have hi8 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.i8 n) = .ok b' → typeDepth (.i8 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.i8 n) (by simp [typeDepth]) b' he
  have hi16 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.i16 n) = .ok b' → typeDepth (.i16 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.i16 n) (by simp [typeDepth]) b' he
  have hi32 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.i32 n) = .ok b' → typeDepth (.i32 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.i32 n) (by simp [typeDepth]) b' he
  have hi64 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.i64 n) = .ok b' → typeDepth (.i64 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.i64 n) (by simp [typeDepth]) b' he
  have hfp32 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.fp32 n) = .ok b' → typeDepth (.fp32 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.fp32 n) (by simp [typeDepth]) b' he
  have hfp64 : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.fp64 n) = .ok b' → typeDepth (.fp64 n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.fp64 n) (by simp [typeDepth]) b' he
  have hstring : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.string n) = .ok b' → typeDepth (.string n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.string n) (by simp [typeDepth]) b' he
  have hbinary : ∀ (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.binary n) = .ok b' → typeDepth (.binary n) ≤ b'.toList.length := by
    intro n b' he
    exact baseMotive (.binary n) (by simp [typeDepth]) b' he
  have hdecimal : ∀ (p s : Nat) (n : Proto.Nullability) (b' : String),
      Emit.Text.typeText (.decimal p s n) = .ok b' → typeDepth (.decimal p s n) ≤ b'.toList.length := by
    intro p s n b' he
    exact baseMotive (.decimal p s n) (by simp [typeDepth]) b' he
  have hlist : ∀ e n, motive e → motive (.list e n) := by
    intro e n ih b' hemit
    cases n with
    | required =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : Emit.Text.typeText e with
      | error em => simp [he] at hemit
      | ok es =>
        simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
        have hb : b' = "list<" ++ es ++ ">" := hemit.symm
        rw [hb]
        simp [typeDepth]
        have hieh := ih es he
        omega
    | nullable =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : Emit.Text.typeText e with
      | error em => simp [he] at hemit
      | ok es =>
        simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
        have hb : b' = "list<" ++ es ++ ">" ++ "?" := hemit.symm
        rw [hb]
        simp [typeDepth]
        have hieh := ih es he
        omega
    | unspecified =>
      rcases typeText_base_ok (.list e .unspecified) b' hemit with ⟨b0, hb0⟩
      rw [Emit.Text.typeText.eq_def, hb0] at hemit
      simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
  have hmap : ∀ k v n, motive k → motive v → motive (.map k v n) := by
    intro k v n ihk ihv b' hemit
    cases n with
    | required =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : Emit.Text.typeText k with
      | error em => simp [he] at hemit
      | ok ks =>
        cases he2 : Emit.Text.typeText v with
        | error em => simp [he, he2] at hemit
        | ok vs =>
          simp [he, he2, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
          have hb : b' = "map<" ++ ks ++ ", " ++ vs ++ ">" := hemit.symm
          rw [hb]
          simp [typeDepth]
          have hk := ihk ks he
          have hv := ihv vs he2
          omega
    | nullable =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : Emit.Text.typeText k with
      | error em => simp [he] at hemit
      | ok ks =>
        cases he2 : Emit.Text.typeText v with
        | error em => simp [he, he2] at hemit
        | ok vs =>
          simp [he, he2, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
          have hb : b' = "map<" ++ ks ++ ", " ++ vs ++ ">" ++ "?" := hemit.symm
          rw [hb]
          simp [typeDepth]
          have hk := ihk ks he
          have hv := ihv vs he2
          omega
    | unspecified =>
      rcases typeText_base_ok (.map k v .unspecified) b' hemit with ⟨b0, hb0⟩
      rw [Emit.Text.typeText.eq_def, hb0] at hemit
      simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
  have hstruct : ∀ fs n, (∀ f, f ∈ fs → motive f) → motive (.struct fs n) := by
    intro fs n hmem b' hemit
    cases n with
    | required =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : fs.mapM Emit.Text.typeText with
      | error em => simp [he] at hemit
      | ok ts =>
        simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
        have hb : b' = "struct<" ++ Emit.Text.sep ", " ts ++ ">" := hemit.symm
        rw [hb]
        simp [typeDepth]
        have hfb : fs.foldl (fun m x => max m (typeDepth x)) 0 ≤
            (Emit.Text.sep ", " ts).toList.length := by
          exact typeDepth_foldl_le_sep fs ts he (fun x hx b'' hb'' => hmem x hx b'' hb'')
        rw [String.toList_intercalate, show (", " : String).toList = [',', ' '] from rfl] at hfb
        omega
    | nullable =>
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
      cases he : fs.mapM Emit.Text.typeText with
      | error em => simp [he] at hemit
      | ok ts =>
        simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
        have hb : b' = "struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?" := hemit.symm
        rw [hb]
        simp [typeDepth]
        have hfb : fs.foldl (fun m x => max m (typeDepth x)) 0 ≤
            (Emit.Text.sep ", " ts).toList.length := by
          exact typeDepth_foldl_le_sep fs ts he (fun x hx b'' hb'' => hmem x hx b'' hb'')
        rw [String.toList_intercalate, show (", " : String).toList = [',', ' '] from rfl] at hfb
        omega
    | unspecified =>
      rcases typeText_base_ok (.struct fs .unspecified) b' hemit with ⟨b0, hb0⟩
      rw [Emit.Text.typeText.eq_def, hb0] at hemit
      simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
  have huser : ∀ a ps n, True → motive (.userDefined a ps n) := by
    intro a ps n _ b' hemit
    simp [Emit.Text.typeText, Emit.Text.typeTextBase] at hemit
  exact ptypeRec motive hbool hi8 hi16 hi32 hi64 hfp32 hfp64 hstring hbinary
    hdecimal hlist hmap hstruct huser t b hemit

/-- **The parser-fuel inversion**: `parseType` at the call-site fuel (the
    remaining text's length + 1) inverts the type text — shift the
    depth-fueled inversion up by monotonicity (depth ≤ text length). -/
private theorem parseType_len_invert (t : Proto.PType) (b : String) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText t = .ok b) :
    parseType ((b.toList ++ rest).length + 1) (b.toList ++ rest) = some (t, rest) := by
  have hbase := parseType_typeText t b rest hrest hemit
  have hdlen : typeDepth t ≤ b.toList.length := typeDepth_le_len t b hemit
  have hle : typeDepth t ≤ (b.toList ++ rest).length + 1 := by
    rw [List.length_append]
    omega
  have hm := parseType_mono_of_le (typeDepth t) ((b.toList ++ rest).length + 1 - typeDepth t)
    (b.toList ++ rest) (t, rest) hbase
  rwa [show typeDepth t + ((b.toList ++ rest).length + 1 - typeDepth t) =
      (b.toList ++ rest).length + 1 by exact Nat.add_sub_of_le hle] at hm

/-- The `:type` literal suffix scans back (the type-suffix text). -/
private theorem scanLitType (t : Proto.PType) (b : String) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText t = .ok b) :
    scanLitSuffix ((":" ++ b).toList ++ rest) = some (some t, rest) := by
  have hcolon : ((":" ++ b).toList ++ rest) = ':' :: (b.toList ++ rest) := by
    rw [String.toList_append]
    have hc : ":".toList = [':'] := by decide
    rw [hc]
    rfl
  rw [hcolon]
  rw [scanLitSuffix.eq_1 (b.toList ++ rest)]
  rw [parseType_len_invert t b rest hrest hemit]
  rfl

/-- The nullable `i64` literal: `42:i64?` scans back. -/
private theorem parseLiteral_i64_nullable (n : Nat) (rest : List Char)
    (hcont : rest.head? ≠ some '?') :
    parseLiteral ((toString n ++ ":i64?").toList ++ rest) =
      some ({ literalType := .i64 (n : Int), nullable := true }, rest) := by
  have htext : ((toString n ++ ":i64?").toList ++ rest) =
      (toString n).toList ++ ([':', 'i', '6', '4', '?'] : List Char) ++ rest := by
    rw [String.toList_append]
    have hc : (":i64?" : String).toList = [':', 'i', '6', '4', '?'] := by decide
    rw [hc]
  rw [htext]
  have hstop' : notDigitHead (([':', 'i', '6', '4', '?'] : List Char) ++ rest) :=
    Or.inr ⟨':', ['i', '6', '4', '?'] ++ rest, rfl, by decide⟩
  cases hn : (toString n).toList with
  | nil => exact (toString_toList_ne_nil n hn).elim
  | cons c cs =>
    have hdim : c.isDigit = true := toString_head_isDigit n c cs hn
    rw [List.append_assoc, List.cons_append]
    have hbin : startsWith (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest)) "{{binary}}" = false := by
      simpa using
        (startsWith_neg_of_head c (cs ++ ([':', 'i', '6', '4', '?'] ++ rest)) "{{binary}}" '{' (by decide)
          (char_ne_digit hdim (by decide : '{'.isDigit = false)))
    have hneg : c ≠ '-' := char_ne_digit hdim (by decide : '-'.isDigit = false)
    have hscn := scanNat_of_toString n (([':', 'i', '6', '4', '?'] : List Char) ++ rest) hstop'
    rw [hn] at hscn
    rw [List.cons_append] at hscn
    have hscn' : scanNat (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest)) =
        some (n, ':' :: 'i' :: '6' :: '4' :: '?' :: rest) := by
      simpa using hscn
    have hsc' : scanInt (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest)) =
        some ((n : Int), ':' :: 'i' :: '6' :: '4' :: '?' :: rest) := by
      rw [scanInt.eq_2 (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest))
        (by intro rest' h'; injection h' with hcc _; exact hneg hcc)]
      rw [Parser.bind_apply, Parser.bind]
      rw [hscn']
      simp
    have hlt := scanLitType (Proto.PType.i64 Proto.Nullability.nullable) "i64?" rest hcont (by
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def]
      simp [Emit.Text.nullSuffix, Proto.PType.nullability, Substrait.Grammar.ScalarCtor.prefix])
    have hlt' : scanLitSuffix (':' :: 'i' :: '6' :: '4' :: '?' :: rest) =
        some (some (Proto.PType.i64 Proto.Nullability.nullable), rest) := by
      have hs : ((":i64?" : String).toList ++ rest) = ':' :: 'i' :: '6' :: '4' :: '?' :: rest := by
        have hc : (":i64?" : String).toList = [':', 'i', '6', '4', '?'] := by decide
        rw [hc]
        rfl
      rw [← hs]
      exact hlt
    simp [parseLiteral,
      char_ne_digit hdim (by decide : 'n'.isDigit = false),
      char_ne_digit hdim (by decide : 't'.isDigit = false),
      char_ne_digit hdim (by decide : 'f'.isDigit = false),
      char_ne_digit hdim (by decide : ('\'' : Char).isDigit = false),
      hbin, hsc', hlt', intLitTail, intLitOf, suffixNullable, nullabilityOf]
    rfl

/-- A non-alpha head makes `scanIdent` fail. -/
private theorem scanIdent_not_alpha (c : Char) (cs : List Char) (hc : c.isAlpha = false) :
    scanIdent (c :: cs) = none := by
  unfold scanIdent scanIdent.scanIdentGo
  simp [Parser.bind_apply, Parser.bind, Parser.peek, Parser.fail, hc]

/-- The prefix conditions for a quoted/named-head expression text (no cast /
    if_then / field / call prefix). -/
private theorem parseExpr_quote_prefix (c : Char) (cs : List Char)
    (hc : c ≠ '(') (hic : c ≠ 'i') (hdc : c ≠ '$') (hα : c.isAlpha = false) :
    ¬ startsWith (c :: cs) "(" = true ∧
    ¬ startsWith (c :: cs) "if_then(" = true ∧
    ¬ startsWith (c :: cs) "$" = true ∧
    scanIdent (c :: cs) = none := by
  constructor
  · exact (by simpa using (startsWith_neg_of_head c cs "(" '(' (by decide) hc))
  · constructor
    · exact (by simpa using (startsWith_neg_of_head c cs "if_then(" 'i' (by decide) hic))
    · constructor
      · exact (by simpa using (startsWith_neg_of_head c cs "$" '$' (by decide) hdc))
      · exact scanIdent_not_alpha c cs hα

/-- The `'…'` string literal (no suffix) scans back. -/
private theorem parseLiteral_string (s : String) (rest : List Char)
    (hnotcolon : rest.head? ≠ some ':') :
    parseLiteral (("'" ++ Emit.Text.escape s ++ "'").toList ++ rest) =
      some ({ literalType := .string s, nullable := false }, rest) := by
  have hshape : (("'" ++ Emit.Text.escape s ++ "'").toList ++ rest) =
      '\'' :: ((Emit.Text.escape s).toList ++ '\'' :: rest) := by
    rw [toList_append3]
    have hq : "'".toList = ['\''] := by decide
    rw [hq]
    simp [List.cons_append, List.append_assoc]
  rw [hshape]
  have hsq : scanQuotedRaw '\'' [] ((Emit.Text.escape s).toList ++ '\'' :: rest) =
      some (s.toList.flatMap escChars, rest) := by
    have h0 := scanQuotedRaw_escape '\'' s.toList [] rest (Or.inr rfl)
    simp only [List.reverse_nil, List.nil_append] at h0
    -- goal input is toList-form; h0 input is flatMap-form; escape_toList bridges both
    have heq : (Emit.Text.escape s).toList = s.toList.flatMap escChars := escape_toList s
    rw [heq]
    exact h0
  rw [parseLiteral.eq_4]
  rw [hsq]
  dsimp
  rw [show unescape (String.ofList (s.toList.flatMap escChars)) = some s by
    rw [← escape_toList, String.ofList_toList, unescape_escape]]
  simp [litWithSuffix, scanLitSuffix_none rest hnotcolon, suffixNullable]

/-- The nullable `i64` literal at the `parseExpr` level: `42:i64?`. -/
theorem parseExpr_lit_i64 (fuel n : Nat) (ctx : FnCtx) (rest : List Char)
    (hstop : notDigitHead rest) (hnotcolon : rest.head? ≠ some ':') :
    parseExpr (fuel + 1) ctx ((toString n).toList ++ rest) =
      some (.literal { literalType := .i64 (n : Int), nullable := false }, rest) := by
  rcases parseExpr_int_prefix n rest with ⟨hnot1, hnot2, hnot3, hsn⟩
  have hnocall : ∀ (fn : String) (r1 : List Char),
      scanIdent ((toString n).toList ++ rest) = some (fn, r1) → expect "(" r1 = none := by
    intro fn r1 h'
    rw [hsn] at h'
    cases h'
  rw [parseExpr_literal_fallback fuel ctx ((toString n).toList ++ rest) hnot1 hnot2 hnot3 hnocall]
  rw [parseLiteral_i64 n rest hstop hnotcolon]

-- ── relations (the line tree) ───────────────────────────────────────────────

/-- Decode-side output width (total; mirrors the emitter's `relWidth`). -/
def relWidthD : Nat → Proto.Rel → Nat
  | 0, _ => 0
  | _ + 1, .read r => (r.baseSchema.map (·.fields.length)).getD 0
  | fuel + 1, .filter r => relWidthD fuel r.input
  | fuel + 1, .project r => relWidthD fuel r.input + r.expressions.length
  | _, .aggregate r => r.groupingExpressions.length + r.measures.length
  | fuel + 1, .sort r => relWidthD fuel r.input
  | fuel + 1, .fetch r => relWidthD fuel r.input
  | fuel + 1, .join r => r.joinType.width (relWidthD fuel r.left) (relWidthD fuel r.right)
  | fuel + 1, .cross r => relWidthD fuel r.left + relWidthD fuel r.right
  | fuel + 1, .set r => (r.inputs.head?).map (relWidthD fuel) |>.getD 0
  | _, .write _ | _, .extensionLeaf _ | _, .extensionSingle _ | _, .extensionMulti _ => 0

/-- The leading whitespace count of a line. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- Split a line's tail into top-level `, `-separated items (depth-tracked
    over `()<>`; v0 limitation: a quoted name containing ", " inside an
    output column splits wrongly — the corpus has none). -/
def splitTopLevel : List Char → Nat → List Char → List (List Char)
  | [], _, cur => [cur.reverse]
  | ',' :: ' ' :: rest, 0, cur => cur.reverse :: splitTopLevel rest 0 []
  | c :: rest, d, cur =>
    let d' := if c == '(' || c == '<' || c == '[' then d + 1
              else if c == ')' || c == '>' || c == ']' then d - 1
              else d
    splitTopLevel rest d' (c :: cur)

/-- Split on the FIRST top-level ` |> ` (Read's explicit mapping). -/
def splitOnPipe : List Char → List Char → Option (List Char × List Char)
  | _, [] => none
  | acc, ' ' :: '|' :: '>' :: ' ' :: rest => some (acc.reverse, rest)
  | acc, c :: rest => splitOnPipe (c :: acc) rest

/-- A whole-item field ref `$n` (nothing else). -/
def parseRefItem : List Char → Option Nat
  | '$' :: rest => match scanNat rest with
    | some (n, []) => some n
    | _ => none
  | _ => none

/-- Join-type name → constructor (inverse of the emitter's table). -/
def joinTypeOfName : String → Option Proto.JoinType
  | "Inner" => some .inner | "Outer" => some .outer | "Left" => some .left
  | "Right" => some .right | "LeftSemi" => some .leftSemi
  | "RightSemi" => some .rightSemi | "LeftAnti" => some .leftAnti
  | "RightAnti" => some .rightAnti | "LeftSingle" => some .leftSingle
  | "RightSingle" => some .rightSingle | "LeftMark" => some .leftMark
  | "RightMark" => some .rightMark | _ => none

/-- Set-op name → constructor. -/
def setOpOfName : String → Option Proto.SetOp
  | "UnionAll" => some .unionAll | "UnionDistinct" => some .unionDistinct
  | "MinusPrimary" => some .minusPrimary | "MinusPrimaryAll" => some .minusPrimaryAll
  | "MinusMultiset" => some .minusMultiset
  | "IntersectionPrimary" => some .intersectionPrimary
  | "IntersectionMultiset" => some .intersectionMultiset
  | "IntersectionMultisetAll" => some .intersectionMultisetAll
  | _ => none

/-- Sort-direction name → constructor. -/
def sortDirOfName : String → Option Proto.SortDirection
  | "AscNullsFirst" => some .ascNullsFirst
  | "AscNullsLast" => some .ascNullsLast
  | "DescNullsFirst" => some .descNullsFirst
  | "DescNullsLast" => some .descNullsLast
  | "Clustered" => some .clustered
  | _ => none

/-- The output-clause tail: refs-only items become the emit mapping
    (identity canonicalizes to `none` — the text does not distinguish
    `.direct` from no-emit; documented lossiness); typed/expression columns
    are redundant with the rel's own structure and yield `none`. -/
def outputMappingOf (width : Nat) (items : List (List Char)) : Option (List Nat) :=
  let refs := items.map parseRefItem
  if refs.any (· == none) then none
  else
    let m := refs.filterMap id
    if m == List.range width then none else some m

/-- The common record for a parsed mapping. -/
def commonOfMapping : Option (List Nat) → Option Proto.RelCommon
  | none => none
  | some m => some { emit := some (.emit m), advancedExtension := none }

/-- A `name:type` column (Read's output fields). -/
def parseNamedCol (cs : List Char) : Option (String × Proto.PType × List Char) :=
  match scanName cs with
  | some (nm, r1) =>
    match expect ":" r1 with
    | some r2 => (parseType (r2.length + 1) r2).map (fun (t, r3) => (nm, t, r3))
    | none => none
  | none => none

/-- A sort field `($n, &Dir)`, consuming and returning the rest. -/
def parseSortField : List Char → Option (Proto.SortField × List Char)
  | '(' :: '$' :: rest =>
    match scanNat rest with
    | some (n, r1) =>
      match expect ", &" r1 with
      | some r2 =>
        match scanIdent r2 with
        | some (dn, r3) =>
          match expect ")" r3 with
          | some r4 =>
            (sortDirOfName dn).map fun d =>
              ({ expr := .field { ordinal := n, segment := none }, direction := d }, r4)
          | none => none
        | none => none
      | none => none
    | none => none
  | _ => none

/-- The parsed header of one rel line: a constructor waiting for children
    (continuations may fail — the line is rejected). -/
inductive HeaderShape where
  | done (r : Proto.Rel)
  | one (mk : Proto.Rel → Option Proto.Rel)
  | two (mk : Proto.Rel → Proto.Rel → Option Proto.Rel)
  | many (mk : List Proto.Rel → Option Proto.Rel)

/-- Parse Read's named-column list into the base schema (`_` = none). -/
def parseReadCols (cs : List Char) : Option (Option Proto.NamedStruct) :=
  if cs == ['_'] then some none
  else
    let items := splitTopLevel cs 0 []
    let cols := items.map parseNamedCol
    if cols.any (· == none) then none
    else
      let cs' := cols.filterMap id
      some (some { fields := cs'.map (·.2.1), names := cs'.map (·.1) })

/-- The Read header: dotted table name, then ` => cols` or
    ` +> cols |> $mapping`. -/
def parseReadHeader (cs : List Char) : Option Proto.ReadRel :=
  match scanName cs with
  | some (tn, r1) =>
    let rec dots (acc : List String) : Nat → List Char → Option (List String × List Char)
      | 0, _ => none
      | dfuel + 1, '.' :: rest => match scanName rest with
        | some (n2, r2) => dots (acc ++ [n2]) dfuel r2
        | none => none
      | _, rr => some (acc, rr)
    match dots [tn] (r1.length + 1) r1 with
    | some (names, r2) =>
      match expect " => " r2 with
      | some r3 =>
        (parseReadCols r3).map fun baseSchema =>
          { readType := .namedTable names, baseSchema, common := none }
      | none =>
        match expect " +> " r2 with
        | some r3 =>
          match splitOnPipe [] r3 with
          | some (colText, mapText) =>
            match parseReadCols colText with
            | some baseSchema =>
              let mitems := splitTopLevel mapText 0 []
              let rs := mitems.map parseRefItem
              if rs.any (· == none) then none
              else some { readType := .namedTable names, baseSchema
                        , common := some { emit := some (.emit (rs.filterMap id))
                                         , advancedExtension := none } }
            | none => none
          | none =>
            (parseReadCols r3).map fun baseSchema =>
              { readType := .namedTable names, baseSchema, common := none }
        | none => none
    | none => none
  | none => none

/-- The Aggregate header: `groups => cols`; `_` is the empty group. The
    output cols repeat the group exprs then the measures (`name(...):ty`).
    A refs-only output clause is an emit mapping — v0 rejects it (not in
    the corpus; the width is not knowable before the measures). -/
def parseAggregateHeader (ctx : FnCtx) (cs : List Char) : Option HeaderShape := do
  let rec groups (lfuel : Nat) (acc : List Proto.Expression) (cc : List Char) :
      Option (List Proto.Expression × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      if startsWith cc "_ => " then some (acc.reverse, cc.drop 5)
      else match parseExpr (cc.length + 1) ctx cc with
        | some (e, r1) =>
          match expect ", " r1 with
          | some r2 => groups lf (e :: acc) r2
          | none =>
            match expect " => " r1 with
            | some r2 => some ((e :: acc).reverse, r2)
            | none => none
        | none => none
  let (gs, r2) ← groups (cs.length + 1) [] cs
  let items := splitTopLevel r2 0 []
  some (.one fun child =>
    let g := gs.length
    let colExprs := items.map (parseExpr (cs.length + 1) ctx · |>.map (·.1))
    if colExprs.any (· == none) then none  -- the refs-only gap (documented)
    else
      let all := colExprs.filterMap id
      let rec toMeasures : List Proto.Expression → Option (List Proto.AggregateMeasure)
        | [] => some []
        | .scalarFunction fr args outTy :: rest =>
          (toMeasures rest).map (fun ms =>
            { measure := { functionReference := fr, args := args, outputType := outTy } } :: ms)
        | _ => none
      match toMeasures (all.drop g) with
      | some mss =>
        some (.aggregate { groupingExpressions := gs, measures := mss
                         , input := child, common := none })
      | none => none)

/-- The Sort header: `($n, &Dir), … => cols`. -/
def parseSortHeader (_ctx : FnCtx) (cs : List Char) : Option HeaderShape := do
  let rec sorts (lfuel : Nat) (acc : List Proto.SortField) (cc : List Char) :
      Option (List Proto.SortField × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      match parseSortField cc with
      | some (sf, r1) =>
        match expect ", " r1 with
        | some r2 => sorts lf (sf :: acc) r2
        | none =>
          match expect " => " r1 with
          | some r2 => some ((sf :: acc).reverse, r2)
          | none => none
      | none => none
  let (sfs, r2) ← sorts (cs.length + 1) [] cs
  let items := splitTopLevel r2 0 []
  some (.one fun child =>
    some (.sort { sorts := sfs, input := child
                , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))

/-- The Fetch header: `limit=N, offset=M => cols` or `_ => cols`. -/
def parseFetchHeader (cs : List Char) : Option HeaderShape := do
  let named (cc : List Char) : Option (String × Nat × List Char) :=
    match scanIdent cc with
    | some (nm, r1) =>
      match expect "=" r1 with
      | some r2 => (scanNat r2).map (fun (n, r3) => (nm, n, r3))
      | none => none
    | none => none
  let rec args (lfuel : Nat) (acc : List (String × Nat)) (cc : List Char) :
      Option (List (String × Nat) × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      match named cc with
      | some (nm, n, r1) =>
        match expect ", " r1 with
        | some r2 => args lf ((nm, n) :: acc) r2
        | none => match expect " => " r1 with
          | some r2 => some (((nm, n) :: acc).reverse, r2)
          | none => none
      | none => none
  if startsWith cs "_ => " then
    let items := splitTopLevel (cs.drop 5) 0 []
    some (.one fun child =>
      some (.fetch { limit := none, offset := none, input := child
                   , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))
  else
    let (nameds, r2) ← args (cs.length + 1) [] cs
    let items := splitTopLevel r2 0 []
    let lim := nameds.lookup "limit"
    let off := nameds.lookup "offset"
    some (.one fun child =>
      some (.fetch { limit := lim, offset := off, input := child
                   , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))

/-- Parse one rel line's header (content after the indent). -/
def parseHeader (ctx : FnCtx) (cs : List Char) : Option HeaderShape :=
  if startsWith cs "Read[" then
    (parseReadHeader (cs.drop 5)).map (.done ∘ .read)
  else if startsWith cs "Filter[" then
    match parseExpr (cs.length + 1) ctx (cs.drop 7) with
    | some (cond, r1) =>
      match expect " => " r1 with
      | some r2 =>
        let items := splitTopLevel r2 0 []
        some (.one fun child =>
          some (.filter { condition := cond, input := child
                        , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))
      | none => none
    | none => none
  else if startsWith cs "Project[" then
    let items := splitTopLevel (cs.drop 8) 0 []
    some (.one fun child =>
      let w := relWidthD (cs.length + 1) child
      let parsed := items.map (parseExpr (cs.length + 1) ctx · |>.map (·.1))
      if parsed.any (· == none) then none
      else
        let es : List Proto.Expression := parsed.filterMap id
        let prefixOk := (List.range w).all fun i =>
          match es[i]? with
          | some (.field ref) => ref.ordinal == i && ref.segment == none
          | _ => false
        if !prefixOk || es.length < w then none  -- explicit-emit Project: the v0 gap
        else some (.project { expressions := es.drop w, input := child, common := none }))
  else if startsWith cs "Aggregate[" then
    parseAggregateHeader ctx (cs.drop 9)
  else if startsWith cs "Sort[" then
    parseSortHeader ctx (cs.drop 5)
  else if startsWith cs "Fetch[" then
    parseFetchHeader (cs.drop 6)
  else if startsWith cs "Join[" then
    match expect "&" (cs.drop 5) with
    | some r0 =>
      match scanIdent r0 with
      | some (jn, r1) =>
        match joinTypeOfName jn with
        | some jt =>
          match expect ", " r1 with
          | some r2 =>
            match parseExpr (cs.length + 1) ctx r2 with
            | some (cond, r3) =>
              match expect " => " r3 with
              | some r4 =>
                let items := splitTopLevel r4 0 []
                some (.two fun l r =>
                    let w := jt.width (relWidthD (cs.length + 1) l)
                      (relWidthD (cs.length + 1) r)
                    let cm := commonOfMapping (outputMappingOf w items)
                    some (.join { joinType := jt, left := l, right := r, condition := cond, postJoinFilter := none, common := cm }))
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  else if startsWith cs "Set[" then
    match expect "&" (cs.drop 4) with
    | some r0 =>
      match scanIdent r0 with
      | some (sn, r1) =>
        match setOpOfName sn with
        | some op =>
          match expect " => " r1 with
          | some r2 =>
            let items := splitTopLevel r2 0 []
            some (.many fun cs' =>
              match cs' with
              | [] => none
              | x :: _ =>
                let cm := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) x) items)
                some (.set { op := op, inputs := cs', common := cm }))
          | none => none
        | none => none
      | none => none
    | none => none
  else if startsWith cs "Cross[" then
    let items := splitTopLevel (cs.drop 6) 0 []
    if items.map parseRefItem |>.any (· == none) then none
    else some (.two fun l r => some (.cross { left := l, right := r, common := none }))
  else none

mutual

/-- Parse as many children at the given indent as present. -/
def parseChildren (ctx : FnCtx) : Nat → Nat → List String → Option (List Proto.Rel × List String)
  | 0, _, rest => some ([], rest)
  | fuel + 1, ind, rest =>
    match rest with
    | [] => some ([], [])
    | l :: _ =>
      if indentOf l == ind then
        match parseRelTree ctx fuel ind rest with
        | some (c, rest') =>
          (parseChildren ctx fuel ind rest').map fun (cs, r2) => (c :: cs, r2)
        | none => none
      else some ([], rest)

/-- Parse one rel node and its subtree. `fuel` bounds tree depth. -/
def parseRelTree (ctx : FnCtx) : Nat → Nat → List String → Option (Proto.Rel × List String)
  | 0, _, _ => none
  | _, _, [] => none
  | fuel + 1, ind, l :: rest =>
    if indentOf l == ind then
      match parseHeader ctx (l.toList.drop ind) with
      | some (.done r) => some (r, rest)
      | some (.one mk) =>
        match parseRelTree ctx fuel (ind + 2) rest with
        | some (c, rest') => (mk c).map (·, rest')
        | none => none
      | some (.two mk) =>
        match parseRelTree ctx fuel (ind + 2) rest with
        | some (c1, r1) =>
          match parseRelTree ctx fuel (ind + 2) r1 with
          | some (c2, r2) => (mk c1 c2).map (·, r2)
          | none => none
        | none => none
      | some (.many mk) =>
        match parseChildren ctx fuel (ind + 2) rest with
        | some (cs', rest') => (mk cs').map (·, rest')
        | none => none
      | none => none
    else none

end


-- ── the plan driver ─────────────────────────────────────────────────────────

/-- `@  1: urn` — a URN entry (anchors right-justified to width 3). -/
def parseUrnEntry (cs : List Char) : Option Proto.SimpleExtensionUrn :=
  let cs := cs.dropWhile (· == ' ')
  match cs with
  | '@' :: rest =>
    let rest := rest.dropWhile (· == ' ')
    match scanNat rest with
    | some (a, r1) =>
      match expect ":" r1 with
      | some r2 => some { extensionUrnAnchor := a, urn := String.ofList (r2.drop 1) }
      | none => none
    | none => none
  | _ => none

/-- `#  1 @  1: name` — a declaration entry. -/
def parseDeclEntry (kind : Nat) (cs : List Char) : Option Proto.ExtensionDeclaration :=
  let cs := cs.dropWhile (· == ' ')
  match cs with
  | '#' :: rest =>
    let rest := rest.dropWhile (· == ' ')
    match scanNat rest with
    | some (anchor, r1) =>
      let r1 := r1.dropWhile (· == ' ')
      match r1 with
      | '@' :: r2 =>
        let r2 := r2.dropWhile (· == ' ')
        match scanNat r2 with
        | some (urnRef, r3) =>
          match expect ":" r3 with
          | some r4 =>
            let nm := String.ofList (r4.drop 1)
            match kind with
            | 0 => some (.function urnRef anchor nm)
            | 1 => some (.extType urnRef anchor nm)
            | _ => some (.typeVariation urnRef anchor nm)
          | none => none
        | none => none
      | _ => none
    | none => none
  | _ => none

/-- The extensions section: URN entries, then Functions/Types/Type
    Variations blocks. Returns the plan fields and the FnCtx. -/
def parseExtensions : List String → Option (List Proto.SimpleExtensionUrn × List Proto.ExtensionDeclaration × FnCtx × List String)
  | [] => none
  | "URNs:" :: rest =>
    let urns := rest.takeWhile (fun l => l.startsWith "  @")
    let urnVals := urns.map (parseUrnEntry ·.toList)
    if urnVals.any (· == none) then none
    else parseDeclBlocks [] [] (rest.length + 1) (rest.drop urns.length) |>.map fun (ds, rest') =>
      (urnVals.filterMap id, ds, fnCtxOf ds, rest')
  | rest => parseDeclBlocks [] [] (rest.length + 1) rest |>.map fun (ds, rest') =>
      ([], ds, fnCtxOf ds, rest')
where
  /-- The function declarations → (name, anchor) pairs — the FnCtx both
      sections build (one helper, used twice). -/
  fnCtxOf (ds : List Proto.ExtensionDeclaration) : FnCtx :=
    ds.filterMap fun d => match d with | .function _ a n => some (n, a) | _ => none
  /-- The block header → its declaration kind number (0 = functions, 1 =
      types, 2 = type variations) — one table instead of three arms. -/
  kindOf (l : String) : Option Nat :=
    if l == "Functions:" then some 0
    else if l == "Types:" then some 1
    else if l == "Type Variations:" then some 2
    else none
  parseDeclBlocks (acc : List Proto.ExtensionDeclaration) (curKind : List Proto.ExtensionDeclaration) :
      Nat → List String → Option (List Proto.ExtensionDeclaration × List String)
    | 0, _ => none
    | bfuel + 1, l :: rest =>
      match kindOf l with
      | none => some (acc, l :: rest)
      | some k =>
          let es := rest.takeWhile (fun l => l.startsWith "  #")
          let vs := es.map (parseDeclEntry k ·.toList)
          if vs.any (· == none) then none
          else parseDeclBlocks (acc ++ vs.filterMap id) curKind bfuel (rest.drop es.length)
    | _ + 1, [] => some (acc, [])

/-- The `=== Version X.Y.Z` header plus optional producer/git_hash lines. -/
def parseVersion : List String → Option (Proto.Version × List String)
  | l :: rest =>
    match expect "=== Version " l.toList with
    | some r1 =>
      match scanNat r1 with
      | some (mj, r2) => match expect "." r2 with
        | some r3 => match scanNat r3 with
          | some (mn, r4) => match expect "." r4 with
            | some r5 => match scanNat r5 with
              | some (pt, []) =>
                let producer := match rest with
                  | p :: _ =>
                    if p.startsWith "  producer: " then [p.drop 12] else []
                  | _ => []
                let afterP := if producer.isEmpty then rest else rest.drop 1
                let git := match afterP with
                  | g :: _ =>
                    if g.startsWith "  git_hash: " then [g.drop 12] else []
                  | _ => []
                let afterG := if git.isEmpty then afterP else afterP.drop 1
                some ({ majorNumber := mj, minorNumber := mn, patchNumber := pt
                      , producer := (producer.headD "").toString, gitHash := (git.headD "").toString }, afterG)
              | _ => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | [] => none

/-- The `=== Plan` body: plan rels separated by blank lines. A `Root[…]`
    line takes an indented child. -/
def parsePlanRels (ctx : FnCtx) : Nat → List String → Option (List Proto.PlanRel)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, "" :: rest => parsePlanRels ctx fuel rest
  | fuel + 1, l :: rest =>
    if l.startsWith "Root[" then
      -- names between Root[ and ]
      let inner := (l.toList.drop 5).takeWhile (· ≠ ']')
      let names := (splitTopLevel inner 0 []).map fun item =>
        (scanName item).map (·.1)
      if names.any (· == none) then none
      else
        match parseRelTree ctx (rest.length + 1) 2 rest with
        | some (input, rest') =>
          (parsePlanRels ctx fuel rest').map
            (.root (names.filterMap id) input :: ·)
        | none => none
    else
      match parseRelTree ctx (rest.length + 1) 0 (l :: rest) with
      | some (r, rest') => (parsePlanRels ctx fuel rest').map (.rel r :: ·)
      | none => none

/-- **The decoder**: text → `Proto.Plan`. The inverse of `Emit.Text.emit`
    (for plans whose rels are all in the grammar; the lossy spots — explicit
    `.direct` vs absent emit kinds, `advancedExtension`, unsorted extension
    declarations — are documented in the module doc). -/
def parsePlan (text : String) : Option Proto.Plan := do
  let lines := text.splitOn "\n"
  let lines := match lines.getLast? with
    | some "" => lines.dropLast
    | _ => lines
  let (version, rest1) := match lines with
    | l :: _ =>
      if l.startsWith "=== Version" then
        match parseVersion lines with
        | some (v, r) => (some v, r)
        | none => (none, lines)
      else (none, lines)
    | [] => (none, [])
  match rest1 with
  | "=== Extensions" :: rest2 =>
    let (urns, decls, fctx, rest3) ← parseExtensions rest2
    let rest4 := match rest3 with | "" :: r => r | r => r
    match rest4 with
    | "=== Plan" :: rest5 =>
      let rels ← parsePlanRels fctx (rest5.length + 1) rest5
      some { version, extensionUrns := urns, extensions := decls, relations := rels }
    | _ => none
  | "=== Plan" :: rest2 =>
    let rels ← parsePlanRels [] (rest2.length + 1) rest2
    some { version, extensionUrns := [], extensions := [], relations := rels }
  | _ => none

/-! ## relations: the inversion theorems (the last parser layer) -/

/- The relation layer is multi-line; the emitter (`Emit.Text.relLines`) writes
   indented lines and the parser (`parseRelTree`/`parseChildren`) recovers the
   indentation tree.  These theorems invert that layer for the well-formed
   fragment: Read (named table with a non-empty schema of plain-typed
   columns), Filter (a field-ref condition), Project (field-ref expressions),
   all with `common = none` (the documented lossiness — explicit emit
   mappings print identically to none and are canonicalized away). -/

/-- A character that `splitTopLevel` passes through unchanged (not the `, `
    separator and not a depth-tracked bracket). -/
def plainChar (c : Char) : Prop :=
  c ≠ ',' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '[' ∧ c ≠ ']'

/-- A char list all of whose chars are plain. -/
def Plain (cs : List Char) : Prop := ∀ c ∈ cs, plainChar c

-- The seven `plainChar` guards (`,` `(` `)` `<` `>` `[` `]`) are used as the
-- raw conjunction projections `h.1`, `h.2.1`, … at the split sites below.

/-- A plain char has `c == '(' = false`, etc. (the depth tests fail). -/
private theorem plain_beq_open (c : Char) (h : plainChar c) :
    (c == '(' || c == '<' || c == '[') = false := by
  have h1 : (c == '(') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.1 (beq_iff_eq.mp j)
  have h2 : (c == '<') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.1 (beq_iff_eq.mp j)
  have h3 : (c == '[') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.2.1 (beq_iff_eq.mp j)
  rw [h1, h2, h3]
  rfl

/-- A plain char has `c == ')' = false`, etc. (the close tests fail). -/
private theorem plain_beq_close (c : Char) (h : plainChar c) :
    (c == ')' || c == '>' || c == ']') = false := by
  have h1 : (c == ')') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.1 (beq_iff_eq.mp j)
  have h2 : (c == '>') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.1 (beq_iff_eq.mp j)
  have h3 : (c == ']') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.2.2 (beq_iff_eq.mp j)
  rw [h1, h2, h3]
  rfl

/-- A plain prefix is accumulated into `cur` by `splitTopLevel` (no splits
    at depth 0, no depth changes). -/
theorem splitTopLevel_plain_prefix (x rest cur : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ rest) 0 cur = splitTopLevel rest 0 (x.reverse ++ cur) := by
  induction x generalizing cur with
  | nil => simp
  | cons c cs ih =>
    have hp := hplain c (by simp)
    have hcs : Plain cs := by
      intro a ha
      exact hplain a (by simp [ha])
    rw [List.cons_append]
    rw [splitTopLevel.eq_3 0 cur c (cs ++ rest) (by
      intro rest' h0 hc hrest
      exact (hp.1 hc).elim)]
    rw [plain_beq_open c hp, plain_beq_close c hp]
    simp
    rw [ih (c :: cur) hcs]

/-- `splitTopLevel` on a lone `]` just accumulates it (the depth saturates
    at 0 for Nat subtraction). -/
theorem splitTopLevel_rbracket_cur (cur : List Char) :
    splitTopLevel [']'] 0 cur = [cur.reverse ++ [']']] := by
  rw [splitTopLevel.eq_3 0 cur ']' [] (by
    intro rest' h0 hc hrest
    cases hrest)]
  have hbr := show (']' == '(' || ']' == '<' || ']' == '[') = false by decide
  have hbc := show (']' == ')' || ']' == '>' || ']' == ']') = true by decide
  rw [hbr, hbc]
  simp
  rw [splitTopLevel.eq_1 0 (']' :: cur)]
  simp [List.reverse_cons]

/-- A single plain item followed by `]` stays one item (the `]` merges in). -/
theorem splitTopLevel_plain_rbracket (x : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ [']']) 0 [] = [x ++ [']']] := by
  rw [splitTopLevel_plain_prefix x [']'] [] hplain]
  simp
  rw [splitTopLevel_rbracket_cur x.reverse]
  simp [List.reverse_reverse]

/-- A plain head followed by the `, ` separator splits off the head. -/
theorem splitTopLevel_comma_head (x rest : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ ([',', ' '] ++ rest)) 0 [] = x :: splitTopLevel rest 0 [] := by
  rw [splitTopLevel_plain_prefix x ([',', ' '] ++ rest) [] hplain]
  change splitTopLevel (',' :: ' ' :: rest) 0 (x.reverse ++ []) = x :: splitTopLevel rest 0 []
  rw [splitTopLevel.eq_2 (x.reverse ++ []) rest]
  simp [List.reverse_reverse]

/-- `splitTopLevel` over the joined items: the head goes to the result, the
    last item absorbs the tail (`]`). -/
def splitAppend (xss : List (List Char)) (tail : List Char) : List (List Char) :=
  match xss with
  | [] => []
  | [x] => [x ++ tail]
  | x :: rest => x :: splitAppend rest tail

/-- The rendered `name:type` column text. -/
def colText (n b : String) : String := Emit.Text.name n ++ ":" ++ b

/-- **The named-column inversion**: `name:type` scans back to the name and
    the parsed type (the type text is consumed via the length-fuel
    inversion). -/
theorem parseNamedCol_emitted (n : String) (t : Proto.PType) (b : String)
    (rest : List Char) (hemit : Emit.Text.typeText t = .ok b)
    (hrest : rest.head? ≠ some '?') :
    parseNamedCol ((colText n b).toList ++ rest) = some (n, t, rest) := by
  unfold parseNamedCol colText
  rw [String.toList_append, String.toList_append]
  -- scanName ((name n).toList ++ ":".toList ++ b.toList ++ rest)
  have hsc' : scanName ((Emit.Text.name n).toList ++ (":".toList ++ (b.toList ++ rest))) =
      some (n, ":".toList ++ (b.toList ++ rest)) := by
    have hs := scanName_name n (":".toList ++ (b.toList ++ rest))
      (Or.inr ⟨':', b.toList ++ rest, rfl, by decide⟩)
    exact hs
  -- normalize the goal's left-nested append chain to the hsc' form
  have hassoc : (Emit.Text.name n).toList ++ ":".toList ++ b.toList ++ rest =
      (Emit.Text.name n).toList ++ (":".toList ++ (b.toList ++ rest)) := by
    simp [List.append_assoc]
  rw [hassoc]
  rw [hsc']
  -- the match over `some` reduces
  -- reduce the outer match (the scanName result is some), then the expect
  -- match, then the type inversion; the final map over some reduces by rfl
  dsimp only
  rw [expect_self ":" (b.toList ++ rest)]
  simp only []
  rw [parseType_len_invert t b rest hrest hemit]
  rfl

/-- The `, `-joined column text of a column list. -/
def colsText (cols : List (String × String)) : String :=
  Emit.Text.sep ", " (cols.map (fun x => colText x.1 x.2))

/-- Elementwise inversion of `splitAppend`: the i-th element of the result
    is the i-th input, extended by `tail` exactly at the last index. -/
theorem splitAppend_getElem? : ∀ (xss : List (List Char)) (tail : List Char)
    (i : Nat) (hi : i < xss.length),
    (splitAppend xss tail)[i]? = some (xss[i]'hi ++ if i = xss.length - 1 then tail else []) := by
  intro xss
  induction xss with
  | nil => intro tail i hi; simp at hi
  | cons x rest ih =>
      intro tail i hi
      cases rest with
      | nil =>
          have hi' : i < 1 := by simpa using hi
          have hi0 : i = 0 := by omega
          subst i
          simp [splitAppend]
      | cons y rest' =>
          cases i with
          | zero =>
              simp [splitAppend]
          | succ j =>
              have hj : j < (y :: rest').length := Nat.lt_of_succ_lt_succ hi
              have hiff :
                  (j + 1 = (x :: y :: rest').length - 1 ↔
                   j = (y :: rest').length - 1) := by
                have hlen : (x :: y :: rest').length = (y :: rest').length + 1 := by
                  simp [List.length_cons]
                have hgt0 : 0 < (y :: rest').length := by simp
                constructor
                · intro h; omega
                · intro h; omega
              have hc : (y :: rest')[j]'hj = (x :: y :: rest')[j+1]'hi := by
                rw [List.getElem_cons_succ]
              have hif : (if j = (y :: rest').length - 1 then tail else []) =
                  (if j + 1 = (x :: y :: rest').length - 1 then tail else []) := by
                by_cases hJ : j = (y :: rest').length - 1
                · have hpos : j + 1 = (x :: y :: rest').length - 1 := hiff.mpr hJ
                  simp [hJ]
                · have hnj : ¬ j + 1 = (x :: y :: rest').length - 1 := by
                    intro h
                    exact hJ (hiff.mp h)
                  simp
              simp only [splitAppend, List.getElem?_cons_succ]
              rw [ih tail j hj]
              rw [hc]
              rw [hif]

/-- The map over a column list, positioned: the i-th mapped element is the
    `colText` of the i-th `(name, b)` pair. -/
theorem colTexts_getElem (cols : List (String × String)) (i : Nat)
    (h : i < cols.length) (h' : i < (cols.map (fun x => (colText x.1 x.2).toList)).length) :
    (cols.map (fun x => (colText x.1 x.2).toList))[i]'h' =
      (colText (cols[i]'h).1 (cols[i]'h).2).toList := by
  simp [List.getElem_map]

/-- **The column-list inversion** (indexed restate): the `, `-joined column
    texts, `splitAppend`-ed with the trailing `]` of the header close, parse
    back to the per-column `(name, type, rest)` triples, where the rest is
    `[']']` exactly at the last index and `[]` elsewhere. – The original draft
    stated this by value equality (`rest = …`), which needs
    `DecidableEq Proto.PType` (mutual inductives don't derive it on this
    toolchain); the indexed formulation with `i = cols.length - 1` dodges it
    entirely. -/
theorem splitAppend_map_parseNamedCol
    (cols : List (String × String))
    (htype : ∀ x ∈ cols, ∃ t : Proto.PType, Emit.Text.typeText t = .ok x.2)
    (i : Nat) (hi : i < cols.length) :
    ((splitAppend (cols.map (fun x => (colText x.1 x.2).toList)) [']']).map parseNamedCol)[i]?
      = some (some ((cols[i]'hi).1,
          (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose,
          if i = cols.length - 1 then [']'] else [])) := by
  let texts : List (List Char) := cols.map (fun x => (colText x.1 x.2).toList)
  have hlen : texts.length = cols.length := by simp [texts]
  have hlen' : texts.length - 1 = cols.length - 1 := by omega
  have hcond : (i = texts.length - 1 ↔ i = cols.length - 1) := by
    constructor
    · intro h; omega
    · intro h; omega
  have htext : texts[i]'(by simpa [hlen] using hi) =
      (colText (cols[i]'hi).1 (cols[i]'hi).2).toList := by
    simp [texts]
  by_cases hlast : i = cols.length - 1
  · let t : Proto.PType := (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose
    have hemit : Emit.Text.typeText t = .ok (cols[i]'hi).2 :=
      (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose_spec
    have hlteq : i = texts.length - 1 := hcond.2 hlast
    rw [List.getElem?_map]
    rw [splitAppend_getElem? texts [']'] i (by simpa [hlen] using hi)]
    simp only [Option.map_some]
    rw [if_pos hlteq]
    rw [htext]
    rw [parseNamedCol_emitted (cols[i]'hi).1 t (cols[i]'hi).2 [']'] hemit (by decide)]
    rw [if_pos hlast]
  · -- the not-last column: the rest is `[]`
    let t : Proto.PType := (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose
    have hemit : Emit.Text.typeText t = .ok (cols[i]'hi).2 :=
      (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose_spec
    have hnotlteq : ¬ i = texts.length - 1 := by
      intro h
      exact hlast (hcond.1 h)
    rw [List.getElem?_map]
    rw [splitAppend_getElem? texts [']'] i (by simpa [hlen] using hi)]
    simp only [Option.map_some]
    rw [if_neg hnotlteq]
    rw [htext]
    rw [parseNamedCol_emitted (cols[i]'hi).1 t (cols[i]'hi).2 [] hemit (by simp)]
    rw [if_neg hlast]

-- ── the typed layer: Proto.Expression → Typed.Expr ──────────────────────

/-!

The wire → typed direction: `Proto.Expression` (what the wire/text carries)
decoded back into the schema-indexed `Substrait.Typed.Expr` GADT — the
inverse of `Typed.Expr.toProto` / `Typed.Args.toProto`.

Deliberate exclusions (the typed grammar has no syntax for them):
- `ifThen` / `cast` / `subquery`: `Typed.Expr` has only `literal`, `field`,
  `call` — the composite proto forms decode to `none`.
- `.null` literal payloads: `LiteralValue` has no null constructor.
- `userDefined` output types: the wire carries an anchor; recovering the
  `(urn, name)` pair needs a type registry the decode context (functions
  only) does not have — `stOfPType` returns `none`.
- `segment != none` field refs: the text grammar has no segment rule and the
  typed layer never produces one.
- `deterministic` / `sessionDependent` sig metadata: `Expr.toProto` erases
  both; decode reconstructs `deterministic := true`, `sessionDependent :=
  false`.  The round-trip statements compare at the Proto level (re-lowering
  the decoded expression), where the erasure is invisible.

Anchors: the decode-side function context `FnInv` is `(anchor, urn, name)`
triples — `fnInvOf` inverts `ExtCtx`'s 1-based `indexOf1` anchoring.

-/

open Substrait.Typed

/-- anchor → (urn, name) — the decode-side inverse of `ExtCtx.functions`'s
    1-based `indexOf1` anchoring. -/
abbrev FnInv := List (Nat × String × String)

/-- The decode-side anchor→(urn, name) table: keys starting at `a`, in
    declaration order (the inverse of `ExtCtx`'s `indexOf1` anchoring). -/
def fnInvGo : Nat → List (String × String) → FnInv
  | _, [] => []
  | a, f :: rest => (a, f.1, f.2) :: fnInvGo (a + 1) rest

/-- Build the decode-side function context from the emission context
    (anchors are 1-based, first-use order — `ExtCtx.indexOf1`'s inverse). -/
def fnInvOf (ctx : ExtCtx) : FnInv := fnInvGo 1 ctx.functions

/-- anchor lookup. -/
def fnOf (inv : FnInv) (a : Nat) : Option (String × String) :=
  (inv.find? (fun e => e.1 == a)).map (fun e => (e.2.1, e.2.2))

/-- Strip nullability: the wire `PType` back to the nullability-free `SType`.
    `userDefined` needs an anchor→type registry (absent here) — `none`. -/
def stOfPType : Proto.PType → Option SType
  | .bool _ => some .bool
  | .i8 _ => some .i8
  | .i16 _ => some .i16
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .fp32 _ => some .fp32
  | .fp64 _ => some .fp64
  | .string _ => some .string
  | .binary _ => some .binary
  | .decimal p s _ => some (.decimal p s)
  | .list e _ => (.list ·) <$> stOfPType e
  | .map k v _ => do
      let k' ← stOfPType k
      let v' ← stOfPType v
      pure (.map k' v')
  | .struct fs _ => (.struct ·) <$> fs.mapM stOfPType
  | .userDefined _ _ _ => none

/-- The wire nullability as a Bool (`false` = required, the typed layer's
    convention). -/
def pTypeNullable (t : Proto.PType) : Bool := nullabilityOf t == .nullable

/-- Build a `HasCol` instance from the runtime schema: the class's `resolves`
    field IS the `get?` proof, so a successful `Schema.get?` manufactures the
    instance the GADT constructors demand. -/
def hasColAt (s : Schema) (i : Nat) (nm : String) (t : SType) (n : Bool)
    (h : Schema.get? s i = some (nm, t, n)) : Substrait.Typed.HasCol s nm t n :=
  { index := i, resolves := h }

/-- Decode a wire literal into the typed literal expression (packed with its
    `(t, n)` indices — `AnyExpr` is the type-erased package).  `null:t` has no
    typed literal — `none`. -/
def decodeLiteral (s : Schema) : Proto.Literal → Option (AnyExpr s)
  | { literalType := .bool b, nullable := n } =>
      some (AnyExpr.mk .bool n (Expr.literal .bool n (.bool b)))
  | { literalType := .i8 v, nullable := n } =>
      some (AnyExpr.mk .i8 n (Expr.literal .i8 n (.i8 v)))
  | { literalType := .i16 v, nullable := n } =>
      some (AnyExpr.mk .i16 n (Expr.literal .i16 n (.i16 v)))
  | { literalType := .i32 v, nullable := n } =>
      some (AnyExpr.mk .i32 n (Expr.literal .i32 n (.i32 v)))
  | { literalType := .i64 v, nullable := n } =>
      some (AnyExpr.mk .i64 n (Expr.literal .i64 n (.i64 v)))
  | { literalType := .fp32 v, nullable := n } =>
      some (AnyExpr.mk .fp32 n (Expr.literal .fp32 n (.fp32 v)))
  | { literalType := .fp64 v, nullable := n } =>
      some (AnyExpr.mk .fp64 n (Expr.literal .fp64 n (.fp64 v)))
  | { literalType := .string v, nullable := n } =>
      some (AnyExpr.mk .string n (Expr.literal .string n (.string v)))
  | { literalType := .binary v, nullable := n } =>
      some (AnyExpr.mk .binary n (Expr.literal .binary n (.binary v)))
  | { literalType := .null _, nullable := _ } => none

/-- The type-erased argument spine (the decode-side package over `Args`, the
    same flattening pattern as `AnyExpr`). -/
inductive AnyArgs (s : Schema) : Type where
  | mk (ts : List (SType × Bool)) (a : Args s ts)

mutual
/-- Decode a wire argument list into the typed spine. -/
def decodeArgs (s : Schema) (inv : FnInv) : List Proto.Expression → Option (AnyArgs s)
  | [] => some (AnyArgs.mk [] Args.nil)
  | e :: rest =>
      match decodeExpr s inv e with
      | some (AnyExpr.mk t n ex) =>
          match decodeArgs s inv rest with
          | some (AnyArgs.mk ts spine) => some (AnyArgs.mk ((t, n) :: ts) (Args.cons t n ex spine))
          | none => none
      | none => none

/-- **The typed decode**: a wire `Proto.Expression` over schema `s`, against
    the decode-side anchor context, yields the packed typed expression (or
    `none` outside the typed grammar — see the exclusions above). -/
def decodeExpr (s : Schema) (inv : FnInv) : Proto.Expression → Option (AnyExpr s)
  | .literal lit => decodeLiteral s lit
  | .field { ordinal := i, segment := none } =>
      match h : s.get? i with
      | some (nm, t, n) =>
          some (AnyExpr.mk t n (@Expr.field s ({ name := nm, ordinal := i } : Column) t n
            (hasColAt s i nm t n h)))
      | none => none
  | .field { ordinal := _, segment := some _ } => none
  | .scalarFunction a args outTy =>
      match fnOf inv a with
      | none => none
      | some (urn, name) =>
          match decodeArgs s inv args with
          | none => none
          | some (AnyArgs.mk ts spine) =>
              match stOfPType outTy with
              | none => none
              | some ret =>
                  let sig := FunctionSig.mkSig name urn ts ret (pTypeNullable outTy) true
                  some (AnyExpr.mk sig.ret sig.retNullable (Expr.call sig spine))
  | .ifThen _ _ | .cast _ _ _ | .subquery _ _ => none
end

/-! ## the typed decode: round-trip evidence -/

/-- Anchor lookup hits the head key. -/
theorem fnOf_go_eq (a : Nat) (f : String × String) (ys : List (String × String)) :
    fnOf (fnInvGo a (f :: ys)) a = some (f.1, f.2) := by
  simp [fnOf, fnInvGo]

/-- Anchor lookup skips a smaller head key. -/
theorem fnOf_go_gt (a k : Nat) (f : String × String) (ys : List (String × String))
    (hk : a < k) :
    fnOf (fnInvGo a (f :: ys)) k = fnOf (fnInvGo (a + 1) ys) k := by
  have hne : (((a, f.1, f.2) : Nat × String × String).1 == k) = false := by
    cases hb : (((a, f.1, f.2) : Nat × String × String).1 == k)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) (Nat.ne_of_lt hk)
  simp only [fnOf, fnInvGo, List.find?_cons]
  cases hb : a == k
  · rfl
  · exact absurd (beq_iff_eq.mp hb) (Nat.ne_of_lt hk)

/-- **Anchor-lookup inversion (kernel-checked)**: a declaration's `indexOf1`
    anchor looks up to exactly that declaration in the decode-side table —
    the emission/decode anchor round trip, general over every context. -/
theorem fnOf_fnInvGo_findIdx : ∀ (a : Nat) (xs : List (String × String)) (x : String × String)
    (i : Nat), xs.findIdx? (fun p => p == x) = some i →
    fnOf (fnInvGo a xs) (a + i) = some x := by
  intro a xs
  induction xs generalizing a with
  | nil => intro x i h; simp at h
  | cons f ys ih =>
    intro x i hfi
    rw [List.findIdx?_cons] at hfi
    by_cases hfx : (f == x) = true
    · rw [if_pos hfx] at hfi
      have hi : 0 = i := Option.some.inj hfi
      subst hi
      rw [Nat.add_zero, fnOf_go_eq]
      have hfx' : f = x := beq_iff_eq.mp hfx
      simp [hfx']
    · rw [if_neg hfx] at hfi
      cases hys : ys.findIdx? (fun p => p == x) with
      | none => rw [hys] at hfi; simp at hfi
      | some j =>
        rw [hys] at hfi
        simp at hfi
        rw [fnOf_go_gt a (a + i) f ys (by omega)]
        rw [show a + i = (a + 1) + j from by omega]
        rw [ih (a + 1) x j hys]

/-! ## the re-encode form: decode → lower recovers the same wire term -/

/-- Re-lowering a decoded argument spine. -/
def argsLower (p : AnyArgs s) (ctx : ExtCtx) : List Proto.Expression :=
  match p with
  | .mk _ spine => spine.toProto ctx

/-- Re-lowering a decoded expression. -/
def anyLower (p : AnyExpr s) (ctx : ExtCtx) : Proto.Expression :=
  match p with
  | .mk _ _ e => e.toProto ctx

-- Ordinal safety: every field reference in `e` points at a schema column
-- (the authoring surface `col` guarantees this — its ordinal IS the
-- `HasCol` index, and `resolves` pins that ordinal in range).  The GADT
-- itself does not enforce it — `Expr.field` takes the column and the
-- instance independently — so the general re-encode theorem carries the
-- predicate explicitly.
mutual
def Expr.okS (ctx : ExtCtx) (s : Schema) : {t : SType} → {n : Bool} → Expr s t n → Prop
  | _, _, .literal .. => True
  | _, _, @Expr.field _ c _ _ _ => s.get? c.ordinal ≠ none
  | _, _, .call sig args =>
      Args.okS ctx s args ∧ stOfPType (toProtoType ctx sig.ret) = some sig.ret

def Args.okS (ctx : ExtCtx) (s : Schema) : {ts : List (SType × Bool)} → Args s ts → Prop
  | _, .nil => True
  | _, .cons _ _ e rest => Expr.okS ctx s e ∧ Args.okS ctx s rest
end

/-- `setNull` preserves the type's shape, so `stOfPType` (which strips
    nullability) cannot see it. -/
private theorem stOfPType_setNull (n : Proto.Nullability) (t : Proto.PType) :
    stOfPType (setNull n t) = stOfPType t := by
  cases t <;> simp [setNull, stOfPType]

/-- `withNullable` is invisible to `stOfPType`. -/
private theorem stOfPType_withNullable (t : Proto.PType) (b : Bool) :
    stOfPType (withNullable t b) = stOfPType t := by
  show stOfPType (setNull (if b then .nullable else .required) t) = stOfPType t
  exact stOfPType_setNull _ _

/-- `setNull` sets the nullability marker. -/
private theorem nullabilityOf_setNull (n : Proto.Nullability) (t : Proto.PType) :
    nullabilityOf (setNull n t) = n := by
  cases t <;> rfl

/-- `pTypeNullable` inverts the nullability `withNullable` sets. -/
private theorem pTypeNullable_withNullable (t : Proto.PType) (b : Bool) :
    pTypeNullable (withNullable t b) = b := by
  show (nullabilityOf (setNull (if b then .nullable else .required) t) == .nullable) = b
  rw [nullabilityOf_setNull]
  cases b <;> rfl

/-- **Literal inversion (kernel-checked)**: decoding the lowered literal
    recovers the packed typed literal — general over the whole `LiteralValue`
    family. -/
theorem decodeLiteral_of_toProto (v : LiteralValue t) (nv : Bool) (s : Schema) :
    decodeLiteral s { literalType := toProtoLiteralValue v, nullable := nv } =
      some (AnyExpr.mk t nv (Expr.literal t nv v)) := by
  cases v <;> rfl

/-- The `get?`-level form of the field inversion (the instance-free slice the
    HasCol version rests on). -/
theorem decodeExpr_field_of_get (s : Schema) (i : Nat) (nm : String) (t : SType) (n : Bool)
    (h : Schema.get? s i = some (nm, t, n)) :
    decodeExpr s [] (Proto.Expression.field { ordinal := i, segment := none }) =
      some (AnyExpr.mk t n (@Expr.field s ({ name := nm, ordinal := i } : Column) t n
        (hasColAt s i nm t n h))) := by
  simp only [decodeExpr]
  split
  · next nm' t' n' heq =>
      have ht : (nm, t, n) = (nm', t', n') := Option.some.inj (h.symm.trans heq)
      have h1 : nm = nm' := congrArg Prod.fst ht
      have h23 : (t, n) = (t', n') := congrArg Prod.snd ht
      have h2 : t = t' := congrArg Prod.fst h23
      have h3 : n = n' := congrArg Prod.snd h23
      subst h1
      subst h2
      subst h3
      rfl
  · next heq =>
      rw [heq] at h
      simp at h

/-- **Field inversion (kernel-checked)**: decoding the lowered field reference
    recovers the packed typed column reference — general over every schema,
    with the `HasCol` instance's own `resolves` proof supplying the ordinal
    lookup (the class field IS the correctness statement). -/
theorem decodeExpr_field_of_toProto (s : Schema) (nm : String) (t : SType) (n : Bool)
    (h : Substrait.Typed.HasCol s nm t n) :
    decodeExpr s [] (Proto.Expression.field { ordinal := h.index, segment := none }) =
      some (pack (@Expr.field s { name := nm, ordinal := h.index } t n h)) := by
  exact decodeExpr_field_of_get s h.index nm t n h.resolves

/-! ## the master re-encode theorem: decode → lower recovers the wire term -/

/- The wire-level round trip: for EVERY typed expression `e` (with its field
   references ordinal-safe and its call output types decodable — the `okS`
   predicate, which the authoring surface `col`/`call` always satisfies),
   decoding `e`'s lowered form and re-lowering the result recovers the same
   wire term.  This is the composition the binary/text wire actually
   consumes: anchors and ordinals round-trip; names (erased by the wire
   shape) are re-derived from the schema. -/
mutual
/-- The args re-encode: decoding a spine's lowered form and re-lowering
    the decode recovers the SAME wire list. -/
theorem decodeArgs_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {ts : List (SType × Bool)} (a : Args s ts), Args.okS ctx s a →
      (decodeArgs s inv (a.toProto ctx)).map (fun p => argsLower p ctx) = some (a.toProto ctx) := by
  intro ts a
  match a with
  | .nil =>
      intro _
      simp [Args.toProto, decodeArgs, argsLower]
  | .cons t n e rest =>
      intro hok
      have he : Expr.okS ctx s e := hok.1
      have hrest : Args.okS ctx s rest := hok.2
      show Option.map (fun p => argsLower p ctx)
          (decodeArgs s inv (e.toProto ctx :: rest.toProto ctx)) =
        some (e.toProto ctx :: rest.toProto ctx)
      simp only [decodeArgs]
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none =>
          have hinv := decodeExpr_reEnc s inv ctx hfn e he
          rw [hd] at hinv
          simp at hinv
      | some p =>
          cases p with
          | mk t' n' ex =>
              simp only [hd]
              have hlow : ex.toProto ctx = e.toProto ctx := by
                have hinv := decodeExpr_reEnc s inv ctx hfn e he
                rw [hd] at hinv
                simpa [anyLower] using hinv
              cases hd2 : decodeArgs s inv (rest.toProto ctx) with
              | none =>
                  have hinv := decodeArgs_reEnc s inv ctx hfn rest hrest
                  rw [hd2] at hinv
                  simp at hinv
              | some q =>
                  cases q with
                  | mk ts' spine =>
                      simp only [hd2]
                      have hlow2 : spine.toProto ctx = rest.toProto ctx := by
                        have hinv := decodeArgs_reEnc s inv ctx hfn rest hrest
                        rw [hd2] at hinv
                        simpa [argsLower] using hinv
                      show some ((Args.cons t' n' ex spine).toProto ctx) = _
                      simp only [Args.toProto]
                      rw [hlow, hlow2]

/-- THE re-encode theorem: for EVERY typed expression `e` (with its
    field references ordinal-safe and its call output types decodable —
    the `okS` predicate, which the authoring surface `col`/`call`
    always satisfies), decoding `e`'s lowered form and re-lowering the
    result recovers the same wire term. This is the composition the
    binary/text wire actually consumes: anchors and ordinals
    round-trip; names (erased by the wire shape) are re-derived from
    the schema. -/
theorem decodeExpr_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okS ctx s e →
      (decodeExpr s inv (e.toProto ctx)).map (fun p => anyLower p ctx) = some (e.toProto ctx) := by
  intro t n e
  match e with
  | .literal t' nv v =>
      intro _
      show (decodeExpr s inv (Proto.Expression.literal
        { literalType := toProtoLiteralValue v, nullable := nv })).map (fun p => anyLower p ctx) =
        some (Proto.Expression.literal { literalType := toProtoLiteralValue v, nullable := nv })
      rw [show decodeExpr s inv (Proto.Expression.literal
          { literalType := toProtoLiteralValue v, nullable := nv }) =
        decodeLiteral s { literalType := toProtoLiteralValue v, nullable := nv } from rfl,
        decodeLiteral_of_toProto v nv s]
      simp [anyLower, Expr.toProto]
  | @Expr.field _ c _ _ h =>
      intro hok
      show (decodeExpr s inv (Proto.Expression.field
        { ordinal := c.ordinal, segment := none })).map (fun p => anyLower p ctx) =
        some (Proto.Expression.field { ordinal := c.ordinal, segment := none })
      simp only [decodeExpr]
      split
      · next nm t' n' h1 =>
          simp [anyLower, Expr.toProto]
      · next h1 =>
          exact absurd h1 hok
  | .call sig args =>
      intro hok
      have hargs : Args.okS ctx s args := hok.1
      have hret : stOfPType (toProtoType ctx sig.ret) = some sig.ret := hok.2
      have hfn' := hfn sig
      show Option.map (fun p => anyLower p ctx)
          (decodeExpr s inv (Proto.Expression.scalarFunction
            (ctx.functionAnchor sig.urn sig.name) (args.toProto ctx)
            (withNullable (toProtoType ctx sig.ret) sig.retNullable))) =
        some (Proto.Expression.scalarFunction (ctx.functionAnchor sig.urn sig.name)
          (args.toProto ctx) (withNullable (toProtoType ctx sig.ret) sig.retNullable))
      simp only [decodeExpr, hfn']
      cases hd : decodeArgs s inv (args.toProto ctx) with
      | none =>
          have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
          rw [hd] at hinv
          simp at hinv
      | some q =>
          cases q with
          | mk ts' spine =>
              simp only [hd]
              have hlow2 : spine.toProto ctx = args.toProto ctx := by
                have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
                rw [hd] at hinv
                simpa [argsLower] using hinv
              have hret' : stOfPType (withNullable (toProtoType ctx sig.ret) sig.retNullable) =
                  some sig.ret := by
                rw [stOfPType_withNullable]
                exact hret
              rw [hret']
              simp [anyLower, Expr.toProto, FunctionSig.mkSig, pTypeNullable_withNullable,
                hlow2]

end

-- ── the typed rel decode: Proto.Rel → Typed.Rel ────────────────────────────

/-!

The wire relation `Proto.Rel` decoded back into the schema-indexed
`Substrait.Typed.Rel` GADT — the inverse of `Typed.Rel.toProtoWith`, the same
`decode → re-lower = id` discipline as the expression layer above.

Deliberate exclusions / canonicalizations (the typed grammar has no syntax
for them):
- `cross`, `extensionLeaf`, `extensionMulti`: no `Typed.Rel` constructor —
  `none`.
- `ReadRel.readType = virtualTable`: the typed layer has only named-table
  reads — `none`; a named-table path longer than one element is rejected too
  (`Typed.Rel.read` carries a single table name).
- `RelCommon.emit = direct` decodes to the typed `emit := none` — the same
  canonicalization the text decoder documents (direct vs absent emit kinds
  are indistinguishable in the typed grammar).
- `ProjectRel` carries no column names: decoded projections get placeholder
  names `""` (the wire never sees them; `projectOut` positions are the
  contract).  Sort keys keep only the ordinal + direction the wire carries;
  the name is re-derived from the decoded input schema.
- Square-input nodes (`filter`/`aggregate`/`sort`/`fetch`) demand the decoded
  input's input/output schemas to agree — a wire filter over a width-changing
  child is valid Substrait but outside the typed grammar, so it decodes to
  `none` (the typed `filter` literally takes `Rel s s`).
- `WriteRel.tableSchema` present but undecodable → `none`; absent → typed
  `none`.
- `ExtensionSingleRel.detail = none` → `none` (the typed ctor requires a
  detail string; the lowering always writes one).

Schema equality checks use a hand-rolled `DecidableEq SType` (this module —
`Schema.lean` deliberately ships none, and Lean's deriving handlers refuse
mutual inductives).

Termination note: the mutual-block `Proto.Rel` defeats Lean's structural
recursion, its derived `sizeOf` simproc disagrees with the instance funs, and
`sizeOf` in a definition body hits an LCNF codegen failure — so the recursion
is well-founded on the ACTUAL `sizeOf` instance, with the decreasing goals
discharged by the `wf*_size` lemmas (proved from the instance funs,
simproc-free).

-/

-- `DecidableEq` for the schema component type — the decode-side square/set
-- schema checks need a decidable equality; hand-rolled (mutual inductives
-- are refused by the deriving handlers).
mutual
def decEqListSType : (xs ys : List SType) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs', y :: ys' =>
      match SType.decEq? x y with
      | isTrue hx =>
          match decEqListSType xs' ys' with
          | isTrue hxs => isTrue (by rw [hx, hxs])
          | isFalse hxs => isFalse (by intro hyp; injection hyp with _ h; exact hxs h)
      | isFalse hx => isFalse (by intro hyp; injection hyp with h _; exact hx h)
  | [], _ :: _ => isFalse (by intro hyp; cases hyp)
  | _ :: _, [] => isFalse (by intro hyp; cases hyp)

def decEqListSParam : (xs ys : List SParam) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs', y :: ys' =>
      match SParam.decEq? x y with
      | isTrue hx =>
          match decEqListSParam xs' ys' with
          | isTrue hxs => isTrue (by rw [hx, hxs])
          | isFalse hxs => isFalse (by intro hyp; injection hyp with _ h; exact hxs h)
      | isFalse hx => isFalse (by intro hyp; injection hyp with h _; exact hx h)
  | [], _ :: _ => isFalse (by intro hyp; cases hyp)
  | _ :: _, [] => isFalse (by intro hyp; cases hyp)

def SType.decEq? : (a b : SType) → Decidable (a = b)
  | .bool, .bool => isTrue rfl
  | .i8, .i8 => isTrue rfl
  | .i16, .i16 => isTrue rfl
  | .i32, .i32 => isTrue rfl
  | .i64, .i64 => isTrue rfl
  | .fp32, .fp32 => isTrue rfl
  | .fp64, .fp64 => isTrue rfl
  | .string, .string => isTrue rfl
  | .binary, .binary => isTrue rfl
  | .decimal p s, .decimal p' s' =>
      if h1 : p = p' then
        if h2 : s = s' then isTrue (by rw [h1, h2])
        else isFalse (by intro hyp; injection hyp with _ h; exact h2 h)
      else isFalse (by intro hyp; injection hyp with h _; exact h1 h)
  | .list e, .list e' =>
      match SType.decEq? e e' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .map k v, .map k' v' =>
      match SType.decEq? k k' with
      | isTrue hk =>
          match SType.decEq? v v' with
          | isTrue hv => isTrue (by rw [hk, hv])
          | isFalse hv => isFalse (by intro hyp; injection hyp with _ h; exact hv h)
      | isFalse hk => isFalse (by intro hyp; injection hyp with h _; exact hk h)
  | .struct fs, .struct fs' =>
      match decEqListSType fs fs' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .userDefined u n p, .userDefined u' n' p' =>
      if hu : u = u' then
        if hn : n = n' then
          match decEqListSParam p p' with
          | isTrue hp => isTrue (by rw [hu, hn, hp])
          | isFalse hp => isFalse (by intro hyp; injection hyp with _ _ h; exact hp h)
        else isFalse (by intro hyp; injection hyp with _ h _; exact hn h)
      else isFalse (by intro hyp; injection hyp with h _ _; exact hu h)
  | .bool, .i8 => isFalse (by intro hyp; cases hyp)
  | .bool, .i16 => isFalse (by intro hyp; cases hyp)
  | .bool, .i32 => isFalse (by intro hyp; cases hyp)
  | .bool, .i64 => isFalse (by intro hyp; cases hyp)
  | .bool, .fp32 => isFalse (by intro hyp; cases hyp)
  | .bool, .fp64 => isFalse (by intro hyp; cases hyp)
  | .bool, .string => isFalse (by intro hyp; cases hyp)
  | .bool, .binary => isFalse (by intro hyp; cases hyp)
  | .bool, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .bool, .list _ => isFalse (by intro hyp; cases hyp)
  | .bool, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .bool, .struct _ => isFalse (by intro hyp; cases hyp)
  | .bool, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .i8, .bool => isFalse (by intro hyp; cases hyp)
  | .i8, .i16 => isFalse (by intro hyp; cases hyp)
  | .i8, .i32 => isFalse (by intro hyp; cases hyp)
  | .i8, .i64 => isFalse (by intro hyp; cases hyp)
  | .i8, .fp32 => isFalse (by intro hyp; cases hyp)
  | .i8, .fp64 => isFalse (by intro hyp; cases hyp)
  | .i8, .string => isFalse (by intro hyp; cases hyp)
  | .i8, .binary => isFalse (by intro hyp; cases hyp)
  | .i8, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .i8, .list _ => isFalse (by intro hyp; cases hyp)
  | .i8, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .i8, .struct _ => isFalse (by intro hyp; cases hyp)
  | .i8, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .i16, .bool => isFalse (by intro hyp; cases hyp)
  | .i16, .i8 => isFalse (by intro hyp; cases hyp)
  | .i16, .i32 => isFalse (by intro hyp; cases hyp)
  | .i16, .i64 => isFalse (by intro hyp; cases hyp)
  | .i16, .fp32 => isFalse (by intro hyp; cases hyp)
  | .i16, .fp64 => isFalse (by intro hyp; cases hyp)
  | .i16, .string => isFalse (by intro hyp; cases hyp)
  | .i16, .binary => isFalse (by intro hyp; cases hyp)
  | .i16, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .i16, .list _ => isFalse (by intro hyp; cases hyp)
  | .i16, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .i16, .struct _ => isFalse (by intro hyp; cases hyp)
  | .i16, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .i32, .bool => isFalse (by intro hyp; cases hyp)
  | .i32, .i8 => isFalse (by intro hyp; cases hyp)
  | .i32, .i16 => isFalse (by intro hyp; cases hyp)
  | .i32, .i64 => isFalse (by intro hyp; cases hyp)
  | .i32, .fp32 => isFalse (by intro hyp; cases hyp)
  | .i32, .fp64 => isFalse (by intro hyp; cases hyp)
  | .i32, .string => isFalse (by intro hyp; cases hyp)
  | .i32, .binary => isFalse (by intro hyp; cases hyp)
  | .i32, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .i32, .list _ => isFalse (by intro hyp; cases hyp)
  | .i32, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .i32, .struct _ => isFalse (by intro hyp; cases hyp)
  | .i32, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .i64, .bool => isFalse (by intro hyp; cases hyp)
  | .i64, .i8 => isFalse (by intro hyp; cases hyp)
  | .i64, .i16 => isFalse (by intro hyp; cases hyp)
  | .i64, .i32 => isFalse (by intro hyp; cases hyp)
  | .i64, .fp32 => isFalse (by intro hyp; cases hyp)
  | .i64, .fp64 => isFalse (by intro hyp; cases hyp)
  | .i64, .string => isFalse (by intro hyp; cases hyp)
  | .i64, .binary => isFalse (by intro hyp; cases hyp)
  | .i64, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .i64, .list _ => isFalse (by intro hyp; cases hyp)
  | .i64, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .i64, .struct _ => isFalse (by intro hyp; cases hyp)
  | .i64, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .fp32, .bool => isFalse (by intro hyp; cases hyp)
  | .fp32, .i8 => isFalse (by intro hyp; cases hyp)
  | .fp32, .i16 => isFalse (by intro hyp; cases hyp)
  | .fp32, .i32 => isFalse (by intro hyp; cases hyp)
  | .fp32, .i64 => isFalse (by intro hyp; cases hyp)
  | .fp32, .fp64 => isFalse (by intro hyp; cases hyp)
  | .fp32, .string => isFalse (by intro hyp; cases hyp)
  | .fp32, .binary => isFalse (by intro hyp; cases hyp)
  | .fp32, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .fp32, .list _ => isFalse (by intro hyp; cases hyp)
  | .fp32, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .fp32, .struct _ => isFalse (by intro hyp; cases hyp)
  | .fp32, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .fp64, .bool => isFalse (by intro hyp; cases hyp)
  | .fp64, .i8 => isFalse (by intro hyp; cases hyp)
  | .fp64, .i16 => isFalse (by intro hyp; cases hyp)
  | .fp64, .i32 => isFalse (by intro hyp; cases hyp)
  | .fp64, .i64 => isFalse (by intro hyp; cases hyp)
  | .fp64, .fp32 => isFalse (by intro hyp; cases hyp)
  | .fp64, .string => isFalse (by intro hyp; cases hyp)
  | .fp64, .binary => isFalse (by intro hyp; cases hyp)
  | .fp64, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .fp64, .list _ => isFalse (by intro hyp; cases hyp)
  | .fp64, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .fp64, .struct _ => isFalse (by intro hyp; cases hyp)
  | .fp64, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .string, .bool => isFalse (by intro hyp; cases hyp)
  | .string, .i8 => isFalse (by intro hyp; cases hyp)
  | .string, .i16 => isFalse (by intro hyp; cases hyp)
  | .string, .i32 => isFalse (by intro hyp; cases hyp)
  | .string, .i64 => isFalse (by intro hyp; cases hyp)
  | .string, .fp32 => isFalse (by intro hyp; cases hyp)
  | .string, .fp64 => isFalse (by intro hyp; cases hyp)
  | .string, .binary => isFalse (by intro hyp; cases hyp)
  | .string, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .string, .list _ => isFalse (by intro hyp; cases hyp)
  | .string, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .string, .struct _ => isFalse (by intro hyp; cases hyp)
  | .string, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .binary, .bool => isFalse (by intro hyp; cases hyp)
  | .binary, .i8 => isFalse (by intro hyp; cases hyp)
  | .binary, .i16 => isFalse (by intro hyp; cases hyp)
  | .binary, .i32 => isFalse (by intro hyp; cases hyp)
  | .binary, .i64 => isFalse (by intro hyp; cases hyp)
  | .binary, .fp32 => isFalse (by intro hyp; cases hyp)
  | .binary, .fp64 => isFalse (by intro hyp; cases hyp)
  | .binary, .string => isFalse (by intro hyp; cases hyp)
  | .binary, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .binary, .list _ => isFalse (by intro hyp; cases hyp)
  | .binary, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .binary, .struct _ => isFalse (by intro hyp; cases hyp)
  | .binary, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .bool => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .i8 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .i16 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .i32 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .i64 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .fp32 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .fp64 => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .string => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .binary => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .list _ => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .struct _ => isFalse (by intro hyp; cases hyp)
  | .decimal _ _, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .list _, .bool => isFalse (by intro hyp; cases hyp)
  | .list _, .i8 => isFalse (by intro hyp; cases hyp)
  | .list _, .i16 => isFalse (by intro hyp; cases hyp)
  | .list _, .i32 => isFalse (by intro hyp; cases hyp)
  | .list _, .i64 => isFalse (by intro hyp; cases hyp)
  | .list _, .fp32 => isFalse (by intro hyp; cases hyp)
  | .list _, .fp64 => isFalse (by intro hyp; cases hyp)
  | .list _, .string => isFalse (by intro hyp; cases hyp)
  | .list _, .binary => isFalse (by intro hyp; cases hyp)
  | .list _, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .list _, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .list _, .struct _ => isFalse (by intro hyp; cases hyp)
  | .list _, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .map _ _, .bool => isFalse (by intro hyp; cases hyp)
  | .map _ _, .i8 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .i16 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .i32 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .i64 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .fp32 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .fp64 => isFalse (by intro hyp; cases hyp)
  | .map _ _, .string => isFalse (by intro hyp; cases hyp)
  | .map _ _, .binary => isFalse (by intro hyp; cases hyp)
  | .map _ _, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .map _ _, .list _ => isFalse (by intro hyp; cases hyp)
  | .map _ _, .struct _ => isFalse (by intro hyp; cases hyp)
  | .map _ _, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .struct _, .bool => isFalse (by intro hyp; cases hyp)
  | .struct _, .i8 => isFalse (by intro hyp; cases hyp)
  | .struct _, .i16 => isFalse (by intro hyp; cases hyp)
  | .struct _, .i32 => isFalse (by intro hyp; cases hyp)
  | .struct _, .i64 => isFalse (by intro hyp; cases hyp)
  | .struct _, .fp32 => isFalse (by intro hyp; cases hyp)
  | .struct _, .fp64 => isFalse (by intro hyp; cases hyp)
  | .struct _, .string => isFalse (by intro hyp; cases hyp)
  | .struct _, .binary => isFalse (by intro hyp; cases hyp)
  | .struct _, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .struct _, .list _ => isFalse (by intro hyp; cases hyp)
  | .struct _, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .struct _, .userDefined _ _ _ => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .bool => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .i8 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .i16 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .i32 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .i64 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .fp32 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .fp64 => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .string => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .binary => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .decimal _ _ => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .list _ => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .map _ _ => isFalse (by intro hyp; cases hyp)
  | .userDefined _ _ _, .struct _ => isFalse (by intro hyp; cases hyp)
def SParam.decEq? : (a b : SParam) → Decidable (a = b)
  | .boolean b, .boolean b' =>
      if h : b = b' then isTrue (by rw [h])
      else isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .integer i, .integer i' =>
      if h : i = i' then isTrue (by rw [h])
      else isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .string s, .string s' =>
      if h : s = s' then isTrue (by rw [h])
      else isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .enum e, .enum e' =>
      if h : e = e' then isTrue (by rw [h])
      else isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .null t, .null t' =>
      match SType.decEq? t t' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .dataType t, .dataType t' =>
      match SType.decEq? t t' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hyp; injection hyp with h'; exact h h')
  | .boolean _, .integer _ => isFalse (by intro hyp; cases hyp)
  | .boolean _, .string _ => isFalse (by intro hyp; cases hyp)
  | .boolean _, .enum _ => isFalse (by intro hyp; cases hyp)
  | .boolean _, .null _ => isFalse (by intro hyp; cases hyp)
  | .boolean _, .dataType _ => isFalse (by intro hyp; cases hyp)
  | .integer _, .boolean _ => isFalse (by intro hyp; cases hyp)
  | .integer _, .string _ => isFalse (by intro hyp; cases hyp)
  | .integer _, .enum _ => isFalse (by intro hyp; cases hyp)
  | .integer _, .null _ => isFalse (by intro hyp; cases hyp)
  | .integer _, .dataType _ => isFalse (by intro hyp; cases hyp)
  | .string _, .boolean _ => isFalse (by intro hyp; cases hyp)
  | .string _, .integer _ => isFalse (by intro hyp; cases hyp)
  | .string _, .enum _ => isFalse (by intro hyp; cases hyp)
  | .string _, .null _ => isFalse (by intro hyp; cases hyp)
  | .string _, .dataType _ => isFalse (by intro hyp; cases hyp)
  | .enum _, .boolean _ => isFalse (by intro hyp; cases hyp)
  | .enum _, .integer _ => isFalse (by intro hyp; cases hyp)
  | .enum _, .string _ => isFalse (by intro hyp; cases hyp)
  | .enum _, .null _ => isFalse (by intro hyp; cases hyp)
  | .enum _, .dataType _ => isFalse (by intro hyp; cases hyp)
  | .null _, .boolean _ => isFalse (by intro hyp; cases hyp)
  | .null _, .integer _ => isFalse (by intro hyp; cases hyp)
  | .null _, .string _ => isFalse (by intro hyp; cases hyp)
  | .null _, .enum _ => isFalse (by intro hyp; cases hyp)
  | .null _, .dataType _ => isFalse (by intro hyp; cases hyp)
  | .dataType _, .boolean _ => isFalse (by intro hyp; cases hyp)
  | .dataType _, .integer _ => isFalse (by intro hyp; cases hyp)
  | .dataType _, .string _ => isFalse (by intro hyp; cases hyp)
  | .dataType _, .enum _ => isFalse (by intro hyp; cases hyp)
  | .dataType _, .null _ => isFalse (by intro hyp; cases hyp)
end

instance : DecidableEq SType := SType.decEq?
instance : DecidableEq SParam := SParam.decEq?

/-- The type-erased relation package (the `AnyExpr` pattern at the rel
    level): `Rel` is indexed by input/output schemas, heterogeneous decode
    results erase both indices. -/
inductive AnyRel : Type where
  | mk (inS outS : Schema) (r : Rel inS outS)

/-- Re-lowering a decoded rel (the wire-level comparison point). -/
def relLower (a : AnyRel) (ctx : ExtCtx) : Proto.Rel :=
  match a with
  | .mk _ _ r => r.toProtoWith ctx

/-- Cast a rel to its square form (`s = s'` pinned). -/
def Rel.castSq {s s' : Schema} (h : s = s') (r : Rel s s') : Rel s s :=
  match h with | rfl => r

/-- Cast a rel across two schema equalities (the `set` shape). -/
def Rel.cast2 {s1 s1' s2 s2' : Schema} (h1 : s1 = s2) (h2 : s1' = s2')
    (r : Rel s2 s2') : Rel s1 s1' :=
  match h1, h2 with | rfl, rfl => r

/-- The cast is invisible to lowering (used by the master theorem). -/
theorem Rel.castSq_toProtoWith {s s' : Schema} (h : s = s') (r : Rel s s') (ctx : ExtCtx) :
    (Rel.castSq h r).toProtoWith ctx = r.toProtoWith ctx := by
  cases h; rfl

/-- The two-schema cast is invisible to lowering. -/
theorem Rel.cast2_toProtoWith {s1 s1' s2 s2' : Schema} (h1 : s1 = s2) (h2 : s1' = s2')
    (r : Rel s2 s2') (ctx : ExtCtx) :
    (Rel.cast2 h1 h2 r).toProtoWith ctx = r.toProtoWith ctx := by
  cases h1; cases h2; rfl

/-- A decoded rel packaged with its (proven-equal) input/output schema — the
    shape the square-input nodes (`filter`/`aggregate`/`sort`/`fetch`) demand.
    (Lean patterns cannot bind one variable twice, so the square package —
    not a repeated-variable pattern — carries the equality.) -/
structure SqRel where
  schema : Schema
  rel : Rel schema schema

def squareOf : AnyRel → Option SqRel
  | .mk s s' r => if h : s = s' then some ⟨s, Rel.castSq h r⟩ else none

/-- Decode a wire `NamedStruct` back into a schema: names and field types
    must have the same length, every field type must decode (`stOfPType`),
    nullability from the wire marker. -/
def schemaOfFields : List String → List Proto.PType → Option Schema
  | [], [] => some []
  | name :: names, t :: ts =>
      match stOfPType t with
      | none => none
      | some t' =>
          match schemaOfFields names ts with
          | none => none
          | some rest => some ((name, t', pTypeNullable t) :: rest)
  | _, _ => none

/-- Read-schema well-formedness: every column's lowered wire type decodes
    back to it.  The read branch's re-encode hypothesis. -/
def schemaOk (ctx : ExtCtx) (sc : Schema) : Prop :=
  ∀ c ∈ sc, stOfPType (toProtoColType ctx c) = some c.2.1

/-- The schema inversion: a well-formed schema's lowering decodes back to it. -/
theorem schemaOfFields_of_toProto (ctx : ExtCtx) :
    ∀ (sc : Schema), schemaOk ctx sc →
      schemaOfFields sc.names (sc.map (toProtoColType ctx)) = some sc := by
  intro sc
  induction sc with
  | nil => intro _; rfl
  | cons c sc ih =>
      intro hok
      obtain ⟨nm, t, n⟩ := c
      have hc : stOfPType (toProtoColType ctx (nm, t, n)) = some t := hok _ (by simp)
      have hnull : pTypeNullable (toProtoColType ctx (nm, t, n)) = n := by
        show pTypeNullable (withNullable (toProtoType ctx t) n) = n
        rw [pTypeNullable_withNullable]
      simp only [List.map_cons, Schema.names, schemaOfFields, hc, hnull,
        ih (fun c2 hc2 => hok c2 (by simp [hc2]))]

/-- The wire emit kind back to the typed mapping (`.direct` canonicalized to
    `none` — the documented lossiness; the lowering never writes `.direct`). -/
def emitOf : Option Proto.RelCommon → Option (List Nat)
  | some { emit := some (.emit m), advancedExtension := _ } => some m
  | _ => none

/-- Re-pack a decoded argument spine into the type-erased list (the
    `Measure.args` shape). -/
def argsPack {s : Schema} : {ts : List (SType × Bool)} → Args s ts → List (AnyExpr s)
  | _, .nil => []
  | _, .cons t n e rest => AnyExpr.mk t n e :: argsPack rest

/-- The wire argument list of a type-erased expression list. -/
def anyExprsLower {s : Schema} (xs : List (AnyExpr s)) (ctx : ExtCtx) :
    List Proto.Expression :=
  xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)

/-- The cons step of `anyExprsLower` (the helpers' iota-exposing rewrite). -/
theorem anyExprsLower_cons {s : Schema} (x : AnyExpr s) (xs : List (AnyExpr s))
    (ctx : ExtCtx) :
    anyExprsLower (x :: xs) ctx =
      (match x with | .mk _ _ e => e.toProto ctx) :: anyExprsLower xs ctx := rfl

/-- Decode a projection list (placeholder names — the wire carries none). -/
def decodeProjections (s : Schema) (inv : FnInv) :
    List Proto.Expression → Option (List (Projection s))
  | [] => some []
  | e :: rest =>
      match decodeExpr s inv e with
      | some (AnyExpr.mk t n ex) =>
          match decodeProjections s inv rest with
          | some ps => some ({ name := "", dtype := t, nullable := n, expr := ex } :: ps)
          | none => none
      | none => none

/-- Decode a grouping-key list. -/
def decodeAnyExprs (s : Schema) (inv : FnInv) :
    List Proto.Expression → Option (List (AnyExpr s))
  | [] => some []
  | e :: rest =>
      match decodeExpr s inv e with
      | some x =>
          match decodeAnyExprs s inv rest with
          | some xs => some (x :: xs)
          | none => none
      | none => none

/-- Lower a measure to its wire shape (the `ToProto` aggregate arm's
    per-measure slice, factored for the round-trip theorem). -/
def measureLower {s : Schema} (ctx : ExtCtx) (m : Measure s) : Proto.AggregateMeasure :=
  { measure := { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                 args := anyExprsLower m.args ctx
                 outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } }

/-- The `ToProto` grouping arm's map IS `anyExprsLower` (the wire-eq bridge). -/
theorem groupings_wire_eq {s : Schema} (ctx : ExtCtx) (xs : List (AnyExpr s)) :
    xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
      anyExprsLower xs ctx := rfl

/-- The `ToProto` measures arm's map IS `measureLower`-mapped (the wire-eq
    bridge). -/
theorem measures_wire_eq {s : Schema} (ctx : ExtCtx) (ms : List (Measure s)) :
    ms.map (fun m =>
      { measure :=
          { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
            args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
            outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } }) =
      ms.map (measureLower ctx) := rfl

/-- Decode a measure list: anchor lookup + argument decode + output type
    decode per measure. -/
def decodeMeasures (s : Schema) (inv : FnInv) :
    List Proto.AggregateMeasure → Option (List (Measure s))
  | [] => some []
  | ⟨am⟩ :: rest =>
      match fnOf inv am.functionReference with
      | none => none
      | some (urn, name) =>
          match decodeArgs s inv am.args with
          | some (AnyArgs.mk ts spine) =>
              match stOfPType am.outputType with
              | some ret =>
                  match decodeMeasures s inv rest with
                  | some ms =>
                      some ({ sig := FunctionSig.mkSig name urn ts ret
                                (pTypeNullable am.outputType) true
                              args := argsPack spine } :: ms)
                  | none => none
              | none => none
          | none => none

/-- Lower a sort key to its wire shape (the `ToProto` sort arm's per-key
    slice). -/
def sortFieldLower {s : Schema} (k : SortKey s) : Proto.SortField :=
  ⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none }, k.direction⟩

/-- Decode a sort-key list: every sort expression must be a plain field
    reference with its ordinal inside the decoded input schema (the typed
    `SortKey` has no expression support). -/
def decodeSortKeys (s : Schema) : List Proto.SortField → Option (List (SortKey s))
  | [] => some []
  | ⟨.field { ordinal := i, segment := none }, dir⟩ :: rest =>
      match s.get? i with
      | some (nm, _, _) =>
          match decodeSortKeys s rest with
          | some ks => some ({ col := { name := nm, ordinal := i }, direction := dir } :: ks)
          | none => none
      | none => none
  | _ :: _ => none

/-! ## the size facts the decode's well-founded recursion needs -/

/-- A wire rel's children are strictly smaller in the actual `sizeOf`
    instance (proved from the instance funs — the derived `sizeOf` simproc
    disagrees with itself on this mutual block, so no `simp [sizeOf]`). -/
theorem wf_filter_size (fr : Proto.FilterRel) :
    sizeOf fr.input < sizeOf (Proto.Rel.filter fr) := by
  cases fr with
  | mk c i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_project_size (pr : Proto.ProjectRel) :
    sizeOf pr.input < sizeOf (Proto.Rel.project pr) := by
  cases pr with
  | mk e i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_aggregate_size (ar : Proto.AggregateRel) :
    sizeOf ar.input < sizeOf (Proto.Rel.aggregate ar) := by
  cases ar with
  | mk g m i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_sort_size (sr : Proto.SortRel) :
    sizeOf sr.input < sizeOf (Proto.Rel.sort sr) := by
  cases sr with
  | mk k i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_fetch_size (fr : Proto.FetchRel) :
    sizeOf fr.input < sizeOf (Proto.Rel.fetch fr) := by
  cases fr with
  | mk l o i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_join_size (jr : Proto.JoinRel) :
    sizeOf jr.left < sizeOf (Proto.Rel.join jr) ∧
      sizeOf jr.right < sizeOf (Proto.Rel.join jr) := by
  cases jr with
  | mk jt l r c pf cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_write_size (wr : Proto.WriteRel) :
    sizeOf wr.input < sizeOf (Proto.Rel.write wr) := by
  cases wr with
  | mk tn op ts i cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_extensionSingle_size (er : Proto.ExtensionSingleRel) :
    sizeOf er.input < sizeOf (Proto.Rel.extensionSingle er) := by
  cases er with
  | mk i d cm =>
      unfold sizeOf
      simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24]
      omega

theorem wf_set_size (sr : Proto.SetRel) (l r : Proto.Rel) (hI : sr.inputs = [l, r]) :
    sizeOf l < sizeOf (Proto.Rel.set sr) ∧ sizeOf r < sizeOf (Proto.Rel.set sr) := by
  cases sr with
  | mk op inputs cm =>
      subst hI
      cases op <;>
        unfold sizeOf <;>
        simp only [Proto.Rel._sizeOf_inst, Proto.EmitKind._sizeOf_24,
          Proto.SetRel._sizeOf_inst, Proto.EmitKind._sizeOf_6] <;>
        omega

/-- **The typed rel decode**: a wire `Proto.Rel` decoded back into the packed
    typed relation (or `none` outside the typed grammar — see the exclusions
    above).  The child schemas come from the decode; every node that indexes
    an expression over its input schema uses the decoded child schema. -/
def decodeRel (inv : FnInv) : Proto.Rel → Option AnyRel
  | .read r =>
      match r.readType with
      | .namedTable [table] =>
          match r.baseSchema with
          | some ns =>
              match schemaOfFields ns.names ns.fields with
              | some sc => some (AnyRel.mk sc sc (Rel.read table sc))
              | none => none
          | none => none
      | _ => none
  | .filter fr =>
      match decodeRel inv fr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeExpr s inv fr.condition with
              | some (AnyExpr.mk .bool n ce) =>
                  some (AnyRel.mk s s (Rel.filter ri ce))
              | _ => none
          | none => none
      | none => none
  | .project pr =>
      match decodeRel inv pr.input with
      | some (AnyRel.mk s p ri) =>
          match decodeProjections p inv pr.expressions with
          | some outs =>
              some (AnyRel.mk s (projectOut p outs)
                (Rel.project ri outs (emitOf pr.common)))
          | none => none
      | none => none
  | .aggregate ar =>
      match decodeRel inv ar.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeAnyExprs s inv ar.groupingExpressions with
              | some grouping =>
                  match decodeMeasures s inv ar.measures with
                  | some measures =>
                      some (AnyRel.mk s (aggregateOut s grouping measures)
                        (Rel.aggregate ri grouping measures))
                  | none => none
              | none => none
          | none => none
      | none => none
  | .sort sr =>
      match decodeRel inv sr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              match decodeSortKeys s sr.sorts with
              | some ks => some (AnyRel.mk s s (Rel.sort ri ks))
              | none => none
          | none => none
      | none => none
  | .fetch fr =>
      match decodeRel inv fr.input with
      | some pkgIn =>
          match squareOf pkgIn with
          | some ⟨s, ri⟩ =>
              some (AnyRel.mk s s (Rel.fetch ri fr.limit fr.offset))
          | none => none
      | none => none
  | .join jr =>
      match decodeRel inv jr.left with
      | some (AnyRel.mk sl sl' rl) =>
          match decodeRel inv jr.right with
          | some (AnyRel.mk sr sr' rr) =>
              match decodeExpr (sl' ++ sr') inv jr.condition with
              | some (AnyExpr.mk .bool n ce) =>
                  some (AnyRel.mk (sl ++ sr) (sl' ++ sr')
                    (Rel.join rl rr ce jr.joinType))
              | _ => none
          | none => none
      | none => none
  | .cross _ => none
  | .set { op := op, inputs := [l, r], common := _ } =>
      match decodeRel inv l with
      | some (AnyRel.mk s1 s1' rl) =>
          match decodeRel inv r with
          | some (AnyRel.mk s2 s2' rr) =>
              if h1 : s1 = s2 then
                if h2 : s1' = s2' then
                  some (AnyRel.mk s1 s1' (Rel.set op rl (Rel.cast2 h1 h2 rr)))
                else none
              else none
          | none => none
      | none => none
  | .set _ => none
  | .write wr =>
      match decodeRel inv wr.input with
      | some (AnyRel.mk s s' ri) =>
          match wr.tableSchema with
          | none => some (AnyRel.mk s s' (Rel.write wr.op wr.tableName none ri))
          | some ns =>
              match schemaOfFields ns.names ns.fields with
              | some sc =>
                  some (AnyRel.mk s s' (Rel.write wr.op wr.tableName (some sc) ri))
              | none => none
      | none => none
  | .extensionLeaf _ => none
  | .extensionSingle er =>
      match er.detail with
      | some d =>
          match decodeRel inv er.input with
          | some (AnyRel.mk s s' ri) =>
              some (AnyRel.mk s s' (Rel.extensionSingle d ri))
          | none => none
      | none => none
  | .extensionMulti _ => none
termination_by w => sizeOf w
decreasing_by
  all_goals (
    first
      | exact wf_filter_size _
      | exact wf_project_size _
      | exact wf_aggregate_size _
      | exact wf_sort_size _
      | exact wf_fetch_size _
      | exact (wf_join_size _).1
      | exact (wf_join_size _).2
      | exact (wf_set_size _ _ _ rfl).1
      | exact (wf_set_size _ _ _ rfl).2
      | exact wf_write_size _
      | exact wf_extensionSingle_size _)

/-- The (input, output) schema pair of a decoded rel. -/
def AnyRel.schemaPair : AnyRel → Schema × Schema
  | .mk i o _ => (i, o)

/-- The REL-level expression well-formedness: like `Expr.okS` but the field
    case pins the column DECODE exactly (`s.get? c.ordinal` resolves to the
    field's own `(name, t, n)`) — what `decodeExpr_shape`'s exact-index claim
    needs (the GADT leaves `c.ordinal` and the `HasCol` instance independent;
    the authoring surface `col` ties them). -/
def Expr.okSR (ctx : ExtCtx) (s : Schema) : {t : SType} → {n : Bool} → Expr s t n → Prop
  | _, _, .literal .. => True
  | _, _, @Expr.field _ c t n _ => s.get? c.ordinal = some (c.name, t, n)
  | _, _, .call sig args =>
      Args.okS ctx s args ∧ stOfPType (toProtoType ctx sig.ret) = some sig.ret

/-- `okSR` is strictly stronger than `okS` (the bridge the re-encode helpers
    use: their wire-level conclusions only need `okS`). -/
theorem Expr.okSR_to_okS (ctx : ExtCtx) (s : Schema) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okSR ctx s e → Expr.okS ctx s e := by
  intro t n e hok
  match e with
  | .literal .. => exact trivial
  | @Expr.field _ c _ _ _ =>
      intro hcontra
      rw [hok] at hcontra
      simp at hcontra
  | .call sig args => exact hok

/-- The expression-level well-formedness of a packaged expr (unwraps the
    package; `Expr.okSR` does the work). -/
def AnyExpr.okSR (ctx : ExtCtx) (s : Schema) (ae : AnyExpr s) : Prop :=
  match ae with
  | .mk _ _ e => Expr.okSR ctx s e

/-- The measure-level well-formedness: the output type decodes and every
    argument expression is well-formed. -/
def Measure.okS (ctx : ExtCtx) (s : Schema) (m : Measure s) : Prop :=
  stOfPType (withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable) = some m.sig.ret ∧
  ∀ ae ∈ m.args, AnyExpr.okSR ctx s ae

/-- Square-schema pinning: EVERY successful decode of `w` yields a rel whose
    input/output schemas are both `s`.  The wire erases schemas, so the typed
    GADT's square-input demand is a property of the decode, recorded here
    where the authoring surface guarantees it. -/
def SqPred (inv : FnInv) (w : Proto.Rel) (s : Schema) : Prop :=
  ∀ pkg, decodeRel inv w = some pkg → ∃ r1, pkg = AnyRel.mk s s r1

/-- Pair-schema pinning (the `project`/`join` shape). -/
def PairPred (inv : FnInv) (w : Proto.Rel) (p : Schema × Schema) : Prop :=
  ∀ pkg, decodeRel inv w = some pkg → ∃ r1, pkg = AnyRel.mk p.1 p.2 r1

/-! The rel-level well-formedness predicate — the `decodeRel_reEnc`
hypothesis, mirroring `Expr.okS`.  Beyond the per-node recursion it pins the
DECODED schemas of the children (`SqPred` / `PairPred`): the wire erases
schemas, so the typed GADT's index demands (square inputs, join condition
over the concatenated schema, set's same-schema inputs) are properties of the
decode, not of the typed term — the predicate records them where the
authoring surface guarantees them. -/
def Rel.okS (ctx : ExtCtx) (inv : FnInv) : {inS outS : Schema} → Rel inS outS → Prop
  | _, _, .read _ sc => schemaOk ctx sc
  | _, _, @Rel.filter s _ input cond =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      Expr.okSR ctx s cond
  | _, _, @Rel.project s p input outs _ =>
      Rel.okS ctx inv input ∧ PairPred inv (input.toProtoWith ctx) (s, p) ∧
      ∀ pr ∈ outs, Expr.okSR ctx p pr.expr
  | _, _, @Rel.aggregate s input grouping measures =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      (∀ ae ∈ grouping, AnyExpr.okSR ctx s ae) ∧ (∀ m ∈ measures, Measure.okS ctx s m)
  | _, _, @Rel.sort s input orderBy =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s ∧
      ∀ k ∈ orderBy, s.get? k.col.ordinal ≠ none
  | _, _, @Rel.fetch s input _ _ =>
      Rel.okS ctx inv input ∧ SqPred inv (input.toProtoWith ctx) s
  | _, _, @Rel.join sl sl' sr sr' _ left right cond _ =>
      Rel.okS ctx inv left ∧ Rel.okS ctx inv right ∧
      PairPred inv (left.toProtoWith ctx) (sl, sl') ∧
      PairPred inv (right.toProtoWith ctx) (sr, sr') ∧
      Expr.okSR ctx (sl' ++ sr') cond
  | _, _, @Rel.set _ _ _ left right =>
      Rel.okS ctx inv left ∧ Rel.okS ctx inv right ∧
      ∀ pkgL pkgR,
        decodeRel inv (left.toProtoWith ctx) = some pkgL →
        decodeRel inv (right.toProtoWith ctx) = some pkgR →
        pkgL.schemaPair = pkgR.schemaPair
  | _, _, @Rel.write _ _ _ _ ts input =>
      Rel.okS ctx inv input ∧
      (match ts with | none => True | some sc => schemaOk ctx sc)
  | _, _, @Rel.extensionSingle _ _ _ input => Rel.okS ctx inv input

/-! ## the rel re-encode: the decode-shape lemma and the helpers -/

/-- The decode-shape lemma (the rel-level workhorse): a well-formed typed
    expression decodes back to a package with its EXACT `(t, n)` indices —
    what the rel GADT's constructors demand. -/
theorem decodeExpr_shape (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {t : SType} {n : Bool} (e : Expr s t n), Expr.okSR ctx s e →
      ∃ e', decodeExpr s inv (e.toProto ctx) = some (AnyExpr.mk t n e') := by
  intro t n e
  match e with
  | .literal t' nv v =>
      intro _
      show ∃ e', decodeExpr s inv (Proto.Expression.literal
        { literalType := toProtoLiteralValue v, nullable := nv }) = some (AnyExpr.mk t' nv e')
      exact ⟨Expr.literal t' nv v, decodeLiteral_of_toProto v nv s⟩
  | @Expr.field _ c _ _ _ =>
      intro hok
      exact ⟨_, decodeExpr_field_of_get s c.ordinal c.name t n hok⟩
  | .call sig args =>
      intro hok
      have hargs : Args.okS ctx s args := hok.1
      have hret : stOfPType (toProtoType ctx sig.ret) = some sig.ret := hok.2
      have hfn' := hfn sig
      show ∃ e', decodeExpr s inv (Proto.Expression.scalarFunction
        (ctx.functionAnchor sig.urn sig.name) (args.toProto ctx)
        (withNullable (toProtoType ctx sig.ret) sig.retNullable)) =
        some (AnyExpr.mk sig.ret sig.retNullable e')
      simp only [decodeExpr, hfn']
      cases hd : decodeArgs s inv (args.toProto ctx) with
      | none =>
          have hinv := decodeArgs_reEnc s inv ctx hfn args hargs
          rw [hd] at hinv
          simp at hinv
      | some q =>
          cases q with
          | mk ts' spine =>
              have hret' : stOfPType (withNullable (toProtoType ctx sig.ret) sig.retNullable) =
                  some sig.ret := by
                rw [stOfPType_withNullable]
                exact hret
              rw [hret', pTypeNullable_withNullable]
              exact ⟨Expr.call (FunctionSig.mkSig sig.name sig.urn ts' sig.ret
                sig.retNullable true) spine, rfl⟩

/-- Projection-list inversion: the lowered projections decode (with
    placeholder names) and re-lower to the same wire expressions. -/
theorem decodeProjections_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (ps : List (Projection s)) (hok : ∀ pr ∈ ps, Expr.okSR ctx s pr.expr) :
    ∃ ps', decodeProjections s inv (ps.map (fun pr => pr.expr.toProto ctx)) = some ps' ∧
      ps'.map (fun pr => pr.expr.toProto ctx) = ps.map (fun pr => pr.expr.toProto ctx) := by
  induction ps with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons pr rest ih =>
      have hpr : Expr.okS ctx s pr.expr := Expr.okSR_to_okS ctx s _ (hok pr (by simp))
      have hrest : ∀ pr' ∈ rest, Expr.okSR ctx s pr'.expr := fun q hq => hok q (by simp [hq])
      obtain ⟨ps', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn pr.expr hpr
      cases hd : decodeExpr s inv (pr.expr.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          cases pkg with
          | mk t n ex =>
              rw [hd] at hdec
              simp only [anyLower, Option.map_some, Option.some.injEq] at hdec
              refine ⟨{ name := "", dtype := t, nullable := n, expr := ex } :: ps', ?_, ?_⟩
              · simp only [List.map_cons, decodeProjections, hd, h1]
              · show ({ name := "", dtype := t, nullable := n, expr := ex } :: ps').map
                    (fun pr => pr.expr.toProto ctx) =
                  (pr :: rest).map (fun pr => pr.expr.toProto ctx)
                show ex.toProto ctx :: ps'.map (fun pr => pr.expr.toProto ctx) =
                  pr.expr.toProto ctx :: rest.map (fun pr => pr.expr.toProto ctx)
                rw [hdec, h2]

/-- Grouping-list inversion (grouping keys; the `AnyExpr` list shape). -/
theorem decodeAnyExprs_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (xs : List (AnyExpr s)) (hok : ∀ ae ∈ xs, AnyExpr.okSR ctx s ae) :
    ∃ xs', decodeAnyExprs s inv (anyExprsLower xs ctx) = some xs' ∧
      xs'.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
        xs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons ae rest ih =>
      obtain ⟨t, n, e⟩ := ae
      have hae : Expr.okS ctx s e := Expr.okSR_to_okS ctx s _ (hok (AnyExpr.mk t n e) (by simp))
      have hrest : ∀ x ∈ rest, AnyExpr.okSR ctx s x := fun y hy => hok y (by simp [hy])
      obtain ⟨xs', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn e hae
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          cases pkg with
          | mk t' n' ex =>
              rw [hd] at hdec
              simp only [anyLower, Option.map_some, Option.some.injEq] at hdec
              refine ⟨AnyExpr.mk t' n' ex :: xs', ?_, ?_⟩
              · rw [anyExprsLower_cons]
                simp only [decodeAnyExprs, hd, h1]
              · show (AnyExpr.mk t' n' ex :: xs').map
                    (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
                  (AnyExpr.mk t n e :: rest).map
                    (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                show ex.toProto ctx ::
                    xs'.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
                  e.toProto ctx ::
                    rest.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                rw [hdec, h2]

/-- Argument-spine inversion over a plain type-erased list: the lowered list
    decodes to a spine, and re-packing + re-lowering recovers the wire list. -/
theorem decodeArgs_anyExprs (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (xs : List (AnyExpr s)) (hok : ∀ ae ∈ xs, AnyExpr.okSR ctx s ae) :
    ∃ ts spine, decodeArgs s inv (anyExprsLower xs ctx) = some (AnyArgs.mk ts spine) ∧
      anyExprsLower (argsPack spine) ctx = anyExprsLower xs ctx := by
  induction xs with
  | nil => exact ⟨[], Args.nil, rfl, rfl⟩
  | cons ae rest ih =>
      obtain ⟨t, n, e⟩ := ae
      have hae : Expr.okS ctx s e := Expr.okSR_to_okS ctx s _ (hok (AnyExpr.mk t n e) (by simp))
      have hrest : ∀ x ∈ rest, AnyExpr.okSR ctx s x := fun y hy => hok y (by simp [hy])
      obtain ⟨ts', spine', h1, h2⟩ := ih hrest
      have hdec := decodeExpr_reEnc s inv ctx hfn e hae
      cases hd : decodeExpr s inv (e.toProto ctx) with
      | none => rw [hd] at hdec; simp at hdec
      | some pkg =>
          cases pkg with
          | mk t' n' ex =>
              rw [hd] at hdec
              simp only [anyLower, Option.map_some, Option.some.injEq] at hdec
              refine ⟨(t', n') :: ts', Args.cons t' n' ex spine', ?_, ?_⟩
              · rw [anyExprsLower_cons]
                simp only [decodeArgs, hd, h1]
              · rw [show argsPack (Args.cons t' n' ex spine') =
                  AnyExpr.mk t' n' ex :: argsPack spine' from rfl,
                  anyExprsLower_cons, anyExprsLower_cons]
                show ex.toProto ctx :: anyExprsLower (argsPack spine') ctx =
                  e.toProto ctx :: anyExprsLower rest ctx
                rw [hdec, h2]

/-- Measure-list inversion: the lowered measures decode and re-lower to the
    same wire measures. -/
theorem decodeMeasures_reEnc (s : Schema) (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name))
    (ms : List (Measure s)) (hok : ∀ m ∈ ms, Measure.okS ctx s m) :
    ∃ ms', decodeMeasures s inv (ms.map (measureLower ctx)) = some ms' ∧
      ms'.map (fun m =>
        ({ measure :=
            { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
              args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
              outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } } :
          Proto.AggregateMeasure)) =
      ms.map (fun m =>
        ({ measure :=
            { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
              args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
              outputType := withNullable (toProtoType ctx m.sig.ret) m.sig.retNullable } } :
          Proto.AggregateMeasure)) := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m rest ih =>
      obtain ⟨sig, marg⟩ := m
      have hm : Measure.okS ctx s { sig := sig, args := marg } := hok _ (by simp)
      obtain ⟨hret, hargs⟩ := hm
      rw [stOfPType_withNullable] at hret
      have hrest : ∀ m' ∈ rest, Measure.okS ctx s m' := fun q hq => hok q (by simp [hq])
      obtain ⟨ms', h1, h2⟩ := ih hrest
      have hfn' : fnOf inv (ctx.functionAnchor sig.urn sig.name) =
          some (sig.urn, sig.name) := hfn sig
      obtain ⟨ts, spine, hda⟩ := decodeArgs_anyExprs s inv ctx hfn marg hargs
      refine ⟨{ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                args := argsPack spine } :: ms', ?_, ?_⟩
      · show decodeMeasures s inv
          (measureLower ctx { sig := sig, args := marg } ::
            rest.map (measureLower ctx)) =
          some ({ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                  args := argsPack spine } :: ms')
        simp only [measureLower, decodeMeasures, hfn', hda, stOfPType_withNullable, hret,
          pTypeNullable_withNullable, h1, FunctionSig.mkSig]
      · have hurm : (argsPack spine).map
            (fun ae => match ae with | .mk _ _ e => e.toProto ctx) =
          marg.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx) := hda.2
        show ({ sig := FunctionSig.mkSig sig.name sig.urn ts sig.ret sig.retNullable true,
                args := argsPack spine } :: ms').map
            (fun m =>
              ({ measure :=
                  { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                    args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                    outputType := withNullable (toProtoType ctx m.sig.ret)
                      m.sig.retNullable } } : Proto.AggregateMeasure)) =
          ({ sig := sig, args := marg } :: rest).map
            (fun m =>
              ({ measure :=
                  { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                    args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                    outputType := withNullable (toProtoType ctx m.sig.ret)
                      m.sig.retNullable } } : Proto.AggregateMeasure))
        simp only [FunctionSig.mkSig, List.map_cons, hurm, h2]

/-- Sort-key-list inversion: the lowered keys decode (names re-derived from
    the schema) and re-lower to the same wire sort fields. -/
theorem decodeSortKeys_reEnc (s : Schema) (ks : List (SortKey s))
    (hok : ∀ k ∈ ks, s.get? k.col.ordinal ≠ none) :
    ∃ ks', decodeSortKeys s (ks.map sortFieldLower) = some ks' ∧
      ks'.map (fun k =>
        (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
          k.direction⟩ : Proto.SortField)) =
      ks.map (fun k =>
        (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
          k.direction⟩ : Proto.SortField)) := by
  induction ks with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons k rest ih =>
      obtain ⟨col, dir⟩ := k
      have hk : s.get? col.ordinal ≠ none :=
        hok { col := col, direction := dir } (by simp)
      have hrest : ∀ k2 ∈ rest, s.get? k2.col.ordinal ≠ none := fun k2 h2 =>
        hok k2 (by simp [h2])
      obtain ⟨ks', h1, h2⟩ := ih hrest
      cases hg : s.get? col.ordinal with
      | none => exact absurd hg hk
      | some col3 =>
          obtain ⟨nm, t3, n3⟩ := col3
          refine ⟨{ col := { name := nm, ordinal := col.ordinal }, direction := dir } :: ks',
            ?_, ?_⟩
          · simp only [List.map_cons, sortFieldLower, decodeSortKeys, hg, h1]
          · show ({ col := { name := nm, ordinal := col.ordinal }, direction := dir } :: ks').map
                (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField)) =
              ({ col := col, direction := dir } :: rest).map
                (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField))
            show ⟨Proto.Expression.field { ordinal := col.ordinal, segment := none },
                dir⟩ :: ks'.map (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField)) =
              ⟨Proto.Expression.field { ordinal := col.ordinal, segment := none },
                dir⟩ :: rest.map (fun k =>
                  (⟨Proto.Expression.field { ordinal := k.col.ordinal, segment := none },
                    k.direction⟩ : Proto.SortField))
            rw [h2]

/-! ## the master rel re-encode theorem -/

/- The wire-level round trip: for EVERY typed rel `r` satisfying `Rel.okS`,
   decoding `r`'s lowered form and re-lowering the decode recovers the SAME
   wire term.  This is the composition the wire consumes: anchors, ordinals,
   and schemas round-trip; names (erased by the wire) are re-derived from the
   decode. -/

/-- `squareOf` on an already-square package. -/
theorem squareOf_mk (s : Schema) (r : Rel s s) :
    squareOf (AnyRel.mk s s r) = some ⟨s, r⟩ := by
  show (if h : s = s then some (SqRel.mk s (Rel.castSq h r)) else none) = some ⟨s, r⟩
  rw [dif_pos rfl]
  rfl

/-- **THE rel re-encode theorem**: for every typed rel `r` (with its
    `Rel.okS` well-formedness — ordinal-safe columns, decodable call output
    types, decodable read schemas, and the decoded-schema pins the GADT
    demands), decoding `r`'s lowered form and re-lowering the result recovers
    the SAME wire term. -/
theorem decodeRel_reEnc (inv : FnInv) (ctx : ExtCtx)
    (hfn : ∀ sig : FunctionSig,
      fnOf inv (ctx.functionAnchor sig.urn sig.name) = some (sig.urn, sig.name)) :
    ∀ {inS outS : Schema} (r : Rel inS outS), Rel.okS ctx inv r →
      (decodeRel inv (r.toProtoWith ctx)).map (fun a => relLower a ctx) =
        some (r.toProtoWith ctx) := by
  intro inS outS r
  induction r with
  | read table sc =>
      intro hok
      show (decodeRel inv (Proto.Rel.read
        { readType := .namedTable [table]
          baseSchema := some { fields := sc.map (toProtoColType ctx), names := sc.names }
          common := none })).map (fun a => relLower a ctx) =
        some (Proto.Rel.read
        { readType := .namedTable [table]
          baseSchema := some { fields := sc.map (toProtoColType ctx), names := sc.names }
          common := none })
      simp only [decodeRel]
      rw [schemaOfFields_of_toProto ctx sc hok]
      simp [relLower, Rel.toProtoWith]
  | @filter s _ input cond ih =>
      intro hok
      obtain ⟨hin, hsq, hcond⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.filter
        { condition := cond.toProto ctx, input := input.toProtoWith ctx,
          common := none })).map (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          simp only [SqPred, hx] at hsq
          obtain ⟨r1, hpkg⟩ := hsq pkg rfl
          rw [hpkg] at ihc
          have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
            simpa [relLower] using ihc
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨ce, hce'⟩ := decodeExpr_shape s inv ctx hfn cond hcond
          rw [hce']
          have hlowce : ce.toProto ctx = cond.toProto ctx := by
            have h2 := decodeExpr_reEnc s inv ctx hfn cond (Expr.okSR_to_okS ctx s _ hcond)
            rw [hce'] at h2
            simpa [anyLower] using h2
          simp [relLower, Rel.toProtoWith, hlowce, hlow]
  | @project s p input outs emit ih =>
      intro hok
      obtain ⟨hin, hpr, houts⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.project
        { expressions := outs.map (fun pr => pr.expr.toProto ctx),
          input := input.toProtoWith ctx,
          common := emit.map (fun m => { emit := some (.emit m), advancedExtension := none }) })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          simp only [PairPred, hx] at hpr
          obtain ⟨r1, hpkg⟩ := hpr pkg rfl
          rw [hpkg] at ihc
          have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
            simpa [relLower] using ihc
          rw [hpkg]
          obtain ⟨ps', hp1, hp2⟩ := decodeProjections_reEnc p inv ctx hfn outs houts
          simp only [hp1]
          cases emit with
          | none => simp [relLower, Rel.toProtoWith, Option.map_none, emitOf, hlow, hp2]
          | some m => simp [relLower, Rel.toProtoWith, Option.map_some, emitOf, hlow, hp2]
  | @aggregate s input grouping measures ih =>
      intro hok
      obtain ⟨hin, hsq, hg, hm⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.aggregate
        { groupingExpressions := anyExprsLower grouping ctx,
          measures := measures.map (measureLower ctx),
          input := input.toProtoWith ctx, common := none })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          simp only [SqPred, hx] at hsq
          obtain ⟨r1, hpkg⟩ := hsq pkg rfl
          rw [hpkg] at ihc
          have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
            simpa [relLower] using ihc
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨gxs, hg1, hg2⟩ := decodeAnyExprs_reEnc s inv ctx hfn grouping hg
          obtain ⟨mxs, hm1, hm2⟩ := decodeMeasures_reEnc s inv ctx hfn measures hm
          simp only [hg1, hm1]
          simp only [Option.map_some, relLower, Rel.toProtoWith]
          show some (Proto.Rel.aggregate
            { groupingExpressions :=
                gxs.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx),
              measures :=
                mxs.map (fun m =>
                  ({ measure :=
                      { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                        args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                        outputType := withNullable (toProtoType ctx m.sig.ret)
                          m.sig.retNullable } } : Proto.AggregateMeasure)),
              input := r1.toProtoWith ctx, common := none }) =
            some (Proto.Rel.aggregate
              { groupingExpressions :=
                  grouping.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx),
                measures :=
                  measures.map (fun m =>
                    ({ measure :=
                        { functionReference := ctx.functionAnchor m.sig.urn m.sig.name
                          args := m.args.map (fun ae => match ae with | .mk _ _ e => e.toProto ctx)
                          outputType := withNullable (toProtoType ctx m.sig.ret)
                            m.sig.retNullable } } : Proto.AggregateMeasure)),
                input := input.toProtoWith ctx, common := none })
          rw [hg2, hm2, hlow]
  | @sort s input orderBy ih =>
      intro hok
      obtain ⟨hin, hsq, hk⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.sort
        { sorts := orderBy.map sortFieldLower, input := input.toProtoWith ctx,
          common := none })).map (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          simp only [SqPred, hx] at hsq
          obtain ⟨r1, hpkg⟩ := hsq pkg rfl
          rw [hpkg] at ihc
          have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
            simpa [relLower] using ihc
          rw [hpkg]
          simp only [squareOf_mk]
          obtain ⟨ks', hk1', hk2'⟩ := decodeSortKeys_reEnc s orderBy hk
          simp only [hk1']
          simp [relLower, Rel.toProtoWith, hk2', hlow]
  | @fetch s input limit offset ih =>
      intro hok
      obtain ⟨hin, hsq⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.fetch
        { limit := limit, offset := offset, input := input.toProtoWith ctx,
          common := none })).map (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          simp only [SqPred, hx] at hsq
          obtain ⟨r1, hpkg⟩ := hsq pkg rfl
          rw [hpkg] at ihc
          have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
            simpa [relLower] using ihc
          rw [hpkg]
          simp only [squareOf_mk]
          simp [relLower, Rel.toProtoWith, hlow]
  | @join sl sl' sr sr' _ left right cond jt ihl ihr =>
      intro hok
      obtain ⟨hl, hr, hpl, hpr, hcond⟩ := hok
      have ihcL := ihl hl
      have ihcR := ihr hr
      show (decodeRel inv (Proto.Rel.join
        { joinType := jt, left := left.toProtoWith ctx, right := right.toProtoWith ctx,
          condition := cond.toProto ctx, postJoinFilter := none, common := none })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx1 : decodeRel inv (left.toProtoWith ctx) with
      | none => rw [hx1] at ihcL; simp at ihcL
      | some pkgL =>
          cases hx2 : decodeRel inv (right.toProtoWith ctx) with
          | none => rw [hx2] at ihcR; simp at ihcR
          | some pkgR =>
              rw [hx1] at ihcL
              rw [hx2] at ihcR
              simp only [PairPred, hx1] at hpl
              simp only [PairPred, hx2] at hpr
              obtain ⟨rl, hpkgL⟩ := hpl pkgL rfl
              obtain ⟨rr, hpkgR⟩ := hpr pkgR rfl
              rw [hpkgL] at ihcL
              rw [hpkgR] at ihcR
              have hlowL : rl.toProtoWith ctx = left.toProtoWith ctx := by
                simpa [relLower] using ihcL
              have hlowR : rr.toProtoWith ctx = right.toProtoWith ctx := by
                simpa [relLower] using ihcR
              rw [hpkgL, hpkgR]
              show Option.map (fun a => relLower a ctx)
                  (match decodeExpr (sl' ++ sr') inv (cond.toProto ctx) with
                  | some (AnyExpr.mk .bool n ce) =>
                      some (AnyRel.mk (sl ++ sr) (sl' ++ sr') (Rel.join rl rr ce jt))
                  | _ => none) =
                some (Proto.Rel.join
                  { joinType := jt, left := left.toProtoWith ctx,
                    right := right.toProtoWith ctx, condition := cond.toProto ctx,
                    postJoinFilter := none, common := none })
              obtain ⟨ce, hce'⟩ := decodeExpr_shape (sl' ++ sr') inv ctx hfn cond hcond
              rw [hce']
              have hlowce : ce.toProto ctx = cond.toProto ctx := by
                have h2 := decodeExpr_reEnc (sl' ++ sr') inv ctx hfn cond (Expr.okSR_to_okS ctx (sl' ++ sr') _ hcond)
                rw [hce'] at h2
                simpa [anyLower] using h2
              simp [relLower, Rel.toProtoWith, hlowL, hlowR, hlowce]
  | @set s s' op left right ihl ihr =>
      intro hok
      obtain ⟨hl, hr, hpair⟩ := hok
      have ihcL := ihl hl
      have ihcR := ihr hr
      show (decodeRel inv (Proto.Rel.set
        { op := op, inputs := [left.toProtoWith ctx, right.toProtoWith ctx],
          common := none })).map (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx1 : decodeRel inv (left.toProtoWith ctx) with
      | none => rw [hx1] at ihcL; simp at ihcL
      | some pkgL =>
          cases hx2 : decodeRel inv (right.toProtoWith ctx) with
          | none => rw [hx2] at ihcR; simp at ihcR
          | some pkgR =>
              rw [hx1] at ihcL
              rw [hx2] at ihcR
              cases pkgL with
              | mk s1 s1' rl =>
                  cases pkgR with
                  | mk s2 s2' rr =>
                      have hlowL : rl.toProtoWith ctx = left.toProtoWith ctx := by
                        simpa [relLower] using ihcL
                      have hlowR : rr.toProtoWith ctx = right.toProtoWith ctx := by
                        simpa [relLower] using ihcR
                      rw [hx1, hx2] at hpair
                      have heq : (s1, s1') = (s2, s2') := by
                        have hp := hpair (AnyRel.mk s1 s1' rl) (AnyRel.mk s2 s2' rr) rfl rfl
                        simpa [AnyRel.schemaPair] using hp
                      have h1 : s1 = s2 := congrArg Prod.fst heq
                      have h2 : s1' = s2' := congrArg Prod.snd heq
                      simp only [Option.map_some, relLower]
                      rw [dif_pos h1, dif_pos h2]
                      show some (Proto.Rel.set
                        { op := op,
                          inputs := [rl.toProtoWith ctx,
                            (Rel.cast2 h1 h2 rr).toProtoWith ctx],
                          common := none }) =
                        some (Proto.Rel.set
                          { op := op,
                            inputs := [left.toProtoWith ctx, right.toProtoWith ctx],
                            common := none })
                      rw [Rel.cast2_toProtoWith, hlowL, hlowR]
  | @write s s' op table ts input ih =>
      intro hok
      obtain ⟨hin, hts⟩ := hok
      have ihc := ih hin
      show (decodeRel inv (Proto.Rel.write
        { tableName := table, op := op,
          tableSchema := ts.map (fun sc =>
            { fields := sc.map (toProtoColType ctx), names := sc.names }),
          input := input.toProtoWith ctx, common := none })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          cases pkg with
          | mk t t' r1 =>
              have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
                simpa [relLower] using ihc
              cases ts with
              | none =>
                  show (match some (AnyRel.mk t t' r1) with
                    | some (AnyRel.mk u u' ri) =>
                        some (AnyRel.mk u u' (Rel.write op table none ri))
                    | none => none).map (fun a => relLower a ctx) = _
                  simp [relLower, Rel.toProtoWith, hlow]
              | some sc =>
                  have hsco := hts
                  show (match some (AnyRel.mk t t' r1) with
                    | some (AnyRel.mk u u' ri) =>
                        match schemaOfFields sc.names (sc.map (toProtoColType ctx)) with
                        | some sc' =>
                            some (AnyRel.mk u u' (Rel.write op table (some sc') ri))
                        | none => none
                    | none => none).map (fun a => relLower a ctx) = _
                  rw [schemaOfFields_of_toProto ctx sc hsco]
                  simp [relLower, Rel.toProtoWith, hlow]
  | @extensionSingle s s' detail input ih =>
      intro hok
      have ihc := ih hok
      show (decodeRel inv (Proto.Rel.extensionSingle
        { input := input.toProtoWith ctx, detail := some detail, common := none })).map
        (fun a => relLower a ctx) = some _
      simp only [decodeRel]
      cases hx : decodeRel inv (input.toProtoWith ctx) with
      | none => rw [hx] at ihc; simp at ihc
      | some pkg =>
          rw [hx] at ihc
          cases pkg with
          | mk t t' r1 =>
              have hlow : r1.toProtoWith ctx = input.toProtoWith ctx := by
                simpa [relLower] using ihc
              show (match some detail with
                | some d => some (AnyRel.mk t t' (Rel.extensionSingle d r1))
                | none => none).map (fun a => relLower a ctx) = _
              simp [relLower, Rel.toProtoWith, hlow]
end Substrait.Decode
