/-
# Substrait.Decode.Basic — the parser monad, escapes, name scanners, prefix kit

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
-/
import Substrait.Emit.Text

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



end Substrait.Decode
