/-
# Substrait.Decode.Expr — the literal/expression parsers and their inversion ladder

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
W5.3 phase 2b: the cast failure-behavior suffix scans the shared
`Grammar.castFbGrammar` table (`castFbScan`, with `castFbScan_token` the
round trip); parens/arrows/`if_then(`/the binary sentinel are the shared
line-shape tokens. The `null`/`true`/`false` value words stay
char-pattern-matched (patterns cannot consume a constant — the
resistant-site note in `Substrait.Grammar`'s header).
-/
import Substrait.Decode.Types

namespace Substrait.Decode

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

/-- Parse a decimal float value: optional `-`, integer digits, `.`,
    fractional digits (at least one digit after `.`).  Uses `scanNat`
    for the integer part, then iterates the fractional digits dividing
    by successive powers of 10 — avoids `Float` exponent (not available
    in core-only) and handles leading zeros in the fractional part. -/
def scanFloat : List Char → Option (Float × List Char)
  | '-' :: cs =>
    match scanFloat cs with
    | some (v, rest) => some (-v, rest)
    | none => none
  | cs =>
    match scanNat cs with
    | some (intPart, '.' :: rest) =>
      -- `started` distinguishes "no digits after the dot" (not a float)
      -- from "input ended INSIDE the fraction" (the float is complete)
      let rec go (started : Bool) (frac : Float) (div : Float) : List Char → Option (Float × List Char)
        | [] => if started then some ((Nat.toFloat intPart) + frac, []) else none
        | c :: rest' =>
          if h : c.isDigit then
            let digit := (c.val.toNat - '0'.val.toNat)
            go true (frac + (Nat.toFloat digit) / div) (div * (10 : Float)) rest'
          else if started then
            some ((Nat.toFloat intPart) + frac, c :: rest')
          else none
      go false 0.0 (10 : Float) rest
    | _ => none

/-- Float literal from the suffix's type (default fp64 when no suffix;
    a non-float suffix type is a parse error). -/
def floatLitOf (v : Float) : Option Proto.PType → Option Proto.LiteralType
  | none => some (.fp64 v)  -- default: fp64 (isDefaultForSyntax)
  | some (.fp32 _) => some (.fp32 v)
  | some (.fp64 _) => some (.fp64 v)
  | _ => none

/-- The float arm's tail: the suffix scan after a scanned float value
    (mirrors `intLitTail`). -/
def floatLitTail (v : Float) (r1 : List Char) : Option (Proto.Literal × List Char) :=
  match scanLitSuffix r1 with
  | some (sfx, r) => (floatLitOf v sfx).map (fun lt =>
      ({ literalType := lt, nullable := suffixNullable sfx }, r))
  | none => none

/-- Parse a literal (the emitter's `literal` forms). The value words
    `null`/`true`/`false` stay char-pattern-matched (patterns cannot consume
    a constant — the resistant-site note in `Substrait.Grammar`'s header);
    the binary sentinel IS the shared `Grammar.binarySentinel`. -/
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
    if startsWith cs Grammar.binarySentinel then
      litWithSuffix (.binary []) (cs.drop Grammar.binarySentinel.length)
    else match scanFloat cs with
      | some (v, r1) => floatLitTail v r1
      | none => match scanInt cs with
        | some (v, r1) => intLitTail v r1
        | none => none

/-- The cast failure-behavior suffix scan over the shared
    `Grammar.castFbGrammar` table (the emitter's `?`/`!` tokens; the bare
    `::t` form scans nothing and the caller rejects `unspecified`). -/
def castFbScan (cs : List Char) : Option (Grammar.CastFbCtor × List Char) :=
  (Grammar.castFbGrammar.find? (fun c => startsWith cs c.token)).map
    (fun c => (c, cs.drop c.token.length))

/-- **Cast-failure round trip** (`parse (emit x) = some x`): the emitter's
    token for a behavior scans back to the ctor. -/
theorem castFbScan_token (c : Grammar.CastFbCtor) (rest : List Char) :
    castFbScan (c.token.toList ++ rest) = some (c, rest) := by
  cases c <;> rfl

mutual

/-- `", "`-separated expression list inside a call; structural on `lfuel`. -/
def parseExprList : Nat → Nat → FnCtx → List Char → Option (List Proto.Expression × List Char)
  | 0, _, _, _ => none
  | lfuel + 1, efuel, ctx, cs =>
    match parseExpr efuel ctx cs with
    | none => none
    | some (e, r1) =>
      match expect Grammar.sepTok r1 with
      | some r2 => match parseExprList lfuel efuel ctx r2 with
        | some (es, r3) => some (e :: es, r3)
        | none => none
      | none => some ([e], r1)

/-- The if_then argument list: `_ -> else` or `cond -> value, ` + more. -/
def parseIfPairs : Nat → Nat → FnCtx → List Char →
    Option (List (Proto.Expression × Proto.Expression) × Proto.Expression × List Char)
  | 0, _, _, _ => none
  | lfuel + 1, efuel, ctx, cs =>
    if startsWith cs Grammar.ifElseTok then
      match parseExpr efuel ctx (cs.drop Grammar.ifElseTok.length) with
      | some (e, r1) => match expect Grammar.rparenTok r1 with
        | some r2 => some ([], e, r2)
        | none => none
      | none => none
    else match parseExpr efuel ctx cs with
      | some (c, r1) =>
        match expect Grammar.ifArrowTok r1 with
        | some r2 => match parseExpr efuel ctx r2 with
          | some (v, r3) =>
            match expect Grammar.sepTok r3 with
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
    if startsWith cs Grammar.lparenTok then
      match parseExpr fuel ctx (cs.drop Grammar.lparenTok.length) with
      | some (e, r1) =>
        match expect Grammar.rparenTok r1 with
        | some r2 =>
          match expect Grammar.castTok r2 with
          | some r3 =>
            let (fb, r4) := match castFbScan r3 with
              | some (c, rr) => (c.toBehavior, rr)
              | none => (Proto.CastFailureBehavior.unspecified, r3)
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
    else if startsWith cs Grammar.kwIfThen then
      match parseIfPairs (cs.length + 1) fuel ctx (cs.drop Grammar.kwIfThen.length) with
      | some (ifs, els, r) => some (.ifThen ifs els, r)
      | none => none
    else if startsWith cs Grammar.dollarTok then
      match scanNat (cs.drop 1) with
      | some (n, r) => some (.field { ordinal := n, segment := none }, r)
      | none => none
    else match scanIdent cs with
    | some (fn, r1) =>
      match expect Grammar.lparenTok r1 with
      | some r2 =>
        match parseExprList (r2.length + 1) fuel ctx r2 with
        | some (args, r3) =>
          match expect Grammar.rparenTok r3 with
          | some r4 =>
            match expect Grammar.colonTok r4 with
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
    (hstop : notDigitHead rest) (hnotcolon : rest.head? ≠ some ':')
    (hnotdot : rest.head? ≠ some '.') :
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
    have hsf : scanFloat (c :: (cs ++ rest)) = none := by
      have hneg' : c ≠ '-' := char_ne_digit hdim (by decide : '-'.isDigit = false)
      rw [scanFloat.eq_2 (c :: (cs ++ rest)) (by
        intro rest' h'
        injection h' with hcc _
        exact hneg' hcc)]
      rw [hsc]
      cases hrest : rest
      · rfl
      · rename_i c' rest'
        have hc' : c' ≠ '.' := by
          intro hdot
          apply hnotdot
          simp [hrest, hdot]
        simp [hrest, hc']
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
      hbin, hsf, hsc', intLitTail, scanLitSuffix_none rest hnotcolon, intLitOf, suffixNullable]



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
theorem parseType_len_invert (t : Proto.PType) (b : String) (rest : List Char)
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
    have hsf : scanFloat (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest)) = none := by
      have hneg' : c ≠ '-' := char_ne_digit hdim (by decide : '-'.isDigit = false)
      rw [scanFloat.eq_2 (c :: (cs ++ ':' :: 'i' :: '6' :: '4' :: '?' :: rest)) (by
        intro rest' h'
        injection h' with hcc _
        exact hneg' hcc)]
      rw [hscn']
      simp
    simp [parseLiteral,
      char_ne_digit hdim (by decide : 'n'.isDigit = false),
      char_ne_digit hdim (by decide : 't'.isDigit = false),
      char_ne_digit hdim (by decide : 'f'.isDigit = false),
      char_ne_digit hdim (by decide : ('\'' : Char).isDigit = false),
      hbin, hsf, hsc', hlt', intLitTail, intLitOf, suffixNullable, nullabilityOf]
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
    (hstop : notDigitHead rest) (hnotcolon : rest.head? ≠ some ':')
    (hnotdot : rest.head? ≠ some '.') :
    parseExpr (fuel + 1) ctx ((toString n).toList ++ rest) =
      some (.literal { literalType := .i64 (n : Int), nullable := false }, rest) := by
  rcases parseExpr_int_prefix n rest with ⟨hnot1, hnot2, hnot3, hsn⟩
  have hnocall : ∀ (fn : String) (r1 : List Char),
      scanIdent ((toString n).toList ++ rest) = some (fn, r1) → expect "(" r1 = none := by
    intro fn r1 h'
    rw [hsn] at h'
    cases h'
  rw [parseExpr_literal_fallback fuel ctx ((toString n).toList ++ rest) hnot1 hnot2 hnot3 hnocall]
  rw [parseLiteral_i64 n rest hstop hnotcolon hnotdot]


end Substrait.Decode
