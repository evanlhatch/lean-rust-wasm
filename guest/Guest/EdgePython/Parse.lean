/-
# Guest.EdgePython.Parse — the Python-subset surface parser: text → Py.Fn

Owner: the guest lane's SECOND FRONTEND (the text face of
`Guest.EdgePython.Ast`). Ported from the legacy lane's intent — the
legacy authored its fixtures as a Lean DSL and named "a string tokenizer
+ syntax embedding" the follow-up; THIS module is that follow-up, over
the tree's parser discipline.

## Riding TextKit (the WIT/WAT parser precedent)

NEVER a hand-rolled parser: every token, atom, and repetition rides
`TextKit`'s GParser lane — the error-carrying carrier
(`TextKit.Error`: the ONE `ParseError` envelope WITH position), the
combinator surface (`TextKit.Combinators`: `<|>` best-error choice,
`many`/`some`/`sepBy`/`optional`, `save`/`jump` backtracking, `label`).
The RECURSIVE/INDENTATION zone is the guarded hand zone — the
`WasmCore.WatParse.funcP` precedent (15 #17's layered composition): a
ctor-armed, context-threaded grammar (block bodies are delimited by
INDENTATION COLUMNS, which a fix payload cannot carry) stays hand-written
over the SAME combinators, fuel-bounded total. The fuel is a model
artifact (every recursive hop consumes input); exhaustion is a parse
refusal, never divergence.

## The accepted language (the honest fragment — E6's productive face)

Modules of `def f(x, y):` functions; statements `return e`, `x = e`,
`if c:` / `else:`, `while c:`, `for x in xs:` with INDENTED block bodies
(spaces only — a tab is a refusal), blank lines free; expressions with
the FULL precedence ladder `or < and < not < cmp < add < mul < unary -
< postfix-index < atom`: `+ - *`, `< <= > >= == !=`, `and or not`,
unary minus, integer literals, `True`/`False`, tuple literals
`(a, b, …)`, list literals `[a, b, …]`, constant index `t[i]`, calls,
parens. Whitespace BETWEEN tokens = spaces (no line continuations);
expressions are single-line.

NO ROUND-TRIP LAW: the legacy lane has NO printer for the Py surface
(it compiled straight to the WAT AST), so the round-trip law's
antecedent fails — the boundary is named, not silently dropped (a
printer would carry the `Wit.Parse`-style law pair).

The parse-time refusals keep their teeth: trailing bytes
(`parseProgram`'s full-consumption check), the keyword reservations
(`if`/`else`/`while`/`for`/`in`/`and`/`or`/`not`/`def`/`return`/
`True`/`False` are not identifiers — the `kw` combinator's word
boundary: a keyword PREFIX of an identifier (`ifx`) is an identifier),
and the excluded forms (strings, `%`, augmented assignment) fail loudly.

The five questions (notes/v3/01-core.md):

- **Root**: Crossing — the Python-subset text read into the closed AST.
- **Carrier grade**: none — the refusals ride TextKit's ParseError lane.
- **Spine reading**: none — the frontend's reading half; `Fe` folds the
  product into the IR spine.
- **Ladder rung**: rung 1 — total fuel-bounded definitions over the
  combinator surface.
- **Gate row**: the Guest row (Gates.Packages) — the module rides the
  Guest lib's glob.
-/

import TextKit.Combinators
import Guest.EdgePython.Ast

namespace Guest.EdgePython.Parse

open TextKit Guest.EdgePython.Py

/-! ## The lexical primitives -/

/-- Spaces between tokens (the ONLY whitespace inside a line; a tab is
    a refusal — the indentation discipline's simplification). -/
def ws : GParser Unit := do
  let _spcs ← many (satisfy "space" (· == ' '))
  pure ()

/-- One newline. -/
def nl : GParser Unit := do
  let _c ← pchar '\n'
  pure ()

/-- The end of a statement: the rest of the line is blank, or the input
    ends (the last statement's face). -/
def eol : GParser Unit := do
  let _c ← (nl <|> eof)
  pure ()

/-- Blank lines: any number of space-only lines. -/
def blanks : GParser Unit := do
  let _ls ← many (do
    let _w ← ws
    let _n ← nl
    pure ())
  pure ()

/-- The reserved words — never identifiers (the parse refusals'
    positive face). -/
def keywords : List String :=
  ["def", "return", "if", "else", "while", "for", "in",
   "and", "or", "not", "True", "False"]

/-- The KEYWORD token: the literal + the word boundary — the next
    character must not be an identifier char (`ifx` is an identifier;
    `tok` alone is a plain prefix match and would split it). -/
def kw (s : String) : GParser Unit := do
  let _t ← tok s
  match ← peek with
  | Option.some c => if TextKit.isIdentChar c then failure else pure ()
  | Option.none => pure ()

/-- An identifier: alpha head, ident-chars after, NOT a keyword. -/
def identP : GParser String := label "identifier" do
  let c ← satisfy "identifier" Char.isAlpha
  let cs ← many (satisfy "identifier" TextKit.isIdentChar)
  let s := String.ofList (c :: cs)
  if keywords.contains s then failure else pure s

/-- An integer literal: one-or-more digits (the machine's face:
    literals at/above 2^64 refuse at CHECK — the model's face is
    Python's unbounded literal, the compiled surface's is the u64
    ring). -/
def natP : GParser Nat := label "integer" do
  let ds ← some (satisfy "digit" Char.isDigit)
  pure (ds.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0)

/-- The column of the next content character (consumes nothing). -/
def peekIndent : GParser Nat := do
  let spcs ← lookAhead (many (satisfy "space" (· == ' ')))
  pure spcs.length

/-- The next non-blank line starts with `s`? (consumes nothing; the
    EOF face is FALSE, never an error — the repetition's stop). -/
def nextIs (s : String) : GParser Bool :=
  (do
    let _b ← blanks
    lookAhead (tok s) >>= fun _ => pure true)
  <|> pure false

/-- The comma separator (with the surrounding spaces). -/
def commaP : GParser Unit := do
  let _c1 ← ws
  let _comma ← tok ","
  let _c2 ← ws
  pure ()

/-! ## The expression grammar (the precedence ladder — the FULL set) -/

mutual
/-- or level: `and (`or` and)…` left-folded (the lowest precedence). -/
def orP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let l ← andP fuel
      let rs ← many do
        let _o ← kw "or"
        let _w ← ws
        let r ← andP fuel
        GParser.result r
      pure (rs.foldl (fun acc r => .bin .or acc r) l)

/-- and level: `not (`and` not)…` left-folded. -/
def andP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let l ← notP fuel
      let rs ← many do
        let _o ← kw "and"
        let _w ← ws
        let r ← notP fuel
        GParser.result r
      pure (rs.foldl (fun acc r => .bin .and acc r) l)

/-- not level: `not not | cmp` (binds tighter than `and`/`or`). -/
def notP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 =>
      (do
        let _o ← kw "not"
        let _w ← ws
        let e ← notP fuel
        GParser.result (.un .not e))
      <|> cmpP fuel

/-- comparison level: ONE optional compare over add (no chaining —
    Python's `a < b < c` is the named exclusion). The LONGER tokens
    (`<=` `>=` `!=` `==`) try before the bare `<` `>` — `tok` is a
    plain prefix match. -/
def cmpP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let l ← addP fuel
      let cmp? ← TextKit.optional do
        let op ← (tok "==" <|> tok "!=" <|> tok "<=" <|> tok ">="
                  <|> tok "<" <|> tok ">")
        let _w ← ws
        let r ← addP fuel
        GParser.result (op, r)
      match cmp? with
      | Option.none => GParser.result l
      | Option.some (op, r) =>
          let cop : CmpOp :=
            if op == "==" then .eq
            else if op == "!=" then .ne
            else if op == "<=" then .le
            else if op == ">=" then .ge
            else if op == "<" then .lt
            else .gt
          GParser.result (.cmp cop l r)

/-- addition level: `mul (+|-) mul …` left-folded. -/
def addP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let l ← mulP fuel
      let ops ← many do
        let op ← (tok "+" <|> tok "-")
        let _w ← ws
        let r ← mulP fuel
        GParser.result (op, r)
      pure (ops.foldl (fun acc p =>
        match p.1 with
        | "+" => .bin .add acc p.2
        | _ => .bin .sub acc p.2) l)

/-- multiplication level. -/
def mulP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let l ← unaryP fuel
      let rs ← many do
        let _op ← tok "*"
        let _w ← ws
        let r ← unaryP fuel
        GParser.result r
      pure (rs.foldl (fun acc r => .bin .mul acc r) l)

/-- unary minus level: `- unary` → `0 - e` (the machine ring's
    spelling; binds tighter than `*`). -/
def unaryP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 =>
      (do
        let _o ← tok "-"
        let _w ← ws
        let e ← unaryP fuel
        GParser.result (.un .neg e))
      <|> postfixP fuel

/-- postfix level: the atom + the index suffixes `t[i]` (the checker
    pins `i` to an int literal). -/
def postfixP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => do
      let a ← atomP fuel
      let ixs ← many do
        let _o ← tok "["
        let _w ← ws
        let i ← exprP fuel
        let _w2 ← ws
        let _c ← tok "]"
        let _w3 ← ws
        GParser.result i
      pure (ixs.foldl (fun acc i => .idx acc i) a)

/-- the atom: literal | True | False | tuple | list | call | var |
    parens. The tuple's face: `(e)` is the paren expression, `(e, …)`
    the tuple (a SINGLETON tuple refuses — the named simplification). -/
def atomP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 =>
      (do
        let n ← natP
        let _w ← ws
        GParser.result (.int n))
      <|> (do
        let _t ← kw "True"
        let _w ← ws
        GParser.result (.boolV true))
      <|> (do
        let _t ← kw "False"
        let _w ← ws
        GParser.result (.boolV false))
      <|> (do
        let _o ← tok "["
        let _w ← ws
        let es ← sepBy (exprP fuel) commaP
        let _w2 ← ws
        let _c ← tok "]"
        let _w3 ← ws
        GParser.result (.listLit es))
      <|> (do
        let _o ← tok "("
        let _w ← ws
        let e1 ← exprP fuel
        let _w2 ← ws
        (do
          let _c ← tok ")"
          let _w3 ← ws
          GParser.result e1)
        <|> (do
          let _comma ← tok ","
          let _w4 ← ws
          let es ← sepBy (exprP fuel) commaP
          let _w5 ← ws
          let _c ← tok ")"
          let _w6 ← ws
          if es.isEmpty then failure else  -- the singleton-tuple refusal
            GParser.result (.tup (e1 :: es))))
      <|> (do
        let f ← identP
        let _w ← ws
        let _o ← tok "("
        let _w2 ← ws
        let args ← sepBy (exprP fuel) commaP
        let _w3 ← ws
        let _c ← tok ")"
        let _w4 ← ws
        GParser.result (.call f args))
      <|> (do
        let x ← identP
        let _w ← ws
        GParser.result (.var x))

/-- the expression entry (the ladder's top; a mutual member so `atomP`
    can call it — the explicit match arms give the termination
    inference its latching point). -/
def exprP : Nat → GParser Expr
  | 0 => failure
  | fuel+1 => orP fuel
end

/-! ## The statement/block zone (the guarded hand zone — the
##    WAT funcP precedent: column-threaded, fuel-bounded) -/

mutual
/-- One statement at column `col` (the indent ALREADY consumed by
    `stmtsP`). The `if`'s optional `else` is detected AFTER its
    then-block: backtracking restores the cursor when the next
    same-column statement is not `else`. -/
def stmtP (col : Nat) : Nat → GParser Stmt
  | 0 => failure
  | fuel+1 =>
      (do
        let _k ← kw "return"
        let _w ← ws
        let e ← exprP fuel
        let _e ← eol
        GParser.result (.ret e))
      <|> (do
        let _k ← kw "if"
        let _w ← ws
        let c ← exprP fuel
        let _w2 ← ws
        let _co ← tok ":"
        let _n ← nl
        let thenB ← blockP col fuel
        let elseB ← optElse col fuel
        GParser.result (.ifelse c thenB elseB))
      <|> (do
        let _k ← kw "while"
        let _w ← ws
        let c ← exprP fuel
        let _w2 ← ws
        let _co ← tok ":"
        let _n ← nl
        let body ← blockP col fuel
        GParser.result (.while c body))
      <|> (do
        let _k ← kw "for"
        let _w ← ws
        let x ← identP
        let _w2 ← ws
        let _in ← kw "in"
        let _w3 ← ws
        let xs ← exprP fuel
        let _w4 ← ws
        let _co ← tok ":"
        let _n ← nl
        let body ← blockP col fuel
        GParser.result (.forIn x xs body))
      <|> (do
        let x ← identP
        let _w ← ws
        let _eq ← tok "="
        let _w2 ← ws
        let e ← exprP fuel
        let _e ← eol
        GParser.result (.assign x e))

/-- The `else:` arm of an `if` at column `col` — `[]` when the next
    same-column line is not `else` (the backtrack default). -/
def optElse (col : Nat) : Nat → GParser (List Stmt)
  | 0 => failure
  | fuel+1 =>
      (do
        let _b ← blanks
        let c ← peekIndent
        if c == col then pure () else failure
        let _w ← ws
        let _e ← kw "else"
        let _w2 ← ws
        let _co ← tok ":"
        let _n ← nl
        let ss ← blockP col fuel
        GParser.result ss)
      <|> GParser.result []

/-- A block body: the statements at the FIRST content line's column,
    which must be strictly deeper than `parentCol` (Python's block
    discipline; a tab-indented line refuses at `satisfy`). -/
def blockP (parentCol : Nat) : Nat → GParser (List Stmt)
  | 0 => failure
  | fuel+1 => do
      let _b ← blanks
      let c ← peekIndent
      if c > parentCol then pure () else failure
      stmtsP c fuel

/-- The statements at EXACTLY column `col` (at least one). -/
def stmtsP (col : Nat) : Nat → GParser (List Stmt)
  | 0 => failure
  | fuel+1 => do
      let c ← peekIndent
      if c == col then pure () else failure
      let _w ← ws
      let s ← stmtP col fuel
      let _b ← blanks
      let c' ← peekIndent
      if c' == col then do
        let ss ← stmtsP col fuel
        GParser.result (s :: ss)
      else GParser.result [s]
end

/-! ## The function + module levels -/

/-- One `def`: the params parenthesized, the body an indented block. -/
def funcP : Nat → GParser Fn
  | 0 => failure
  | fuel+1 => do
      let _k ← kw "def"
      let _w ← ws
      let name ← identP
      let _w2 ← ws
      let _o ← tok "("
      let _w3 ← ws
      let params ← sepBy identP commaP
      let _w4 ← ws
      let _c ← tok ")"
      let _w5 ← ws
      let _d ← tok ":"
      let _n ← nl
      let body ← blockP 0 fuel
      GParser.result { name := name, params := params, body := body }

/-- The module: the functions, blank-line separated, to the end. -/
def programP : Nat → GParser (List Fn)
  | 0 => failure
  | fuel+1 => do
      let _b ← blanks
      let isDef ← nextIs "def"
      if isDef then do
        let f ← funcP fuel
        let fs ← programP fuel
        GParser.result (f :: fs)
      else do
        let _b2 ← blanks
        let _e ← eof
        GParser.result []

/-! ## The entry -/

/-- Parse a module's text (the full-consumption check rides `programP`'s
    `eof`). The fuel is a model artifact: every recursive hop consumes
    input, so `4 * length + 8` bounds the deepest program; exhaustion
    is the honest parse refusal. -/
def parseProgram (text : String) : Except String (List Py.Fn) :=
  match runG (programP (4 * text.length + 8)) text.toList with
  | .error e => .error s!"edgepython parse: {TextKit.Diag.toString e.toDiag}"
  | .ok (fns, rest) =>
      if rest.isEmpty then .ok fns
      else .error s!"edgepython parse: {rest.length} trailing characters"

end Guest.EdgePython.Parse
