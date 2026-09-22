/-
# Substrait.Meta.Inversion — `declare_inversion`: the parse∘emit row
# inversion theorems, generated

Does NOT import the Substrait packages, only names them (the DECLARED
names resolve in the use-site namespace; every other reference is written
by the entry and elaborated at the site).

The theorem family `parse (emit x) = some x` is THE row shape inverted, and
each member is generated from ONE row spec, so the statement and the
resolution chain cannot drift from the row:

    declare_inversion inv_urnLine where
      parse := parseUrnEntry
      emit := Emit.Text.urnLine a urn
      binders := (a : Nat) (urn : String)
      result := { extensionUrnAnchor := a, urn := urn }
      line := [invtok Grammar.indentUnit "  " invlit "@" invanchor a
               invtok Grammar.colonSpTok ": " invname urn]
      steps := [invreduce parseUrnEntryBody.eq_1 invscan a invexpect colonTok invfinish]
      cor := parseUrnEntry_urnLine

generates, in the enclosing namespace:

    theorem inv_urnLine (a : Nat) (urn : String) :
        parseUrnEntry (Emit.Text.urnLine a urn).toList =
          some { extensionUrnAnchor := a, urn := urn } := by
      have hline : ... := by
        rw [Emit.Text.urnLine]; repeat rw [String.toList_append]
        rw [show Grammar.indentUnit.toList = [' ', ' '] from by decide]
        ...
        simp [List.append_assoc]
      unfold parseUrnEntry
      rw [hline]
      rw [List.dropWhile_cons_of_pos (by decide), ...]
      rw [parseUrnEntryBody.eq_1]
      rw [rightJustify_dropWhile_append]
      rw [scanNat_of_toString a (':' :: ' ' :: urn.toList) (notDigitHead_colon _)]
      dsimp only
      rw [expect_colon]
      dsimp only
      simp [String.ofList_toList]

    theorem parseUrnEntry_urnLine (a : Nat) (urn : String) :
        ... := inv_urnLine a urn

The `invcor` corollary keeps the pre-macro theorem name live — the axiom
gate's `#print axioms` list pins exactly those names.

## The family vocabulary (the row grammar)

`line` is the emitted row's character content as space-separated segments:

- `lit "…"` — a verbatim character run (revealed `by decide`).
- `tok <ident> "…"` — a token CONSTANT whose value is the run; the reveal
  targets the constant (e.g. `Grammar.indentUnit.toList`), and the run is
  the self-checking witness (a stale run fails `decide` at build).
- `pfx` — `Grammar.versionPfx` (the version header's lead; its `.toList`
  atom balances the header equation, so it is never revealed).
- `dot` — `Grammar.dotTok` (the version dots; the family's one dot token).
- `anchor <x>` — a Nat field right-justified to width 3
  (`Emit.Text.rightJustify 3 x`): the decoder's `scanNat` reads it back
  through `rightJustify_dropWhile_append`.
- `num <x>` — a Nat field rendered bare (`toString x`): the version numbers.
- `name <v>` — the trailing String field (read back via `String.ofList`).

`steps` is the resolution chain (the hand-proof ladders this command
replaces), also space-separated:

- `reduce <thm>` — `rw [thm]` (a parser equation lemma, e.g.
  `parseUrnEntryBody.eq_1`).
- `scan <x>` — the anchor/number scan: `rightJustify_dropWhile_append`
  (anchors) then `scanNat_of_toString x (material) (notDigitHead_<c> _)`
  then `dsimp only`.  The stop lemma comes from the segment right after
  `x` (`:` → `notDigitHead_colon`, `.` → `notDigitHead_dot`, a space →
  `notDigitHead_space` — the closed family).  An `anchor` scan with
  nothing after it is an error; a `num` scan with an empty tail emits the
  `Or.inl rfl` empty-tail form (a patch number).
- `peel "…"` — a mid-row `dropWhile` (usage: `peel " @"`): spaces →
  `List.dropWhile_cons_of_pos`, the first non-space → `_of_neg` (the decl
  entry's `" @"` separator).
- `expect <tok>` — `rw [expect_colon]`/`rw [expect_dot]` by token name,
  then `dsimp only`.
- `finish` — `simp [String.ofList_toList]` (the trailing name read-back).
- `tail` — splice the entry's `proof := by …` block verbatim (the version
  row's presence-conditional producer/git case split — the ONE non-row-
  shaped part of the cluster; its references are public by design).

## Row kinds

- **Anchor rows** (`line` has an `anchor`): the emitted text is one
  String; the proof unfolds the parser, peels the lead (`dropWhile`),
  reduces the equation lemmas, and walks the scans/expects.
- **Version rows** (`line` starts with `pfx`): the emitted text is a
  List String whose head is the version header; the proof destructures
  the version record, reduces the header (`expect_self`), walks the three
  number-dot scans, and splices the `tail`.

## Deliberate exclusions

- The Root-names row (`parseRootNames_emitted`): its proof rides the
  private `splitTopLevel`/identifier lemma stack in Decode.Plan — not a
  row-shape twin; it stays hand-written there.
- The scalar-type suffix rows (`parseType_scalar_withNull` + the required/
  nullable twins): lexCtor-shaped, not anchor/scan-shaped; their shared
  core lemma stays private in Decode.Types.
- Only the closed token set above is known (three stop lemmas, two expect
  lemmas, one dot, one pfx).  A row needing a new separator extends THIS
  module, never an entry's raw text.

## Mechanics (the binop/EnumWire lessons, not re-paid)

- `@[command_elab]`, not `macro`: the entry fields are parsed pieces
  (binders, line, steps) that the generator re-composes, and the optional
  `cor`/`proof` blocks are named syntax categories (the pattern for
  keyword-wrapped optionals in `syntax`, probed on v4.33.0).
- Template references are TEXT: the generated body is source text
  (`Parser.runParserCategory` + `elabCommand`, the EnumWire pattern); a
  generator mistake is an internal parse/elab error, never silent drift.
- The DECLARED names (`inv_urnLine`, the `cor` theorem) are scope-free in
  the generated text — they resolve in the use-site namespace
  (`Substrait.Decode`); every other constant is written by the entry and
  elaborated there.
- Segment/step contents are extracted POSITIONALLY from the syntax nodes
  (named kinds, `isOfKind`); custom-category QUOTATION patterns and
  category-annotated quotations are deliberately avoided (they mis-parse
  and one crashed the probes — recorded under the probe lessons).
- The materializer's nesting is list-constructor-canonical (`'c' :: `
  conses and ` ++ ` joins); `rw` matches any defeq association, so the
  generated forms never need to mirror the hand proofs' parentheses.
- The `line`/`steps` lists are space-separated (no commas): a repeated
  custom category in a `syntax` declaration quotes as `$segs:cat*`, and
  the comma form `$($segs:cat),*` is not supported by quotation.

## Pitfalls (probed on v4.33.0)

- Every `syntax "…"` ATOM registers as a RESERVED TOKEN in every file that
  imports this module.  All atoms are therefore `inv`-prefixed (never
  bare words like `parse`/`emit`/`name` — the module chain broke the whole
  Substrait Tests bundle on import when they were bare); a future atom
  must follow the prefix rule.
- A seven-letter `invemit` atom failed to register while the six-letter
  `invent` works; only spells that have compiled in-build are safe — treat
  the atoms below as closed and verify any new one in a scratch file.
- `docComment ?` before this command is rejected (the command has no doc
  slot), and `/-- -/` docs must not precede `namespace` commands.
- `bracketedBinder*` followed by a keyword field is greedy — a bare-ident
  binder can swallow the keyword; write binders parenthesized.

Core-only: `public import Lean` and nothing else — the generated theorems
consume the package, the command does not.
-/

module

public import Lean

public meta section

namespace Substrait.Meta

open Lean Lean.Parser.Command Lean.Elab.Command

/-- A `line` segment (see the module header). -/
declare_syntax_cat inversionSeg

syntax (name := invLit) "invlit " str : inversionSeg
syntax (name := invTok) "invtok " ident str : inversionSeg
syntax (name := invPfx) "invpfx" : inversionSeg
syntax (name := invDot) "invdot" : inversionSeg
syntax (name := invAnchor) "invanchor " ident : inversionSeg
syntax (name := invNum) "invnum " ident : inversionSeg
syntax (name := invName) "invname " ident : inversionSeg

/-- A resolution step (see the module header). -/
declare_syntax_cat inversionStep

syntax (name := invReduce) "invreduce " term : inversionStep
syntax (name := invScan) "invscan " ident : inversionStep
syntax (name := invPeel) "invpeel " str : inversionStep
syntax (name := invExpect) "invexpect " ident : inversionStep
syntax (name := invFinish) "invfinish" : inversionStep
syntax (name := invTail) "invtail" : inversionStep

/-- The optional `cor <oldName>` corollary block. -/
declare_syntax_cat inversionCor
syntax (name := invCor) "invcor " " := " ident : inversionCor

/-- The optional `proof := by …` bespoke tail. -/
declare_syntax_cat inversionProof
syntax (name := invProof) "invproof " " := " term : inversionProof

/--
`declare_inversion <newName> where` — see the module header for the field
vocabulary and the generated shapes.

```
declare_inversion <newName> where
  invparse := <parser term>
  invent := <emitter application>
  invbinders := <bracket binder list>
  invresult := <the `some` payload>
  invline := [<segment>*]
  invsteps := [<step>*]
  invcor := <old-name corollary>      (optional)
  invproof := by <tail>               (optional; only read with a `tail` step)
```
-/
syntax (name := declareInversion)
  "declare_inversion " ident " where"
  " invparse " " := " term
  " invent " " := " term
  " invbinders " " := " bracketedBinder*
  " invresult " " := " term
  " invline " " := " "[" inversionSeg* "]"
  " invsteps " " := " "[" inversionStep* "]"
  optional(inversionCor) optional(inversionProof) : command


namespace InversionImpl

/- Segment extraction: named kinds (`invLit` …), positional args (the node
   arg 0 is the leading ATOM token; content sits at arg 1+).  The accessor
   names avoid the syntax-atom tokens (`lit`, `tok`, `dot`, `num`, `name`,
   `scan`, `expect`, `finish`, `tail`, `pfx` — the `syntax "…"` atoms
   register as reserved tokens inside this module). -/

/-- Kind comparison: `syntax (name := invX)` registers its kind under the
    declaration namespace; compare the last component only. -/
def isKindRoot (stx : Syntax) (nm : Name) : Bool :=
  (stx.getKind).toString.endsWith ("." ++ nm.toString)

namespace Seg

def isLit : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invLit
def isTok : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invTok
def isPfx : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invPfx
def isDot : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invDot
def isAnchor : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invAnchor
def isNum : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invNum
def isName : TSyntax `inversionSeg → Bool := fun s => isKindRoot s.raw `invName

/-- The literal run of a `lit`/`tok` segment. -/
def litStr : TSyntax `inversionSeg → Option String
  | s =>
    if isLit s then (s.raw.getArg 1).isStrLit?
    else if isTok s then (s.raw.getArg 2).isStrLit?
    else none

/-- The token constant ident of a `tok` segment. -/
def tokName : TSyntax `inversionSeg → Option Name
  | s => if isTok s then some (s.raw.getArg 1).getId else none

/-- The carried variable of an `anchor`/`num`/`name` segment. -/
def var : TSyntax `inversionSeg → Option Name
  | s => if isAnchor s || isNum s || isName s then some (s.raw.getArg 1).getId else none

end Seg

/-- The character run of a literal, cons-headed (`'a' :: 'b' :: `). -/
def charRun : String → String
  | s => String.intercalate " :: " (s.toList.map (fun c => s!"'{c}'")) ++ " :: "

/-- The material fragment of one segment. -/
def segMaterial : TSyntax `inversionSeg → String
  | s =>
    if Seg.isLit s then charRun (Seg.litStr s).get!
    else if Seg.isTok s then charRun (Seg.litStr s).get!
    else if Seg.isPfx s then "Grammar.versionPfx.toList"
    else if Seg.isDot s then "'.' :: "
    else if Seg.isAnchor s then s!"(Emit.Text.rightJustify 3 {(Seg.var s).get!}).toList"
    else if Seg.isNum s then s!"(toString {(Seg.var s).get!}).toList"
    else if Seg.isName s then s!"{(Seg.var s).get!}.toList"
    else "⟨inversionSeg⟩"

/-- The materialized row (recursive): a cons-headed piece wraps the rest in
    parens (`'c' :: (…)`, so every term is CONS-HEADED — the `dropWhile`/rl
    rewrites match by shape); a `.toList` piece joins with ` ++ `.  The
    result is defeq to any hand-written parenthesized form. -/
partial def materialized : List (TSyntax `inversionSeg) → String
  | [] => ""
  | seg :: rest =>
    let p := segMaterial seg
    let m := materialized rest
    if m == "" then p
    else if p.endsWith ":: " then p ++ "(" ++ m ++ ")"
    else p ++ " ++ " ++ m

/-- The first character of a segment's material (the scan stop). -/
def segHeadChar : TSyntax `inversionSeg → Option Char
  | s => match Seg.litStr s with
    | some str => str.toList.head?
    | none => if Seg.isDot s then some '.' else none

/-- Scan-stop lemma for the closed family. -/
def stopLemma : Char → Option String
  | ':' => some "notDigitHead_colon"
  | '.' => some "notDigitHead_dot"
  | ' ' => some "notDigitHead_space"
  | _ => none

/-- The expect lemma for `colonTok`/`dotTok`. -/
def expectLemma : Name → Option String
  | `colonTok => some "expect_colon"
  | `dotTok => some "expect_dot"
  | _ => none

/-- The index of the segment carrying `x`. -/
def segIdx (segs : Array (TSyntax `inversionSeg)) (x : Name) : Option Nat :=
  segs.toList.findIdx? (fun s => Seg.var s == some x)

/-- Scan metadata: the material after `x` and its stop; `none` stop means
    an empty tail (the `Or.inl rfl` patch form). -/
def scanInfo (segs : Array (TSyntax `inversionSeg)) (x : Name) : Except String (String × Option String) := do
  let some idx := segIdx segs x
    | .error s!"declare_inversion: scan {x} has no anchor/num segment"
  let tl := segs.toList.drop (idx + 1)
  if tl.isEmpty then
    pure ("", none)
  else
    let mat := materialized tl
    let c ← match segHeadChar tl.head! with
      | some c => pure c
      | none => .error s!"declare_inversion: scan {x} tail starts with a non-literal segment"
    let lem ← match stopLemma c with
      | some lem => pure lem
      | none => .error s!"declare_inversion: no notDigitHead lemma for '{c}' after {x}"
    pure (mat, some lem)

/-- The scan step text (anchor vs number mode; the empty-tail patch form). -/
def scanStep (segs : Array (TSyntax `inversionSeg)) (x : Name) : Except String String := do
  let some idx := segIdx segs x
    | .error s!"declare_inversion: scan {x} has no anchor/num segment"
  let (mat, stop) ← scanInfo segs x
  if Seg.isAnchor segs[idx]! then
    let lem ← match stop with
      | some lem => pure lem
      | none => .error s!"declare_inversion: anchor scan {x} needs a following separator segment"
    pure s!"  rw [rightJustify_dropWhile_append]\n  rw [scanNat_of_toString {x} ({mat}) ({lem} _)]\n  dsimp only"
  else if Seg.isNum segs[idx]! then
    match stop with
    | some lem => pure s!"  rw [scanNat_of_toString {x} ({mat}) ({lem} _)]\n  dsimp only"
    | none => pure s!"  have hpt := scanNat_of_toString {x} ([] : List Char) (Or.inl rfl)\n  rw [List.append_nil] at hpt\n  rw [hpt]\n  dsimp only"
  else
    .error s!"declare_inversion: scan {x} is not an anchor/num segment"

/-- The mid-row `dropWhile` peels. -/
def peelStep (s : String) : String :=
  let rws := s.toList.map (fun c => if c == ' ' then "List.dropWhile_cons_of_pos (by decide)" else "List.dropWhile_cons_of_neg (by decide)")
  "  rw [" ++ String.intercalate ", " rws ++ "]"

/-- The header reveal rewrites: one `rw [show <atom>.toList = [...] from by
    decide]` per literal/token run (the hline proof flattens every `++` and
    the reveals fire on each `.toList` atom, anchors/names excepted). -/
def leadReveals (segs : Array (TSyntax `inversionSeg)) : String :=
  let pre := segs.toList.filter (fun s => Seg.litStr s != none)
  String.intercalate "\n" (pre.map fun seg =>
    let chars := String.intercalate ", " ((Seg.litStr seg).get!.toList.map (fun c => s!"'{c}'"))
    let atomTxt := if Seg.isTok seg then s!"{(Seg.tokName seg).get!}" else s!"\"{(Seg.litStr seg).get!}\""
    s!"    rw [show {atomTxt}.toList = [{chars}] from by decide]")

/-- The lead `dropWhile` peels (spaces → `_of_pos`, the first non-space →
    `_of_neg`). -/
def leadPeels (segs : Array (TSyntax `inversionSeg)) : String :=
  let pre := segs.toList.takeWhile (fun s => Seg.var s == none)
  let rws := (pre.flatMap (fun seg =>
    match Seg.litStr seg with
    | some s => s.toList
    | none => [])).map (fun c => if c == ' ' then "List.dropWhile_cons_of_pos (by decide)" else "List.dropWhile_cons_of_neg (by decide)")
  if rws.isEmpty then "" else "  rw [" ++ String.intercalate ", " rws ++ "]"

/-- Version-row detection (`pfx`-leading line). -/
def isVersion : Array (TSyntax `inversionSeg) → Bool
  | segs => match segs[0]? with | some seg => Seg.isPfx seg | none => false

/-- The `tail` marker (the step list position where the proof splices). -/
def markTail : String := "⟨⟨tail⟩⟩"

/-- The version record destructuring + the `hvl` line-shape preamble. -/
def versionPreamble : String :=
  "  obtain ⟨mj, mn, pt, prod, git⟩ := v\n" ++
  "  show parseVersion (Emit.Text.versionLines ⟨mj, mn, pt, prod, git⟩ ++ rest)\n" ++
  "    = some (⟨mj, mn, pt, prod, git⟩, rest)\n" ++
  "  have hvl : Emit.Text.versionLines ⟨mj, mn, pt, prod, git⟩ =\n" ++
  "      (Grammar.versionPfx ++ toString mj ++ Grammar.dotTok ++ toString mn ++\n" ++
  "        Grammar.dotTok ++ toString pt) ::\n" ++
  "        ((if prod.isEmpty then [] else [Grammar.producerPfx ++ prod]) ++\n" ++
  "          (if git.isEmpty then [] else [Grammar.gitHashPfx ++ git])) := by\n" ++
  "    rfl\n" ++
  "  rw [hvl, List.cons_append]\n" ++
  "  unfold parseVersion\n" ++
  "  dsimp only"

/-- The version header equation (LHS in `Grammar` token form; RHS from the
    row material). -/
def versionHeader (segs : List (TSyntax `inversionSeg)) : String :=
  let rest := segs.drop 1  -- the `pfx` lead is the header's literal prefix
  let xs := rest.map (fun s =>
    if Seg.isNum s then s!"toString {(Seg.var s).get!}"
    else if Seg.isDot s then "Grammar.dotTok"
    else "")
  let lhs := String.intercalate " ++ " xs
  let rhs := "Grammar.versionPfx.toList ++ (" ++ materialized rest ++ ")"
  s!"  have hheader : (Grammar.versionPfx ++ {lhs}).toList = {rhs} := by\n" ++
  "    repeat rw [String.toList_append]\n" ++
  "    rw [show Grammar.dotTok.toList = ['.'] from by decide]\n" ++
  "    simp [List.append_assoc]\n" ++
  "  rw [hheader]\n" ++
  "  rw [expect_self]\n" ++
  "  dsimp only"

/-- Binder pieces (positional — bracket binder nodes are NOT
    term-quotation-shaped): the ident syntaxes and the optional type. -/
def binderParts (b : Syntax) : Except String (Array Syntax × Option Syntax) := do
  if b.isOfKind `Lean.Parser.Term.explicitBinder then
    let ids := b.getArg 1
    let ty := b.getArg 2
    pure (ids.getArgs, some (ty.getArg 1))
  else if b.isOfKind `Lean.Parser.Term.binderIdent then
    pure (#[b], none)
  else
    .error s!"declare_inversion: unsupported binder shape {b}"

/-- The main proof body for a version row (preamble + header + step texts
    + the spliced tail). -/
def versionBody (segs : Array (TSyntax `inversionSeg)) (stepTxts : Array String)
    (tailProof : Option String) : Except String String := do
  let mut lines := (versionPreamble.splitOn "\n") ++ (versionHeader segs.toList).splitOn "\n"
  for t in stepTxts do
    if t == markTail then
      match tailProof with
      | some p => lines := lines ++ p.splitOn "\n"
      | none => .error "declare_inversion: a `tail` step needs a `proof := by …` block"
    else
      lines := lines ++ t.splitOn "\n"
  pure (String.intercalate "\n" lines)

/-- The main proof body for an anchor row (hline + unfold + peels + step
    texts). -/
def anchorBody (parseFn emitFn fnName : String) (segs : Array (TSyntax `inversionSeg))
    (stepTxts : Array String) : Except String String := do
  let hlineRHS := materialized segs.toList
  let mut lines : List String :=
    [ s!"  have hline : ({emitFn}).toList = {hlineRHS} := by"
    , s!"    rw [{fnName}]"
    , "    repeat rw [String.toList_append]" ]
    ++ (leadReveals segs).splitOn "\n" ++ ["    simp [List.append_assoc]"]
    ++ [ s!"  unfold {parseFn}"
       , "  rw [hline]" ]
    ++ (if leadPeels segs == "" then [] else [leadPeels segs])
  for t in stepTxts do
    if t == markTail then
      .error "declare_inversion: a `tail` step is only valid on a version row"
    else
      lines := lines ++ t.splitOn "\n"
  pure (String.intercalate "\n" lines)

/-- Two-space indentation of the generated body. -/
def indent : String → String := fun s =>
  String.intercalate "\n" ((s.splitOn "\n").map (fun l => if l == "" then "" else "  " ++ l))

/-- The leftmost function symbol of an application term (raw syntax). -/
partial def rawAppFn : Syntax → Syntax
  | t => if t.isOfKind `Lean.Parser.Term.app then rawAppFn (t.getArg 0) else t

/-- The two generated declarations: (theorem source, corollary source). -/
def generated (thmName : String) (parseFn parseHead emitFn res : String) (emitFnName : String)
    (bt args : String)
    (segs : Array (TSyntax `inversionSeg))
    (stepTxts : Array String) (corN : Option String) (tailProof : Option String) :
    Except String (String × String) := do
  let version := isVersion segs
  let emitted := if version then "(" ++ emitFn ++ ")" else "(" ++ emitFn ++ ").toList"
  let statement := parseFn ++ " " ++ emitted ++ " = " ++ res
  let body ← if version then versionBody segs stepTxts tailProof
    else anchorBody parseHead emitFn emitFnName segs stepTxts
  let thm := s!"theorem {thmName} {bt} :\n    {statement} := by\n" ++ body ++ "\n"
  let corS := match corN with
    | some c =>
      s!"theorem {c} {bt} :\n    {statement} := {thmName} {args}\n"
    | none => ""
  pure (thm, corS)

/-- Elaborate the generated source; parse errors are internal (the
    generator wrote the code). -/
def elabGenerated (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e => throwError ("declare_inversion: internal: generated code failed to parse\n" ++ src ++ "\n" ++ e)

end InversionImpl

/- The `declare_inversion` command handler: slices the entry's source text
   for every spliced syntax piece (Syntax.toString renders the tree, not
   the source), builds the step texts, and drives the generator. -/
@[command_elab declareInversion]
def elabDeclareInversion : CommandElab := fun stx => do
  match stx with
  | `(declare_inversion $thm:ident where
      invparse := $parseT:term
      invent := $emitT:term
      invbinders := $bs*
      invresult := $resT:term
      invline := [$segs:inversionSeg*]
      invsteps := [$stps:inversionStep*]
      $[$corB?:inversionCor]? $[$proofB?:inversionProof]?) => do
    let fm ← getFileMap
    let srcOf (s : Syntax) : CommandElabM String := do
      match s.getPos?, s.getTailPos? with
      | some a, some b => pure (String.Pos.Raw.extract fm.source a b)
      | _, _ => pure (toString s)
    let parseS ← srcOf parseT
    let parseHeadS ← srcOf (InversionImpl.rawAppFn parseT)
    let emitS ← srcOf emitT
    let resS ← srcOf resT
    let emitFnS ← srcOf (InversionImpl.rawAppFn emitT)
    let mut binderTxts : Array String := #[]
    let mut allArgs : Array String := #[]
    for b in bs do
      let (ids, ty) ← match InversionImpl.binderParts b with
        | .ok p => pure p
        | .error e => throwError e
      let mut idTxts : Array String := #[]
      for i in ids do
        let is ← srcOf i
        allArgs := allArgs.push is
        idTxts := idTxts.push is
      match ty with
      | some t =>
        let ts ← srcOf t
        binderTxts := binderTxts.push ("(" ++ String.intercalate " " idTxts.toList ++ " : " ++ ts ++ ")")
      | none =>
        binderTxts := binderTxts.push (String.intercalate " " idTxts.toList)
    let bt := String.intercalate " " binderTxts.toList
    let args := String.intercalate " " allArgs.toList
    let stepTxts ← stps.mapM fun stp => do
      if InversionImpl.isKindRoot stp.raw `invReduce then
        pure (s!"  rw [{← srcOf (stp.raw.getArg 1)}]")
      else if InversionImpl.isKindRoot stp.raw `invScan then
        match InversionImpl.scanStep segs (stp.raw.getArg 1).getId with
        | .ok s => pure s
        | .error e => throwError e
      else if InversionImpl.isKindRoot stp.raw `invPeel then
        pure (InversionImpl.peelStep ((stp.raw.getArg 1).isStrLit?.getD ""))
      else if InversionImpl.isKindRoot stp.raw `invExpect then
        match InversionImpl.expectLemma (stp.raw.getArg 1).getId with
        | some lem => pure (s!"  rw [{lem}]\n  dsimp only")
        | none => throwError "declare_inversion: expect takes colonTok or dotTok"
      else if InversionImpl.isKindRoot stp.raw `invFinish then
        pure "  simp [String.ofList_toList]"
      else if InversionImpl.isKindRoot stp.raw `invTail then
        pure InversionImpl.markTail
      else
        throwError "declare_inversion: unknown step"
    let corN ← match corB? with
      | some c => pure (some (s!"{(c.raw.getArg 2).getId}"))
      | none => pure none
    let tailS ← match proofB? with
      | some p =>
        -- the source of `proof := by <seq>` starts with the `by` line;
        -- splice only the sequence that follows it
        let src ← srcOf (p.raw.getArg 2)
        let rest := match src.splitOn "\n" with
          | _ :: tl =>
            -- re-base the entry's `by`-block (base 4 in the entry) onto the
            -- generated body (base 2): strip two leading spaces per line
            String.intercalate "\n" (tl.map (fun l => if l.startsWith "  " then (l.drop 2).toString else l))
          | [] => src
        pure (some rest)
      | none => pure none
    match InversionImpl.generated (thm.getId.eraseMacroScopes.toString) parseS parseHeadS emitS resS emitFnS bt args segs stepTxts corN tailS with
    | .ok (thmSrc, corSrc) =>
        InversionImpl.elabGenerated thmSrc
        if corSrc != "" then InversionImpl.elabGenerated corSrc
    | .error e => throwError e
  | _ => throwError "declare_inversion: unsupported syntax"

end Substrait.Meta

end -- public meta section
