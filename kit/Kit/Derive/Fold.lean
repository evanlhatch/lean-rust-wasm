/-
# Kit.Derive.Fold — the initial-algebra fold generator (`declare_fold`)

`declare_fold <Ind>` over a closed, parameter-free, index-free inductive
generates the fold's whole entourage MECHANICALLY (06 §7: a family of N
near-identical decls is a macro that hasn't been written; 01 §1: every
closed universe gets its fold):

- `<Ind>Alg (α : Type)` — the ALGEBRA record: one field per constructor,
  each receiving the folded children (a recursive argument's slot is the
  carrier `α`; every other argument passes through raw). Exhaustiveness
  in the type: a new constructor refuses to compile until every algebra
  grows its row (15-patterns #15).
- `fold<Ind>` — THE FOLD: total, structural, kernel-visible (the
  `foldTy` shape; concrete algebras reduce by `rfl`).
- `fold<Ind>_<ctor>` — the equation set (06 §5), all `rfl` (the
  recursion is structural, so the equations are kernel reduction).
- `fold<Ind>_unique` — THE INITIALITY LAW: a function that commutes
  with the algebra on every constructor IS the fold. The proof is the
  TEMPLATE (the recursor + per-ctor `rw [h_<ctor> args, ihs…, eq
  lemma]` blocks — 06 §10: template-generated, never grind-grown),
  emitted from the same ctor analysis the equations came from.

HONEST SCOPE (each refusal is a curated `Kit.Diag`, the unsupported
shape NAMED — 05 §4):

- indexed (GADT) inductives — the DEPENDENT fold (the motive riding
  the index, 06 §2's `foldValue` discipline) has LANDED as
  `Kit.Derive.DepFold`'s `declare_dependent_fold` (the one-index,
  ctor-headed-index fragment; multi-index, mutual-sibling, and
  variable-index shapes stay out);
- type parameters — the parameter-threaded fragment is the named
  extension (V1 is the parameter-free closed fragment);
- empty constructor sets — the empty universe's fold is `nomatch`,
  which an algebra record cannot carry;
- nested occurrences (`List <Ind>` below the root) and dependent
  constructor arguments — the flat-sibling/sigma shapes are the 06 §2
  pattern;
- non-explicit (implicit/instance) constructor arguments.

The proof discipline: the generated theorems are recursor-driven
templates over the ctor data — the same build-stability class as
`decide` (06 §10); a shape the template cannot carry fails to
elaborate (wrongness does not elaborate).

THE EMISSION IS THE PARSE ROUTE (15-patterns #19; the wave-30 probe's
migration): the generated commands render to SOURCE TEXT + re-parse
(`Lean.Parser.runParserCategory`), never quotation splices — the fresh
parse elaborates exactly like hand code, and the emission carries no
macro-scope machinery (DepFold's wave-29 lesson). The quotation-route
helpers this module still carries are BRIDGE's (its probe has not
landed); they stay with their consumer.

E-codes: the `KD00xx` rows below (Kit-derive; the same convention as
`Kit.Lane`'s `KL00xx` — the registry's persisted allocation is the
code-registry gate's business when the row lands).

Core-only (imports Lean + Kit.Diag — the cone rule). META module: the
generated decls are ordinary core-level definitions + theorems.

Five questions (notes/v3/01-core.md):
- root: META — the initial-algebra discipline's generator face (01 §1).
- carrier grade: none of its own; the generated surface is the algebra
  record + the fold (the consumers' algebras are the carriers).
- spine reading: the SHARED recursion stage — one fold per universe,
  consumers as algebras.
- ladder rung: the generated laws are recursor templates + `rfl`
  equations (kernel-visible; zero axioms — pinned by KitTests).
- gate row: KitTests' fold suite (the fixture fold ≡ the hand fold via
  the initiality citation + the refusal teeth + the negative controls).
-/

import Lean
import Kit.Diag
import Kit.Derive.Common

namespace Kit.Derive.Fold

open Lean Elab Command Meta

/-! ## The curated failures -/

/-- The KD family — the fold generator's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    DECLARATION — the sites below use them, never a bare string, and
    the code-registry gate's coverage scan ties every spelling to its
    allocated live row (a hand-strung code is a gate refusal).
    (`throwDiag`, the refusal engine, is Kit.Derive.Common's — the
    drivers' ONE copy; opened below.) -/
def eKD0001 : Kit.ECode := ⟨"KD0001"⟩
def eKD0002 : Kit.ECode := ⟨"KD0002"⟩
def eKD0003 : Kit.ECode := ⟨"KD0003"⟩
def eKD0004 : Kit.ECode := ⟨"KD0004"⟩
def eKD0005 : Kit.ECode := ⟨"KD0005"⟩
def eKD0006 : Kit.ECode := ⟨"KD0006"⟩
def eKD0007 : Kit.ECode := ⟨"KD0007"⟩
def eKD0008 : Kit.ECode := ⟨"KD0008"⟩
def eKD0009 : Kit.ECode := ⟨"KD0009"⟩

open Kit.Derive.Common (throwDiag resolveConst?)

/-! ## The inductive analysis -/

/-- One constructor's analyzed shape: the ctor's full name, its row name
    (the last component), the argument types in order, and the positions
    of the RECURSIVE arguments (the arguments that ARE the inductive). -/
structure CtorShape where
  name : Name
  field : String
  argTys : Array Expr
  recArgs : Array Nat

/-- The inductive's last component (the generated names' base). -/
def baseNameOf (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The V1-scope checks over the resolved inductive, before any ctor
    analysis (the quadruple is Kit.Derive.Common's ONE copy — the codes
    + the message spellings are THIS driver's, byte-identical to the
    KitTests pins). -/
def checkScope (ind : TSyntax `ident) (ii : InductiveVal) : CommandElabM Unit :=
  Kit.Derive.Common.checkScope ii
    { code := eKD0002
      message := s!"declare_fold {ind.getId}: `{ii.name}` is index \
        (GADT)-indexed — the generator's scope is the SIMPLE closed \
        inductives; the DEPENDENT fold (the motive riding the index, \
        06 §2) is `Kit.Derive.DepFold`'s `declare_dependent_fold` for \
        the one-index ctor-headed-index fragment — outside that \
        fragment, write it by hand (the `foldValue` shape) and cite \
        this refusal" }
    { code := eKD0003
      message := s!"declare_fold {ind.getId}: `{ii.name}` has type \
        parameters — the parameter-threaded fragment is the named \
        extension; the V1 scope is the parameter-free closed inductives" }
    { code := eKD0004
      message := s!"declare_fold {ind.getId}: `{ii.name}` has no \
        constructors — the empty universe's fold is `nomatch`, which an \
        algebra record cannot carry" }
    { code := eKD0008
      message := s!"declare_fold {ind.getId}: `{ii.name}` is part of a \
        MUTUAL block — the mutual-sibling fragment (the algebra record \
        carrying the whole family's rows, the `ValueAlg` shape) is the \
        named extension" }

/-- The per-ctor checks: explicit binders, flat non-dependent argument
    types, the recursive positions detected. -/
def checkCtor (ind : TSyntax `ident) (indName : Name) (ctorName : Name) :
    CommandElabM CtorShape := do
  let env ← getEnv
  let some cci := env.find? ctorName |
    throwDiag eKD0001
      s!"declare_fold {ind.getId}: missing constructor `{ctorName}`"
  let (argTys, result) ← liftTermElabM do
    forallTelescope cci.type fun args result => do
      let tys ← args.mapM fun fvar => do
        let d ← getFVarLocalDecl fvar
        unless d.binderInfo == .default do
          throwDiag eKD0006
            s!"declare_fold {ind.getId}: constructor `{ctorName}` carries \
              a non-explicit (implicit/instance) argument — the \
              generated algebra needs the full explicit shape; the \
              instance-carrying fragment is the named extension"
        pure d.type
      pure (tys, result)
  unless result.isConstOf indName do
    throwDiag eKD0002
      s!"declare_fold {ind.getId}: constructor `{ctorName}` does not \
        return the inductive — the indexed fragment is out of scope"
  let mut recArgs : Array Nat := #[]
  for i in [0:argTys.size] do
    let ty := argTys[i]!
    if ty.isConstOf indName then
      recArgs := recArgs.push i
    else
      if ty.hasFVar then
        throwDiag eKD0007
          s!"declare_fold {ind.getId}: constructor `{ctorName}`'s \
            argument {i} has a dependent type — the \
            dependent-constructor fragment is out of scope"
      if (ty.find? (fun e => e.isConstOf indName)).isSome then
        throwDiag eKD0005
          s!"declare_fold {ind.getId}: constructor `{ctorName}`'s \
            argument {i} mentions the inductive below the root — the \
            NESTED fragment (e.g. `List {ind.getId}`) is out of scope; \
            flat siblings or sigma-encoded packages are the 06 §2 \
            pattern"
  pure { name := ctorName, field := baseNameOf ctorName
         argTys := argTys, recArgs := recArgs }

/-- Analyze the `declare_fold` target: resolve it, refuse every shape
    outside the generator's honest scope, and return the inductive's
    value + the per-ctor shapes. -/
def analyzeInd (ind : TSyntax `ident) :
    CommandElabM (InductiveVal × Array CtorShape) := do
  let some indName := ← resolveConst? ind |
    throwDiag eKD0001
      s!"declare_fold {ind.getId}: unknown constant — valid usage: \
        `declare_fold <Inductive>` over a closed, parameter-free, \
        index-free inductive"
  let env ← getEnv
  let some ci := env.find? indName |
    throwDiag eKD0001
      s!"declare_fold {ind.getId}: `{indName}` is not a declaration — \
        valid usage: `declare_fold <Inductive>` over a closed, \
        parameter-free, index-free inductive"
  let ii? : Option InductiveVal :=
    match ci with
    | .inductInfo ii => some ii
    | _ => none
  let some ii := ii? |
    throwDiag eKD0001
      s!"declare_fold {ind.getId}: `{indName}` is not an inductive — \
        valid usage: `declare_fold <Inductive>` over a closed, \
        parameter-free, index-free inductive"
  checkScope ind ii
  let ctorShapes ← ii.ctors.mapM (checkCtor ind ii.name)
  pure (ii, ctorShapes.toArray)

/-! ## The string emission (the parse route)

The emission is the PARSE ROUTE (15-patterns #19; DepFold's wave-29
lesson): the generated commands are rendered to SOURCE TEXT and parsed
by the real parser (`Lean.Parser.runParserCategory`), then elaborated —
never spliced as quotation syntax. The quotation route this module
landed with carried the macro-scope machinery (20 `mkIdentFrom` scope
anchors, 26 `TSyntax` annotations, 25 splices — the ONE-shared-scope
token discipline of 06 §7) whose failure mode is the recorded wall:
generated syntax that does not elaborate like the byte-identical hand
code. The parse route removes the dependence: plain source text, freshly
parsed, elaborates exactly like hand code — and the generated
statements carry the hand spellings verbatim (the KitTests migration
pins are the byte-tie). -/

/-- The generator's delab refusal: a constructor argument type outside
    the delaboratable fragment (constant / application / non-dependent
    arrow shapes) — deterministic, never the stock delaborator's
    synthetic-hole fallback (a silent wrongness). -/
def throwUnsupportedTy {m : Type → Type} [Monad m] [MonadError m]
    (e : Expr) : m α :=
  throwDiag eKD0009
    s!"declare_fold: constructor argument type `{e}` is outside the \
      generator's delaboratable fragment (constant / application / \
      non-dependent arrow shapes)"

/-! ## The quotation-route helpers (Bridge's)

`Kit.Derive.Bridge` still rides the quotation route and consumes these
TSyntax-face helpers (it `open`s them from this module). Fold's OWN
emission migrated to the parse route below; the helpers stay HERE —
with their consumer — until Bridge's probe lands (the leftover rule:
nothing lands without a consumer; nothing stays without one either).
-/

/-- The closed FIRST-ORDER type delab (the TSyntax face Bridge's
    quotations splice): constants, apps, and non-dependent arrows only;
    anything else is the curated refusal. -/
def tyToSyntax : Expr → CommandElabM Term
  | .const n _ => pure (mkIdent n)
  | .app f a => do
    let fS ← tyToSyntax f
    let aS ← tyToSyntax a
    `($fS $aS)
  | .forallE _ d b _ =>
    if b.hasFVar then throwUnsupportedTy b
    else do
      let dS ← tyToSyntax d
      let bS ← tyToSyntax b
      `($dS → $bS)
  | .mdata _ e => tyToSyntax e
  | e => throwUnsupportedTy e

/-- The binder idents `a1 … aₙ` for one ctor's arguments (the shared
    macro-scope discipline — the parse route below needs none). -/
def argIdents (stx : Syntax) (c : CtorShape) : Array (TSyntax `ident) :=
  (Array.range c.argTys.size).map fun i =>
    mkIdentFrom stx (Name.mkSimple s!"a{i + 1}")

/-- The ihs `ih1 … ihₖ` for one ctor's recursive arguments (named by
    their ARGUMENT position, since only the recursive positions get an
    ih from the recursor). -/
def ihIdents (stx : Syntax) (c : CtorShape) : Array (TSyntax `ident) :=
  c.recArgs.map fun i => mkIdentFrom stx (Name.mkSimple s!"ih{i + 1}")

/-- The ctor pattern `.<ctor> a1 … aₙ` (dotted — the trap rule). -/
def ctorPattern (stx : Syntax) (c : CtorShape) : CommandElabM Term := do
  let binders := argIdents stx c
  let cid : TSyntax `ident := mkIdentFrom stx (Name.mkSimple c.field)
  if c.argTys.isEmpty then `(.$cid) else `(.$cid $binders*)

/-- The type of a ctor argument as binder syntax: the recursive
    positions are the inductive, the others their own type. -/
def argTyTerm (indId : Term) (c : CtorShape) (i : Nat) : CommandElabM Term := do
  if c.recArgs.contains i then pure indId
  else tyToSyntax c.argTys[i]!

/-! ## The string emission (the parse route) -/

/-- Is `s` an atomic render (no parens needed as an argument)?
    (DepFold's helper shape — `private` there, duplicated here rather
    than promoted across the cone for 4 lines.) -/
private def atomicS (s : String) : Bool :=
  let bad := s.any (fun ch => ch == ' ' || ch == '(')
  !bad

/-- The closed FIRST-ORDER type renderer (the string face of the
    generator's delab): constants (FULL names — freshly parsed source
    resolves them, no ident-hygiene question), applications
    (non-atomic arguments parenthesized), non-dependent arrows;
    anything else is the curated refusal. -/
def renderTyS : Expr → CommandElabM String
  | .const n _ => pure n.toString
  | .app f a => do
      let fS ← renderTyS f
      let aS ← renderTyS a
      if atomicS aS then pure (fS ++ " " ++ aS)
      else pure (fS ++ " (" ++ aS ++ ")")
  | .forallE _ d b _ =>
      if b.hasFVar then throwUnsupportedTy b
      else do
        let dS ← renderTyS d
        let bS ← renderTyS b
        pure (dS ++ " → " ++ bS)
  | .mdata _ e => renderTyS e
  | e => throwUnsupportedTy e

/-- Parse ONE generated command with the real parser and elaborate it.
    A parse failure is a curated diagnostic (the generator's own bug —
    named, never silent). -/
private def elabParsed (ind : TSyntax `ident) (src : String) :
    CommandElabM Unit := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src (fileName := "<gen>") with
  | .ok s => elabCommand s
  | .error e =>
    throwDiag eKD0009
      s!"declare_fold {ind.getId}: the generated command failed to \
        parse — the emission is out of the fragment: {e}"

/-- The algebra row's type for one ctor (string face): one arrow
    segment per argument (a recursive argument's segment is the carrier
    `α`), right-nested; a nullary ctor's row is `α`. -/
def buildFieldTyS (c : CtorShape) : CommandElabM String := do
  let segs : Array String ← (Array.range c.argTys.size).mapM fun i =>
    if c.recArgs.contains i then pure "α"
    else renderTyS c.argTys[i]!
  let mut acc := "α"
  for s in segs.reverse do
    acc := s!"{s} → {acc}"
  pure acc

/-- The ctor pattern `.ctor a1 … aₙ` (string face; dotted — the trap
    rule). -/
def ctorPatS (c : CtorShape) : String :=
  if c.argTys.isEmpty then s!".{c.field}"
  else
    let bs := (Array.range c.argTys.size).map (fun i => s!"a{i + 1}")
    s!".{c.field} {String.intercalate " " bs.toList}"

/-- The fold arm's rhs (string face): the algebra row applied to `alg`
    and the arguments (a recursive position re-enters the fold). -/
def foldRhsS (base : String) (c : CtorShape) : CommandElabM String := do
  let mut parts : Array String := #[]
  for i in [0:c.argTys.size] do
    if c.recArgs.contains i then
      parts := parts.push s!"(fold{base} alg a{i + 1})"
    else
      parts := parts.push s!"a{i + 1}"
  if parts.isEmpty then pure s!"{base}Alg.{c.field} alg"
  else pure s!"{base}Alg.{c.field} alg {String.intercalate " " parts.toList}"

/-- The ctor's argument binders `a1 … aₙ` (string face; the parse route
    needs no scopes — each generated command is its own fresh parse). -/
def argNames (c : CtorShape) : Array String :=
  (Array.range c.argTys.size).map (fun i => s!"a{i + 1}")

/-- The ihs `ih1 … ihₖ` for one ctor's recursive arguments (named by
    their ARGUMENT position, since only the recursive positions get an
    ih from the recursor). -/
def ihNames (c : CtorShape) : Array String :=
  c.recArgs.map (fun i => s!"ih{i + 1}")

syntax (name := declareFoldCmd) "declare_fold " ident : command

/-- THE FOLD GENERATOR: `declare_fold <Ind>` — see the module header for
    the generated surface + the honest scope. -/
@[command_elab Kit.Derive.Fold.declareFoldCmd]
def elabDeclareFold : CommandElab
  | _stx@`(command| declare_fold $ind:ident) => do
    let (ii, ctorShapes) ← analyzeInd ind
    let base := baseNameOf ii.name
    let indS := ii.name.toString
    -- THE ALGEBRA RECORD: one field per ctor, children folded.
    let mut fieldLines : Array String := #[]
    for c in ctorShapes do
      let ty ← buildFieldTyS c
      fieldLines := fieldLines.push s!"  {c.field} : {ty}"
    elabParsed ind <|
      "/-- GENERATED by `declare_fold` — the ALGEBRA record: one field per\n" ++
      "constructor, each receiving the folded children (a recursive\n" ++
      "argument's slot is the carrier). A new constructor refuses to\n" ++
      "compile until every algebra grows its row (15-patterns #15). -/\n" ++
      s!"structure {base}Alg (α : Type) where\n" ++
      ((fieldLines.map (· ++ "\n")).foldl (· ++ ·) "")
    -- THE FOLD: the one walk. `α` is auto-bound (the hand spelling the
    -- fixtures pin — the fresh parse IS hand code).
    let mut armLines : Array String := #[]
    for c in ctorShapes do
      let rhs ← foldRhsS base c
      armLines := armLines.push s!"  | alg, {ctorPatS c} => {rhs}"
    elabParsed ind <|
      "/-- GENERATED by `declare_fold` — THE FOLD: the closed universe's\n" ++
      "one walk (01 §1's initial-algebra face). Total, structural,\n" ++
      "kernel-visible. -/\n" ++
      s!"def fold{base} : {base}Alg α → {indS} → α\n" ++
      ((armLines.map (· ++ "\n")).foldl (· ++ ·) "")
    -- THE EQUATION SET: all `rfl` (structural recursion = kernel
    -- reduction; 06 §5 — consumers prove against these).
    for c in ctorShapes do
      let bs := argNames c
      let mut impBinders : Array String := #[]
      for i in [0:c.argTys.size] do
        let ty ←
          if c.recArgs.contains i then pure indS
          else renderTyS c.argTys[i]!
        impBinders := impBinders.push ("{" ++ bs[i]! ++ " : " ++ ty ++ "}")
      let rhs ← foldRhsS base c
      elabParsed ind <|
        "/-- GENERATED by `declare_fold` — one arm of the equation set\n" ++
        "    (06 §5): kernel reduction, cited by the initiality law's\n" ++
        "    template. -/\n" ++
        s!"theorem fold{base}_{c.field} " ++
        s!"{String.intercalate " " impBinders.toList} :\n" ++
        s!"    fold{base} alg ({ctorPatS c}) = {rhs} := rfl\n"
    -- THE INITIALITY LAW: the recursor template — per ctor,
    -- `rw [h_<ctor> args…, ihs…, fold<Ind>_<ctor>]` (06 §10: the
    -- template, never grind).
    let mut hyps : Array String := #[]
    let mut minors : Array String := #[]
    for c in ctorShapes do
      let bs := argNames c
      let ihs := ihNames c
      -- the hypothesis: explicit binders + the commutation row
      let mut expl : Array String := #[]
      let mut rhsParts : Array String := #[]
      for i in [0:c.argTys.size] do
        let ty ←
          if c.recArgs.contains i then pure indS
          else renderTyS c.argTys[i]!
        expl := expl.push s!"({bs[i]!} : {ty})"
        if c.recArgs.contains i then
          -- parenthesized: a multi-token application must ride as ONE
          -- argument (the same non-atomic rule as renderTyS)
          rhsParts := rhsParts.push s!"(f {bs[i]!})"
        else rhsParts := rhsParts.push bs[i]!
      let pat := ctorPatS c
      let fieldApp :=
        if rhsParts.isEmpty then s!"{base}Alg.{c.field} alg"
        else s!"{base}Alg.{c.field} alg {String.intercalate " " rhsParts.toList}"
      -- the ctor pattern rides PARENTHESIZED in TERM position: the
      -- quotation route grouped `.lit a1` as ONE application argument
      -- (the dot resolves against the expected type as a unit); bare
      -- source text elaborates `f .lit` alone — `f (.lit a1)` is the
      -- byte-equivalent hand spelling
      let hypBody :=
        if c.argTys.isEmpty then s!"f ({pat}) = {fieldApp}"
        else
          s!"∀ {String.intercalate " " expl.toList}, f ({pat}) = {fieldApp}"
      hyps := hyps.push s!"(h_{c.field} : {hypBody})"
      -- THE MINOR: `by rw [h_<ctor> args…, ihs…, fold<Ind>_<ctor>]`.
      -- The hyp rides ALWAYS (a nullary ctor's hyp is the bare `h` —
      -- the original template's shape; dropping it leaves the goal's
      -- LHS unrewritten and the rw cannot close).
      let mut rules : Array String := #[]
      if c.argTys.isEmpty then
        rules := rules.push s!"h_{c.field}"
      else
        rules := rules.push
          s!"h_{c.field} {String.intercalate " " bs.toList}"
      for ih in ihs do rules := rules.push ih
      rules := rules.push s!"fold{base}_{c.field}"
      -- THE MINOR's source shape: a `by` block elaborates with the
      -- expected type ONLY inside a parenthesized argument — a bare
      -- `fun … => (by …)` as an application argument loses it (the
      -- quotation route grouped the minor as ONE atomic node; the
      -- source spelling groups it with parens around the WHOLE fun)
      let rwTac := s!"rw [{String.intercalate ", " rules.toList}]"
      let minor :=
        if c.argTys.isEmpty then s!"(by {rwTac})"
        else
          s!"(fun {String.intercalate " " (bs.toList ++ ihs.toList)} => by {rwTac})"
      minors := minors.push minor
    elabParsed ind <|
      "/-- GENERATED by `declare_fold` — THE INITIALITY LAW: a function\n" ++
      "    that commutes with the algebra on every constructor IS the\n" ++
      "    fold (one structural induction, generated once here, cited by\n" ++
      "    every migrated consumer — the `foldTy_unique` shape). -/\n" ++
      ("theorem fold" ++ base ++ "_unique {alg : " ++ base ++ "Alg α} " ++
        "{f : " ++ indS ++ " → α}\n") ++
      ((hyps.map (fun h => s!"    {h}\n")).foldl (· ++ ·) "") ++
      s!"    (x : {indS}) : f x = fold{base} alg x :=\n" ++
      -- the rec application rides ONE parenthesized block — a bare
      -- newline-separated application would end the command at the
      -- first line (the parser's indentation rule)
      s!"  ({indS}.rec (motive := fun x => f x = fold{base} alg x)\n" ++
      ((minors.map (fun m => s!"    {m}\n")).foldl (· ++ ·) "") ++
      "    x)\n"
  | _ => Elab.throwUnsupportedSyntax

end Kit.Derive.Fold
