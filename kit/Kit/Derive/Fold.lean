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

- indexed (GADT) inductives — the DEPENDENT fold (the motive riding the
  index, 06 §2's `foldValue` discipline) is the named extension;
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

namespace Kit.Derive.Fold

open Lean Elab Command Meta
open Lean.Parser.Command (structSimpleBinder)
open Lean.Parser.Term (matchAltExpr bracketedBinder)
open Lean.Parser.Tactic (rwRule)

/-! ## The curated failures -/

/-- The KD family — the fold generator's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    DECLARATION — the sites below use them, never a bare string, and
    the code-registry gate's coverage scan ties every spelling to its
    allocated live row (a hand-strung code is a gate refusal). -/
def eKD0001 : Kit.ECode := ⟨"KD0001"⟩
def eKD0002 : Kit.ECode := ⟨"KD0002"⟩
def eKD0003 : Kit.ECode := ⟨"KD0003"⟩
def eKD0004 : Kit.ECode := ⟨"KD0004"⟩
def eKD0005 : Kit.ECode := ⟨"KD0005"⟩
def eKD0006 : Kit.ECode := ⟨"KD0006"⟩
def eKD0007 : Kit.ECode := ⟨"KD0007"⟩
def eKD0008 : Kit.ECode := ⟨"KD0008"⟩
def eKD0009 : Kit.ECode := ⟨"KD0009"⟩

/-- Throw the refusal (the Diag rendered verbatim, the Lane discipline):
    the unsupported shape named — the code row + the message + the error
    severity. The Diag literal is built HERE, once: a named standalone
    constructor would be the alpha-twin of `Kit.Lane.usageDiag` (the
    dupDefBodies catch), and the generator's imports stay Lean +
    Kit.Diag — no Lane delegation. The code slot is an `ECode` of the
    registry's allocated family (above) — a bare string cannot reach
    the throw. -/
def throwDiag {m : Type → Type} [Monad m] [MonadError m]
    (code : Kit.ECode) (message : String) : m α :=
  throwError m!"{({ code := code, message := message, severity := .error } : Kit.Diag)}"

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
    analysis. -/
def checkScope (ind : TSyntax `ident) (ii : InductiveVal) : CommandElabM Unit := do
  let indName := ii.name
  if ii.numIndices != 0 then
    throwDiag eKD0002
      s!"declare_fold {ind.getId}: `{indName}` is index (GADT)-indexed — \
        the generator's scope is the SIMPLE closed inductives; the \
        DEPENDENT fold (the motive riding the index, 06 §2) is the \
        named extension — write it by hand (the `foldValue` shape) and \
        cite this refusal"
  if ii.numParams != 0 then
    throwDiag eKD0003
      s!"declare_fold {ind.getId}: `{indName}` has type parameters — the \
        parameter-threaded fragment is the named extension; the V1 scope \
        is the parameter-free closed inductives"
  if ii.ctors.isEmpty then
    throwDiag eKD0004
      s!"declare_fold {ind.getId}: `{indName}` has no constructors — the \
        empty universe's fold is `nomatch`, which an algebra record \
        cannot carry"
  if ii.all.length > 1 then
    throwDiag eKD0008
      s!"declare_fold {ind.getId}: `{indName}` is part of a MUTUAL block — \
        the mutual-sibling fragment (the algebra record carrying the \
        whole family's rows, the `ValueAlg` shape) is the named extension"

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
  let resolved? : Option Name ← liftCoreM do
    try
      some <$> Lean.resolveGlobalConstNoOverload ind
    catch _ =>
      pure none
  let some indName := resolved? |
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

/-! ## The builders -/

/- The ident token discipline (06 §7): every binder ident the generated
    decls share (`α`, `alg`, `f`, the arg/ihs/hyp names) is built with
    `mkIdentFrom <command syntax>` — ONE shared macro scope, so a binder
    built in one quotation binds in every quotation that splices it. The
    generated NAMES (`FruitAlg`, `foldFruit`, …) are plain short names
    resolved in the consumer's namespace at `elabCommand` time. Antiquot
    splices are BY NAME only (`$(…) ` is not quotation syntax): every
    spliced subterm is pre-bound to a `let`. -/

/-- The closed FIRST-ORDER type delab (the generator's own — deterministic;
    the stock delaborator's fallback is a synthetic hole, which would
    elaborate as a fresh mvar — a silent wrongness). Constants, apps, and
    non-dependent arrows/Pis only; anything else is a curated refusal. -/
def throwUnsupportedTy {m : Type → Type} [Monad m] [MonadError m]
    (e : Expr) : m α :=
  throwDiag eKD0009
    s!"declare_fold: constructor argument type `{e}` is outside the \
      generator's delaboratable fragment (constant / application / \
      non-dependent arrow shapes)"

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

/-- The algebra row's type for one ctor: one arrow segment per argument
    (a recursive argument's segment is the carrier `α`, every other
    argument's type passes through raw); a nullary ctor's row is `α`. -/
def buildFieldTy (alphaId : TSyntax `ident) (c : CtorShape) : CommandElabM Term := do
  let alphaT : Term := ⟨alphaId.raw⟩
  let segs : Array Term ← (Array.range c.argTys.size).mapM fun i => do
    if c.recArgs.contains i then
      pure (⟨alphaId.raw⟩ : Term)
    else
      tyToSyntax c.argTys[i]!
  -- the row: right-nested arrows (splice protection parens on the
  -- RIGHT of `→` are semantically inert — right associativity).
  let mut acc : Term := alphaT
  for s in segs.reverse do
    acc := ← `($s → $acc)
  pure acc

/-- The binder idents `a1 … aₙ` for one ctor's arguments. -/
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

/-- The fold arm's rhs: the algebra row applied to `alg` and the
    arguments (a recursive position re-enters the fold). -/
def foldRhs (algRef : TSyntax `ident) (algName : Name) (foldName : Name)
    (c : CtorShape) : CommandElabM Term := do
  let binders := argIdents algRef.raw c
  let algT : Term := ⟨algRef.raw⟩
  let foldRef : Term := mkIdentFrom algRef foldName
  let fieldFn : Term := mkIdentFrom algRef (algName ++ Name.mkSimple c.field)
  let rhsParts : Array Term ← (Array.range c.argTys.size).mapM fun i => do
    let bT : Term := ⟨binders[i]!.raw⟩
    if c.recArgs.contains i then `($foldRef $algT $bT)
    else pure bT
  `($fieldFn $algT $rhsParts*)

/-! ## The command -/

syntax (name := declareFoldCmd) "declare_fold " ident : command

/-- THE FOLD GENERATOR: `declare_fold <Ind>` — see the module header for
    the generated surface + the honest scope. -/
@[command_elab Kit.Derive.Fold.declareFoldCmd]
def elabDeclareFold : CommandElab
  | stx@`(command| declare_fold $ind:ident) => do
    let (ii, ctorShapes) ← analyzeInd ind
    let baseStr := baseNameOf ii.name
    let algName := Name.mkSimple s!"{baseStr}Alg"
    let foldName := Name.mkSimple s!"fold{baseStr}"
    let algId : TSyntax `ident := mkIdentFrom stx algName
    let foldId : TSyntax `ident := mkIdentFrom stx foldName
    let indId : Term := mkIdentFrom stx ii.name
    let recId : Term := mkIdentFrom stx (ii.name ++ `rec)
    -- THE shared binder idents (one macro scope across every quotation).
    let alphaId : TSyntax `ident := mkIdentFrom stx `α
    let algRef : TSyntax `ident := mkIdentFrom stx `alg
    let fRef : TSyntax `ident := mkIdentFrom stx `f
    let xRef : TSyntax `ident := mkIdentFrom stx `x
    let algT : Term := ⟨algRef.raw⟩
    let fT : Term := ⟨fRef.raw⟩
    let xT : Term := ⟨xRef.raw⟩
    let alphaT : Term := ⟨alphaId.raw⟩
    -- THE ALGEBRA RECORD: one field per ctor, children folded.
    let fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) ←
      ctorShapes.mapM fun c => do
        let ty ← buildFieldTy alphaId c
        let fid : TSyntax `ident := mkIdentFrom stx (Name.mkSimple c.field)
        `(Lean.Parser.Command.structSimpleBinder| $fid:ident : $ty)
    elabCommand (← `(command|
      /-- GENERATED by `declare_fold` — the ALGEBRA record: one field per
          constructor, each receiving the folded children (a recursive
          argument's slot is the carrier). A new constructor refuses to
          compile until every algebra grows its row (15-patterns #15). -/
      structure $algId:ident ($alphaId : Type) where
        $[$fields:structSimpleBinder]*))
    -- THE FOLD: the one walk.
    let arms : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
      ctorShapes.mapM fun c => do
        let pat ← ctorPattern stx c
        let rhs ← foldRhs algRef algName foldName c
        `(matchAltExpr| | $algRef, $pat => $rhs)
    elabCommand (← `(command|
      /-- GENERATED by `declare_fold` — THE FOLD: the closed universe's
          one walk (01 §1's initial-algebra face). Total, structural,
          kernel-visible. -/
      def $foldId:ident : $algId $alphaT → $indId → $alphaT
        $[$arms:matchAlt]*))
    -- THE EQUATION SET: all `rfl` (structural recursion = kernel
    -- reduction; 06 §5 — consumers prove against these).
    for c in ctorShapes do
      let binders := argIdents stx c
      let eqId : TSyntax `ident := mkIdentFrom stx
        (Name.mkSimple s!"fold{baseStr}_{c.field}")
      let impBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
        (Array.range c.argTys.size).mapM fun i => do
          let b : TSyntax `ident := binders[i]!
          let bty ← argTyTerm indId c i
          `(bracketedBinder| {$b:ident : $bty})
      let pat ← ctorPattern stx c
      let rhs ← foldRhs algRef algName foldName c
      elabCommand (← `(command|
        /-- GENERATED by `declare_fold` — one arm of the equation set
            (06 §5): kernel reduction, cited by the initiality law's
            template. -/
        theorem $eqId:ident {$algRef : $algId $alphaT} $[$impBinders:bracketedBinder]* :
            $foldId $algT $pat = $rhs := rfl))
    -- THE INITIALITY LAW: the recursor template — per ctor,
    -- `rw [h_<ctor> args…, ihs…, fold<Ind>_<ctor>]` (06 §10: the
    -- template, never grind).
    let mut hyps : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    let mut minors : Array Term := #[]
    for c in ctorShapes do
      let binders := argIdents stx c
      let ihs := ihIdents stx c
      let hypId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"h_{c.field}")
      let fieldFn : Term := mkIdentFrom stx (algName ++ Name.mkSimple c.field)
      let hypT : Term := ⟨hypId.raw⟩
      let explicitBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
        (Array.range c.argTys.size).mapM fun i => do
          let b : TSyntax `ident := binders[i]!
          let bty ← argTyTerm indId c i
          `(bracketedBinder| ($b:ident : $bty))
      let pat ← ctorPattern stx c
      let hypTy : Term ←
        if c.argTys.isEmpty then
          `($fT $pat = $fieldFn $algT)
        else
          let rhsParts : Array Term ← (Array.range c.argTys.size).mapM fun i => do
            let bT : Term := ⟨binders[i]!.raw⟩
            if c.recArgs.contains i then `($fT $bT)
            else pure bT
          `(∀ $[$explicitBinders:bracketedBinder]*, $fT $pat = $fieldFn $algT $rhsParts*)
      hyps := hyps.push (← `(bracketedBinder| ($hypId : $hypTy)))
      -- THE MINOR: `by rw [h_<ctor> args…, ihs…, fold<Ind>_<ctor>]`.
      let eqId : Term := mkIdentFrom stx
        (Name.mkSimple s!"fold{baseStr}_{c.field}")
      let hypTerms : Array Term ←
        if c.argTys.isEmpty then pure #[hypT]
        else do let hApp : Term ← `($hypT $binders*); pure #[hApp]
      let allRules : Array Term :=
        hypTerms ++ (ihs.map fun ih => (⟨ih.raw⟩ : Term)) ++ #[eqId]
      let rwRules : Array (TSyntax `Lean.Parser.Tactic.rwRule) ←
        allRules.mapM fun r => do `(rwRule| $r:term)
      let rwTac : Term ← `(by rw [$[$rwRules],*])
      let minor : Term ←
        if c.argTys.isEmpty then pure rwTac
        else `(fun $binders* $ihs* => $rwTac)
      minors := minors.push minor
    let algBinder ← `(bracketedBinder| {$algRef : $algId $alphaT})
    let fBinder ← `(bracketedBinder| {$fRef : $indId → $alphaT})
    let uniqId : TSyntax `ident := mkIdentFrom stx
      (Name.mkSimple s!"fold{baseStr}_unique")
    elabCommand (← `(command|
      /-- GENERATED by `declare_fold` — THE INITIALITY LAW: a function
          that commutes with the algebra on every constructor IS the
          fold (one structural induction, generated once here, cited by
          every migrated consumer — the `foldTy_unique` shape). -/
      theorem $uniqId:ident $algBinder $fBinder $[$hyps:bracketedBinder]*
          ($xRef : $indId) : $fT $xT = $foldId $algT $xT :=
        $recId (motive := fun x => $fT x = $foldId $algT x) $minors* $xT))
  | _ => Elab.throwUnsupportedSyntax

end Kit.Derive.Fold
