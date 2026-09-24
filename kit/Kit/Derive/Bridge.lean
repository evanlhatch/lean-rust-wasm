/-
# Kit.Derive.Bridge — the relation+checker bridge generator (`declare_bridge`)

`declare_bridge <name> := <checker>, <relation> where | <ctor> => <shape>`
generates pattern #1's crossing (relation-as-spec + executable checker +
proved bridge) for a closed, parameter-free, index-free inductive whose
checker is `Ind → Row → Bool` and whose relation is `Ind → Row → Prop`:

- `<name>_iff` — THE BRIDGE: `∀ p r, checker p r = true ↔ relation p r`,
  the iff-shaped induction (15-patterns #1's discovery: soundness and
  completeness under `not` need EACH OTHER — one iff-induction carries
  both). The proof is the TEMPLATE (06 §10): the recursor over the ctor
  analysis, with the combinator rows done mechanically — a two-recursive-
  argument row via `Bool.and_eq_true`/`Bool.or_eq_true` + the relation's
  `∧`/`∨` shape, the one-recursive-argument row via the under-negation
  discipline (each direction of the `not` case consumes the OTHER
  direction of the ih, exactly the hand `check_iff` shape) — and the
  LEAF rows as caller-supplied hypotheses `h_<ctor>` (the leaf semantics
  are the domain's content, not the template's; the generator's
  statement carries them so nothing is assumed silently).
- `<name>_sound` / `<name>_complete` — the two projections.
- `<name>_checked` — the `Kit.CheckedProp` assembly (soundness
  mandatory; completeness `.proved` from the bridge — the loud
  two-constructor choice honored).

The row classification is DATA in the command (the generator cannot
read semantics off a matcher): `| <ctor> => leaf|and|or|not`. A row
naming an unknown ctor refuses through the closed-world constructor
(got + the valid space + the ONE engine's suggestion); a shape that
does not fit its ctor's arity refuses with the mismatch named.

HONEST SCOPE (the same fragment as `Kit.Derive.Fold`, plus): the
checker must have EXACTLY the shape `Ind → Row → Bool` (the relation
`Ind → Row → Prop`, same `Ind` and `Row`) — the parameterized/indexed
fragments (the GADT `Pred` shape) are the named extension. The
combinator template reads the checker/relation through their equation
lemmas (`simp only [checker, relation, …]`) — a checker whose arms do
not reduce that way fails to elaborate (wrongness does not elaborate),
it is not silently accepted.

E-codes: the `KB00xx` rows (Kit-bridge; the `KD00xx`/`KL00xx`
convention).

Core-only (imports Lean + Kit.Diag + Kit.CheckedProp — the cone rule).
META module: the generated decls are ordinary core-level theorems.

Five questions (notes/v3/01-core.md):
- root: META — pattern #1's generator face (the bridge written once at
  the structure, cited by every lane after).
- carrier grade: none of its own; the generated surface is the iff +
  the projections + the CheckedProp assembly.
- spine reading: the correspondence stage — spec ⇔ decidable shadow.
- ladder rung: the generated iff is a recursor template over the
  equation lemmas (build-stable; zero axioms — pinned by KitTests).
- gate row: KitTests' bridge suite (the generated iff's pins + the
  refusal teeth + the negative controls).
-/

import Lean
import Kit.Diag
import Kit.CheckedProp
import Kit.Derive.Fold

namespace Kit.Derive.Bridge

open Lean Elab Command Meta
open Kit.Derive.Fold
open Kit.Derive.Fold (baseNameOf checkCtor throwDiag tyToSyntax argIdents ihIdents ctorPattern argTyTerm)

/-! ## The KB family — the bridge generator's E-codes -/

/-- The KB family — the bridge generator's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    DECLARATION — the sites below use them, never a bare string, and
    the code-registry gate's coverage scan ties every spelling to its
    allocated live row (a hand-strung code is a gate refusal). -/
def eKB0001 : Kit.ECode := ⟨"KB0001"⟩
def eKB0002 : Kit.ECode := ⟨"KB0002"⟩
def eKB0003 : Kit.ECode := ⟨"KB0003"⟩
def eKB0004 : Kit.ECode := ⟨"KB0004"⟩
def eKB0005 : Kit.ECode := ⟨"KB0005"⟩
def eKB0006 : Kit.ECode := ⟨"KB0006"⟩
def eKB0007 : Kit.ECode := ⟨"KB0007"⟩
def eKB0008 : Kit.ECode := ⟨"KB0008"⟩

/-! ## The row shapes -/

/-- The four combinator/leaf shapes a row can classify its ctor as. -/
def validShapes : List String := ["leaf", "and", "or", "not"]

/-- One row of the `where` block: the ctor (by name) + its shape. -/
structure BridgeRow where
  ctor : Name
  shape : String

/-! ## The command -/

declare_syntax_cat bridgeRow
syntax "| " ident " => " ident : bridgeRow

syntax (name := declareBridgeCmd) "declare_bridge " ident " := " term ", " term
  " where" (ppSpace colGt bridgeRow)* : command

/-- THE BRIDGE GENERATOR: `declare_bridge <name> := <checker>, <relation>
    where …` — see the module header for the generated surface + the
    honest scope. -/
@[command_elab Kit.Derive.Bridge.declareBridgeCmd]
def elabDeclareBridge : CommandElab
  | stx@`(command| declare_bridge $name:ident := $chk:term, $rel:term where $[$rows:bridgeRow]*) => do
    let env ← getEnv
    -- THE CHECKER'S SHAPE: `Ind → Row → Bool` — the inductive and the
    -- row carrier come OFF the checker's type (declared once, never
    -- mis-wired).
    let chkTy ← liftTermElabM do
      let e ← Lean.Elab.Term.elabTerm chk none
      let e ← instantiateMVars e
      whnfR (← inferType e)
    let .forallE _ domA bodyA _ := chkTy |
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the checker's type is not a \
          two-argument function — the bridge template needs exactly \
          `checker : Ind → Row → Bool` (the parameterized/indexed \
          fragments are the named extension)"
    let .forallE _ domB bodyB _ ← liftTermElabM (whnfR bodyA) |
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the checker's type is not a \
          two-argument function — the bridge template needs exactly \
          `checker : Ind → Row → Bool` (the parameterized/indexed \
          fragments are the named extension)"
    unless bodyB.isConstOf ``Bool do
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the checker's codomain is not \
          `Bool` — the bridge template needs exactly \
          `checker : Ind → Row → Bool`"
    unless domA.isConst do
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the checker's domain is not a \
          plain inductive constant — the parameterized/indexed fragments \
          are the named extension"
    let indName := domA.constName!
    let some (.inductInfo ii) := env.find? indName |
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the checker's domain `{indName}` \
          is not an inductive"
    -- the shared scope checks (the fold's fragment)
    if ii.numIndices != 0 then
      throwDiag eKB0002
        s!"declare_bridge {name.getId}: `{indName}` is index (GADT)-indexed — \
          the generator's scope is the SIMPLE closed inductives; the \
          dependent bridge (the motive riding the index) is the named \
          extension — write it by hand (the `check_iff` shape) and cite \
          this refusal"
    if ii.numParams != 0 then
      throwDiag eKB0003
        s!"declare_bridge {name.getId}: `{indName}` has type parameters — \
          the parameter-threaded fragment is the named extension"
    if ii.ctors.isEmpty then
      throwDiag eKB0004
        s!"declare_bridge {name.getId}: `{indName}` has no constructors — \
          the empty universe's bridge is `nomatch`-vacuous; refuse"
    if ii.all.length > 1 then
      throwDiag eKB0005
        s!"declare_bridge {name.getId}: `{indName}` is part of a MUTUAL \
          block — the mutual-sibling fragment is the named extension"
    -- THE RELATION'S SHAPE: same `Ind`, same `Row`, codomain `Prop`.
    let relTy ← liftTermElabM do
      let e ← Lean.Elab.Term.elabTerm rel none
      let e ← instantiateMVars e
      whnfR (← inferType e)
    let .forallE _ relDomA relBodyA _ := relTy |
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the relation's type is not a \
          two-argument function — the bridge template needs exactly \
          `relation : Ind → Row → Prop` over the checker's `Ind` and `Row`"
    let .forallE _ relDomB relBodyB _ ← liftTermElabM (whnfR relBodyA) |
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the relation's type is not a \
          two-argument function — the bridge template needs exactly \
          `relation : Ind → Row → Prop` over the checker's `Ind` and `Row`"
    unless relDomA == domA do
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the relation's domain is \
          `{relDomA}` but the checker's is `{domA}` — one crossing, one \
          carrier"
    unless relDomB == domB do
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the relation's row carrier is \
          `{relDomB}` but the checker's is `{domB}` — one crossing, one \
          carrier"
    unless relBodyB.isProp do
      throwDiag eKB0001
        s!"declare_bridge {name.getId}: the relation's codomain is not \
          `Prop` — the bridge template needs exactly \
          `relation : Ind → Row → Prop`"
    -- THE ROWS: parse + the closed-world checks (unknown ctor / unknown
    -- shape refuse through the ONE engine's constructor).
    let parsedRows : Array BridgeRow ← rows.mapM fun row => do
      let ctorIdent : TSyntax `ident := ⟨row.raw[1]!⟩
      let shapeIdent : TSyntax `ident := ⟨row.raw[3]!⟩
      let shape := shapeIdent.getId.toString
      let ctorStr := ctorIdent.getId.toString
      unless validShapes.contains shape do
        throwError m!"{Kit.Diag.closedWorld eKB0006
          s!"declare_bridge {name.getId}: unknown row shape `{shape}`"
          .error shape validShapes}"
      let some fullCtor := ii.ctors.find? (fun c => baseNameOf c == ctorStr) |
        throwError m!"{Kit.Diag.closedWorld eKB0006
          s!"declare_bridge {name.getId}: `{ctorStr}` is not a \
            constructor of `{indName}`"
          .error ctorStr
          (ii.ctors.map baseNameOf)}"
      pure { ctor := fullCtor, shape := shape }
    -- coverage: every ctor classified, exactly once.
    let rowCtors := parsedRows.map (·.ctor)
    let missing := ii.ctors.filter (fun c => !rowCtors.contains c)
    let duplicated := rowCtors.filter (fun c => rowCtors.count c > 1)
    unless missing.isEmpty && duplicated.isEmpty do
      throwDiag eKB0007
        s!"declare_bridge {name.getId}: the row block must classify every \
          constructor of `{indName}` exactly once — missing: \
          {missing.map baseNameOf}, duplicated: {duplicated.map baseNameOf}"
    -- THE CTOR ANALYSIS (the fold's checker) + the shape fit.
    let shapeAssoc : List (Name × String) :=
      parsedRows.toList.map (fun r => (r.ctor, r.shape))
    let ctorShapes ← ii.ctors.mapM fun ctorName => do
      let some shape := shapeAssoc.lookup ctorName |
        throwDiag eKB0007 s!"declare_bridge {name.getId}: `{ctorName}` \
          unclassified"
      let c ← checkCtor ⟨stx⟩ indName ctorName
      let recCount := c.recArgs.size
      let argCount := c.argTys.size
      let ok := match shape with
        | "leaf" => recCount == 0
        | "and" | "or" => argCount == 2 && recCount == 2
        | "not" => argCount == 1 && recCount == 1
        | _ => false
      unless ok do
        throwDiag eKB0008
          s!"declare_bridge {name.getId}: the row `{baseNameOf ctorName} \
            => {shape}` does not fit the constructor's shape \
            ({argCount} argument(s), {recCount} recursive) — `leaf` \
            needs 0 recursive arguments, `and`/`or` need exactly 2, \
            `not` needs exactly 1"
      pure (c, shape)
    -- THE SURFACE.
    let baseStr := name.getId.toString
    let iffId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"{baseStr}_iff")
    let soundId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"{baseStr}_sound")
    let completeId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"{baseStr}_complete")
    let checkedId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"{baseStr}_checked")
    let recId : Term := mkIdentFrom stx (indName ++ `rec)
    -- THE shared binder idents (one macro scope across every quotation).
    let pRef : TSyntax `ident := mkIdentFrom stx `p
    let rowRef : TSyntax `ident := mkIdentFrom stx `r
    let hRef : TSyntax `ident := mkIdentFrom stx `h
    let pT : Term := ⟨pRef.raw⟩
    let rowT : Term := ⟨rowRef.raw⟩
    let hT : Term := ⟨hRef.raw⟩
    let indT : Term := mkIdentFrom stx indName
    let rowTyT : Term ← tyToSyntax domB
    let chkT : Term := chk
    let relT : Term := rel
    let iffApp : Term := mkIdentFrom stx (Name.mkSimple s!"{baseStr}_iff")
    -- The per-ctor leaf hypotheses (the leaf rows' caller-supplied iff).
    let mut leafHyps : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    let mut leafHypTerms : Array Term := #[]
    let mut minors : Array Term := #[]
    for (c, shape) in ctorShapes do
      let binders := argIdents stx c
      let ihs := ihIdents stx c
      let pat ← ctorPattern stx c
      let hypId : TSyntax `ident := mkIdentFrom stx (Name.mkSimple s!"h_{c.field}")
      let hypT : Term := ⟨hypId.raw⟩
      let explicitBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
        (Array.range c.argTys.size).mapM fun i => do
          let b : TSyntax `ident := binders[i]!
          let bty ← argTyTerm indT c i
          `(bracketedBinder| ($b:ident : $bty))
      let hypTy : Term ←
        `(∀ $[$explicitBinders:bracketedBinder]* ($rowRef : $rowTyT),
            $chkT $pat $rowT = true ↔ $relT $pat $rowT)
      -- THE MINOR.
      let argTerms : Array Term := binders.map (fun b => (⟨b.raw⟩ : Term))
      let minor : Term ←
        match shape with
        | "leaf" => do
            let app : Term ← `($hypT $argTerms* $rowT)
            `(fun $binders* $rowRef => $app)
        | "and" | "or" => do
            let boolLemma : Term :=
              mkIdentFrom stx (if shape == "and" then ``Bool.and_eq_true else ``Bool.or_eq_true)
            let ihApps : Array Term ← ihs.mapM fun ih => do
              let ihT : Term := ⟨ih.raw⟩
              `($ihT $rowT)
            `(fun $binders* $ihs* $rowRef =>
                by simp only [$chkT:term, $relT:term, $boolLemma:term, $[$ihApps:term],*])
        | "not" => do
            let ih0 : Term := ⟨ihs[0]!.raw⟩
            let b0T : Term := ⟨binders[0]!.raw⟩
            let ihApp : Term ← `($ih0 $rowT)
            let chkApp : Term ← `($chkT $b0T $rowT)
            `(fun $binders* $ihs* $rowRef =>
                by
                  simp only [$chkT:term, $relT:term]
                  constructor
                  · intro h hs
                    rw [($(ihApp)).mpr hs] at h
                    simp at h
                  · intro hs
                    cases hc : $chkApp with
                    | false => simp
                    | true => exact absurd (($(ihApp)).mp hc) hs)
        | _ => throwUnsupportedTy domB
      if shape == "leaf" then
        leafHyps := leafHyps.push (← `(bracketedBinder| ($hypId : $hypTy)))
        leafHypTerms := leafHypTerms.push hypT
      minors := minors.push minor
    -- THE IFF (one induction carries both directions).
    elabCommand (← `(command|
      /-- GENERATED by `declare_bridge` — THE BRIDGE (15-patterns #1):
          the iff-shaped induction; under `not` the two directions need
          EACH OTHER, and one induction carries both. The leaf rows' iff
          hypotheses are the domain's content (caller-supplied); the
          combinator rows are the template's. -/
      theorem $iffId:ident $[$leafHyps:bracketedBinder]*
          ($pRef : $indT) ($rowRef : $rowTyT) :
          $chkT $pT $rowT = true ↔ $relT $pT $rowT :=
        $recId (motive := fun p => ∀ ($rowRef : $rowTyT), $chkT p $rowT = true ↔ $relT p $rowT)
          $minors* $pT $rowT))
    -- THE TWO PROJECTIONS.
    elabCommand (← `(command|
      /-- GENERATED by `declare_bridge` — SOUNDNESS: a `true` verdict is
          a proof of the relation (the checker never fabricates a
          satisfaction). -/
      theorem $soundId:ident $[$leafHyps:bracketedBinder]*
          ($pRef : $indT) ($rowRef : $rowTyT) ($hRef : $chkT $pT $rowT = true) :
          $relT $pT $rowT :=
        ($iffApp $leafHypTerms* $pT $rowT).mp $hT))
    elabCommand (← `(command|
      /-- GENERATED by `declare_bridge` — COMPLETENESS: every satisfying
          row's verdict is `true` (the fragment decidable both ways, so
          the CheckedProp assembly takes `.proved`). -/
      theorem $completeId:ident $[$leafHyps:bracketedBinder]*
          ($pRef : $indT) ($rowRef : $rowTyT) ($hRef : $relT $pT $rowT) :
          $chkT $pT $rowT = true :=
        ($iffApp $leafHypTerms* $pT $rowT).mpr $hT))
    -- THE CHECKEDPROP ASSEMBLY.
    elabCommand (← `(command|
      /-- GENERATED by `declare_bridge` — the statement-as-instance
          (soundness mandatory; completeness `.proved` from the bridge —
          the loud two-constructor choice honored). -/
      def $checkedId:ident $[$leafHyps:bracketedBinder]*
          ($pRef : $indT) : Kit.CheckedProp $rowTyT where
        P := fun r => $relT $pT r
        check := fun r => $chkT $pT r
        sound := fun r h => $soundId $leafHypTerms* $pT r h
        complete? := .proved (fun r h => $completeId $leafHypTerms* $pT r h)))
  | _ => Elab.throwUnsupportedSyntax

end Kit.Derive.Bridge
