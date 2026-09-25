/-
# Kit.Derive.Cascade — the WF-cascade bridge generator (`declare_cascade`)

The close-out audit's #7: the lanes' checker is a per-rung cascade
(rung N's check = the local check + rung N-1's check), and every rung
carried a hand-proved `rungDiags = [] ↔ RungOk` bridge — the shape is
mechanical per cascade, the content is THIS generator (06 §7: a family
of N near-identical decls is a macro that hasn't been written). Two
commands, the per-rung registration + the assembled theorem:

- `declare_cascade_walk <row> (binders)* := <walkHead>, <elemRel> via
  <elemBridge>` — the WALK rung's bridge, GENERATED:
  `<row>_eq_nil_iff : ∀ (l : List _), walkHead l = [] ↔ ∀ x, x ∈ l →
  elemRel x`. The walk decomposes into the head element's check + the
  tail's walk; the bridge follows by induction + the componentwise
  discipline from the element bridge (the cons reshuffle is the
  template's fixed tail).
- `declare_cascade <name> (binders)* := <master-checker>,
  <master-relation> where | <rung> := via <bridge>` — THE MASTER: the
  full cascade's iff `<name>_eq_nil_iff : masterCheck binders = [] ↔
  masterRel binders`, one `simp only` over the master's equations + the
  FIXED list set (append/flatMap/map nil) + the registered rung
  bridges, closing on the componentwise relation chain — plus
  `<name>_sound` / `<name>_complete`, the two projections (the Keys
  lane's naming preserved).

HONEST SCOPE:

- the master checker must be a NAMED checker applied to the cascade's
  explicit `(x : T)` binders, with codomain `List _` (the diag
  envelope's carrier — any element type);
- the master relation must be the componentwise `∧`-chain of the
  rungs' relations, NESTED like the checker's append decomposition
  (the master `simp only` closes by rfl on exactly that shape — a
  mis-nested or mis-ordered chain refuses: wrongness does not
  elaborate);
- OR the RECORD face: a STRUCTURE application whose fields ARE the
  rung relations, in declaration order (the entity-machine preset's
  `EntityWf` shape — one row per field, each row's bridge stating the
  rung's CHUNK iff; a flatMap/map rung's composite bridge composes the
  per-element face by hand, since the record face's fixed simp set
  drops the flatMap/map decompositions to keep the template's
  rewrites deterministic against the chunk forms). The generated iff
  transports the checker's LEFT-nested append decomposition through
  the fields; an arity/order/nesting mismatch refuses (KD0014);
- the walk head must be the walk checker fully applied except its list
  argument (`List α → List β`);
- the match/if rungs' own bridges stay hand (the domain's content: the
  `cases find?` analysis is not mechanical — the `declare_bridge`
  leaf discipline); the generator composes them, it does not re-derive
  them.

E-codes: the `KD0010`–`KD0014` rows (Kit-derive, the `KD` family
extended; the registry's persisted allocation is the code-registry
gate's business — the rows land with this module).

Core-only (imports Lean + Kit.Diag + Kit.Derive.Fold — the cone rule).
META module: the generated decls are ordinary core-level theorems.

Five questions (notes/v3/01-core.md):
- root: META — the bridge cascade's generator face (the audit's #7).
- carrier grade: none of its own; the generated surface is the per-rung
  walk bridge + the master iff + the two projections.
- spine reading: the correspondence stage — the diagnostic authority ⇔
  the reasoning authority, rung by rung and whole.
- ladder rung: the generated bridges are `simp only` templates over the
  equation lemmas + one structural induction (build-stable; zero
  axioms — pinned by KitTests).
- gate row: KitTests' cascade suite (the fixture cascade → the
  generated lemmas + their use + the migration pins; the refusal teeth
  + the negative controls).
-/

import Lean
import Kit.Diag
import Kit.Derive.Fold

namespace Kit.Derive.Cascade

open Lean Elab Command Meta
open Kit.Derive.Common (throwDiag logRefusal gateCmd resolveConst?)

/-! ## The KD cascade rows — the generator's E-codes -/

/-- The cascade generator's E-codes, allocated from the PERSISTED
    registry (`notes/code-registry.txt`, the spec of record; 05 §4's
    stable-allocation rule) — the `KD` family extended. The constants
    are the family's DECLARATION — the sites below use them, never a
    bare string, and the code-registry gate's coverage scan ties every
    spelling to its allocated live row. -/
def eKD0010 : Kit.ECode := ⟨"KD0010"⟩
def eKD0011 : Kit.ECode := ⟨"KD0011"⟩
def eKD0012 : Kit.ECode := ⟨"KD0012"⟩
def eKD0013 : Kit.ECode := ⟨"KD0013"⟩
def eKD0014 : Kit.ECode := ⟨"KD0014"⟩

/-! ## The general helper (the cascade's fixed list set) -/

/-- The flatMap nil iff: the general face of the cascade's flatMap
    rung (the Keys lane's hand helper, promoted to the generator's
    fixed set — one proof, every cascade). -/
theorem flatMap_nil_iff {α β : Type} (f : α → List β) :
    ∀ (l : List α), l.flatMap f = [] ↔ ∀ a, a ∈ l → f a = [] := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.append_eq_nil_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ a' hmem'
        rcases List.mem_cons.mp hmem' with e | hmem2
        · subst e; exact h1
        · exact h2 a' hmem2
      · intro h
        exact ⟨h a List.mem_cons_self,
          fun a' hmem' => h a' (List.mem_cons_of_mem _ hmem')⟩

/-! ## The small elaborator helpers -/

/-- The pi chain's BODY (pure syntactic walk — the elaborated lambda's
    inferred type is already the syntactic pi). -/
private def piBody? : Expr → Option Expr
  | .forallE _ _ b _ => piBody? b
  | e => some e

/-- The pi chain's LAST domain (the walk checker's list argument's
    domain — pure syntactic walk). -/
private def piLastDom? : Expr → Option Expr
  | .forallE _ d b _ =>
      match piLastDom? b with
      | some d' => some d'
      | none => some d
  | _ => none

/-- The lambda chain's body (pure syntactic walk — the relation
    face's head read). -/
private def lamBody : Expr → Expr
  | .lam _ _ b _ => lamBody b
  | e => e

/-- The head constant of a binder-scoped checker: peel the elaborated
    lambda, take the application's head — a const, or none (the
    literal-lambda fragment is out of scope). -/
private partial def lamHead? : Expr → Option Name
  | .lam _ _ b _ => lamHead? b
  | e =>
      match e.getAppFn with
      | .const n _ => some n
      | _ => none

/-- The row's bridge check: the ident resolves to a CONSTANT whose
    type's head is `Iff` (the bridge is an iff — the componentwise
    discipline's currency). Unknown or non-iff → the curated refusal
    (KD0012). -/
private def checkBridge (cmdName : Name) (rowName : String)
    (bridgeIdent : TSyntax `ident) : CommandElabM Name := do
  let env ← getEnv
  let bridgeStr := bridgeIdent.getId.toString
  let some bn := ← resolveConst? bridgeIdent |
    throwDiag eKD0012
      s!"declare_cascade {cmdName}: the row `{rowName}`'s bridge \
        `{bridgeStr}` does not resolve — the bridge is the rung's \
        iff-valued lemma (`rungDiags = [] ↔ RungOk`)"
  match env.find? bn with
  | some ci =>
      let headOk : Bool ← liftTermElabM do
        let ty : Expr ← (liftM (whnfR ci.type) : TermElabM Expr)
        pure ((piBody? ty).get!.isAppOf ``Iff)
      unless headOk do
        throwDiag eKD0012
          s!"declare_cascade {cmdName}: the row `{rowName}`'s bridge \
            `{bridgeStr}` is not an iff — the componentwise \
            discipline's currency is `rungDiags = [] ↔ RungOk`"
      pure bn
  | none =>
      throwDiag eKD0012
        s!"declare_cascade {cmdName}: the row `{rowName}`'s bridge \
          `{bridgeStr}` does not resolve — the bridge is the rung's \
          iff-valued lemma (`rungDiags = [] ↔ RungOk`)"

/-- The binder's IDENT slot: the explicit/implicit binder's raw shape is
    `( <binderIdent+> : T )` — the ident list is args[1]; a HOLE (`_`)
    there is the anonymous fragment (refused). -/
private def binderIdent? (bRaw : Syntax) : Option Syntax := do
  match bRaw[1]!.getArgs[0]? with
  | some idStx => if idStx.isIdent then some idStx else none
  | none => none

/-- The named `(x : T)` / `{x : T}` binders' check + their ident terms
    (the generated theorems re-spell them, so the idents must exist;
    the anonymous fragments are the named extension). -/
private def checkBinders (cmdName : Name)
    (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :
    CommandElabM (Array Term) := do
  let mut binderTerms : Array Term := #[]
  for b in binders do
    let some idStx := binderIdent? b.raw |
      throwDiag eKD0010
        s!"declare_cascade {cmdName}: the cascade's binders must be \
          NAMED `(x : T)` binders — the generated theorems re-spell \
          them (the anonymous fragments are the named extension)"
    binderTerms := binderTerms.push ⟨idStx⟩
  pure binderTerms

/- The PROOF GATE + the refusal logger are Kit.Derive.Common's (the
    drivers' ONE copy — the DRY sweep finding; the generated commands'
    refusal discipline is byte-identical to the pre-common private
    copies this module carried). -/

/-! ## The walk command — the per-rung registration -/

/-- THE WALK RUNG's registration: the walk head + the element relation
    (comma-separated, the `declare_bridge` checker/relation shape) + the
    element bridge. -/
syntax (name := cascadeWalkCmd) "declare_cascade_walk " ident
  (ppSpace bracketedBinder)* " := " term ", " term " via " ident : command

/-- THE WALK RUNG's registration: `declare_cascade_walk <row>
    (binders)* := <walkHead>, <elemRel> via <elemBridge>` —
    generates the walk rung's bridge `<row>_eq_nil_iff` by the
    componentwise discipline (the module header has the scope). -/
@[command_elab Kit.Derive.Cascade.cascadeWalkCmd]
def elabCascadeWalk : CommandElab
  | stx@`(command| declare_cascade_walk $name:ident
        $[$binders:bracketedBinder]* := $walkHead:term, $elemRel:term
        via $elemBridge:ident) => do
    discard (checkBinders (`declare_cascade_walk ++ name.getId) binders)
    -- THE WALK HEAD: a NAMED walk checker, fully applied except its
    -- list argument (`List α → List β`).
    let funBinders : TSyntaxArray `Lean.Parser.Term.funBinder :=
      binders.map (fun b => (⟨b.raw⟩ : TSyntax `Lean.Parser.Term.funBinder))
    let headLam ← liftTermElabM do
      let lam ← Lean.Elab.Term.elabTerm
        (← `(fun $funBinders* => $walkHead:term)) none
      instantiateMVars lam
    let some walkHeadName := lamHead? headLam |
      throwDiag eKD0013
        s!"declare_cascade_walk {name.getId}: the walk head must be a \
          NAMED walk checker applied to the walk's binders — the \
          literal-lambda / projector fragments are the named extension"
    let walkTy ← liftTermElabM ((liftM (inferType headLam) : TermElabM Expr))
    let some listDom := piLastDom? walkTy |
      throwDiag eKD0013
        s!"declare_cascade_walk {name.getId}: the walk head is fully \
          applied — a walk checker takes the LIST as its last argument \
          (`List α → List β`)"
    unless listDom.isAppOf ``List do
      throwDiag eKD0013
        s!"declare_cascade_walk {name.getId}: the walk head's last domain \
          is `{listDom}` — a walk checker takes the LIST as its last \
          argument (`List α → List β`)"
    -- THE ELEMENT BRIDGE: an iff-valued constant.
    let bridgeName ← checkBridge name.getId name.getId.toString elemBridge
    -- THE GENERATED BRIDGE: the walk's componentwise induction — the
    -- nil rung is `simp`-trivial, the cons rung rewrites the walk's
    -- equation + the fixed append iff + the ih + the element bridge,
    -- then the fixed cons reshuffle (literal binders — the quotation's
    -- own macro scope; no cross-quotation sharing).
    let headT : Term := mkIdentFrom stx walkHeadName
    let bridgeT : Term := mkIdentFrom stx bridgeName
    let walkHeadT : Term := walkHead
    let iffId : TSyntax `ident := mkIdentFrom stx
      (Name.mkSimple s!"{name.getId.toString}_eq_nil_iff")
    let lBinder ← `(bracketedBinder| (l : List _))
    let tail : Term ← `(by
      induction l with
      | nil => simp [$headT:term]
      | cons fk fks ih =>
          simp only [$headT:term, List.append_eq_nil_iff, ih, $bridgeT:term]
          first
            | constructor
              · rintro ⟨h1, h2⟩ x hmem
                rcases List.mem_cons.mp hmem with e | hmem
                · subst e; exact h1
                · exact h2 x hmem
              · intro h
                exact ⟨h fk List.mem_cons_self,
                  fun x hmem => h x (List.mem_cons_of_mem _ hmem)⟩
            | skip)
    let walkCmd ← `(command|
      /-- GENERATED by `declare_cascade_walk` — the WALK rung's bridge
          (the per-rung generation): the walk decomposes into the head
          element's check + the tail's walk; the bridge follows by
          induction + the componentwise discipline from the element
          bridge. -/
      theorem $iffId:ident $[$binders:bracketedBinder]* $lBinder:bracketedBinder :
          $walkHeadT:term l = [] ↔ ∀ x, x ∈ l → $elemRel:term x :=
        $tail)
    -- THE GATE: a walk head the template cannot carry (the element
    -- bridge mismatching the walk's body, a non-list recursion) refuses
    -- here — wrongness does not elaborate; sorry never lands.
    let refuseMsg : String :=
      s!"declare_cascade_walk {name.getId}: the generated bridge failed \
        to elaborate — the walk head's body must be the componentwise \
        walk (the head element's check ++ the tail's walk) and the \
        element bridge must state its iff (a refused rung commits \
        nothing; Lean's sorry recovery never lands)"
    let refused ← gateCmd walkCmd
    if refused then
      logRefusal eKD0014 refuseMsg
  | _ => Elab.throwUnsupportedSyntax

/-! ## The master command — the assembled theorem -/

declare_syntax_cat cascadeRowCat

/-- The chain row: the rung's bridge already exists (the match/if
    rungs are the domain's content; the walk rungs' bridges are the
    `declare_cascade_walk` commands' generated lemmas) — register the
    rung in the cascade. The name is the rung's label in the list. -/
syntax (name := cascadeViaRow) "| " ident " := " " via " ident : cascadeRowCat

syntax (name := declareCascadeCmd) "declare_cascade " ident
  (ppSpace bracketedBinder)* " := " term ", " term " where"
  (ppSpace colGt cascadeRowCat)* : command

/-- THE CASCADE GENERATOR: `declare_cascade <name> (binders)* :=
    <master-checker>, <master-relation> where …` — the master bridge +
    the two projections (the module header has the scope). -/
@[command_elab Kit.Derive.Cascade.declareCascadeCmd]
def elabDeclareCascade : CommandElab
  | stx@`(command| declare_cascade $name:ident $[$binders:bracketedBinder]*
        := $chk:term, $rel:term where $[$rows:cascadeRowCat]*) => do
    let binderTerms ← checkBinders name.getId binders
    -- THE MASTER CHECKER'S SHAPE: a NAMED checker, codomain `List _`.
    let funBinders : TSyntaxArray `Lean.Parser.Term.funBinder :=
      binders.map (fun b => (⟨b.raw⟩ : TSyntax `Lean.Parser.Term.funBinder))
    let chkLam ← liftTermElabM do
      let lam ← Lean.Elab.Term.elabTerm
        (← `(fun $funBinders* => $chk:term)) none
      instantiateMVars lam
    let some chkHead := lamHead? chkLam |
      throwDiag eKD0010
        s!"declare_cascade {name.getId}: the master checker must be a \
          NAMED checker applied to the cascade's binders — the \
          literal-lambda / projector fragments are the named extension"
    let chkTy ← liftTermElabM ((liftM (inferType chkLam) : TermElabM Expr))
    let some chkCod := piBody? chkTy |
      throwDiag eKD0010
        s!"declare_cascade {name.getId}: the master checker's codomain is \
          not a `List _` — the cascade's checker is a diagnostic \
          authority, its codomain is the diag envelope's carrier"
    unless chkCod.isAppOf ``List do
      throwDiag eKD0010
        s!"declare_cascade {name.getId}: the master checker's codomain is \
          `{chkCod}` — the cascade's checker is a diagnostic authority, \
          its codomain is the diag envelope's carrier (`List _`)"
    -- THE MASTER RELATION'S SHAPE: same binders, codomain `Prop`.
    let relLam ← liftTermElabM do
      let lam ← Lean.Elab.Term.elabTerm
        (← `(fun $funBinders* => $rel:term)) none
      instantiateMVars lam
    let relTy ← liftTermElabM ((liftM (inferType relLam) : TermElabM Expr))
    let some relCod := piBody? relTy |
      throwDiag eKD0011
        s!"declare_cascade {name.getId}: the master relation's type is not \
          a Prop — the cascade's reasoning authority is a Prop: the \
          componentwise `∧`-chain of the rungs' relations"
    unless relCod.isSort && relCod.sortLevel!.isZero do
      throwDiag eKD0011
        s!"declare_cascade {name.getId}: the master relation's type is not \
          a Prop — the cascade's reasoning authority is a Prop: the \
          componentwise `∧`-chain of the rungs' relations"
    -- THE ROWS: the rung list, each bridge checked.
    let mut bridges : Array Name := #[]
    for row in rows do
      match row with
      | `(cascadeRowCat| | $n:ident := via $b:ident) =>
          let bridgeName ← checkBridge name.getId n.getId.toString b
          bridges := bridges.push bridgeName
      | _ => Elab.throwUnsupportedSyntax
    -- THE RELATION FACE: the master relation is either the
    -- componentwise `∧`-chain (the And face — the master `simp only`
    -- closes by rfl on exactly that shape) or a RECORD conjunction: a
    -- structure application whose fields ARE the rung relations, in
    -- declaration order (the preset's `EntityWf` shape — one row per
    -- field, each row's bridge stating the rung's CHUNK iff).
    let env ← getEnv
    let relHead : Option Name :=
      match (lamBody relLam).getAppFn with
      | .const n _ => some n
      | _ => none
    let recordFields? : Option (Name × Array Name) :=
      match relHead with
      | some S =>
          if S == `And || !(Lean.isStructure env S) then none
          else some (S, Lean.getStructureFields env S)
      | none => none
    if let some rFields := recordFields? then
      unless rFields.2.size ≥ 2 do
        throwDiag eKD0011
          s!"declare_cascade {name.getId}: the record face needs at least \
            two fields/rungs — a single-rung cascade's relation is the \
            rung itself (spell it as the componentwise chain face)"
    -- THE SIMP SET: the master's equations + the FIXED list set (the
    -- componentwise discipline's shared face) + the rung bridges. The
    -- record face's fixed set drops the flatMap/map decompositions —
    -- its rows cite the rung bridges at the CHUNK level (a composite
    -- bridge composes the per-element face by hand), so the template's
    -- rewrites stay deterministic against the chunk forms.
    let fixedList : Array Term :=
      if recordFields?.isSome then
        #[(mkIdentFrom stx ``List.append_eq_nil_iff : Term)]
      else
        #[(mkIdentFrom stx ``List.append_eq_nil_iff : Term),
          (mkIdentFrom stx ``Kit.Derive.Cascade.flatMap_nil_iff : Term),
          (mkIdentFrom stx ``List.map_eq_nil_iff : Term)]
    let simpSet : Array Term :=
      #[(mkIdentFrom stx chkHead : Term)] ++ fixedList ++
      bridges.map (fun bn => (mkIdentFrom stx bn : Term))
    -- THE GENERATED SURFACE.
    let baseStr := name.getId.toString
    let iffId : TSyntax `ident := mkIdentFrom stx
      (Name.mkSimple s!"{baseStr}_eq_nil_iff")
    let soundId : TSyntax `ident := mkIdentFrom stx
      (Name.mkSimple s!"{baseStr}_sound")
    let completeId : TSyntax `ident := mkIdentFrom stx
      (Name.mkSimple s!"{baseStr}_complete")
    -- THE MASTER TACTIC: the chain face closes by rfl over the simp
    -- fixpoint; the record face TRANSPORTS the checker's LEFT-nested
    -- append decomposition through the fields (the numeric projections
    -- of the intro'd chain, the projection FUNCTIONS of the record —
    -- no dotted-ident tokens, the hygiene stays mechanical).
    let masterTac : Term ←
      match recordFields? with
      | some (S, rFields) => do
          let n := rFields.size
          let hId : TSyntax `ident := mkIdentFrom stx `hChain
          -- direction 1: the record built from the left-nested chain's
          -- numeric projections (F1 = h.1…1, F2 = h.1…2, …, FN = h.2…2)
          let mut projs : Array Term := #[]
          for i in Array.range n do
            let k := i + 1
            let ones : Nat := if k == 1 then n - 1 else n - k
            let mut acc : Term := hId
            for _ in List.range ones do
              acc ← `(($acc).1)
            if k > 1 then
              acc ← `(($acc).2)
            projs := projs.push acc
          -- direction 2: the chain built from the record's field
          -- PROJECTION FUNCTIONS (no dotted-ident tokens), nested LEFT
          -- like the checker's append decomposition
          let mut items : Array Term := #[]
          for f in rFields do
            let some pf := Lean.getProjFnForField? env S f |
              throwDiag eKD0011
                s!"declare_cascade {name.getId}: the record face's field \
                  `{f}` has no projection function"
            let pfT : Term := mkIdentFrom stx pf
            items := items.push (← `($pfT $hId))
          let mut chain : Term := items[0]!
          for i in Array.range (n - 1) do
            chain ← `(⟨$chain, $(items[i + 1]!)⟩)
          `(by
              constructor
              · intro $hId:ident
                simp only [$[$simpSet:term],*] at $hId:ident
                exact ⟨$[$projs:term],*⟩
              · intro $hId:ident
                simp only [$[$simpSet:term],*]
                exact $chain)
      | none => `(by simp only [$[$simpSet:term],*])
    let masterCmd ← `(command|
      /-- GENERATED by `declare_cascade` — THE MASTER BRIDGE (pattern #1
          at the cascade tier): the full cascade's iff — the diagnostic
          authority's empty envelope IS the componentwise conjunction of
          the rungs' relations. -/
      theorem $iffId:ident $[$binders:bracketedBinder]* :
          $chk:term = [] ↔ $rel:term := $masterTac)
    -- THE GATE: a decomposition the componentwise template cannot
    -- carry (the relation chain mis-nested/mis-ordered against the
    -- checker's append decomposition, a rung bridge that does not fit
    -- the master's body) refuses here — wrongness does not elaborate;
    -- sorry never lands.
    let refuseMsg : String :=
      if recordFields?.isSome then
        s!"declare_cascade {name.getId}: the generated theorem failed to \
          elaborate — the record face's rows must be the rung bridges at \
          the chunk level, ONE PER FIELD in the fields' declaration \
          order, and the checker's append decomposition must be \
          LEFT-nested against them (a refused cascade commits nothing; \
          Lean's sorry recovery never lands)"
      else
        s!"declare_cascade {name.getId}: the generated theorem failed to \
          elaborate — the master relation must be the componentwise \
          `∧`-chain of the rungs' relations, nested like the checker's \
          append decomposition (a refused cascade commits nothing; \
          Lean's sorry recovery never lands)"
    let masterRefused ← gateCmd masterCmd
    if masterRefused then
      logRefusal eKD0014 refuseMsg
    else
      -- THE PROJECTIONS (the Keys lane's naming preserved).
      let soundCmd ← `(command|
        /-- GENERATED by `declare_cascade` — soundness: a clean run
            transports INTO the componentwise relation chain. -/
        theorem $soundId:ident $[$binders:bracketedBinder]* :
            $chk:term = [] → $rel:term := ($iffId:term $binderTerms*).mp)
      let soundRefused ← gateCmd soundCmd
      if !soundRefused then
        let completeCmd ← `(command|
          /-- GENERATED by `declare_cascade` — completeness: the
              componentwise relation chain certifies a clean run. -/
          theorem $completeId:ident $[$binders:bracketedBinder]* :
              $rel:term → $chk:term = [] :=
            ($iffId:term $binderTerms*).mpr)
        if ← gateCmd completeCmd then
          logRefusal eKD0014 refuseMsg
  | _ => Elab.throwUnsupportedSyntax

end Kit.Derive.Cascade
