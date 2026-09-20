/-
# SchemaLang.Meta.EntityMachine — `schema_entity_machine` (W8.4)

The entity-machine preset's COMMAND half (the authoring surface). The
DATA + the generic laws live in `SchemaLang.EntityMachine`; this module
resolves names, gates, and emits the generated surface — the
`schema_keys`/`schema_update` command pattern.

    schema_entity_machine ticketMachine for Ticket := status : TicketState
      initial: new
      rewind: reopen
      transition: assign (new → triaged)
      transition: start (triaged → closed)
      transition: reopen (closed → new)

One declaration, the five artifacts (`EntityMachine.lean`'s header):

1. the `machine!` declaration (Inv := True — the closed enum IS the
   invariant) with the FULL entourage: `states:` clause generates the
   state space, the transition table, the table lookup, the agreement
   theorem, and the `DecidablePred` instance; the `rank:` clause
   (emitted when `rewind:` is declared — the rank = the state CODE,
   declaration order) generates the acyclicity pair (the rewind
   story);
2. the per-transition keyed updates (`Update2` items — the deltas on
   the state column: guard `status = from`, set `status := to`);
3. the legality relation (`legalFrom` — DFA membership) + the journal
   antijoin check + replay (`<m>LegalFrom`, `<m>Replay`,
   `<m>Replay_ok`);
4. the typestate hook (`<m>Hook`, the legality pin, the Rust text as a
   DEF — no emitter registration, the byte-tie holds by construction);
5. the obligation views (`<m>Obligations` — each transition's
   guard/postcondition at `decidableNow`).

The gates (all elaboration-time, the tightest tier): the record must be
a registered `Item.record` (did-you-mean); the state column must exist
(did-you-mean) and be `u64` (the state CODE — transitions are u64
deltas on it); the state type must be an inductive with NULLARY
constructors only (the closed-enum discipline); the initial state and
every transition edge must name constructors; transition names must be
unique; the rewind edge must name a declared transition.

Word-token discipline: `initial:`/`rewind:`/`transition:` are
colon-suffixed (the `machine!` lesson — the global token table is
untouched); the edge separator is the `→` punctuation (the
`schema_keys` lesson — never a common word).

The generated-syntax traps this file paid for (do not re-pay):
`Term` is ALWAYS spelled `Lean.Term` (with `open Lean Elab` the bare
name resolves to the ELABORATOR structure); every quotation-producing
helper is MONADIC (a quotation's macro-scope construction needs
`MonadQuotation`); antiquotes are PRE-BOUND to local idents; custom-
category splices carry the KIND ascription (`$[$xs:machineClause]*`);
the machine!-generated surface's names are HYBRID — the states-clause
entourage is STRING-concatenated (`<m>States`, `<m>Trans`,
`<m>TableStep?` — the Dsl convention), the labels pair and the Label
TYPE are NAME-appended (DOTTED: `<m>.labels`, `<m>.labels_complete`,
`<m>.Label`); the ColPath is built POSITIONALLY (`there`/`here` over
the field's index — the `HasCol` instance search breaks under a meta
import, the W5.4 constraint-7 lesson); `deriving DecidableEq` does NOT
bring `ReflBEq`/`LawfulBEq` (the journal/replay laws' instances are
emitted, per generated machine, with the NAMED-CTOR form — the
anonymous-⟨⟩ form mis-binds against LawfulBEq's ReflBEq parent); the
replay's type parameters are pinned by NAME (`(S := …) (L := …)`) —
the step? function's own type is phrased over the machine's FIELD
projections, which the instance search cannot unfold.

Ownership: the W8.4 entity-machine lane's command half. Deliberate
exclusions: no registration into `update2ItemExt` (the update lane
owns that registry's elaborator route; the preset emits the update
DATA as defs — wiring the preset's rows in is a follow-up); no emitter
registration (byte-tie by construction, the `Meta.Keys` pattern).
-/

module

public import Lean
public import Machines.Dsl
public meta import SchemaLang.Meta.Reflect
public meta import SchemaLang.Meta.Keys
public meta import SchemaLang.Meta.Derive
public meta import SchemaLang.EntityMachine

public meta section

namespace SchemaLang.Meta

open Lean Elab Command
-- the clause-kit category quotations + antiquotation ascriptions resolve
-- the category BARE (the `open` — `declare_syntax_cat` registers the
-- category under the name AS WRITTEN, un-namespaced: quotations and
-- antiquotation ascriptions use `machineClause`, while the RULE kinds
-- (`machineStateClause` etc.) stay namespace-qualified
-- `Machines.Dsl.machineStateClause` — the `getKind` dispatch keys)

-- The clause category (the Machines.Dsl clause-kit discipline — one
-- named rule per clause, the low-priority unknown-clause catch-all
-- rejecting typos with a did-you-mean at ELABORATION). Word-token
-- discipline: `initial:`/`rewind:`/`transition:` are
-- colon-suffixed (the `machine!` lesson — the global token table is
-- untouched); the edge separator is the `→` punctuation (the
-- `schema_keys` lesson — never a common word). The category parks in
-- Lean's namespace BY DESIGN (the `updateClause` precedent).
set_option linter.guestlang.packageNamespace false in
declare_syntax_cat entityMachineClause

attribute [nolint linter.guestlang.dupDefBodies "syntax-category bodies are identical by construction (a category carries no payload)"]
  Lean.Parser.Category.entityMachineClause

/-- `initial: <ctor>` — the lifecycle's start state (exactly one; the
    elaborator enforces the cardinality the positional grammar baked
    in). -/
syntax (name := entityInitialClause) "initial:" ident : entityMachineClause

/-- `rewind: <transition>` — the optional recovery edge (at most one). -/
syntax (name := entityRewindClause) "rewind:" ident : entityMachineClause

/-- One transition clause: `transition: <name> (<src> → <dst>)` — bare
    constructor names (the command emits the dotted refs). -/
syntax (name := entityTransitionClause) "transition:" ident " (" ident " → " ident ")"
  : entityMachineClause

/-- The unknown-clause catch-all (the Machines.Dsl clause-kit
discipline): low priority, so the named clauses win; anything else
well-formed (`<typo>: <term>`) parses and is rejected at ELABORATION
with a did-you-mean over the legal clauses. -/
syntax (name := entityUnknownClause) (priority := low) ident ": " term : entityMachineClause

/-- THE AUTHORING SURFACE (see the module header). The body is a
    uniform CLAUSE LIST (the Machines.Dsl clause-kit discipline). -/
syntax (name := schemaEntityMachine) "schema_entity_machine " ident
  " for " ident " := " ident " : " ident entityMachineClause* : command

/-- `.ctor` — the dotted constructor reference (term AND pattern — the
    same `dotIdent` node kind). -/
private def dotRef (id : TSyntax `ident) : Lean.Term :=
  ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent
    #[mkAtom ".", id.raw]⟩

/-- The did-you-mean suffix — the Machines.Dsl clause-kit's one tree-wide
    format (the `Meta.Keys` message discipline). The `KeyTy`/`Ty`/`Field`
    renderers are the SHARED walkers (`Meta.keyTerm`/`Meta.tyTerm`/
    `Meta.fieldTerm` in `Meta.Derive` — the one `Ty` reifier per level;
    this lane no longer keeps its own). -/
private def hintOf (s : String) (cands : List String) : String :=
  Machines.Dsl.didYouMeanHint s cands

/-- The elaborator: resolve + gate + emit (the generated surface is
    listed in the module header). -/
@[command_elab SchemaLang.Meta.schemaEntityMachine]
def elabSchemaEntityMachine : CommandElab := fun stx => do
  -- stx = [cmd, name, " for ", recId, " := ", stateCol, " : ", stateTy,
  --        clausesNode] — the clauses arrive in SOURCE ORDER; the sweep
  -- dispatches on the clause KIND (the Machines.Dsl clause-kit
  -- discipline: cardinalities here, unknown clauses → did-you-mean).
  let base : TSyntax `ident := ⟨stx[1]!⟩
  let baseName := stx[1]!.getId.toString
  let recId := stx[3]!.getId
  let stateCol := stx[5]!.getId.toString
  let stateTyId : TSyntax `ident := ⟨stx[7]!⟩
  let legalClauses : List String := ["initial", "rewind", "transition"]
  let mut initState? : Option Syntax := none
  let mut optRw : Option Syntax := none
  let mut trs : Array Syntax := #[]
  for c in stx[8]!.getArgs do
    match c.getKind with
    | ``entityInitialClause =>
        if initState?.isSome then
          throwError s!"schema_entity_machine `{baseName}`: duplicate `initial:` clause — exactly one"
        initState? := some c[1]!
    | ``entityRewindClause =>
        if optRw.isSome then
          throwError s!"schema_entity_machine `{baseName}`: duplicate `rewind:` clause — at most one"
        optRw := some c
    | ``entityTransitionClause => trs := trs.push c
    -- entityUnknownClause = [clauseName-ident, ":", payload-term]
    | ``entityUnknownClause =>
        Machines.Dsl.didYouMeanError s!"schema_entity_machine `{baseName}`"
          (c[0]!.getId.toString) legalClauses
    | _ => throwUnsupportedSyntax
  let initState : String ←
    match initState? with
    | some i => pure i.getId.toString
    | none =>
        throwError s!"schema_entity_machine `{baseName}`: missing `initial:` clause — the lifecycle's start state"
  -- entityTransitionClause = ["transition:", name, " (", src, " → ", dst, ")"]
  let rwName? : Option String := optRw.map (fun rw => rw[1]!.getId.toString)
  -- the record: a registered `Item.record`, or did-you-mean (the
  -- `schema_keys` pattern)
  let (recordName, fields) ← resolveKeyRecord "schema_entity_machine" recId
  -- the state column: present + u64 (the CODE discipline)
  match fields.find? (·.name == stateCol) with
  | none =>
      throwError s!"schema_entity_machine `{baseName}`: `{stateCol}` is not a \
        column of `{recordName}`" ++
        hintOf stateCol (fields.map (·.name))
  | some sf =>
      unless sf.ty = .u64 do
        throwError s!"schema_entity_machine `{baseName}`: the state column \
          `{stateCol}` must be `u64` (the state CODE — transitions are u64 \
          deltas on it; the wire record carries the code, the enum is the \
          host-side discipline)"
  -- the state type: an inductive, NULLARY constructors only (the
  -- closed-enum discipline — the code is the declaration order)
  let ind ← liftCoreM <| getConstInfoInduct stateTyId.getId
  let ctorNames : List String := ind.ctors.map (·.getString!)
  for c in ind.ctors do
    let ci ← liftCoreM <| getConstInfoCtor c
    unless ci.numFields == 0 do
      throwError s!"schema_entity_machine `{baseName}`: the state type \
        `{stateTyId}` has a payload constructor `{c}` — the states must be \
        nullary (the closed-enum discipline: the code is the declaration \
        order)"
  -- the state codes (the declared states' order)
  let codes : List (String × Nat) :=
    ctorNames.zip (List.range ctorNames.length)
  let codeOf (s : String) : CommandElabM Nat :=
    match codes.find? (fun p => p.1 == s) with
    | some p => pure p.2
    | none =>
        throwError s!"schema_entity_machine `{baseName}`: `{s}` is not a \
          constructor of `{stateTyId}`" ++ hintOf s ctorNames
  unless initState ∈ ctorNames do
    throwError s!"schema_entity_machine `{baseName}`: initial `{initState}` \
      is not a constructor of `{stateTyId}`" ++ hintOf initState ctorNames
  -- the transitions: names unique, edges declared
  let mut seen : List String := []
  let mut trData : Array (String × String × String) := #[]
  for tr in trs do
    let tName := tr[1]!.getId.toString
    if tName ∈ seen then
      throwError s!"schema_entity_machine `{baseName}`: duplicate transition \
        name `{tName}`"
    seen := seen ++ [tName]
    let src := tr[3]!.getId.toString
    let dst := tr[5]!.getId.toString
    unless src ∈ ctorNames do
      throwError s!"schema_entity_machine `{baseName}`: transition `{tName}`: \
        `{src}` is not a constructor of `{stateTyId}`" ++ hintOf src ctorNames
    unless dst ∈ ctorNames do
      throwError s!"schema_entity_machine `{baseName}`: transition `{tName}`: \
        `{dst}` is not a constructor of `{stateTyId}`" ++ hintOf dst ctorNames
    trData := trData.push (tName, src, dst)
  if trData.isEmpty then
    throwError s!"schema_entity_machine `{baseName}`: no transitions — an \
      entity machine needs at least one `transition:` clause"
  -- the optional rewind edge: a DECLARED transition
  if let some rwName := rwName? then
    unless rwName ∈ seen do
      throwError s!"schema_entity_machine `{baseName}`: rewind `{rwName}` is \
        not a declared transition" ++ hintOf rwName seen

  -- Artifact 1 — the rank (the state CODE) + the machine! declaration
  -- (+ the entourage)

  let rankId := mkIdentFrom stx (baseName ++ "Rank").toName
  let rankAlts : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
    ctorNames.toArray.zipIdx.mapM fun (c, i) => do
      let lhs := dotRef (mkIdentFrom stx c.toName)
      let rhs := (quote i : Lean.Term)
      `(Lean.Parser.Term.matchAltExpr| | $lhs => $rhs)
  elabCommand (← `(command|
    /-- The lifecycle rank: the state's CODE (declaration order) —
        W8.4 preset-generated (the rewind clause's acyclicity input). -/
    def $rankId:ident : $stateTyId:ident → Nat $[$rankAlts:matchAlt]*))
  Machines.Dsl.addEntourageUnexp stx rankId.getId s!"{baseName}'s rank"
  -- the rank clause spliced as a 0-or-1 ARRAY (the `$[$x]?` antisplice
  -- does not parse at a `machineClause*` repetition position — only the
  -- `*` form does; the W8.4 trap list's kind-ascription sibling)
  let rankSplice : Array (TSyntax `machineClause) ←
    match rwName? with
    | none => pure #[]
    | some rwName => do
        let rwId := mkIdentFrom stx rwName.toName
        pure #[← `(machineClause|
          rank: $rankId:ident rewind: $rwId:ident)]
  let machineEvents : Array (TSyntax `machineClause) ←
    trData.mapM fun (tName, src, dst) => do
      let srcDot : Lean.Term := dotRef (mkIdentFrom stx src.toName)
      let dstDot : Lean.Term := dotRef (mkIdentFrom stx dst.toName)
      `(machineClause|
          event: $(mkIdentFrom stx tName.toName):ident
            guard: (fun s => s = $srcDot)
            action: (fun _ _ => $dstDot))
  let stateDots : Array Lean.Term :=
    (ctorNames.map fun c => dotRef (mkIdentFrom stx c.toName)).toArray
  elabCommand (← `(command|
    machine! $base:ident where
      State: $stateTyId:ident
      Inv: fun _ => True
      $[$rankSplice:machineClause]*
      states: [$stateDots,*]
      $[$machineEvents:machineClause]*))

  -- Artifact 1b — the generated-surface handles

  let labelsId := mkIdentFrom stx s!"{baseName}.labels".toName
  let statesId := mkIdentFrom stx (baseName ++ "States").toName
  let transId := mkIdentFrom stx (baseName ++ "Trans").toName
  let tstepId := mkIdentFrom stx (baseName ++ "TableStep?").toName
  let tieId := mkIdentFrom stx (baseName ++ "TableStep?_eq_step?").toName
  let completeId := mkIdentFrom stx (baseName ++ "States_complete").toName
  let honestId := mkIdentFrom stx (baseName ++ "Trans_honest").toName
  let labelTyId := mkIdentFrom stx s!"{baseName}.Label".toName
  let stTyT : Lean.Term := ⟨stateTyId.raw⟩
  let lbTyT : Lean.Term := ⟨labelTyId.raw⟩
  let fieldTerms := (← fields.mapM fieldTerm).toArray
  let fieldsT ← `(term| [$fieldTerms,*])

  elabCommand (← `(command|
    theorem $completeId:ident :
        ∀ s : $stateTyId:ident, s ∈ $statesId:ident := by
      intro s; cases s <;> simp [$statesId:ident]))
  Machines.Dsl.addEntourageUnexp stx completeId.getId
    s!"{baseName}'s states complete"
  elabCommand (← `(command|
    theorem $honestId:ident :
        ∀ e ∈ $transId:ident,
          Machines.Machine.step? $base:ident e.2.1 e.1 = some e.2.2 :=
      SchemaLang.EntityMachine.trans_honest $base:ident $labelsId:ident
        $statesId:ident $transId:ident rfl))
  Machines.Dsl.addEntourageUnexp stx honestId.getId
    s!"{baseName}'s transitions honest"

  -- the LawfulBEq bridges: `deriving DecidableEq` does NOT bring
  -- `ReflBEq`/`LawfulBEq`, and the journal/replay laws' instance
  -- searches key on the types AS WRITTEN (the state type + the
  -- generated Label type). The NAMED-CTOR form (the anonymous-⟨⟩ form
  -- mis-binds against LawfulBEq's ReflBEq parent).
  elabCommand (← `(command|
    instance : ReflBEq $stateTyId:ident :=
      ReflBEq.mk (rfl := by intro a; cases a <;> decide)))
  elabCommand (← `(command|
    instance : LawfulBEq $stateTyId:ident :=
      LawfulBEq.mk (eq_of_beq := by
        intro a b h; cases a <;> cases b <;>
          first | rfl | exact absurd h (by decide))))
  elabCommand (← `(command|
    instance : ReflBEq $labelTyId:ident :=
      ReflBEq.mk (rfl := fun {a} => decide_eq_true rfl)))
  elabCommand (← `(command|
    instance : LawfulBEq $labelTyId:ident :=
      LawfulBEq.mk (eq_of_beq := fun {_ _} h => of_decide_eq_true h)))

  -- Artifact 2 — the per-transition keyed updates (the deltas): the
  -- ColPath is built POSITIONALLY (`there`/`here` over the field's
  -- index; the `HasCol` instance search breaks under a meta import).

  let statusIdx := (fields.findIdx? (·.name == stateCol)).getD 0
  let suffixT := (← (fields.drop (statusIdx + 1)).mapM fieldTerm).toArray
  let pathT ← (List.range statusIdx).foldlM
    (fun p _ => `(term| SchemaLang.ColPath.there $p))
    (← `(term| SchemaLang.ColPath.here (fs := [$suffixT,*])))
  let updOblTs : Array Lean.Term ← trData.mapM fun (tName, src, dst) => do
    let fCode ← codeOf src
    let tCode ← codeOf dst
    let updName := mkIdentFrom stx
      (baseName ++ "Update" ++ tName.capitalize).toName
    let fCodeE := (quote fCode : Lean.Term)
    let tCodeE := (quote tCode : Lean.Term)
    let bnE := (quote baseName : Lean.Term)
    let tnE := (quote tName : Lean.Term)
    let rnE := (quote recordName : Lean.Term)
    let updRhs ← `(term| SchemaLang.SomeUpdate2.mk $fieldsT
      (SchemaLang.EntityMachine.transitionUpdate $bnE $tnE $rnE $pathT
        $fCodeE $tCodeE))
    elabCommand (← `(command|
      /-- W8.4 preset: the transition's keyed update — the delta on the
          state column (`SchemaLang.EntityMachine.transitionUpdate`). -/
      def $updName:ident : SchemaLang.SomeUpdate2 := $updRhs))
    Machines.Dsl.addEntourageUnexp stx updName.getId
      s!"{baseName}'s {tName} update"
    let oblT ← `(term|
      SchemaLang.EntityMachine.transitionObligations
        $bnE $tnE $updName $fCodeE $tCodeE)
    pure oblT
  let updTerms := updOblTs

  -- Artifact 5 — the obligation views

  elabCommand (← `(command|
    def $(mkIdentFrom stx (baseName ++ "Obligations").toName) :
        List SchemaLang.EntityMachine.EntityObligation :=
      ([$updTerms,*]).flatten))
  Machines.Dsl.addEntourageUnexp stx (baseName ++ "Obligations").toName
    s!"{baseName}'s obligations"

  -- Artifact 3 — legality, journal antijoin, replay

  let legalFromId := mkIdentFrom stx (baseName ++ "LegalFrom").toName
  let replayId := mkIdentFrom stx (baseName ++ "Replay").toName
  elabCommand (← `(command|
    /-- W8.4 preset: the legality relation — the run accepts (DFA
        membership; `SchemaLang.EntityMachine.legalFrom`). -/
    def $legalFromId:ident (init : $stTyT)
        (seq : List $lbTyT) : Bool :=
      SchemaLang.EntityMachine.legalFrom $base:ident init seq))
  Machines.Dsl.addEntourageUnexp stx legalFromId.getId
    s!"{baseName}'s legality"
  elabCommand (← `(command|
    def $replayId:ident (init : $stTyT) :
        List ($lbTyT × $stTyT × $stTyT) →
          Option $stTyT :=
    SchemaLang.EntityMachine.replay (S := $stTyT) (L := $lbTyT)
      (Machines.Machine.step? $base:ident) init))
  Machines.Dsl.addEntourageUnexp stx replayId.getId
    s!"{baseName}'s replay"
  elabCommand (← `(command|
    theorem $(mkIdentFrom stx (baseName ++ "Replay_ok").toName)
        (init : $stTyT)
        (journal : List ($lbTyT × $stTyT × $stTyT))
        (hlegal : SchemaLang.EntityMachine.legalJournal $transId:ident journal
          = true)
        (hchain : SchemaLang.EntityMachine.ChainsFrom init journal) :
        ∃ fin, $replayId:ident init journal = some fin :=
      SchemaLang.EntityMachine.replay_of_legalJournal
        (S := $stTyT) (L := $lbTyT)
        (Machines.Machine.step? $base:ident) $transId:ident $honestId:ident
        journal hlegal init hchain))
  Machines.Dsl.addEntourageUnexp stx (baseName ++ "Replay_ok").toName
    s!"{baseName}'s replay law"

  -- Artifact 4 — the typestate hook

  let stateAlts : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
    ctorNames.toArray.zipIdx.mapM fun (c, _) => do
      let lhs := dotRef (mkIdentFrom stx c.toName)
      let rhs := (quote c.capitalize : Lean.Term)
      `(Lean.Parser.Term.matchAltExpr| | $lhs => $rhs)
  let eventAlts : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
    trData.mapM fun (tName, _, _) => do
      let lhs := dotRef (mkIdentFrom stx tName.toName)
      let rhs := (quote tName : Lean.Term)
      `(Lean.Parser.Term.matchAltExpr| | $lhs => $rhs)
  let hookId := mkIdentFrom stx (baseName ++ "Hook").toName
  -- the naming maps as EQUATIONAL defs (the alts splice into the def
  -- form; a `match … with $[...]*` splice does not parse)
  let stateStructId := mkIdentFrom stx (baseName ++ "StateStruct").toName
  let eventMethodId := mkIdentFrom stx (baseName ++ "EventMethod").toName
  elabCommand (← `(command|
    /-- W8.4 preset: the typestate's Rust struct name per state. -/
    def $stateStructId:ident : $stateTyId:ident → String $[$stateAlts:matchAlt]*))
  Machines.Dsl.addEntourageUnexp stx stateStructId.getId
    s!"{baseName}'s state-struct map"
  elabCommand (← `(command|
    /-- W8.4 preset: the typestate's Rust method name per event. -/
    def $eventMethodId:ident : $lbTyT → String $[$eventAlts:matchAlt]*))
  Machines.Dsl.addEntourageUnexp stx eventMethodId.getId
    s!"{baseName}'s event-method map"
  let rwField ←
    match rwName? with
    | some rwName => do
        let rwRef : Lean.Term :=
          ⟨mkIdentFrom stx s!"{baseName}.Label.{rwName}".toName⟩
        pure ((← `(term| Option.some $rwRef)),
               ← `(term| SchemaLang.EntityMachine.hookEdges $transId:ident
                    (Option.some $rwRef)))
    | none =>
        pure ((← `(term| (Option.none : Option $lbTyT))),
               ← `(term| $transId:ident))
  let rw1 := rwField.1
  let rw2 := rwField.2
  elabCommand (← `(command|
    def $hookId:ident :
        SchemaLang.EntityMachine.TypestateHook $base:ident :=
      SchemaLang.EntityMachine.TypestateHook.mk $rw1 $rw2
        $stateStructId $eventMethodId))
  Machines.Dsl.addEntourageUnexp stx hookId.getId
    s!"{baseName}'s typestate hook"
  elabCommand (← `(command|
    theorem $(mkIdentFrom stx (baseName ++ "Hook_edges_legal").toName) :
        ((SchemaLang.EntityMachine.hookEdges $transId:ident
            ($rw1 : Option $lbTyT)
            |>.map (fun e => $tstepId:ident e.1 e.2.1)).all Option.isSome)
          = true :=
      SchemaLang.EntityMachine.hookEdges_legal $base:ident
        ($rw1 : Option $lbTyT)
        $transId:ident $tstepId:ident
        (fun e s => $tieId:ident e s ($completeId:ident s))
        $honestId:ident))
  Machines.Dsl.addEntourageUnexp stx (baseName ++ "Hook_edges_legal").toName
    s!"{baseName}'s hook-edges law"
  let initDot := dotRef (mkIdentFrom stx initState.toName)
  let srcLabel := (quote s!"SchemaLang.{baseName} (W8.4 entity-machine preset)"
    : Lean.Term)
  elabCommand (← `(command|
    def $(mkIdentFrom stx (baseName ++ "TypestateRust").toName) : String :=
      SchemaLang.EntityMachine.hookRust $hookId $initDot $srcLabel))
  Machines.Dsl.addEntourageUnexp stx (baseName ++ "TypestateRust").toName
    s!"{baseName}'s typestate rust"

  -- The declaration row (the provenance data)

  let trTerms ← trData.mapM fun (tName, src, dst) => do
    let tN := (quote tName : Lean.Term)
    let sN := (quote src : Lean.Term)
    let dN := (quote dst : Lean.Term)
    `(term| SchemaLang.EntityMachine.EntityTransition.mk $tN $sN $dN)
  let bnE := (quote baseName : Lean.Term)
  let rnE := (quote recordName : Lean.Term)
  let scE := (quote stateCol : Lean.Term)
  let ctE := (quote ctorNames : Lean.Term)
  let declRhs ← `(term|
    SchemaLang.EntityMachine.EntityMachineDecl.mk
      $bnE $rnE $scE $ctE [$trTerms,*])
  elabCommand (← `(command|
    /-- W8.4 preset: the declaration row (the provenance data). -/
    def $(mkIdentFrom stx (baseName ++ "EntityDecl").toName) :
        SchemaLang.EntityMachine.EntityMachineDecl := $declRhs))
  Machines.Dsl.addEntourageUnexp stx (baseName ++ "EntityDecl").toName
    s!"{baseName}'s declaration row"
  pure ()

end SchemaLang.Meta

end -- public meta section
