/-
# SchemaLang.Meta.Register.Updates — the `schema_update` command (v1 + v2)

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the v1/v2 update
registries, the volatile-fn scan, the update clause syntax, and the
`schema_update` elaborator. The typed-quotation helpers live in
`Register.Quotes`.
-/
module

public import Lean
public import Qq
public import CodegenCore.AttrKit
public import CodegenCore
public meta import SchemaLang.Ty
public meta import SchemaLang.Item
public meta import SchemaLang.Invariant
public meta import SchemaLang.Update
public meta import SchemaLang.Keys
-- Update2 is mathlib-FREE by construction (the neutrality family moved
-- to Update.lean at W8.3 — TickCascade's `Dbsp.Effects` dependency
-- must NOT reach legacy `Meta.Reflect` consumers: the feature-flags
-- `Flag` collision lesson). Keep it that way: Update2 imports
-- Update/Keys/CodegenCore only.
public meta import SchemaLang.Update2
public meta import SchemaLang.Meta.Register.Core
public meta import SchemaLang.Meta.Register.Keys
public meta import SchemaLang.Meta.Register.Quotes
-- The S5 meta-toolkit (`declare_registry_member` — RegisterKit): the
-- registry below is its emitted skeleton (plain-rows mode).
public meta import SchemaLang.Meta.RegisterKit

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Updates — `schema_update <name> for <Record> set <col> := <value> where <guard>`

The update registry is a SEPARATE extension (`update2ItemExt`) over
`SomeUpdate2` (SchemaLang.Update2 — imported above, NOT moved: the core
is owned elsewhere; importing keeps one definition). `Item` is the
closed boundary universe and cannot carry the `VExpr` family — the same
reason invariants got their own extension.

V2 (the v1→v2 demotion): the v2 registry (`update2ItemExt`) is THE
row — every `schema_update` registers there and the emitter consumes
IT (the byte-tie; `Emit.GenCtx.updates2`). The v1 registry and its
surface were DELETED (the migration) — only the v2 rows exist.

The `where` clause is REQUIRED: `VExpr .bool` has no literal-true node,
so there is no honest default — an unconditional update is written
`where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)` (the always-true idiom;
the demo's self-reading row pins it).

Gates at elaboration (the invariant lane's pattern):
- the record must be a registered `Item.record` (did-you-mean over the
  registered record names),
- the written column must be one of the record's fields — looked up BY
  NAME here, so a misspelled column is a did-you-mean error (not a bare
  `HasCol` instance failure),
- the value term elaborates against `VExpr <the record's real fields>
  <the FIELD's OWN TYPE>` — a u64 expression on a string column FAILS
  HERE (the type gate; the GADT index),
- the guard term elaborates against `VExpr <fields> .bool`,
- the write path is resolved by elaborating `VExpr.colOf <col>` and
  extracting its `.col` constructor path (data, the `ColPath` doctrine).
-/

/- The v2 update registry (W8.3; the v1→v2 migration — the ONE
   update registry): append-only, replayed from oleans at import (the
   `CodegenCore.mkRegistryExt` semantics — a SEPARATE extension
   because `Item` cannot carry the VExpr family). Every `schema_update`
   registers HERE — the emitter and the trace batches' source; the
   v1 registry was DELETED with the v1 surface. S5 (the meta-toolkit):
   the two declarations below are the EMITTED skeleton now
   (`declare_registry_member` — RegisterKit) — PLAIN rows (`plain!`: the
   `SomeUpdate2` IS the row; its own `name` field is the registry key,
   so the `Name × <kind>` pair would be redundant; the reader keeps
   replaying `List SomeUpdate2` exactly as before). The command
   elaborator below IS the write path (the toolkit emits no writer
   for form (i) — the consumer's command IS the write path). -/
declare_registry_member update2ItemExt registeredUpdates2 : SomeUpdate2 plain!

/-- Registered v2 update names (dup detection). -/
def registeredUpdate2Names (env : Environment) : List String :=
  (registeredUpdates2 env).map (fun u => u.update.name)

/-- The volatile schema-func names referenced by an elaborated term:
    the post-elaboration constant walk — collect the `.const` refs and
    match them against the registry's func bodies (a func item whose
    `FuncSig.body` names the const) with `sem.determinism == volatile`.
    THE FIRST PURE-CONTEXT CONSUMER: the armed `volatileInPureContext`
    diag fires on a hit (a `volatile` fn referenced from a value/guard
    VExpr would be fused/reordered by a pure consumer — only `pure`
    may fuse/reorder, so `volatile` and `stable` are the safe
    determinisms here and the diag enumerates them). -/
partial def volatileSchemaFns (env : Environment) (e : Expr) : List String :=
  go e []
where
  go : Expr → List String → List String
    | .const n _, acc =>
        match (schemaItemExt.getState env).find? (fun (ln, _it) => ln == n) with
        | some (_, .func sig) =>
            if sig.sem.determinism == .volatile then sig.name :: acc else acc
        | _ => acc
    | .app f a, acc => go a (go f acc)
    | .lam _ _ b _, acc => go b acc
    | .forallE _ _ b _, acc => go b acc
    | .letE _ t v b _, acc => go b (go v (go t acc))
    | .mdata _ b, acc => go b acc
    | .proj _ _ s, acc => go s acc
    | _, acc => acc

-- `schema_update <name> for <Record> <clause>,* where <guardTerm>` —
-- the `where` clause is REQUIRED (no literal-true in `VExpr .bool`;
-- see the section header). The `set` position is marked by `:=`
-- alone — NOT by a `set` token: declaring `" set "` in a syntax
-- RESERVES the word globally (the lexer makes it a keyword everywhere
-- — identifiers named `set` stop parsing; the WasmBackend do-block
-- casualty that taught this trap, the `prefix` lesson's class). Never
-- declare common words as syntax tokens. W8.3's insert/delete markers
-- are PUNCTUATION (`+` / `-`), same lesson.
--
-- v2 clauses (W8.3 — SchemaLang.Update2):
--   `<col> := <valueTerm>`  a SET clause (one or more — the
--                           simultaneous multi-write; every value
--                           reads the ORIGINAL row — the batch law)
--   `+ (e₁, …, eₙ)`         INSERT: a FULL row, one expression per
--                           field in field order, computed per guarded
--                           row (the INSERT-SELECT reading); the
--                           record's DECLARED key is required (W8.2)
--   `-`                     DELETE the guarded rows (keyed)

-- The clause syntax category parks in Lean's namespace BY DESIGN
-- because declare_syntax_cat cannot live in a library namespace (the
-- `vexpr` precedent). Syntax-category bodies are identical by
-- construction, hence the dupDefBodies opt-out too.
set_option linter.guestlang.packageNamespace false in -- because declare_syntax_cat parks the category in Lean's namespace by design
declare_syntax_cat updateClause

-- Syntax-category bodies are identical by construction (a category
-- carries no payload) — the dupDefBodies pair with `vexpr` is structural.
attribute [nolint linter.guestlang.dupDefBodies "syntax-category bodies are identical by construction (a category carries no payload)"]
  Lean.Parser.Category.updateClause

syntax ident " := " term : updateClause
syntax "+ " "(" term,* ")" : updateClause
syntax "-" : updateClause

syntax (name := schemaUpdate) "schema_update " ident " for " ident
  updateClause,* " where " term : command

/-- One SET clause as a typed quotation (the per-clause assembly —
    the `fieldToExpr` projection discipline: `path`/`e`'s indices are
    projections OF the `fQ` binder so the quotation elaborator keeps
    them shared). -/
def setClauseQ (fsList : Q(List Field)) (fQ : Q(Field))
    (path : Q(ColPath ($fQ).name ($fQ).ty $fsList))
    (e : Q(VExpr $fsList ($fQ).ty)) : Q(SetClause $fsList) :=
  q(SetClause.mk (fs := $fsList) $fQ $path $e)

/-- The empty clause list (the fold's seed). -/
def setClausesNilQ (fsList : Q(List Field)) : Q(List (SetClause $fsList)) :=
  q([])

/-- `cons` on the clause-list literal. -/
def setClausesConsQ (fsList : Q(List Field)) (cQ : Q(SetClause $fsList))
    (accQ : Q(List (SetClause $fsList))) : Q(List (SetClause $fsList)) :=
  q($cQ :: $accQ)

/-- The empty insert template. -/
def rowTmplNilQ (fsList : Q(List Field)) :
    Q(RowTmpl $fsList ([] : List Field)) :=
  q(RowTmpl.nil)

/-- `cons` on the insert-template literal (the index term's field list
    grows with the quotation — the `fieldsToExpr` discipline). -/
def rowTmplConsQ (fsList : Q(List Field)) (fQ : Q(Field))
    (gsQ : Q(List Field)) (e : Q(VExpr $fsList ($fQ).ty))
    (acc : Q(RowTmpl $fsList $gsQ)) : Q(RowTmpl $fsList ($fQ :: $gsQ)) :=
  q(RowTmpl.cons (f := $fQ) (gs := $gsQ) $e $acc)

/-- The registered v2 item as a typed quotation (the `Q(_)` casts are
    `implicit_reducible` defeq, sound by the gates — the
    `updatePureInstTyQ` precedent). -/
def update2ItemQ (fsList : Q(List Field)) (unameQ : Q(String))
    (recQ : Q(String)) (g : Q(VExpr $fsList Ty.bool))
    (setsQ : Q(List (SetClause $fsList))) (keyQ : Q(Option String))
    (insQ : Q(Option (RowTmpl $fsList $fsList))) (delQ : Q(Bool)) :
    Q(Update2Item $fsList) :=
  q(Update2Item.mk (fs := $fsList) $unameQ $recQ $g $setsQ $keyQ $insQ
    $delQ [])

/-- The `Update2Pure` instance TYPE for a registered v2 update. -/
def update2PureInstTyQ (fsList : Q(List Field)) (unameQ : Q(String))
    (recQ : Q(String)) (g : Q(VExpr $fsList Ty.bool))
    (setsQ : Q(List (SetClause $fsList))) (keyQ : Q(Option String))
    (insQ : Q(Option (RowTmpl $fsList $fsList))) (delQ : Q(Bool)) :
    Q(Prop) :=
  q(Update2Pure $fsList
    $(update2ItemQ fsList unameQ recQ g setsQ keyQ insQ delQ))

/-- The instance PROOF: `Update2Pure.emptyScan`'s `rfl` reduces on the
    literal `[]` scan result with the binders still abstract (the
    `updatePureInstPfQ` precedent — the named lemma is the
    Qq-compatible discharge). -/
def update2PureInstPfQ (fsList : Q(List Field)) (unameQ : Q(String))
    (recQ : Q(String)) (g : Q(VExpr $fsList Ty.bool))
    (setsQ : Q(List (SetClause $fsList))) (keyQ : Q(Option String))
    (insQ : Q(Option (RowTmpl $fsList $fsList))) (delQ : Q(Bool)) :
    Q(Update2Pure $fsList
      $(update2ItemQ fsList unameQ recQ g setsQ keyQ insQ delQ)) :=
  q(Update2Pure.emptyScan (fs := $fsList) (n := $unameQ) (rec := $recQ)
    (g := $g) (sets := $setsQ) (key? := $keyQ) (ins := $insQ)
    (del := $delQ))

open Lean Elab Command Term in
@[command_elab SchemaLang.Meta.schemaUpdate]
unsafe def elabSchemaUpdate : CommandElab := fun (stx : Syntax) => do
  let uname := stx[1]!.getId.toString
  let recId := stx[3]!.getId
  -- the v2 syntax layout: [4]=the clause list, [5]="where", [6]=guard
  let guardStx := stx[6]!
  let env ← getEnv
  -- partition the clauses: SET assignments / the insert row / the
  -- delete flag (the v1 surface is the singleton-SET case)
  let mut setStxs : Array (String × TSyntax `term) := #[]
  let mut insertTerms : Option (Array (TSyntax `term)) := none
  let mut deleteFlag := false
  for c in stx[4]!.getSepArgs do
    match (⟨c⟩ : TSyntax `updateClause) with
    | `(updateClause| $x:ident := $v:term) =>
        setStxs := setStxs.push (x.getId.toString, v)
    | `(updateClause| + ($es,*)) =>
        if insertTerms.isSome then
          throwError s!"schema_update `{uname}`: duplicate insert clause — one `+ (…)` per update"
        insertTerms := some es.getElems
    | `(updateClause| -) =>
        if deleteFlag then
          throwError s!"schema_update `{uname}`: duplicate delete clause"
        deleteFlag := true
    | _ => throwUnsupportedSyntax
  if setStxs.isEmpty && insertTerms.isNone && !deleteFlag then
    throwError s!"schema_update `{uname}`: no effect — an update needs at least one `<col> := <value>`, an insert `+ (…)`, or a delete `-`"
  -- the record: a registered `Item.record`, or a did-you-mean error
  -- (the invariant lane's pattern)
  let recordNames := (schemaItemExt.getState env).filterMap
    (fun (_, it) => match it with | .record n _ => some n | _ => none)
  let found? : Option (Name × Item) :=
    (schemaItemExt.getState env).find? (fun (ln, _) => ln == recId)
  let (recordName, fields) : String × List Field ←
    match found? with
    | some (_, .record n fields) => pure (n, fields)
    | _ =>
        let cands := CodegenCore.didYouMean recId.toString recordNames
        let hint := if cands.isEmpty then ""
          else s!" — did you mean: {String.intercalate ", " cands}?"
        throwError s!"schema_update `{uname}`: `{recId}` is not a registered record{hint}"
  -- the written FIELDs, looked up by NAME: a misspelled column is a
  -- did-you-mean error (louder than the bare `HasCol` instance miss),
  -- per SET clause
  let fieldNames := fields.map (·.name)
  let mut fVals : Array Field := #[]
  for (colId, _) in setStxs do
    match fields.find? (fun fl => fl.name == colId) with
    | some f => fVals := fVals.push f
    | none =>
        let cands := CodegenCore.didYouMean colId fieldNames
        let hint := if cands.isEmpty then ""
          else s!" — did you mean: {String.intercalate ", " cands}?"
        throwError s!"schema_update `{uname}`: `{colId}` is not a column of `{recordName}`{hint}"
  -- the SET columns are DISTINCT (the `applySets_perm` premise —
  -- clause-order freedom — is EARNED here, not re-checked downstream)
  let mut seen : Array String := #[]
  for (colId, _) in setStxs do
    if seen.contains colId then
      throwError s!"schema_update `{uname}`: duplicate set column `{colId}` — the multi-write's columns must be distinct (the clause order is unobservable under that premise)"
    seen := seen.push colId
  -- the dup-name gate (the ONE registry's names)
  if (registeredUpdate2Names env).contains uname then
    throwError s!"schema_update `{uname}`: duplicate update name"
  -- the DECLARED KEY (W8.2): insert/delete updates need it (the
  -- remove-delta's key image, the obligation view); a set-only update
  -- adopts the declared key when one is registered
  let key? : Option String ←
    if insertTerms.isSome || deleteFlag then
      match registeredKeyDecl? env recordName with
      | some kd => pure (some kd.key)
      | none =>
          throwError s!"schema_update `{uname}`: insert/delete updates need `{recordName}`'s DECLARED key (W8.2) — register it first (`schema_keys for {recId} := primary <field>`)"
    else
      pure ((registeredKeyDecl? env recordName).map (·.key))
  -- key immutability (a key change is a delete + insert — the
  -- event-sourcing reading; the lowering correspondence's premise is
  -- earned here)
  if let some key := key? then
    if (fVals.map (·.name)).contains key then
      throwError s!"schema_update `{uname}`: `{key}` is `{recordName}`'s declared key — the key column cannot be written (a key change is a delete + insert)"
  -- elaborate the guard + every clause's value against the REAL
  -- fields, evaluate the GADT values, resolve the write paths (the
  -- `VExpr.colOf` route per clause), evaluate the insert template —
  -- all data by the time it registers
  let (row2, inst2Name, inst2Ty, inst2Val) ← liftTermElabM do
    let fsList := fieldsToExpr fields
    let expectedFs : Q(Type) := q(List Field)
    let fsVal : List Field ← Meta.evalExpr (List Field) expectedFs fsList
    -- per SET clause: the value against `VExpr <fields> f.ty` (the
    -- FIELD's OWN TYPE is the type gate) and the write path
    let mut setVals : Array (SetClause fsVal) := #[]
    let mut valueExprs : Array Expr := #[]
    let mut pathExprs : Array Expr := #[]
    for i in [:setStxs.size] do
      let (colId, valueStx) := setStxs[i]!
      let fVal := fVals[i]!
      let expectedValue : Expr := vexprTyQ fsList (tyToExpr fVal.ty)
      let e ← elabTerm valueStx (some expectedValue)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      -- the TYPE GATE, stated loud: the value expression's `Ty` index
      -- must BE the written field's own type (a u64 expr on a string
      -- column fails HERE, with the two types named — the
      -- did-you-mean grade)
      let eT ← Meta.whnf (← Meta.inferType e)
      let tGot : Ty ←
        if eT.isAppOf ``SchemaLang.VExpr && eT.getAppNumArgs == 2 then
          Meta.evalExpr Ty (mkConst ``SchemaLang.Ty) eT.getAppArgs[1]!
        else
          throwError s!"schema_update `{uname}`: the value is not a `VExpr`"
      unless tGot == fVal.ty do
        throwError s!"schema_update `{uname}`: the value expression has type {repr tGot} — "
          ++ s!"the written column `{colId}` is {repr fVal.ty} — the value expression "
          ++ "must have the COLUMN'S OWN TYPE (the GADT gate)"
      if e.hasExprMVar then
        throwError s!"schema_update `{uname}`: unresolved metavariables in the value"
      let valueVal : VExpr fsVal fVal.ty ← Meta.evalExpr (VExpr fsVal fVal.ty) expectedValue e
      -- the write path: elaborate `VExpr.colOf <col>`, extract the
      -- `.col` constructor path (data — the `ColPath` doctrine)
      let colLit : Term ← Lean.Elab.Term.exprToSyntax (mkStrLit colId)
      let colStx ← `(SchemaLang.VExpr.colOf $colLit)
      let pe ← elabTerm colStx (some expectedValue)
      Term.synthesizeSyntheticMVarsNoPostponing
      let pe ← instantiateMVars pe
      if pe.hasExprMVar then
        throwError s!"schema_update `{uname}`: column `{colId}` is not on `{recordName}`"
      let peCtor ← Meta.whnf pe
      unless peCtor.getAppFn.isConstOf ``SchemaLang.VExpr.col do
        throwError s!"schema_update `{uname}`: internal: `colOf` did not reduce to the .col ctor"
      let pathE := peCtor.getAppArgs[peCtor.getAppArgs.size - 1]!
      let pathTyE : Expr := colPathTyQ fsList (toExpr fVal.name) (tyToExpr fVal.ty)
      let pathVal : ColPath fVal.name fVal.ty fsVal ←
        Meta.evalExpr (ColPath fVal.name fVal.ty fsVal) pathTyE pathE
      setVals := setVals.push { field := fVal, path := pathVal, value := valueVal }
      valueExprs := valueExprs.push e
      pathExprs := pathExprs.push pathE
    -- the guard: against `VExpr <fields> .bool`
    let expectedGuard : Expr := vexprBoolTyQ fsList
    let g ← elabTerm guardStx (some expectedGuard)
    Term.synthesizeSyntheticMVarsNoPostponing
    let g ← instantiateMVars g
    if g.hasExprMVar then
      throwError s!"schema_update `{uname}`: unresolved metavariables in the guard"
    let guardVal : VExpr fsVal .bool ← Meta.evalExpr (VExpr fsVal .bool) expectedGuard g
    -- the insert row (W8.3): a FULL row, one expression per field in
    -- field order, each against the FIELD'S OWN TYPE (the GADT gate,
    -- per position)
    let mut insertExprs : Array Expr := #[]
    if let some es := insertTerms then
      unless es.size == fields.length do
        throwError s!"schema_update `{uname}`: the insert row has {es.size} fields — `{recordName}` has {fields.length} (a FULL row, in field order)"
      for i in [:fields.length] do
        let f := fields[i]!
        let expectedI : Expr := vexprTyQ fsList (tyToExpr f.ty)
        let e ← elabTerm es[i]! (some expectedI)
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let eT ← Meta.whnf (← Meta.inferType e)
        let tGot : Ty ←
          if eT.isAppOf ``SchemaLang.VExpr && eT.getAppNumArgs == 2 then
            Meta.evalExpr Ty (mkConst ``SchemaLang.Ty) eT.getAppArgs[1]!
          else
            throwError s!"schema_update `{uname}`: the insert row's field `{f.name}` is not a `VExpr`"
        unless tGot == f.ty do
          throwError s!"schema_update `{uname}`: the insert row's field `{f.name}` has type {repr tGot} — the field is {repr f.ty} — each insert expression must have the FIELD'S OWN TYPE (the GADT gate)"
        if e.hasExprMVar then
          throwError s!"schema_update `{uname}`: unresolved metavariables in the insert row"
        insertExprs := insertExprs.push e
    -- the DETERMINISM GATE (the armed `volatileInPureContext` diag's
    -- firing site): the value, insert, and guard terms may reference
    -- REGISTERED schema functions; a volatile one in this pure-context
    -- lane fails elaboration, naming the fn and the update. The scan
    -- is the post-elaboration constant walk of EVERY term
    -- (`volatileSchemaFns`).
    let volatileHits :=
      ((valueExprs.toList ++ insertExprs.toList).flatMap (volatileSchemaFns env)
        ++ volatileSchemaFns env g).eraseDups
    unless volatileHits.isEmpty do
      throwError s!"schema_update `{uname}`: " ++
        String.intercalate "; " (volatileHits.map fun fn =>
          SchemaDiag.render (.volatileInPureContext fn s!"schema_update {uname}"))
    -- the insert template: assemble the GADT literal (typed
    -- quotations), evaluate the value
    let (insQ, insertVal?) ←
      match insertTerms with
      | none =>
          pure ((q(Option.none) : Q(Option (RowTmpl $fsList $fsList))), none)
      | some _ => do
          let rec buildTmpl : (gs : List Field) → List Expr → TermElabM Expr
            | [], [] => pure (rowTmplNilQ fsList)
            | gf :: gs', e :: es' => do
                let acc ← buildTmpl gs' es'
                pure (rowTmplConsQ fsList (fieldToExpr gf) (fieldsToExpr gs') e acc)
            | _, _ => throwError s!"schema_update `{uname}`: internal: insert arity"
          let tmplE : Q(RowTmpl $fsList $fsList) := ← buildTmpl fields insertExprs.toList
          let tmplVal ← Meta.evalExpr (RowTmpl fsVal fsVal)
            (mkAppN (mkConst ``SchemaLang.RowTmpl) #[fsList, fsList]) tmplE
          pure ((q(Option.some $tmplE) : Q(Option (RowTmpl $fsList $fsList))),
            some tmplVal)
    -- assemble the v2 item (the scan's decided fact rides
    -- `volatileRefs` — the `UpdatePure` proof discipline)
    let item2 : Update2Item fsVal :=
      { name := uname, record := recordName, guard := guardVal
      , sets := setVals.toList, key? := key?, insert? := insertVal?
      , delete := deleteFlag, volatileRefs := volatileHits }
    let setsQ : Q(List (SetClause $fsList)) :=
      (List.range setStxs.size).foldr (fun i accQ =>
        setClausesConsQ fsList
          (setClauseQ fsList (fieldToExpr fVals[i]!) pathExprs[i]! valueExprs[i]!)
          accQ) (setClausesNilQ fsList)
    let keyQ : Q(Option String) := toExpr key?
    let delQ : Q(Bool) := toExpr deleteFlag
    let inst2Ty : Expr :=
      update2PureInstTyQ fsList (toExpr uname) (toExpr recordName) g setsQ keyQ insQ delQ
    let inst2Pf : Expr :=
      update2PureInstPfQ fsList (toExpr uname) (toExpr recordName) g setsQ keyQ insQ delQ
    -- THE COMPOSABLE LOCK (the second layer — the scan above stays
    -- the first): the scan's decided fact is discharged as a PROOF.
    -- The command EMITS the `Update2Pure` instance; its proof is `rfl`
    -- against the STORED `volatileRefs` data — if the gate ever stored
    -- a nonempty scan, this `rfl` FAILS to elaborate (the proof checks
    -- the gate). The instance assembly is fully typed (Qq): the
    -- elaborated terms are passed to the typed-quotation helpers with
    -- their CHECKED types (the `VExpr`/`ColPath` gates above) — the
    -- `Q(_)` casts are `implicit_reducible` defeq, sound by the gates.
    pure ({ fields := fsVal, update := item2 : SomeUpdate2 },
      ((`SchemaLang).str "instUpdate2Pure").str uname, inst2Ty, inst2Pf)
  modifyEnv fun env =>
    update2ItemExt.addEntry env row2
  -- the instance: a def with the instance attribute (4.33's `Declaration`
  -- has no `instanceDecl` constructor — the `instance` command's own
  -- route is defn + addInstance)
  -- KNOWN FALSE POSITIVE: `warn.classDefReducibility` flags these
  -- (`instUpdate2Pure.*` — Demo/Tests) as
  -- "semireducible" EVEN THOUGH the hints ARE `.abbrev` — the linter
  -- reads only attribute-site declarations, not the addDecl route.
  -- Accepted (documented), NOT silenced: `set_option ... false` would
  -- trip the noLinterDisable lint, and the instances resolve fine (the
  -- consumers prove it).
  liftTermElabM do
    Lean.addDecl (Declaration.defnDecl {
      name := inst2Name, levelParams := [], type := inst2Ty
      , value := inst2Val, hints := Lean.ReducibilityHints.abbrev
      , safety := Lean.DefinitionSafety.safe })
    Lean.Meta.addInstance inst2Name .global 1000


end SchemaLang.Meta

end -- public meta section
