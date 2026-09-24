/-
# Kit.Lane — the lane substrate (the env extension + the attribute mount, as ONE kit call)

`register_lane <Item> where naming := <fn>` mechanizes the lane
recipe's steps 1–2 (notes/v3/12-construction.md §2) into a single
command. It generates, per lane (the name convention: the lane's base
name — the `attr` clause override, default the item type's last
component decapitalized — derives every generated name):

- `<base>Ext` — the `SimplePersistentEnvExtension <Item> (List <Item>)`:
  the compile-time event log (15-patterns #7), append-only
  (`addEntryFn` appends; replay order = registration order),
  `addImportedFn` concatenates the imported arrays (the trap-list
  discipline: it takes `Array (Array α)`).
- `@[<base>]` — the attribute mount: on a `def` whose type is the item
  type, the entry is the def's VALUE (evaluated at elaboration —
  `@[demoLaneItem] def x : DemoLaneItem := …` appends). An `attr :=`
  clause renames the attribute; a `builder :=` clause swaps the
def-value route for a custom builder `Environment → Name → Except
String Item` (the structure-reflection shape; its refusals carry the
builder's own curation, wrapped with the `@[attr] decl:` prefix).
- `get<base>s` — the replay accessor: `Environment → List <Item>`.
- `<base>Registry` — the fold hook: the replay materialized into a
  `Kit.DataRegistry` (the registry = the integral of the event log);
  a duplicate name is the loud `.error` (decided, never assumed).
- `<base>NameOf` — the naming function (the registry's lookup key).
- `<base>ObligationView` — THE OBLIGATION-VIEW hook: the obligation
  labels the lane attests (one per registered item, in registration
  order) — the entourage's attests face, auto-filled at registration.
- `<base>LedgerDemand` — THE LEDGER-ROWS hook: the lane's DEMAND SET
  (Kit.Ledger.DemandSet) — the lane's registration records the
  collections it reads (its OWN extension, whose growth invalidates
  every replay), the rows it folds (the registered items as names),
  and its emitter revision. The honest minimal of the demand-set
correction (Kit.Ledger): a lane's replays depend on the collection
  AS-A-SET, so the registration declares the dependency at the mount,
  never by memory.
- `<base>AttrReg` — the attribute's `initialize` binding.

The clause keywords (`naming`, `attr`, `builder`) become parser
keywords globally — the reserved-token cost of the surface, the same
class as `machine!`'s clause words (do not spell a structure field
`naming`/`attr`/`builder` with `:=`).

The generated `initialize`s must run at import (the trap-list rule:
attr-registering initializers ride the initializer chain — plain-file
`initialize`, exactly the SchemaCore.Register shape). A module's own
initializers do not run during ITS OWN elaboration, so the
registration and the consumption are different modules (the fixture:
KitTests.LaneReg → KitTests.LaneDemo). The default builder's misuse
failures are Diag-flavored (Kit.Diag): the E-code + the valid usage.
The duplicate-name refusal is the closed-world Diag (`closedWorld` —
got + the taken names + the ONE engine's suggestion).

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/Registry.lean` (`mkRegistryExt` —
the extension factory + the boring-on-purpose semantics) and
`legacy/lean/schema-lang/SchemaLang/Meta/Register/Schema.lean` (the
attribute mount's checks). The Pattern-port, not the file: the generic
machinery lives ONCE here; the macro emits thin instantiations.

Core-only (no mathlib/Batteries). META module: elab machinery — the
generated initializers run at import in the consumer's process (the
slice's driver replay proves the discipline).

Five questions (notes/v3/01-core.md):
- root: META — the lane recipe's steps 1–2 mechanized (the substrate
  every lane mounts).
- carrier grade: host-side elaboration surface over first-order item
  data (the ext state replays into plain lists).
- spine reading: registration = append → replay = the accessor →
  fold = the DataRegistry materialization.
- ladder rung: rung 1 (the discipline lives in the shapes: append-only
  ext, decided nodup, closed-world refusals).
- gate row: KitTests (the demo lane end-to-end + the curated-failure
  negative controls) + the slice migration's driver replay
  (`lake exe schema` / `gates gen-check`).
-/

import Lean
import Kit.Diag
import Kit.Ledger
import Kit.Registry

namespace Kit.Lane

/-! ## The extension semantics (pure, boring on purpose) -/

/-- Merge imported environments' registries: keep order, concatenate
    (the `addImportedFn` semantics — it takes `Array (Array α)`, the
    trap-list discipline; extracted so tests exercise it purely). -/
def mergeImported {α : Type} : Array (Array α) → List α :=
  fun ess => ess.foldl (fun acc arr => acc ++ arr.toList) []

/-- The lane extension factory: one `SimplePersistentEnvExtension` per
    lane — append on add (registration order), concatenate on import.
    Call from the generated `initialize`:

    ```
    initialize myItemExt : SimplePersistentEnvExtension MyItem (List MyItem) ←
      Kit.Lane.mkLaneExt `My.myItemExt
    ```
-/
def mkLaneExt {α : Type} [Inhabited α] (name : Lean.Name) :
    IO (Lean.SimplePersistentEnvExtension α (List α)) :=
  Lean.registerSimplePersistentEnvExtension {
    name := name
    addEntryFn := fun xs x => xs ++ [x]
    addImportedFn := mergeImported
  }

/-- The fold hook's face: the replayed items materialized into a
    `Kit.DataRegistry` — the nodup fact DECIDED (not assumed); a
    duplicate name is the loud `.error` (the closed-world rejection;
    there is no silent acceptance path). -/
def materialize {α : Type} (nameOf : α → String) (items : List α) :
    Except String (Kit.DataRegistry α) :=
  if h : (items.map nameOf).Nodup then
    .ok { items := items, nameOf := nameOf, nodup := h }
  else
    .error s!"duplicate names: {items.map nameOf} — \
      every registered item needs a unique name"

/-! ## The curated failures (Kit.Diag) -/

/-- The KL family — the lane substrate's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    DECLARATION — the sites below use them, never a bare string, and
    the code-registry gate's coverage scan ties every spelling to its
    allocated live row (a hand-strung code is a gate refusal). -/
def eKL0001 : Kit.ECode := ⟨"KL0001"⟩
def eKL0002 : Kit.ECode := ⟨"KL0002"⟩
def eKL0003 : Kit.ECode := ⟨"KL0003"⟩
def eKL0004 : Kit.ECode := ⟨"KL0004"⟩
def eKL0005 : Kit.ECode := ⟨"KL0005"⟩
def eKL0006 : Kit.ECode := ⟨"KL0006"⟩

/-- The literal Diag for a positional misuse (no got/valid slot — the
    message names the context, the construct, the valid usage). The
    code slot is an `ECode` of the registry's allocated family — a
    bare string cannot reach the envelope. -/
def usageDiag (code : Kit.ECode) (message : String) : Kit.Diag :=
  { code := code, message := message, severity := .error }

/-- The duplicate-registration Diag: the closed-world constructor —
    got + the taken names + the ONE engine's suggestion, unforgable. -/
def dupDiag (attrStr declName : String) (got : String) (taken : List String) :
    Kit.Diag :=
  Kit.Diag.closedWorld eKL0001
    s!"@[{attrStr}] {declName}: `{got}` is already a registered item — \
      names must be fresh"
    .error got taken

/-! ## The default builder — a `def` of the lane's item type -/

/-- The default lane builder: the entry is a `def` whose type is the
    lane's item type; the VALUE is the item, evaluated at elaboration
    (the interpreter route — `unsafe` because `evalExpr'` is). The
    misuse failures are Diag-rendered (E-code + valid usage). -/
unsafe def evalLaneItem {Item : Type} [Inhabited Item] (itemTy : Lean.Name)
    (attrStr : String) (env : Lean.Environment) (declName : Lean.Name) :
    Lean.Meta.MetaM (Except String Item) := do
  match env.find? declName with
  | none =>
    return .error (usageDiag eKL0002
      s!"@[{attrStr}] {declName}: no such declaration — the entry must be \
        a `def` in this module whose type is `{itemTy}`").toString
  | some (.defnInfo dv) =>
    unless dv.type.isConstOf itemTy do
      return .error (usageDiag eKL0003
        s!"@[{attrStr}] {declName}: the entry's type is not the lane's item \
          type `{itemTy}` — valid usage: \
          `@[{attrStr}] def {declName} : {itemTy} := <value>`").toString
    try
      return .ok (← Lean.Meta.evalExpr' Item itemTy dv.value)
    catch e =>
      let _ := e
      return .error (usageDiag eKL0004
        s!"@[{attrStr}] {declName}: the entry's value could not be evaluated \
          — the item must be a closed literal value").toString
  | some _ =>
    return .error (usageDiag eKL0005
      s!"@[{attrStr}] {declName}: not a `def` — the lane entry must be a \
        `def` whose type is `{itemTy}`").toString

/-! ## The attribute installer -/

/-- The custom-builder wrapper: the builder's own curated refusal,
    prefixed with the mount (the legacy `@[attr] decl:` error shape).
    The `builder :=` clause's generated face — the wrapper lives HERE
    (not in the generated quotation) so the prefix string is spliced,
    never interpolated inside a quotation (the macro-scope trap). -/
def wrapBuilder {Item : Type}
    (attrStr : String)
    (b : Lean.Environment → Lean.Name → Except String Item)
    (env : Lean.Environment) (declName : Lean.Name) :
    Lean.Meta.MetaM (Except String Item) :=
  pure (match b env declName with
    | .error msg => .error s!"@[{attrStr}] {declName}: {msg}"
    | .ok item => .ok item)

/-- Install the lane's attribute mount: global use only, no args, never
    on imported decls; the builder produces the item, the fresh-name
    gate refuses duplicates (the closed-world Diag), the entry appends.
    `unsafe`: the default builder evaluates values (`evalExpr'`). -/
unsafe def installLaneAttr {Item : Type} [Inhabited Item]
    (attrName : Lean.Name) (ref : Lean.Name)
    (ext : Lean.SimplePersistentEnvExtension Item (List Item))
    (nameOf : Item → String)
    (build : Lean.Environment → Lean.Name → Lean.Meta.MetaM (Except String Item))
    (what : String := "item") : IO Unit :=
  Lean.registerBuiltinAttribute {
    name := attrName
    descr := s!"register a {what} in the `@[{attrName}]` lane's event log \
      (append-only; replay = the materialization)"
    ref := ref
    applicationTime := .afterTypeChecking
    add := fun declName stx kind => do
      Lean.Attribute.Builtin.ensureNoArgs stx
      unless kind == .global do
        Lean.throwError "invalid attribute use, must be global"
      let env ← Lean.getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        Lean.throwError m!"@[{attrName}] cannot be applied to decls in \
          imported modules"
      match ← Lean.Meta.MetaM.run' (build env declName) with
      | .error msg => Lean.throwError m!"{msg}"
      | .ok item =>
        let taken := (ext.getState (← Lean.getEnv)).map nameOf
        if taken.contains (nameOf item) then
          Lean.throwError
            m!"{dupDiag attrName.toString declName.toString (nameOf item) taken}"
        Lean.modifyEnv fun env => ext.addEntry env item
  }

/-- Parse a dotted name string into a `Name` — the generated code
    passes full names as string literals (no name-literal
    antiquotation; the components are machine-generated, so the
    unescaping question never arises). -/
def nameOfStr (s : String) : Lean.Name :=
  match s.splitOn "." with
  | [] => .anonymous
  | c :: rest =>
      rest.foldl (fun n p => Lean.Name.str n p) (Lean.Name.mkSimple c)

/-! ## The command — `register_lane <Item> where …` -/

/-- One `where` clause of `register_lane` (the category + one parser
    per clause shape — quotation matching needs the shapes
    distinguishable). -/
declare_syntax_cat laneClause
syntax "naming" " := " term : laneClause
syntax "attr" " := " ident : laneClause
syntax "builder" " := " term : laneClause

/-- THE lane substrate command: mechanizes the lane recipe's steps 1–2
    (12-construction §2) — the env extension + the attribute mount —
    into one kit call. See the module header for the generated pieces
    and the name convention. -/
syntax (name := registerLaneCmd) "register_lane " ident " where"
  (ppSpace colGt laneClause)* : command

@[command_elab Kit.Lane.registerLaneCmd]
def elabRegisterLane : Lean.Elab.Command.CommandElab
  | `(command| register_lane $item:ident where $[$clauses:laneClause]*) => do
    let mut naming? : Option Lean.Term := none
    let mut attr? : Option Lean.Name := none
    let mut builder? : Option Lean.Term := none
    for c in clauses do
      match c with
      | `(laneClause| naming := $t:term) => naming? := some t
      | `(laneClause| attr := $i:ident) =>
          attr? := some i.getId.eraseMacroScopes
      | `(laneClause| builder := $t:term) => builder? := some t
      | _ => Lean.throwError "invalid lane clause"
    let some namingT := naming? |
      let d := usageDiag eKL0006
        "register_lane: the `where naming := <fn>` clause is required — \
          naming is the item's naming function (the registry's lookup key); \
          valid usage: `register_lane <Item> where naming := <fn>` with the \
          optional clauses `attr := <name>` (the attribute's name) and \
          `builder := <fn>` (a custom builder \
          `Environment → Name → Except String Item`)"
      Lean.throwError m!"{d}"
    let itemTyName := item.getId.eraseMacroScopes
    let itemLast := (itemTyName.toString.splitOn ".").getLast!
    let baseStr := match attr? with
      | some a => a.toString
      | none => itemLast.decapitalize
    let ns := (← Lean.Elab.Command.getScope).currNamespace
    let extStr := s!"{baseStr}Ext"
    let extId := Lean.mkIdent (Lean.Name.mkSimple extStr)
    let accId := Lean.mkIdent (Lean.Name.mkSimple s!"get{baseStr.capitalize}s")
    let nameOfId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}NameOf")
    let regId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}Registry")
    let oblId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}ObligationView")
    let demId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}LedgerDemand")
    let attrRegId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}AttrReg")
    let extFullNameStr := (ns ++ Lean.Name.mkSimple extStr).toString
    let attrRefStr := (ns ++ Lean.Name.mkSimple s!"{baseStr}Attr").toString
    let itemTyFullNameStr := (ns ++ itemTyName).toString
    let itemT : Lean.Term := ⟨item.raw⟩
    -- The template references: PRERESOLVED idents (mkIdent) — plain
    -- quoted idents carry macro scopes and silently fail on dotted
    -- names (06 §7).
    let kitMk : Lean.Term := Lean.mkIdent `Kit.Lane.mkLaneExt
    let kitNameOfStr : Lean.Term := Lean.mkIdent `Kit.Lane.nameOfStr
    let kitMat : Lean.Term := Lean.mkIdent `Kit.Lane.materialize
    let kitReg : Lean.Term := Lean.mkIdent `Kit.DataRegistry
    let kitDemandSet : Lean.Term := Lean.mkIdent `Kit.Ledger.DemandSet
    let kitNamesOf : Lean.Term := Lean.mkIdent `Kit.Ledger.namesOf
    let kitInstall : Lean.Term := Lean.mkIdent `Kit.Lane.installLaneAttr
    let kitEval : Lean.Term := Lean.mkIdent `Kit.Lane.evalLaneItem
    let kitWrap : Lean.Term := Lean.mkIdent `Kit.Lane.wrapBuilder
    let buildFn : Lean.Term ← match builder? with
      | some b =>
        `(($kitWrap $(Lean.quote baseStr) $b))
      | none =>
        `((($kitEval (Item := $itemT))
            ($kitNameOfStr $(Lean.quote itemTyFullNameStr)) $(Lean.quote baseStr)))
    Lean.Elab.Command.elabCommand (← `(command|
      initialize $extId : Lean.SimplePersistentEnvExtension $itemT (List $itemT) ←
        ($kitMk ($kitNameOfStr $(Lean.quote extFullNameStr)))))
    Lean.Elab.Command.elabCommand (← `(command|
      def $accId (env : Lean.Environment) : List $itemT :=
        ($extId).getState env))
    Lean.Elab.Command.elabCommand (← `(command|
      def $nameOfId : $itemT → String := $namingT))
    Lean.Elab.Command.elabCommand (← `(command|
      def $regId (env : Lean.Environment) :
          Except String ($kitReg $itemT) :=
        ($kitMat $nameOfId ($accId env))))
    -- THE ENTOURAGE HOOKS (16-surface §3's discipline, at the lane
    -- face): the obligation view (the attests labels, one per item) +
    -- the ledger demand (the lane records the collections it READS —
    -- its own extension, whose growth invalidates every replay — plus
    -- the rows it folds and its emitter revision). Auto-filled at the
    -- mount; there is no lane-side tier to hand-set.
    Lean.Elab.Command.elabCommand (← `(command|
      def $oblId (env : Lean.Environment) : List String :=
        ($accId env).map $nameOfId))
    Lean.Elab.Command.elabCommand (← `(command|
      def $demId (env : Lean.Environment) : $kitDemandSet :=
        { rows := ($accId env).map (fun it => $kitNamesOf ($nameOfId it))
          collections := [$kitNamesOf $(Lean.quote extFullNameStr)]
          emitterRev := "register_lane" }))
    Lean.Elab.Command.elabCommand (← `(command|
      unsafe initialize $attrRegId : Unit ←
        (($kitInstall (Item := $itemT))
          ($kitNameOfStr $(Lean.quote baseStr))
          ($kitNameOfStr $(Lean.quote attrRefStr))
          $extId $nameOfId $buildFn)))
  | _ => Lean.Elab.throwUnsupportedSyntax

end Kit.Lane
