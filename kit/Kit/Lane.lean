/-
# Kit.Lane — the lane substrate (the ONE compile-time event log + the attribute mount, as ONE kit call)

`register_lane <Item> where naming := <fn>` mechanizes the lane
recipe's steps 1–2 (notes/v3/12-construction.md §2) into a single
command. THE ONE-LOG REGISTRY DISCIPLINE (wave-30 A2; 15-patterns #7;
10 Phase 5): there is ONE compile-time event log — `laneLogExt` — and
EVERY lane's registration appends to it. The lane's identity is DATA:
the row carries the lane's id (the item type's full name, derived at
the mount), and the per-lane replay is the log's fold FILTERED to the
lane. A new lane lands as ONE row (the `register_lane` call) + ONE
reader (the derived accessor) — no substrate change.

Per lane (the name convention: the lane's base name — the `attr`
clause override, default the item type's last component decapitalized
— derives every generated name):

- `<base>LaneId` — the lane's identity, as data (the item type's full
  name at the mount; the replay's routing key).
- `@[<base>]` — the attribute mount: on a `def` whose type is the item
  type, the entry is the def's VALUE (evaluated at elaboration —
  `@[demoLaneItem] def x : DemoLaneItem := …` appends). An `attr :=`
  clause renames the attribute; a `builder :=` clause swaps the
  def-value route for a custom builder `Environment → Name → Except
  String Item` (the structure-reflection shape; its refusals carry the
  builder's own curation, wrapped with the `@[attr] decl:` prefix).
- `get<base>s` — THE READER: the per-lane replay — the shared log's
  fold filtered to the lane, each row's item re-materialized by the
  lane's own builder route (the default route re-evaluates the def's
  value; a custom builder re-runs — it is env-based). `CoreM` face:
  the pins run in `#eval show Lean.CoreM`; the IO shells run it
  through `Kit.Lane.runCoreIO`.
- `<base>Registry` — the fold hook: the reader's items materialized
  into a `Kit.DataRegistry` (the registry = the integral of the
  event log); a duplicate name is the loud `.error` (decided, never
  assumed).
- `<base>NameOf` — the naming function (the registry's lookup key).
- `<base>ObligationView` — THE OBLIGATION-VIEW hook: the obligation
  labels the lane attests (the routed rows' names, in registration
  order) — the entourage's attests face, auto-filled at registration.
- `<base>LedgerDemand` — THE LEDGER-ROWS hook: the lane's DEMAND SET
  (Kit.Ledger.DemandSet) — the lane's registration records the rows it
  folds (the routed rows' names) and its emitter revision; the
  collection it reads is THE ONE LOG (`Kit.Lane.laneLogName`) — a
  lane's replays depend on the log AS-A-SET (any lane's growth
  invalidates every replay; the conservative face is the honest
  minimal). The registration declares the dependency at the mount,
  never by memory.
- `<base>AttrReg` — the attribute's `initialize` binding.

The ONE log (15-patterns #7 at the substrate level): `laneLogExt` —
append-only (`addEntryFn` appends; replay order = registration
order), `addImportedFn` concatenates the imported arrays (the
trap-list discipline: it takes `Array (Array α)`). The ROWS are
first-order data (lane id + name + the defining decl's name) — the
log is the byte-tie-able face; the VALUES are materialized by the
readers (the replay = the materialization).

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

Core-only (no mathlib/Batteries). META module: elab machinery —
the generated initializers run at import in the consumer's process.

Five questions (notes/v3/01-core.md):
- root: META — the lane recipe's steps 1–2 mechanized (the substrate
  every lane mounts); the ONE compile-time event log.
- carrier grade: host-side elaboration surface over first-order row
  data (the log replays into a plain list; the readers re-materialize
  the values).
- spine reading: registration = append (to the ONE log) → the
  per-lane replay = the log's fold filtered to the lane → the fold =
  the DataRegistry materialization.
- ladder rung: rung 1 (the discipline lives in the shapes: append-only
  log, decided nodup, closed-world refusals, the routing as data).
- gate row: KitTests (the demo lanes end-to-end + the curated-failure
  negative controls) + the slice migration's driver replay
  (`lake exe schema` / `gates gen-check`) + the snapshot's lane-row
  coverage (SchemaCore.Snapshot).
-/

import Lean
import Kit.Diag
import Kit.Ledger
import Kit.Registry
import Kit.Derive.Common

namespace Kit.Lane

/-! ## The ONE log (the extension semantics: pure, boring on purpose) -/

/-- The lane's identity, as data: the item type's full name at the
    mount. The closed-world discipline: the log routes BY this id —
    each row belongs to exactly the lane its mount declared, and the
    per-lane reader answers only its own id's rows. -/
abbrev LaneId : Type := String

/-- One row of the ONE compile-time event log: the lane's id (the
    routing key), the item's registered name (the naming function's
    verdict, computed at the mount), and the defining declaration
    (the value's home — the reader re-materializes it). First-order
    data: the log marshals across imports exactly as the values did. -/
structure LaneRow where
  /-- The lane the row belongs to (the mount's identity). -/
  lane : LaneId
  /-- The item's registered name (the registry's lookup key). -/
  name : String
  /-- The defining declaration (the reader's re-materialization face). -/
  decl : Lean.Name
  deriving Inhabited, Repr, BEq

/-- Merge imported environments' log shards: keep order, concatenate
    (the `addImportedFn` semantics — it takes `Array (Array α)`, the
    trap-list discipline; extracted so tests exercise it purely). -/
def mergeImported {α : Type} : Array (Array α) → List α :=
  fun ess => ess.foldl (fun acc arr => acc ++ arr.toList) []

/-- The lane extension factory — called ONCE, for the ONE log:
    append on add (registration order), concatenate on import. -/
def mkLaneExt {α : Type} [Inhabited α] (name : Lean.Name) :
    IO (Lean.SimplePersistentEnvExtension α (List α)) :=
  Lean.registerSimplePersistentEnvExtension {
    name := name
    addEntryFn := fun xs x => xs ++ [x]
    addImportedFn := mergeImported
  }

/-- THE one compile-time event log (15-patterns #7): every lane's
    registration appends HERE. Initialized at Kit.Lane's import —
    before any consumer module's mount can run. (The registration is
    INLINED — an `initialize` that routes through the factory constant
    makes the interpreter's import-time evaluation chase a
    reducer-auxiliary decl the olean does not carry.) -/
initialize laneLogExt : Lean.SimplePersistentEnvExtension LaneRow (List LaneRow) ←
  mkLaneExt `Kit.Lane.laneLogExt

/-- The ONE log's registered name (the ledger demand's collection
    face: every lane reads the log AS A SET). -/
def laneLogName : String := "Kit.Lane.laneLogExt"

/-- The whole log (the registration order, import-shards concatenated). -/
def laneLog (env : Lean.Environment) : List LaneRow :=
  laneLogExt.getState env

/-- THE PER-LANE REPLAY: the log's fold filtered to the lane. This IS
    the routing — a row belongs to exactly one lane, and the lane's
    reader answers its own id's rows in registration order. -/
def laneRows (env : Lean.Environment) (lane : LaneId) : List LaneRow :=
  (laneLog env).filter (fun r => r.lane == lane)

/-- The registered lane family: the log's lane ids, first-seen order
    (the closed-world data — the snapshot's lane face covers it). -/
def laneFamilies (env : Lean.Environment) : List LaneId :=
  (laneLog env).foldl
    (fun acc r => if acc.contains r.lane then acc else acc ++ [r.lane]) []

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

/-! ## The values' re-materialization (the readers' evaluation face) -/

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

/-- The DEFAULT route's replay builder: the row's decl is a `def` of
    the item type; the reader re-evaluates its value. -/
unsafe def evalReplayBuilder {Item : Type} [Inhabited Item]
    (itemTy : Lean.Name) (attrStr : String) :
    Lean.Environment → Lean.Name → Lean.CoreM (Except String Item) :=
  fun env decl => (evalLaneItem (Item := Item) itemTy attrStr env decl).run'

/-- THE READER'S CORE: the per-lane replay's value face — the routed
    rows' items re-materialized by the lane's own builder (the default
    route re-evaluates the def's value; a custom builder re-runs — it
    is env-based, so replay = registration byte-for-byte). -/
unsafe def replayLane {Item : Type} [Inhabited Item]
    (rows : List LaneRow)
    (build : Lean.Environment → Lean.Name → Lean.CoreM (Except String Item))
    (env : Lean.Environment) : Lean.CoreM (Except String (List Item)) := do
  let mut out : Except String (List Item) := .ok []
  for r in rows do
    match out with
    | .error e => out := .error e
    | .ok xs =>
        match ← build env r.decl with
        | .error e => out := .error e
        | .ok v => out := .ok (xs ++ [v])
  pure out

/-- The IO shell over a `CoreM` face (the gates'/regen writers' route:
    `loadPkgEnv`'s process shape — the replay runs the reader in a
    fresh Core context over the loaded env). -/
unsafe def runCoreIO (env : Lean.Environment) (act : Lean.CoreM (Except String α)) :
    IO (Except String α) := do
  let coreCtx : Lean.Core.Context :=
    { fileName := "<lane-replay>", fileMap := Lean.FileMap.ofString "" }
  match ← act.run coreCtx { env := env } |>.toBaseIO with
  | .ok (a, _) => pure a
  | .error e => pure (.error (← e.toMessageData.toString))

/-! ## The fold hook's face -/

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

/-- The fold hook's combinator: the replay's result materialized (the
    reader's `Except` mapped into the registry's decided nodup). -/
def registryOf {α : Type} (nameOf : α → String)
    (r : Except String (List α)) : Except String (Kit.DataRegistry α) :=
  r >>= materialize nameOf

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
    gate refuses duplicates (the closed-world Diag), the ROW appends to
    the ONE log. `unsafe`: the default builder evaluates values
    (`evalExpr'`). -/
unsafe def installLaneAttr {Item : Type} [Inhabited Item]
    (attrName : Lean.Name) (ref : Lean.Name)
    (laneId : LaneId)
    (nameOf : Item → String)
    (build : Lean.Environment → Lean.Name → Lean.Meta.MetaM (Except String Item))
    (what : String := "item") : IO Unit :=
  Lean.registerBuiltinAttribute {
    name := attrName
    descr := s!"register a {what} in the `@[{attrName}]` lane's rows of the \
      ONE compile-time event log (append-only; the per-lane replay = \
      the log's fold filtered to the lane)"
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
        let taken := (laneRows env laneId).map (·.name)
        if taken.contains (nameOf item) then
          Lean.throwError
            m!"{dupDiag attrName.toString declName.toString (nameOf item) taken}"
        Lean.modifyEnv fun env =>
          laneLogExt.addEntry env
            { lane := laneId, name := nameOf item, decl := declName }
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
    (12-construction §2) — the attribute mount + the lane's row family
    — into one kit call. The ONE log is the substrate's own (`laneLogExt`);
    the mount appends lane-tagged rows. See the module header for the
    generated pieces and the name convention. -/
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
      -- the shared throw (Kit.Derive.Common's ONE copy — the plain-Diag
      -- envelope rendering is byte-identical to the usageDiag + m!"{d}"
      -- spelling this site carried; the A7 unification)
      Kit.Derive.Common.throwDiag eKL0006
        "register_lane: the `where naming := <fn>` clause is required — \
          naming is the item's naming function (the registry's lookup key); \
          valid usage: `register_lane <Item> where naming := <fn>` with the \
          optional clauses `attr := <name>` (the attribute's name) and \
          `builder := <fn>` (a custom builder \
          `Environment → Name → Except String Item`)"
    let itemTyName := item.getId.eraseMacroScopes
    let itemLast := (itemTyName.toString.splitOn ".").getLast!
    let baseStr := match attr? with
      | some a => a.toString
      | none => itemLast.decapitalize
    let ns := (← Lean.Elab.Command.getScope).currNamespace
    let accId := Lean.mkIdent (Lean.Name.mkSimple s!"get{baseStr.capitalize}s")
    let laneIdId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}LaneId")
    let nameOfId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}NameOf")
    let regId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}Registry")
    let oblId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}ObligationView")
    let demId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}LedgerDemand")
    let attrRegId := Lean.mkIdent (Lean.Name.mkSimple s!"{baseStr}AttrReg")
    let attrRefStr := (ns ++ Lean.Name.mkSimple s!"{baseStr}Attr").toString
    let itemTyFullNameStr := (ns ++ itemTyName).toString
    let itemT : Lean.Term := ⟨item.raw⟩
    -- The template references: PRERESOLVED idents (mkIdent) — plain
    -- quoted idents carry macro scopes and silently fail on dotted
    -- names (06 §7).
    let kitLaneId : Lean.Term := Lean.mkIdent `Kit.Lane.LaneId
    let kitRows : Lean.Term := Lean.mkIdent `Kit.Lane.laneRows
    let kitNameOfStr : Lean.Term := Lean.mkIdent `Kit.Lane.nameOfStr
    let kitReplay : Lean.Term := Lean.mkIdent `Kit.Lane.replayLane
    let kitEvalB : Lean.Term := Lean.mkIdent `Kit.Lane.evalReplayBuilder
    let _kitMat : Lean.Term := Lean.mkIdent `Kit.Lane.materialize
    let kitReg : Lean.Term := Lean.mkIdent `Kit.DataRegistry
    let kitDemandSet : Lean.Term := Lean.mkIdent `Kit.Ledger.DemandSet
    let kitNamesOf : Lean.Term := Lean.mkIdent `Kit.Ledger.namesOf
    let kitLogName : Lean.Term := Lean.mkIdent `Kit.Lane.laneLogName
    let kitInstall : Lean.Term := Lean.mkIdent `Kit.Lane.installLaneAttr
    let kitEval : Lean.Term := Lean.mkIdent `Kit.Lane.evalLaneItem
    let kitWrap : Lean.Term := Lean.mkIdent `Kit.Lane.wrapBuilder
    let buildFn : Lean.Term ← match builder? with
      | some b =>
        `(($kitWrap $(Lean.quote baseStr) $b))
      | none =>
        `((($kitEval (Item := $itemT))
            ($kitNameOfStr $(Lean.quote itemTyFullNameStr)) $(Lean.quote baseStr)))
    -- THE READER'S BUILDER ROUTE: the default route re-evaluates the
    -- def's value; a custom builder re-runs (it is env-based).
    let replayB : Lean.Term ← match builder? with
      | some b => `(fun env decl => pure ($b env decl))
      | none =>
        `(($kitEvalB (Item := $itemT)
            ($kitNameOfStr $(Lean.quote itemTyFullNameStr)) $(Lean.quote baseStr)))
    Lean.Elab.Command.elabCommand (← `(command|
      def $laneIdId : $kitLaneId := $(Lean.quote itemTyFullNameStr)))
    Lean.Elab.Command.elabCommand (← `(command|
      unsafe def $accId (env : Lean.Environment) :
          Lean.CoreM (Except String (List $itemT)) :=
        ($kitReplay (Item := $itemT) ($kitRows env $laneIdId) $replayB env)))
    Lean.Elab.Command.elabCommand (← `(command|
      def $nameOfId : $itemT → String := $namingT))
    Lean.Elab.Command.elabCommand (← `(command|
      unsafe def $regId (env : Lean.Environment) :
          Lean.CoreM (Except String ($kitReg $itemT)) :=
        (Kit.Lane.registryOf $nameOfId) <$> ($accId env)))
    -- THE ENTOURAGE HOOKS (16-surface §3's discipline, at the lane
    -- face): the obligation view (the attests labels, one per routed
    -- row) + the ledger demand (the lane records the rows it folds;
    -- the collection it reads is THE ONE LOG). Both PURE (the rows are
    -- data — no value re-materialization needed). Auto-filled at the
    -- mount; there is no lane-side tier to hand-set.
    Lean.Elab.Command.elabCommand (← `(command|
      def $oblId (env : Lean.Environment) : List String :=
        ($kitRows env $laneIdId).map (fun r => r.name)))
    Lean.Elab.Command.elabCommand (← `(command|
      def $demId (env : Lean.Environment) : $kitDemandSet :=
        { rows := ($kitRows env $laneIdId).map (fun r => $kitNamesOf r.name)
          collections := [$kitNamesOf $kitLogName]
          emitterRev := "register_lane" }))
    Lean.Elab.Command.elabCommand (← `(command|
      unsafe initialize $attrRegId : Unit ←
        (($kitInstall (Item := $itemT))
          ($kitNameOfStr $(Lean.quote baseStr))
          ($kitNameOfStr $(Lean.quote attrRefStr))
          $laneIdId $nameOfId $buildFn)))
  | _ => Lean.Elab.throwUnsupportedSyntax
/-! ## The lane teeth (the audit's E3 — the fixture teeth shape, ONE macro)

The lane fixture's negative controls were byte-comparable boilerplate
across the tree's lane fixtures (KitTests.LaneDemo, the schemacore
Check/Keys slices, the faults lane, the DemoApp/LedgerApp lanes — the
scaffolder emits the shape as a template): the DUPLICATE-NAME control
and the WRONG-TYPE control, each a refusal whose expected text was
hand-copied. The teeth commands are the ONE shape, and they take the
control command VERBATIM — the `#guard_msgs` discipline
(`lane_dup_tooth … in <command>`), NO syntax splicing: the caller
writes the `@[<attr>] def <ctl> : <Ty> := <value>` control exactly as
it would stand in the fixture, and the tooth PARSES the attribute, the
control name, and the entry type back out of the command's syntax (a
read-only pattern match — nothing is reassembled). The macro derives
the expected refusal from the mount's OWN Diag constructors and checks
the control's elaboration log against it — exactly one message,
byte-identical (whitespace-normalized, the `#guard_msgs` default; the
pins' text is the teeth). The teeth cannot rot silently: a message,
code, or valid-space drift fails the build.

The taking of the expected text from the mount's constructors (not a
hand copy) is DELIBERATE: the envelope, the valid-space enumeration,
and the did-you-mean are `closedWorld`'s business, already pinned at
Kit.Diag's own teeth; the tooth pins THAT THE MOUNT REFUSES with THAT
Diag — the refusal fires, the code is the family's, the text is the
mount's. -/

/-- The tooth's check face (the `#guard_msgs` core, restricted): the
    control's log must be EXACTLY the one expected message —
    `severity: text`, whitespace-normalized. On a pass the expected
    refusal is CONSUMED (cleared from the log — it never leaks into a
    later guard); on a drift the tooth errors loudly. -/
private def checkTooth (ctlStr expected : String) (cmd : Lean.Syntax) :
    Lean.Elab.Command.CommandElabM Unit := do
  let msgs ← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages cmd
  let rendered : List String ← msgs.toList.mapM fun m => do
    let txt ← m.data.toString
    pure (match m.severity with
      | .error => s!"error: {txt}"
      | .warning => s!"warning: {txt}"
      | .information => s!"info: {txt}")
  let norm := rendered.map (·.replace "\n" " ")
  unless norm == [expected] do
    Lean.throwError s!"lane tooth `{ctlStr}` drifted — expected the single \
      refusal `{expected}`, got {norm}"
  -- the expected refusal is consumed: the log is clean for later teeth
  modify fun s => { s with messages := {}, snapshotTasks := #[] }

/-- The plain-attribute's name: the `@[<name>]` shape's ident, read
    STRUCTURALLY off the `Lean.Parser.Attr.simple` node (no
    `attr`-category quotation — the lane's own `attr :=` clause keyword
    makes `attr` a token, and a keyword cannot name a quotation's
    category or an antiquotation's variable; the structural read is the
    keyword-proof route). A compound attribute gets `none` — the teeth
    require the plain `@[<name>]` shape. -/
private def attrIdentOf? (a : Lean.Syntax) : Option String :=
  match a.getArgs.find? (·.isIdent) with
  | some id => some id.getId.toString
  | none => none

/-- Parse the tooth's data out of the VERBATIM control command — a
    read-only pattern match over the caller's syntax (never a splice):
    the `@[<attr>]` attribute and the `<ctl>` def name. The control
    must be exactly a plain attributed `def` with a type ascription
    (the fixture's shape). -/
private def parseCtl (cmd : Lean.Syntax) :
    Lean.Elab.Command.CommandElabM (String × String) :=
  match cmd with
  | `(command| @[$a:attr] def $ctl:ident : $_ty:term := $_body:term) => do
      let some attrStr := attrIdentOf? a.raw |
        Lean.throwError "lane tooth: the control's attribute must be a \
          plain `@[<name>]` — valid usage: `@[<attr>] def <name> : <ty> \
          := <value>`"
      pure (attrStr, ctl.getId.eraseMacroScopes.toString)
  | _ => Lean.throwError "lane tooth: the control must be a plain \
      attributed `def` — valid usage: `@[<attr>] def <name> : <ty> := \
      <value>`"

/-- THE DUP TOOTH: `lane_dup_tooth <got> <valid> in @[<attr>] def
    <ctl> : <ItemTy> := <value>` — the duplicate-name control (KL0001).
    The control is taken VERBATIM (the `#guard_msgs` shape; nothing is
    spliced). `<got>` is the duplicate item's name (the lane's naming
    function's verdict over the control's value); `<valid>` is the
    valid-space LIST LITERAL the tooth EXPECTS at its point (the names
    registered so far, in replay order) — the tooth FIRST pins that
    list against the LIVE registration state (the lane's generated
    `<base>ObligationView`; a drifted pin is a loud refusal), then
    computes the expected refusal from the mount's OWN `dupDiag` and
    checks the control's log against it. The valid list is a BARE term
    (no surrounding brackets of the tooth's own — the tooth's syntax
    must not eat the list literal's brackets). -/
syntax (name := laneDupToothCmd) "lane_dup_tooth " str term
  " in " command : command

@[command_elab Kit.Lane.laneDupToothCmd]
def elabLaneDupTooth : Lean.Elab.Command.CommandElab
  | `(command| lane_dup_tooth $gotS:str $takenT:term in $cmd:command) => do
    let got := gotS.getString
    let (attrStr, ctlStr) ← parseCtl cmd.raw
    -- the valid-space pin: the caller's list must BE the live
    -- registration state (the lane's obligation view at the tooth) —
    -- a #eval replay, collected (a drift is the collected error)
    let taken : List String ←
      match takenT with
      | `(term| []) => pure []
      | `(term| [$[$ss:str],*]) => pure ((ss.map (·.getString)).toList)
      | _ => Lean.throwError s!"lane_dup_tooth: the <valid> slot must be \
        a string-list literal"
    let oblIdent := Lean.mkIdent (Lean.Name.mkSimple s!"{attrStr}ObligationView")
    let pinCmd ← `(command|
      #eval show Lean.CoreM Unit from do
        let env ← Lean.getEnv
        let taken := $oblIdent env
        unless taken == $takenT do
          Lean.throwError s!"lane tooth: the valid-list pin drifted: {taken}")
    let pinMsgs ←
      Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages pinCmd
    unless pinMsgs.toList.isEmpty do
      Lean.throwError s!"lane_dup_tooth {ctlStr}: the valid-list pin \
        failed — the tooth's `<valid>` is not the live registration state"
    let expected := s!"error: {(dupDiag attrStr ctlStr got taken).toString}"
    checkTooth ctlStr expected cmd.raw
  | _ => Lean.Elab.throwUnsupportedSyntax

/-- THE WRONG-TYPE TOOTH: `lane_wrong_tooth <ItemTy> in @[<attr>] def
    <ctl> : <Ty> := <value>` — the entry-type control (KL0003): a def
    whose type is NOT the lane's item type must refuse with the curated
    usage message. `<ItemTy>` is the LANE's item type (the message's
    type slot — the mount names its own item type, never the control's
    declared type), spelled exactly as the mount renders it (the
    registration-time `currNamespace`-qualified name); the control
    itself is taken VERBATIM (the `#guard_msgs` shape — nothing
    spliced). -/
syntax (name := laneWrongToothCmd) "lane_wrong_tooth " ident
  " in " command : command

@[command_elab Kit.Lane.laneWrongToothCmd]
def elabLaneWrongTooth : Lean.Elab.Command.CommandElab
  | `(command| lane_wrong_tooth $ty:ident in $cmd:command) => do
    let (attrStr, ctlStr) ← parseCtl cmd.raw
    let tyStr := ty.getId.eraseMacroScopes.toString
    let msg := s!"@[{attrStr}] {ctlStr}: the entry's type is not the \
      lane's item type `{tyStr}` — valid usage: \
      `@[{attrStr}] def {ctlStr} : {tyStr} := <value>`"
    let expected := s!"error: {(usageDiag eKL0003 msg).toString}"
    checkTooth ctlStr expected cmd.raw
  | _ => Lean.Elab.throwUnsupportedSyntax

end Kit.Lane
