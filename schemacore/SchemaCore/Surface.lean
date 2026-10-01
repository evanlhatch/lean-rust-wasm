/- # SchemaCore.Surface — the `table!` clause macro (the authoring surface, wave-30 E1)

One declaration generates THE ENTOURAGE — the machine! precedent
(15-patterns #9) applied to the schema lane, riding the parse-route
discipline (15-patterns #19; the emission renders to source text and
re-parses — never quotation splices):

```lean
table! Account v2 where
  key: id                      -- the primary key (the keys lane's row)
  ref: cust : Customer         -- a foreign ref (the target's key types the field)
  id : UInt64                  -- the field lines (the item's fields, in order)
  owner : String
  rule: Positive := .u64GtLit "limit" 0   -- the check lane's row
  deriving: WireCodec, row_bridge         -- the capability set (the default)
```

THE SIX-WORD VOCABULARY (16-surface §2): `table`, `key`, `ref`,
`rule`, `state`, `event`. THIS FRAGMENT lands the first four words;
`state` (the variant-item face) and `event` (the stream idiom's
clause) are the NAMED NEXT ROWS — they wait for the variant-item
model and the journal-lane clause, respectively (the honest gaps, not
hidden ones). The unknown-clause refusal enumerates the LANDED
vocabulary; this doc is where the next rows are named.

## What one declaration expands to (the entourage, per 16-surface §3)

- `table!` — the plain structure + `@[schema]` (the SAME mount,
  `Register.lean`'s lane; the ONE reflection path
  `Describe.reflectItemViaDescr` is fed, never bypassed — D19) with
  the defaulted capabilities (`deriving WireCodec, row_bridge`
  injected; the derivation stays lazy — the default IS the named set).
  The codecs' evidence entourage (obligation rows, the LCG sweep, the
  mechanical sabotage controls, the simp-set registrations) is the
  deriving handlers' unchanged emission — the tests' scaffolding hooks.
- `key:` / `ref:` — the `KeyDecl` row emitted into the keys lane at
  the declaration (the second-module + string-record-ref friction,
  killed): `record` is THIS declaration's full name (hygienic, never
  hand-strung), `fields` is the row_bridge-generated snapshot (ONE
  copy), and a `ref:`'s field is TYPED BY the target's declared key
  (determinacy driving the API shape, 02 §3 — the target must be
  registered WITH a declared key: the foreignDecl rung at authoring
  time).
- `rule:` — the `CheckItem` row(s) emitted into the check lane (the
  shared authority over valid worlds, 02 §1 — the violating rows ARE
  the payload; the obligation row rides `CheckItem.obligation`).
- `v<N>` — THE EVOLUTION FACE: the prior version is looked up in the
  ONE log (the registry IS the accumulated event log, 15 #7; the
  versions ARE its rows), the diff→plan→upcaster pipeline is the
  migration lane's OWN machinery (`deriveUpcaster` — consumed, not
  re-rolled), and the unsupported change shapes REFUSE AT
  ELABORATION, before anything is emitted, in the ONE Diag envelope:
  removals (no value-map target), unremedied retypes (the inline
  `remedy:` clause is the named next row), reorders/mid-inserts
  (order-aligned derivation; the stable-id lane is the named
  follow-up), key moves (a migrated key is a different entity set —
  08 §19), and additions without a type default.
- (every declaration) — the build-time teeth: the replayed lanes' WF
  (the keys cascade, the checks' scoping) + the derived plan's key
  stability, pinned at the declaration site.

## The token discipline + the curated failures

- The command word is `table!` and the clause words are
  COLON-SUFFIXED (`key:`, `ref:`, `rule:`, `deriving:`) — the
  machine! precedent's token-pollution lesson verbatim: the bare
  spellings (`table`, `key`, `ref`) are live identifiers and
  struct-field names across the tree (substrait's `table` field,
  KeysSlice's `key :=` instance slot), and a bare keyword would break
  them package-wide. `table!` is a fresh token; the colon-suffixed
  atoms are distinct from the bare idents.
- The clause list is a CLOSED WORLD: an unknown clause reaches the
  ELABORATOR via the low-priority catch-alls and is rejected with the
  legal-clause enumeration + the ONE did-you-mean engine
  (`Kit.Diag.closedWorld`'s suggest slot). The Dsl.lean limit's
  analogue: a colon-shaped typo (`ky: id`) shares the field line's
  exact shape (`name : type`) and is the REFLECTION's curated refusal
  (the SD envelope at the mount) — the catch-alls are exact for the
  non-colon shapes.
- EVERY refusal fires BEFORE the first emission (the analysis —
  types, refs, versions, the diff — runs on the clause syntax; a
  refused `table!` declaration emits nothing). The negative controls
  are therefore clean: no lane row, no structure, no residue.

E-codes: the `SR0001`–`SR0007` family (schema surface; allocated from
the PERSISTED registry, `notes/code-registry.txt` — the constants are
the family's DECLARATION, the sites use them, never a bare string).

Core-only (imports Lean + the lanes it desugars onto — the cone rule;
everything is `Kit`/`SchemaCore`-rooted). META module: the generated
decls are ordinary declarations; the macro is elaboration-time only.

Five questions (notes/v3/01-core.md):
- root: META — the authoring face (12 §1's two-idiom frontend, the
  table idiom's first words); the lanes it feeds are the machinery.
- carrier grade: none of its own — the generated surface is the
  plain structure + the lane rows (the same carriers as the mounts).
- spine reading: the AUTHORING stage — one declaration → the same
  mounts' rows → the same replay/emitter/gate consumption.
- ladder rung: rung 1 (the closed-world refusals, the pre-emission
  analysis, the parse-route emission); no proofs of its own — the
  generated laws are the mounts' citations.
- gate row: SchemaTests' surface suite (the evolution teeth + the
  curated-failure negative controls + the six-word acceptance spec) +
  the byte-identity migration proof (SchemaCore.Slice re-authored;
  gen-check is the tooth) + the axiom report.
-/

import Lean
import Kit.Diag
import Kit.Derive.Common
import SchemaCore.Register
import SchemaCore.DeriveMeta
import SchemaCore.Keys
import SchemaCore.Check
import SchemaCore.Migrate

namespace SchemaCore.Surface

open Lean Elab Command

/-! ## The E-codes (the SR family — the registry's persisted allocation) -/

/-- The unknown clause (the closed-world clause vocabulary). -/
def eSR0001 : Kit.ECode := ⟨"SR0001"⟩
/-- The key clause's misuse (duplicate, or names no declared field). -/
def eSR0002 : Kit.ECode := ⟨"SR0002"⟩
/-- The ref clause's target resolution (unregistered, keyless, or
    non-scalar-keyed target). -/
def eSR0003 : Kit.ECode := ⟨"SR0003"⟩
/-- The capability set (an unknown capability; a key/ref table that
    opted out of the row_bridge the fields snapshot rides). -/
def eSR0004 : Kit.ECode := ⟨"SR0004"⟩
/-- The version face (a `v<N>` with no prior version; an unversioned
    redeclaration of a registered name; a versioned table without a
    declared key). -/
def eSR0005 : Kit.ECode := ⟨"SR0005"⟩
/-- THE EVOLUTION REFUSAL — the migration lane's `MigrateRefusal`,
    surfaced at the declaration. -/
def eSR0006 : Kit.ECode := ⟨"SR0006"⟩
/-- A field type outside the boundary fragment (the closed `Ty`
    universe's authoring spellings). -/
def eSR0007 : Kit.ECode := ⟨"SR0007"⟩

/-- The closed-world refusal (the ONE envelope: got + the valid space
    + the ONE engine's did-you-mean — `Kit.suggestFor` fills the
    envelope's suggest slot, so every `throwClosed` site's refusal
    enumerates the valid space and suggests, unforgably). -/
def throwClosed {α : Type} (code : Kit.ECode) (msg got : String)
    (valid : List String) : CommandElabM α :=
  throwError m!"{(Kit.Diag.closedWorld code msg .error got valid : Kit.Diag)}"

/-! ## The clause vocabulary (the closed world) -/

/-- The LANDED clause words (the refusal's valid space; the six-word
    vocabulary's `state`/`event` are the named next rows — the module
    header, not this list, names them). -/
def legalClauses : List String :=
  ["key:", "ref:", "rule:", "deriving:", "name : type"]

/-- The landed capabilities (the deriving: vocabulary). -/
def legalCaps : List String := ["WireCodec", "row_bridge"]

declare_syntax_cat tableClause

/-- The primary key (at most one — the keys lane's v1 granularity:
    single-field keys). -/
syntax (name := tableKeyClause) "key: " ident : tableClause

/-- A foreign ref: the field's type IS the target's declared key (the
    determinacy-driven API shape); the target must be a registered
    table WITH a declared key. -/
syntax (name := tableRefClause) "ref: " ident " : " ident : tableClause

/-- The shared authority: the invariant as a `Pred` row over the
    table's fields (the check lane's mount; the violating rows are the
    payload). -/
syntax (name := tableRuleClause) "rule: " ident " := " term : tableClause

/-- The capability set (the DEFAULT when absent: both). -/
syntax (name := tableDerivingClause) "deriving: " ident,* : tableClause

/-- The field line — the item's fields, in source order. -/
syntax (name := tableFieldClause) ident " : " term : tableClause

/-- The unknown-clause catch-alls (the Dsl.lean discipline): low
    priority, so the named clauses win; the caught shapes are rejected
    at ELABORATION with the legal enumeration + did-you-mean. A
    colon-shaped typo (`ky: id`) shares the field line's shape and is
    the reflection's curated SD refusal at the mount (the term-led
    limit's analogue — named in the module header). -/
syntax (name := tableUnknownEq) (priority := low) ident " := " term : tableClause
syntax (name := tableUnknownEq2) (priority := low) ident ident " := " term : tableClause
syntax (name := tableUnknownIdents) (priority := low) ident ident : tableClause

/-- THE CLAUSE LIST (the structFields discipline, Lean/Parser/Command.lean,
    verbatim): `withPosition` + `checkColGe` per clause. THE TERM-GOBBLING
    WALL, defeated here with Lean's OWN mechanism: a clause's trailing
    `term` would otherwise juxtapose the next clause's first ident
    (`a : Bool\n  b : UInt64` parses as `a : (Bool b)` — the application
    parser's `checkColGt` argument guard passes without a saved column);
    the `withPosition`-scoped `checkColGe` gives every term's argument
    check a saved column at the clause list, stopping the application at
    the line break. NOT expressible in the `syntax`-decl DSL — the DSL's
    `(ppSpace colGt clause)*` carries no `withPosition` (defeat #1,
    recorded; this def is the fix). -/
def tableClausesP : Lean.Parser.Parser :=
  Lean.Parser.withPosition <| Lean.Parser.many
    (Lean.Parser.checkColGe "irrelevant" >>
      (Lean.Parser.ppLine >> Lean.Parser.categoryParser `tableClause 0))

/-- THE TABLE COMMAND: `table! <Name> (v<N>)? where <clauses>`. The
    version is mandatory from the second declaration of a name — the
    first declaration IS v1 (the version row IS the lane log's row). -/
syntax (name := tableCmd) "table! " ident (ppSpace ident)? " where"
  tableClausesP : command

/-! ## The analysis (pre-emission — a refusal emits nothing) -/

/-- One analyzed field line: the name, the type syntax (the
    structure's emission carries it verbatim — a `ref:`'s is the
    target's key spelling, generated), the resolved `Ty`, and — for a
    `ref:` — the target's full registered name. -/
structure TableRow where
  name : String
  tyStx : Syntax
  ty : Ty
  isRef : Bool
  refTarget? : Option String

-- (the `ref:` clause's target, as its last-name string; resolved to
-- the registered record below)

/-- The analyzed table: everything the emission needs, computed BEFORE
    the first command is emitted. -/
structure TableSpec where
  tnStr : String
  fullStr : String
  ver? : Option Nat
  priorName? : Option String
  fields : List TableRow
  key? : Option String
  rules : Array (String × Syntax)
  capsWire : Bool
  capsRow : Bool

/-- The four scalars' Lean spellings (the ref field's generated type;
    the closed universe's authoring spellings — `Describe`'s fragment). -/
def scalarSpelling : Ty → Option String
  | .bool => some "Bool"
  | .u64 => some "UInt64"
  | .i64 => some "Int64"
  | .string => some "String"
  | _ => none

/-- The version ident's shape: `v` + digits. -/
def versionOf? (id : Lean.Name) : Option Nat :=
  let s := id.toString
  let ds := (s.toList.drop 1)
  if s.length >= 2 && s.startsWith "v" && ds.all Char.isDigit then
    some (ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

open Kit.Derive.Common (throwDiag)

/-- The clause-walk refusal: the unknown clause, with the legal
    enumeration + did-you-mean (the closed-world constructor —
    `Kit.suggestFor` fills the suggest slot). -/
def unknownClause (w : String) : CommandElabM α :=
  throwClosed eSR0001
    s!"table!: unknown clause `{w}` — the clause list is a closed world \
      (field lines are `name : type`)" w legalClauses

/-- The evolution refusal mapped to the surface's envelope (the
    migration lane's obligation named, the named follow-up stated). -/
def evolutionRefusal (tnStr : String) (ver : Nat)
    (r : SchemaCore.MigrateRefusal) : CommandElabM α :=
  let detail : String :=
    match r with
    | .fieldRemoved _ f =>
        s!"removes field `{f}` — gone data has no value-map target \
          (the stable-id lane is the named follow-up)"
    | .fieldUnremedied _ f =>
        s!"retypes field `{f}` without a registered remedy — the inline \
          `remedy:` clause is the named next row"
    | .fieldReordered _ f =>
        s!"reorders field `{f}` — the derivation is order-aligned; \
          mid-list inserts refuse (the stable-id lane is the named \
          follow-up)"
    | .keyUnstable _ f =>
        s!"moves the key to `{f}` — a migrated key is a different \
          entity set (08 §19: stable identities)"
    | .noDefault _ f =>
        s!"adds field `{f}` whose type has no default value (a cap-0 \
          `bounded` is uninhabited) — the fill needs the type's default"
  throwClosed eSR0006
    s!"table! {tnStr} v{ver}: the evolution refuses — {detail}" tnStr []

/-- The analysis: the clauses' syntax → the `TableSpec` (types
    elaborated + reified, refs resolved, versions checked). Everything
    here REFUSES before any emission. -/
unsafe def analyze (name : TSyntax `ident)
    (ver? : Option (TSyntax `ident)) (clauses : Array Syntax) :
    CommandElabM TableSpec := do
  let tn := name.getId.eraseMacroScopes
  let tnStr := tn.toString
  let currNs ← getCurrNamespace
  let fullStr := (currNs ++ tn).toString
  -- ── the clause walk (source order) ──
  let mut fields : Array TableRow := #[]
  let mut fieldNames : Array String := #[]
  let mut key? : Option String := none
  let mut refCount := 0
  let mut rules : Array (String × Syntax) := #[]
  let mut capsWire := true
  let mut capsRow := true
  let mut derivingSeen := false
  for c in clauses do
    match c with
    | `(tableClause| key: $f:ident) =>
        let fStr := f.getId.eraseMacroScopes.toString
        if key?.isSome then
          throwClosed eSR0002
            s!"table! {tnStr}: duplicate `key:` clause — at most one (the \
              keys lane's v1 granularity: a single-field key)"
            fStr (key?.toList ++ fieldNames.toList)
        key? := some fStr
    | `(tableClause| ref: $f:ident : $t:ident) =>
        let fStr := f.getId.eraseMacroScopes.toString
        if fieldNames.contains fStr then
          throwClosed eSR0002
            s!"table! {tnStr}: duplicate field `{fStr}` — a table's field \
              names are distinct (the fields-nodup obligation)"
            fStr fieldNames.toList
        refCount := refCount + 1
        fieldNames := fieldNames.push fStr
        fields := fields.push
          { name := fStr, tyStx := f.raw, ty := .u64, isRef := true
            refTarget? := some t.getId.eraseMacroScopes.toString }
    | `(tableClause| deriving: $[$cs:ident],*) =>
        derivingSeen := true
        capsWire := false
        capsRow := false
        for ci in cs do
          let cStr := ci.getId.eraseMacroScopes.toString
          if cStr == "WireCodec" then capsWire := true
          else if cStr == "row_bridge" then capsRow := true
          else
            -- the closed-world refusal: legalCaps is the valid space,
            -- `Kit.suggestFor` the did-you-mean (throwClosed's envelope)
            throwClosed eSR0004
              s!"table! {tnStr}: unknown capability in `deriving:` — the \
                capability set is a closed world" cStr legalCaps
    | `(tableClause| $f:ident : $t:term) =>
        let fStr := f.getId.eraseMacroScopes.toString
        -- the type: elaborated + reified NOW (a fragment refusal is
        -- the surface's SR envelope, before any emission)
        let tyExpr ← liftTermElabM (Lean.Elab.Term.elabType t.raw)
        match SchemaCore.tyOfExpr? tyExpr with
        | none =>
            throwClosed eSR0007
              s!"table! {tnStr}: field `{fStr}`'s type is outside the \
                boundary fragment — `describe` reflects the closed \
                universe's leaves, wrapped in option/list/sum/map/bounded"
              fStr SchemaCore.describeFragment
        | some ty =>
            if fieldNames.contains fStr then
              throwClosed eSR0002
                s!"table! {tnStr}: duplicate field `{fStr}` — a table's \
                  field names are distinct (the fields-nodup obligation)"
                fStr fieldNames.toList
            fieldNames := fieldNames.push fStr
            fields := fields.push
              { name := fStr, tyStx := t.raw, ty := ty, isRef := false
                refTarget? := none }
    | c =>
        -- the `:=`-carrying clauses (rule + the catch-alls) dispatch by
        -- KIND — `:=` is a token no quotation pattern can spell; the
        -- rule's args are [ident, term], the catch-alls' first arg is
        -- the (typo'd) clause word
        let k := c.getKind
        -- the literal tokens ("rule: ", " := ") OCCUPY arg slots: the
        -- rule's shape is [atom, ident, atom, term]
        if k == ``tableRuleClause then
          rules := rules.push
            (c.getArgs[1]!.getId.eraseMacroScopes.toString, c.getArgs[3]!)
        else if k == ``tableUnknownEq || k == ``tableUnknownEq2 ||
            k == ``tableUnknownIdents then
          unknownClause c.getArgs[0]!.getId.eraseMacroScopes.toString
        else
          Lean.Elab.throwUnsupportedSyntax
  if fields.isEmpty then
    throwClosed eSR0002
      s!"table! {tnStr}: a table needs at least one field line \
        (`name : type`)" tnStr fieldNames.toList
  match key? with
  | some k =>
      unless fieldNames.contains k do
        throwClosed eSR0002
          s!"table! {tnStr}: the `key:` clause names `{k}`, which is not \
            a declared field — the key is one of the table's own field \
            lines" k fieldNames.toList
  | none => pure ()
  if derivingSeen && !capsWire && !capsRow then
    throwDiag eSR0004
      s!"table! {tnStr}: an empty capability set — name at least one of \
        WireCodec / row_bridge (deriving is lazy; the default is BOTH)"
  let env ← getEnv
  -- ── the ref resolution: the target's declared key types the field ──
  let keyDecls : List KeyDecl ←
    match ← liftCoreM (SchemaCore.getKeys env) with
    | .error e => throwError s!"table! {tnStr}: the keys replay refused: {e}"
    | .ok kds => pure kds
  let mut resolved : Array TableRow := #[]
  for f in fields do
    match f.refTarget? with
    | none => resolved := resolved.push f
    | some target =>
        let candidates :=
          keyDecls.filter (fun kd => SchemaCore.lastName kd.record == target)
        match candidates.getLast? with
        | none =>
            throwClosed eSR0003
              s!"table! {tnStr}: the `ref:` target `{target}` is not a \
                registered table with a declared key — declare the \
                target's `table!` with its `key:` first (the forward \
                reference rung, at authoring time)"
              target (keyDecls.map (fun kd => SchemaCore.lastName kd.record))
        | some kd =>
            let keyField := kd.fields.find? (fun fl => fl.name == kd.key)
            match keyField with
            | none =>
                throwClosed eSR0003
                  s!"table! {tnStr}: the `ref:` target `{target}`'s key \
                    declaration is corrupt (no key field on its snapshot)"
                  target []
            | some kf =>
                match scalarSpelling kf.ty with
                | none =>
                    throwClosed eSR0003
                      s!"table! {tnStr}: the `ref:` target `{target}`'s \
                        key is outside the scalar fragment — a ref field \
                        is typed by the target's scalar key (02 §3)"
                      target ["Bool", "UInt64", "Int64", "String"]
                | some sp =>
                    resolved := resolved.push
                      { name := f.name
                        tyStx := Lean.mkIdent (Lean.Name.mkSimple sp)
                        ty := kf.ty, isRef := true
                        refTarget? := some kd.record }
  -- ── the capability/entourage coupling ──
  if (key?.isSome || refCount > 0) && !capsRow then
    throwDiag eSR0004
      s!"table! {tnStr}: the `key:`/`ref:` clauses need the row_bridge \
        capability (the fields snapshot `T.fields` is the ONE copy the \
        key rows ride) — drop the `deriving:` restriction or add \
        row_bridge"
  -- ── the version face: the prior version from the ONE log ──
  let verNat? : Option Nat ← match ver? with
    | none => pure none
    | some v =>
        match versionOf? v.getId.eraseMacroScopes with
        | some n => pure (some n)
        | none =>
            throwClosed eSR0005
              s!"table! {tnStr}: the version must be spelled `v<N>` (the \
                first declaration IS v1; the second declaration bumps to \
                `v2`)" v.getId.eraseMacroScopes.toString []
  let schemaItems : List Item ←
    match ← liftCoreM (SchemaCore.getSchemas env) with
    | .error e => throwError s!"table! {tnStr}: the schema replay refused: {e}"
    | .ok items => pure items
  let priors :
      List Kit.Lane.LaneRow :=
    (Kit.Lane.laneRows env SchemaCore.schemaLaneId).filter
      (fun r => SchemaCore.lastName r.name == tnStr && r.name != fullStr)
  let priorName? : Option String := (priors.getLast?).map (·.name)
  if verNat?.isSome && priors.isEmpty then
    throwClosed eSR0005
      s!"table! {tnStr}: versioned declaration with no prior version in \
        the registry — the first declaration of a name is v1 (no `v<N>` \
        spelling); a version rides the registry's OWN event log (15 #7)"
      tnStr []
  if verNat?.isNone && !priors.isEmpty then
    throwClosed eSR0005
      s!"table! {tnStr}: `{tnStr}` is already registered — a \
        redeclaration bumps the version (`table! {tnStr} v2 where …`); \
        the versions ARE the registry's rows" tnStr []
  if let some ver := verNat? then
    match key? with
    | none =>
        throwClosed eSR0005
          s!"table! {tnStr} v{ver}: a versioned table declares its key — \
            stable identities, 08 §19" tnStr ["a `key:` clause"]
    | some k =>
        -- the key must not MOVE: the prior's declared key is the
        -- entity set's identity (a migrated key is a different set)
        let priorKey? :=
          (priors.getLast?).bind (fun p =>
            (keyDecls.find? fun kd => kd.record == p.name).map (·.key))
        match priorKey? with
        | some pk =>
            unless pk == k do
              throwClosed eSR0006
                s!"table! {tnStr} v{ver}: the key moves from `{pk}` to \
                  `{k}` — a migrated key is a different entity set \
                  (08 §19: stable identities required)"
                k [pk]
        | none => pure ()
        -- THE EVOLUTION CHECK: the migration lane's own derivation
        -- (consumed, not re-rolled), at the declaration, pre-emission.
        let oldIt? :=
          schemaItems.find? fun it =>
            it.name == (priorName?.getD "")
        let newIt : Item :=
          { name := fullStr
            fields :=
              (resolved.map (fun f => { name := f.name, ty := f.ty })).toList }
        match oldIt? with
        | some oldIt =>
            match SchemaCore.deriveUpcaster k [] oldIt newIt with
            | .error r => evolutionRefusal tnStr ver r
            | .ok _ => pure ()
        | none =>
            throwError s!"table! {tnStr} v{ver}: the version chain \
              drifted (the prior item did not replay)"
  pure
    { tnStr := tnStr, fullStr := fullStr, ver? := verNat?
      priorName? := priorName?, fields := resolved.toList, key? := key?
      rules := rules, capsWire := capsWire, capsRow := capsRow }

/-! ## The emission (the parse route — pattern #19) -/

/-- Render a syntax fragment to source text (the parse route's
    renderer — the author's spellings carried verbatim). -/
def renderStx (stx : Syntax) : String :=
  Lean.Format.pretty stx.prettyPrint (width := 120)

/-- The generated commands, as SOURCE TEXT (the parse route: rendered
    → re-parsed by the real parser → elaborated exactly like hand
    code; DepFold's wave-29 lesson). -/
def renderCommands (spec : TableSpec) : CommandElabM (Array String) := do
  let mut cmds : Array String := #[]
  -- ── 1. THE STRUCTURE (the same @[schema] mount, capabilities defaulted) ──
  let mut structSrc := ""
  structSrc := structSrc ++
    "/-- GENERATED by the `table!` surface (SchemaCore.Surface) — the \
      one-declaration authoring act. The entourage is the SAME mounts \
      (`@[schema]` + the lanes), never a parallel path. -/\n"
  structSrc := structSrc ++ "@[schema] structure " ++ spec.tnStr ++ " where\n"
  for f in spec.fields do
    structSrc := structSrc ++ "  " ++ f.name ++ " : " ++ renderStx f.tyStx ++ "\n"
  let mut caps : Array String := #[]
  if spec.capsWire then caps := caps.push "SchemaCore.WireCodec"
  if spec.capsRow then caps := caps.push "SchemaCore.row_bridge"
  unless caps.isEmpty do
    structSrc := structSrc ++ "  deriving " ++ String.intercalate ", " caps.toList
  cmds := cmds.push structSrc
  -- ── 2. THE KEY/REF ROW (the keys lane, at the declaration) ──
  if spec.key?.isSome || spec.fields.any (·.isRef) then
    let mut foreign : Array String := #[]
    for f in spec.fields do
      if f.isRef then
        foreign := foreign.push
          ("{ field := \"" ++ f.name ++ "\", target := \"" ++
            f.refTarget?.get! ++ "\" }")
    let fkSrc :=
      if foreign.isEmpty then "[]"
      else "[" ++ String.intercalate ", " foreign.toList ++ "]"
    cmds := cmds.push
      (s!"/-- GENERATED by the `table!` surface — the table's declared \
          key + its foreign refs, as the keys lane's row (the \
          second-module + string-ref friction killed; the fields \
          snapshot is the row_bridge's ONE copy). -/\n" ++
        "@[key] def " ++ spec.tnStr ++ ".keyRow : SchemaCore.KeyDecl :=\n" ++
        "  { record := \"" ++ spec.fullStr ++ "\"\n" ++
        "    fields := " ++ spec.tnStr ++ ".fields\n" ++
        "    key := \"" ++ spec.key?.getD "" ++ "\"\n" ++
        "    foreign := " ++ fkSrc ++ " }")
  -- ── 3. THE RULE ROWS (the check lane, at the declaration) ──
  for (rName, rStx) in spec.rules do
    let defName := spec.tnStr ++ ".rule" ++ rName.capitalize
    cmds := cmds.push
      (s!"/-- GENERATED by the `table!` surface — the `{rName}` rule as \
          the check lane's row (the shared authority over valid worlds; \
          the violating rows are the payload). -/\n" ++
        "@[check] def " ++ defName ++ " : SchemaCore.CheckItem :=\n" ++
        "  { name := \"" ++ spec.tnStr ++ "-" ++ rName ++ "\"\n" ++
        "    schemaRef := \"" ++ spec.fullStr ++ "\"\n" ++
        "    fields := " ++ spec.tnStr ++ ".fields\n" ++
        "    pred := " ++ renderStx rStx ++ " }")
  -- ── 4. THE TEETH (the lanes' WF + the plan's stability, at the site) ──
  -- (a `--` comment, not a docstring: a doc comment does not attach to
  -- `#eval` — it parses as a standalone moduleDoc command and the tooth
  -- becomes a second, unparseable command)
  let mut tooth := ""
  tooth := tooth ++ "-- GENERATED by the `table!` surface — the declaration's \
    build-time teeth: the registration's replay, the keys cascade's WF, \
    the rules' scoping, and (versioned tables) the derived plan's key \
    stability.\n"
  tooth := tooth ++ "#eval show Lean.CoreM Unit from do\n"
  tooth := tooth ++ "  let env ← Lean.getEnv\n"
  tooth := tooth ++ "  match ← SchemaCore.getSchemas env with\n"
  tooth := tooth ++ "  | .error e => throwError s!\"table! " ++ spec.tnStr ++
    ": the schema replay refused: {e}\"\n"
  tooth := tooth ++ "  | .ok items =>\n"
  tooth := tooth ++ "    unless (items.any fun it => it.name == \"" ++
    spec.fullStr ++ "\") do\n"
  tooth := tooth ++ "      throwError s!\"table! " ++ spec.tnStr ++
    ": the registration drifted — the item is not in the replayed \
      universe\"\n"
  if spec.key?.isSome then
    tooth := tooth ++ "    match ← SchemaCore.getKeys env with\n"
    tooth := tooth ++ "    | .error e => throwError s!\"table! " ++
      spec.tnStr ++ ": the keys replay refused: {e}\"\n"
    tooth := tooth ++ "    | .ok kds =>\n"
    tooth := tooth ++ "      let wf := SchemaCore.keyDeclsCheck items kds\n"
    tooth := tooth ++ "      unless wf.isEmpty do\n"
    tooth := tooth ++ "        throwError s!\"table! " ++ spec.tnStr ++
      ": the keys lane WF drifted: {wf}\"\n"
    tooth := tooth ++ "      unless (kds.any fun kd => kd.record == \"" ++
      spec.fullStr ++ "\" && kd.key == \"" ++ spec.key?.getD "" ++ "\") do\n"
    tooth := tooth ++ "        throwError s!\"table! " ++ spec.tnStr ++
      ": the key row drifted\"\n"
  unless spec.rules.isEmpty do
    tooth := tooth ++ "    match ← SchemaCore.getChecks env with\n"
    tooth := tooth ++ "    | .error e => throwError s!\"table! " ++
      spec.tnStr ++ ": the checks replay refused: {e}\"\n"
    tooth := tooth ++ "    | .ok cis =>\n"
    tooth := tooth ++ "      let mine := cis.filter fun ci => ci.schemaRef == \"" ++
      spec.fullStr ++ "\"\n"
    tooth := tooth ++ "      unless mine.length == " ++ toString spec.rules.size ++ " do\n"
    tooth := tooth ++ "        throwError s!\"table! " ++ spec.tnStr ++
      ": the rule rows drifted ({mine.length} of " ++ toString spec.rules.size ++ ")\"\n"
    tooth := tooth ++ "      for ci in mine do\n"
    tooth := tooth ++ "        let diags := ci.scopedDiags items\n"
    tooth := tooth ++ "        unless diags.isEmpty do\n"
    tooth := tooth ++ "          throwError s!\"table! " ++ spec.tnStr ++
      ": the rule `{ci.name}` is not legal: {diags}\"\n"
  match spec.ver?, spec.priorName? with
  | some ver, some prior =>
      tooth := tooth ++ "    match items.find? fun it => it.name == \"" ++
        prior ++ "\", items.find? fun it => it.name == \"" ++
        spec.fullStr ++ "\" with\n"
      tooth := tooth ++ "    | some o, some n =>\n"
      tooth := tooth ++ "        match SchemaCore.deriveUpcaster \"" ++
        spec.key?.getD "" ++ "\" [] o n with\n"
      tooth := tooth ++ "        | .error r => throwError s!\"table! " ++
        spec.tnStr ++ " v" ++ toString ver ++ ": the migration plan \
          drifted: {repr r}\"\n"
      tooth := tooth ++ "        | .ok p =>\n"
      tooth := tooth ++ "            unless p.stableKey \"" ++
        spec.key?.getD "" ++ "\" do\n"
      tooth := tooth ++ "              throwError s!\"table! " ++ spec.tnStr ++
        " v" ++ toString ver ++ ": the derived plan's key stability \
          drifted\"\n"
      tooth := tooth ++ "    | _, _ =>\n"
      tooth := tooth ++ "        throwError s!\"table! " ++ spec.tnStr ++
        " v" ++ toString ver ++ ": the version chain drifted\"\n"
  | _, _ => pure ()
  cmds := cmds.push tooth
  pure cmds

/-- The parse-route emission: each rendered command re-parsed by the
    REAL parser, then elaborated (never quotation splices). -/
def elabParsed (tnStr : String) (src : String) : CommandElabM Unit := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src
      (fileName := "<table-gen>") with
  | .ok s => elabCommand s
  | .error e =>
      throwDiag eSR0001
        s!"table! {tnStr}: the generated command failed to parse — the \
          emission is out of the fragment: {e}"

/-- THE ELABORATOR: analyze (pre-emission; every refusal fires here) →
    emit (the parse route). The reflection path stays ONE: the emitted
    structure carries the SAME `@[schema]` mount. -/
unsafe def elabTableImpl (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(command| table! $name:ident $[$ver?:ident]? where $[$clauses:tableClause]*) =>
      let spec ← analyze name ver? clauses
      for src in ← renderCommands spec do
        elabParsed spec.tnStr src
  | _ => Lean.Elab.throwUnsupportedSyntax

@[command_elab SchemaCore.Surface.tableCmd]
unsafe def elabTable : Lean.Elab.Command.CommandElab := elabTableImpl

end SchemaCore.Surface
