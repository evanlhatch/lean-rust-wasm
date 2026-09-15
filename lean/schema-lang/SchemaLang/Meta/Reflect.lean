/-
# SchemaLang.Meta.Reflect — `@[schema]`: native Lean types as the spec

The authoring surface is PLAIN Lean declarations. The attributes reflect
them at elaboration time into registry items — the author never writes
`Ty` or `Item` by hand. This is the buf model with the descriptor
produced by the compiler itself.

Reflection coverage (the four item kinds):
- `@[schema]` on a structure  → `Item.record`
- `@[schema]` on an inductive → `Item.variant` (payload-carrying ctors)
- `@[schema_fn]` on a def     → `Item.func` (the SIGNATURE is the spec;
                                 the body is irrelevant to emission).
                                 Optional ident arg sets the semantic
                                 fields (6.5.1): `@[schema_fn volatile]`,
                                 `@[schema_fn strict.volatile]`, …
- `@[schema_resource]` on a def/type → `Item.resource` (opaque handle)

Reifier scope (v1, honest limits):
- Scalars: Bool, UInt8..UInt64, Int8..Int64, Float32, Float — 1:1
- `String`, `ByteArray`, `List T`, `Option T`, `Sum T E` — recursive
- `Future T` / `Stream T` marker defs (authoring-module wrappers) →
  `.future` / `.stream` (WASI 0.3 async at the boundary)
- The head is ANOTHER `@[schema]` declaration → `.ty` ref
  (forward references fail — register the referenced type first)
- Everything else (Subtype, Nat, functions, opaque types) → a
  domain-voiced elaboration error enumerating the boundary fragment
- Parameterized inductives are rejected (v1): a parameterized inductive's
  ctors carry implicit binders the naive arg-walk would misread.

Registration: a `SimplePersistentEnvExtension` replayed from oleans at
import — the driver (`forge gen`) imports the demo module, reads the
environment, and the emitters see exactly what was registered.
-/

import Lean
import Qq
import CodegenCore
import SchemaLang.Item
import SchemaLang.Invariant
import SchemaLang.Update

namespace SchemaLang.Meta

open Lean
open Qq

/-- The registry: Lean declaration name ↦ schema item, append-only
    (the `CodegenCore.mkRegistryExt` semantics: append on add,
    concatenate on import — not a hand copy of them). -/
initialize schemaItemExt :
    SimplePersistentEnvExtension (Name × Item) (List (Name × Item)) ←
  CodegenCore.mkRegistryExt `schemaItemExt

/-- Registered items from an environment (the emitter entry point). -/
def registeredItems (env : Environment) : List (Name × Item) :=
  schemaItemExt.getState env

/-- Register one reflected item (the attribute handler's write path). -/
def registerSchemaItem (leanName : Name) (item : Item) : CoreM Unit :=
  modifyEnv fun env =>
    schemaItemExt.addEntry env (leanName, item)

/-! ## Provenance — doc strings for registered items (parallel registry)

The declaring Lean constant's doc string is stored in a SEPARATE
persistent extension, NOT on `Item` — `Item` is the closed boundary
universe, and a provenance field would poison its BEq/specEq/snapshot
surface (see `FuncSig.body` for the precedent, extended to all item
kinds). The extension is replayed from oleans at import, exactly like
`schemaItemExt`. -/

/-- Provenance extension: Lean declaration name ↦ doc string (the ONE
    doc string for the declaring constant). -/
initialize schemaItemDocsExt :
    SimplePersistentEnvExtension (Name × String) (List (Name × String)) ←
  CodegenCore.mkRegistryExt `schemaItemDocsExt

/-- All registered doc strings from an environment (the emitter entry
    point). -/
def registeredItemDocs (env : Environment) : List (Name × String) :=
  schemaItemDocsExt.getState env

/-- Look up the doc string for one declared schema item. Returns the
    empty string when no doc string was written (not all declarations
    carry one). -/
def itemDoc? (env : Environment) (leanName : Name) : String :=
  match (registeredItemDocs env).find? (fun (n, _) => n == leanName) with
  | some (_, doc) => doc
  | none => ""

/-- Register the doc string for one reflected item. Silent when the
    declaration carries no doc string. -/
def registerSchemaItemDoc (leanName : Name) : CoreM Unit := do
  let env ← getEnv
  let doc? ← liftM <| findDocString? env leanName
  if let some doc := doc? then
    modifyEnv fun env =>
      schemaItemDocsExt.addEntry env (leanName, doc)

/-- Provenance summary for ONE registered item: `"declName: docString"`
    (the first line of the doc string; empty when undocumented). The
    emitters (and the `#schema` debug command) may call this per item
    to annotate emitted artifacts with origins. -/
def provenanceOf (env : Environment) (leanName : Name) (_item : Item) : String :=
  let doc := itemDoc? env leanName
  let line := doc.splitOn "\n" |>.head? |>.getD "" |>.trimAscii
  if line.isEmpty then s!"{leanName}"
  else s!"{leanName}: {line}"

/-- The schema name for a reflected declaration (kebab at emission). -/
def schemaNameOf (leanName : Name) : String := leanName.toString

/-- The case name of a constructor: the inductive's full name stripped
    (`OrderError.invalidItem` → `invalidItem`; emission kebabs it).
    `splitOn` + `getLast!` is robust to namespaced ctors
    (`Foo.Role.admin` → `admin`). -/
def ctorNameOf (_declName ctor : Name) : String :=
  (String.splitOn ctor.toString ".").getLast!

/-- Already-registered schema names (dup detection + did-you-mean space). -/
def registeredNames (env : Environment) : List String :=
  (schemaItemExt.getState env).map (fun (_, item) => item.name)

/-- The registered name of a func parameter: the binder name with a
    leading `_` stripped. Authors underscore a stub body's dead binder
    (`def getUser (_id : UInt64) := …`) but the SPEC's param name is the
    written word (`id`) — the underscore is a Lean-body convention, not
    wire content. -/
def paramNameOf (name : Name) : String :=
  match String.dropPrefix? name.toString "_" with
  | some rest => (rest : String.Slice).toString
  | none => name.toString

/-- Partial reifier: a Lean type expression → schema `Ty`, when the type
    is in the boundary fragment. `env` resolves references to previously
    reflected declarations. -/
partial def tyOfExpr? (env : Environment) (e : Expr) : Option Ty :=
  let e := e.headBeta
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    match c, args with
    | ``Bool, #[] => some .bool
    | ``UInt8, #[] => some .u8
    | ``UInt16, #[] => some .u16
    | ``UInt32, #[] => some .u32
    | ``UInt64, #[] => some .u64
    | ``Int8, #[] => some .i8
    | ``Int16, #[] => some .i16
    | ``Int32, #[] => some .i32
    | ``Int64, #[] => some .i64
    | ``Float32, #[] => some .f32
    | ``Float, #[] => some .f64
    | ``String, #[] => some .string
    | ``ByteArray, #[] => some .bytes
    | ``Option, #[a] => .option <$> tyOfExpr? env a
    | ``List, #[a] => .list <$> tyOfExpr? env a
    | ``Sum, #[ok, err] =>
        match tyOfExpr? env ok, tyOfExpr? env err with
        | some o, some i => some (.result o i)
        | _, _ => none
    | _, #[a] =>
        -- the async marker wrappers (authoring-module defs matched by
        -- name; they cannot be quoted here because they live in the
        -- module that imports this one, and `Stream` collides with core)
        if c.toString == "Async.Future" then .future <$> tyOfExpr? env a
        else if c.toString == "Async.Stream" then .stream <$> tyOfExpr? env a
        else none
    | _, #[] =>
        -- a previously-reflected declaration (structure, variant, or
        -- resource): a named reference
        match (schemaItemExt.getState env).find? (fun (ln, _) => ln == c) with
        | some (_, item) => some (.ty item.name)
        | none => none
    | _, _ => none
  | _ => none

/-- The constructor's field types, in declaration order, EXCLUDING
    implicit binders (params of parameterized inductives). Flat
    structures: no subobject parents, no typeclass binders. -/
def ctorArgTypes : Expr → List Expr
  | .forallE _ d b bi =>
      if bi.isExplicit then d :: ctorArgTypes b else ctorArgTypes b
  | .letE _ _ _ b _ => ctorArgTypes b
  | _ => []

/-! ## Records — `@[schema]` on a structure -/

/-- Pure structural check: diagnostics or fields. NO monad — the
    generalization traps of CoreM do-blocks don't apply to a Sum. -/
def checkStruct (env : Environment) (declName : Name) :
    Sum (List SchemaDiag) (List Field) :=
  if !(Lean.isStructure env declName) then
    .inl [SchemaDiag.notAStructure declName.toString]
  else
    let fieldNames := Lean.getStructureFields env declName
    let ctor := Lean.getStructureCtor env declName
    match env.find? ctor.name with
    | none => .inl [SchemaDiag.noCtor declName.toString]
    | some (.ctorInfo ci) =>
      let tys := ctorArgTypes ci.type
      if tys.length != fieldNames.size then
        .inl [SchemaDiag.binderMismatch declName.toString]
      else
        let known := registeredNames env
        let step (acc : Sum (List SchemaDiag) (List Field)) (pair : Name × Expr) :=
          let (f, tE) := pair
          match acc with
          | .inl ds => .inl ds
          | .inr fields =>
            match checkSchemaIdent (s!"field of `{declName}`") f.toString with
            | ds@(_ :: _) => .inl ds
            | [] => match tyOfExpr? env tE with
              | some t => .inr (fields ++ [{ name := f.toString, ty := t }])
              | none => .inl [SchemaDiag.nonBoundaryType f.toString (toString tE)]
        let acc := (fieldNames.toList.zip tys).foldl step (.inr [])
        match acc with
        | .inl ds => .inl ds
        | .inr fields =>
          if known.contains (schemaNameOf declName) then
            .inl [SchemaDiag.dupName (schemaNameOf declName)]
          else .inr fields
    | _ => .inl [SchemaDiag.noCtor declName.toString]

/-- Register one reflected structure. -/
def registerSchemaStruct (declName : Name) : CoreM Unit := do
  let env ← getEnv
  match checkStruct env declName with
  | .inl ds => throwError ("@[schema] `" ++ declName.toString ++ "`: "
      ++ String.intercalate "; " (ds.map SchemaDiag.render))
  | .inr fields => do
    registerSchemaItem declName (.record (schemaNameOf declName) fields)
    registerSchemaItemDoc declName

/-! ## Variants — `@[schema]` on a non-parameterized inductive -/

/-- Pure inductive check: diagnostics or variant cases. v1 limits:
    non-parameterized only, each ctor with at most ONE payload arg
    (the WIT variant-case shape). -/
def checkInductive (env : Environment) (declName : Name) :
    Sum (List SchemaDiag) (List VariantCase) :=
  match env.find? declName with
  | some (.inductInfo ii) =>
      if ii.numParams != 0 then
        .inl [SchemaDiag.binderMismatch declName.toString]
      else
        let known := registeredNames env
        let step (acc : Sum (List SchemaDiag) (List VariantCase))
            (ctor : Name) : Sum (List SchemaDiag) (List VariantCase) :=
          let caseName := ctorNameOf declName ctor
          match acc with
          | .inl ds => .inl ds
          | .inr cases =>
            match checkSchemaIdent (s!"case of `{declName}`") caseName with
            | ds@(_ :: _) => .inl ds
            | [] =>
              match env.find? ctor with
              | none => .inl [SchemaDiag.noCtor caseName]
              | some (.ctorInfo ci) =>
                  match ctorArgTypes ci.type with
                  | [] => .inr (cases ++ [(caseName, none)])
                  | [t] =>
                      match tyOfExpr? env t with
                      | some ty => .inr (cases ++ [(caseName, some ty)])
                      | none => .inl [SchemaDiag.nonBoundaryType caseName (toString t)]
                  | _ => .inl [SchemaDiag.multiPayload caseName]
              | _ => .inl [SchemaDiag.noCtor caseName]
        let acc := ii.ctors.foldl step (.inr [])
        match acc with
        | .inl ds => .inl ds
        | .inr cases =>
          if known.contains (schemaNameOf declName) then
            .inl [SchemaDiag.dupName (schemaNameOf declName)]
          else .inr cases
  | _ => .inl [SchemaDiag.noCtor declName.toString]

/-- Register one reflected inductive as a variant. -/
def registerSchemaVariant (declName : Name) : CoreM Unit := do
  let env ← getEnv
  match checkInductive env declName with
  | .inl ds => throwError ("@[schema] `" ++ declName.toString ++ "`: "
      ++ String.intercalate "; " (ds.map SchemaDiag.render))
  | .inr cases => do
    registerSchemaItem declName (.variant (schemaNameOf declName) cases)
    registerSchemaItemDoc declName

/-- `@[schema]` — reflect a structure OR a non-parameterized inductive
    into the schema registry. -/
initialize registerBuiltinAttribute {
  name := `schema
  descr := "register a structure or inductive as a schema item (the boundary universe)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    let env ← getEnv
    if Lean.isStructure env decl then
      registerSchemaStruct decl
    else
      match env.find? decl with
      | some (.inductInfo _) => registerSchemaVariant decl
      | _ => throwError ("@[schema] supports structures and inductives only: `"
        ++ decl.toString ++ "`")
}

/-! ## Functions — `@[schema_fn]` on a def -/

/-- One optional attr-arg node → its ident name (present = the node
    wraps the ident at `[0]`; absent = `null`). -/
def optArgIdent? (stx : Syntax) : Except String (Option String) :=
  if stx.isNone then .ok none
  else if stx[0]!.isIdent then .ok (some stx[0]!.getId.toString)
  else .error s!"unexpected @[schema_fn] argument: {stx}"

/-- Parse the optional `@[schema_fn]` semantic args into a `FuncSem`
    (6.5.1). The builtin `simple` attr parser admits ONE optional
    ident — a dedicated two-ident attr parser was tried and is
    SHADOWED (`simple` wins every parse it can consume; there is no
    fallback across attr parsers), so all axes travel in ONE ident,
    dot-separated: `@[schema_fn volatile]` (determinism only),
    `@[schema_fn strict]` (nullSem only), `@[schema_fn
    strict.volatile]` (both, either order), `@[schema_fn stream]`
    (delivery), `@[schema_fn strict.volatile.stream]` (all three).
    Each part names a NullSem, Determinism, or Delivery ctor; unknown
    names, duplicated axes, and >3 parts are LOUD errors enumerating
    the valid space. -/
def funcSemOfStx (stx : Syntax) : Except String FuncSem := do
  let step (acc : Option NullSem × Option Determinism × Option Delivery) (name : String)
      : Except String (Option NullSem × Option Determinism × Option Delivery) :=
    let (nullSem?, det?, del?) := acc
    match name with
    | "strict" | "propagate" | "custom" =>
        if nullSem?.isSome then
          .error s!"duplicate nullSem argument `{name}` — one of strict, propagate, custom"
        else
          .ok (NullSem.ofToken? name, det?, del?)
    | "pure" | "stable" | "volatile" =>
        if det?.isSome then
          .error s!"duplicate determinism argument `{name}` — one of pure, stable, volatile"
        else
          .ok (nullSem?, Determinism.ofToken? name, del?)
    | "stream" | "once" =>
        if del?.isSome then
          .error s!"duplicate delivery argument `{name}` — one of stream, once"
        else
          .ok (nullSem?, det?, Delivery.ofToken? name)
    | other =>
        .error (s!"unknown @[schema_fn] argument `{other}` — valid: "
          ++ "strict, propagate, custom (nullSem); pure, stable, volatile (determinism); "
          ++ "stream, once (delivery)")
  -- `simple` shape: [name ident, one optional arg]; .missing =
  -- programmatic application (no args)
  let opts := match stx with
    | .missing => []
    | _ => stx.getArgs.toList.drop 1
  match opts.mapM optArgIdent? with
  | .error e => .error e
  | .ok idents =>
    let parts := (idents.filterMap id).flatMap (String.splitOn · ".")
    if parts.length > 3 then
      .error s!"too many @[schema_fn] arguments ({parts.length}) — at most one nullSem, one determinism, one delivery"
    else
      let init : Option NullSem × Option Determinism × Option Delivery := (none, none, none)
      match parts.foldlM (fun (acc : Option NullSem × Option Determinism × Option Delivery) name =>
          step acc name) init with
      | .error e => .error e
      | .ok (nullSem?, det?, del?) =>
          .ok { nullSem := nullSem?.getD .propagate
              , determinism := det?.getD .pure
              , delivery := del?.getD .once }

/-- Walk a def's type: gather the EXPLICIT binder (param) types and the
    return type. The signature is the spec; the body is never read. -/
def funcSignature (env : Environment) (declName : Name) :
    Except String FuncSig := do
  let di ← match env.find? declName with
    | some (.defnInfo di) => pure di
    | _ => throw ("`" ++ declName.toString ++ "` is not a def")
  let rec go (acc : List (String × Ty)) (t : Expr) : Except String FuncSig :=
    match t with
    | .forallE name d b bi =>
        if bi.isExplicit then
          match tyOfExpr? env d with
          | some ty => go (acc ++ [(paramNameOf name, ty)]) b
          | none => throw s!"param `{name}` has non-boundary type: {d}"
        else go acc b
    | _ =>
        match tyOfExpr? env t with
        | some ret => pure { name := schemaNameOf declName, params := acc, ret := ret
                           , body := declName }
        | none => throw s!"return type not in the boundary fragment: {t}"
  go [] di.type

/-- Register one reflected function signature, with its semantic
    contract fields (6.5.1). -/
def registerSchemaFunc (declName : Name) (sem : FuncSem := {}) : CoreM Unit := do
  let env ← getEnv
  match funcSignature env declName with
  | .error msg => throwError ("@[schema_fn] `" ++ declName.toString ++ "`: " ++ msg)
  | .ok sig => do
    registerSchemaItem declName (.func { sig with sem })
    registerSchemaItemDoc declName

/-- `@[schema_fn]` — reflect a function's SIGNATURE into the schema
    registry (params + return type; the body is not part of the spec).
    Optional ident args set the semantic fields (one ident, dot-joined
    for both axes — see `funcSemOfStx`): `@[schema_fn volatile]`,
    `@[schema_fn strict.volatile]`, … -/
initialize registerBuiltinAttribute {
  name := `schema_fn
  descr := "register a function signature as a schema func item"
  applicationTime := .afterCompilation
  add := fun decl stx _kind => do
    let sem ← match stx with
      | .missing => pure ({} : FuncSem)
      | _ => match funcSemOfStx stx with
        | .ok sem => pure sem
        | .error msg =>
            throwError ("@[schema_fn] `" ++ decl.toString ++ "`: " ++ msg)
    registerSchemaFunc decl sem
}

/-! ## Resources — `@[schema_resource]` on an opaque type -/

/-- Register one reflected resource (an opaque handle: the name is the
    schema content; there is nothing to check). -/
def registerSchemaResource (declName : Name) : CoreM Unit := do
  registerSchemaItem declName (.resource (schemaNameOf declName))
  registerSchemaItemDoc declName

/-- `@[schema_resource]` — register an opaque handle type as a schema
    resource item (its method surface arrives as `func` items referencing
    it in their first param). -/
initialize registerBuiltinAttribute {
  name := `schema_resource
  descr := "register an opaque type as a schema resource item"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (registerSchemaResource decl : CoreM Unit)
}

/-! ## Invariants — `schema_invariant <name> for <Record> := <term>`

The invariant registry is a SEPARATE extension (`invariantItemExt`) —
`Item` is the closed boundary universe and cannot carry the VExpr
family. The command elaborates the author's term against
`VExpr <the record's real fields> .bool` — the fields looked up from
`schemaItemExt` at elab time, so an unknown record is a did-you-mean
error and a misspelled COLUMN is the `HasCol` instance failure (the
same gate the validator tests pin). The tier is COMPUTED here: an
executable term alone registers `boundaryCheck`; the optional `proved
<thm>` clause cites a theorem name, RESOLVED at registration
(`SchemaLang.checkCitation?` — the `Dbsp.Certs.#check_cert` pattern:
missing, non-theorem, sorry-tainted, or wrong-shape citations fail
to elaborate).
-/

/-- The invariant registry: append-only, replayed from oleans at import
    (the `CodegenCore.mkRegistryExt` semantics — a SEPARATE extension
    because `Item` is the closed boundary universe and cannot carry the
    VExpr family). -/
initialize invariantItemExt :
    SimplePersistentEnvExtension InvariantItem (List InvariantItem) ←
  CodegenCore.mkRegistryExt `invariantItemExt

/-- The registered invariant rows (the emission entry point). -/
def registeredInvariants (env : Environment) : List InvariantItem :=
  invariantItemExt.getState env

/-- Registered invariant names (dup detection). -/
def registeredInvariantNames (env : Environment) : List String :=
  (registeredInvariants env).map (·.name)

/-! ## Typed-quotation helpers (Qq)

Every `q(...)` quotation takes its runtime data as BINDERS, never
let-bound or inline `toExpr` antiquotes: Qq's unquoter unfolds
let-values/definitions before checking for the `Quoted` type, so only
binder-position `Q(_)` variables survive (`unquoteExpr: ... : Expr`
otherwise). The plain wrappers then fill the binders with `toExpr`
casts — sound because the `ToExpr` instances emit literal denotations. -/

/-- `Ty` → its constructor tree as a TYPED quotation (the
    expected-type builder: the command elaborates the author's term
    against `VExpr <the record's real fields> .bool`). The `Q(Ty)`
    ascription is sound: the `ToExpr Ty` instance (Ty.lean) emits the
    literal denotation. -/
def tyToExpr (t : Ty) : Q(Ty) :=
  toExpr t

/-- One field → the `Field.mk` application (the binder-discipline
    quotation; see the section note). -/
def fieldToExprQ (n : Q(String)) (t : Q(Ty)) : Q(Field) :=
  q(Field.mk $n $t)

/-- One field → the `Field.mk` application (the GADT's index term),
    as a typed quotation. -/
def fieldToExpr (f : Field) : Q(Field) :=
  fieldToExprQ (toExpr f.name) (tyToExpr f.ty)

/-- The empty field list (the fold's seed; binder discipline). -/
def fieldsNilQ : Q(List Field) := q([])

/-- `cons` on the field-list literal (binder discipline). -/
def fieldsConsQ (f : Q(Field)) (fs : Q(List Field)) : Q(List Field) :=
  q($f :: $fs)

/-- The record's fields as a `List Field` literal term — the index the
    expected type carries, so the `HasCol` instance search walks the
    REAL schema (a misspelled column fails instance search). Pure Qq
    fold (was `Meta.mkListLit`). -/
def fieldsToExpr (fields : List Field) : Q(List Field) :=
  fields.foldr (fun f acc => fieldsConsQ (fieldToExpr f) acc) fieldsNilQ

/-- `VExpr <fields> .bool` as a type quotation. -/
def vexprBoolTyQ (fsList : Q(List Field)) : Q(Type) :=
  q(VExpr $fsList Ty.bool)

/-- `VExpr <fields> <ty>` as a type quotation. -/
def vexprTyQ (fsList : Q(List Field)) (t : Q(Ty)) : Q(Type) :=
  q(VExpr $fsList $t)

/-- `ColPath <name> <ty> <fields>` as a type quotation. -/
def colPathTyQ (fsList : Q(List Field)) (n : Q(String)) (t : Q(Ty)) : Q(Type) :=
  q(ColPath $n $t $fsList)

/-- The `UpdatePure` instance TYPE for a registered update, as a typed
    quotation. The projections `($fQ).ty`/`($fQ).name` (not separate
    antiquotes) keep the quotation elaborator's indices SHARED with the
    `fQ` binder — opaque per-piece antiquotes would not unify against
    `UpdateItem.mk`'s signature. -/
def updatePureInstTyQ (fsList : Q(List Field)) (fQ : Q(Field))
    (unameQ : Q(String)) (g : Q(VExpr $fsList Ty.bool))
    (e : Q(VExpr $fsList ($fQ).ty))
    (path : Q(ColPath ($fQ).name ($fQ).ty $fsList)) : Q(Prop) :=
  q(UpdatePure $fsList $fQ
    (UpdateItem.mk (fs := $fsList) (f := $fQ) $unameQ $g $e $path []))

/-- The instance PROOF: `UpdatePure.emptyScan`'s `rfl` reduces on the
    literal `[]` scan result with the binders still abstract (a raw
    `⟨rfl⟩` inside a quotation sees opaque antiquotes and cannot
    reduce — the named lemma is the Qq-compatible discharge). -/
def updatePureInstPfQ (fsList : Q(List Field)) (fQ : Q(Field))
    (unameQ : Q(String)) (g : Q(VExpr $fsList Ty.bool))
    (e : Q(VExpr $fsList ($fQ).ty))
    (path : Q(ColPath ($fQ).name ($fQ).ty $fsList)) :
    Q(UpdatePure $fsList $fQ
      (UpdateItem.mk (fs := $fsList) (f := $fQ) $unameQ $g $e $path [])) :=
  q(UpdatePure.emptyScan)

/-- The invariant's NAME may be an ident OR a string literal: the registry
names are kebab (`id-positive`) — the emitted Rust's fn suffix and the
emitted comment carry them verbatim — but a kebab word is not a Lean
ident. The string form is the authoring surface for those; the ident
form stays for Lean-friendly names.

`schema_invariant <name> for <Record> (proved <thm>)? := <term>` —
    elaborate the predicate against the registered record's fields,
    register the `InvariantItem` (tier computed per `tierOf`). -/
syntax (name := schemaInvariant) "schema_invariant " (ident <|> str)
  " for " ident (" proved " ident)? " := " term : command

open Lean Elab Command Term in
@[command_elab SchemaLang.Meta.schemaInvariant]
unsafe def elabSchemaInvariant : CommandElab := fun (stx : Syntax) => do
  -- the name: ident OR string literal (the kebab registry names are
  -- not Lean idents — see the syntax note above)
  let invName : String :=
    match stx[1]!.isStrLit? with
    | some s => s
    | none => stx[1]!.getId.toString
  let recId := stx[3]!.getId
  let proofName? : Option Name :=
    let opt : Syntax := stx[4]!
    if opt.isNone then none else some opt[1]!.getId
  let env ← getEnv
  -- the record: a registered `Item.record`, or a did-you-mean error
  -- over the registered RECORD names (variants/resources cannot take
  -- field-indexed invariants)
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
        throwError s!"schema_invariant `{invName}`: `{recId}` is not a registered record{hint}"
  if (registeredInvariantNames env).contains invName then
    throwError s!"schema_invariant `{invName}`: duplicate invariant name"
  -- the predicate: elaborated against `VExpr <fields> .bool`, then
  -- evaluated to the GADT value (the emitter compiles the VALUE)
  let (exprTerm, inv) : Expr × SchemaInvariant ← liftTermElabM do
    let fsList := fieldsToExpr fields
    let expectedFs : Q(Type) := q(List Field)
    let expected : Expr := vexprBoolTyQ fsList
    let e ← elabTerm stx[6]! (some expected)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwError s!"schema_invariant `{invName}`: unresolved metavariables in the predicate"
    let fsVal : List Field ← Meta.evalExpr (List Field) expectedFs fsList
    let ev : VExpr fsVal .bool ← Meta.evalExpr (VExpr fsVal .bool) expected e
    pure (e, { fields := fsVal, expr := ev })
  -- THE PROVED-TIER CITATION GATE (the wire — `SchemaLang.checkCitation?`,
  -- the `Dbsp.Certs.#check_cert` pattern): a `proved <thm>` citation must
  -- resolve HERE — missing, non-theorem, sorry-tainted, or wrong-shape
  -- citations are ELABORATION errors (the stored-but-unchecked hole is
  -- closed; formerly "resolution is CI's job later").
  if let some pn := proofName? then
    liftTermElabM do
      let env' ← getEnv
      let fsListE := fieldsToExpr fields
      match ← checkCitation? env' fsListE exprTerm pn with
      | some d => throwError s!"schema_invariant `{invName}`: {d}"
      | none => pure ()
  modifyEnv fun env =>
    invariantItemExt.addEntry env
      { name := invName, schemaRef := recordName, tier := tierOf proofName?
      , proofName := proofName?, inv := inv, exprTerm := exprTerm }

/-! ## Updates — `schema_update <name> for <Record> set <col> := <value> where <guard>`

The update registry is a SEPARATE extension (`updateItemExt`) over
`SomeUpdate` (SchemaLang.Update — imported above, NOT moved: the core is
owned elsewhere; importing keeps one definition). `Item` is the closed
boundary universe and cannot carry the `VExpr` family — the same reason
invariants got their own extension.

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

/-- The registry-state inhabitant (the `InvariantItem` default's
    pattern): SOME GADT shape must witness the type; the empty-schema
    shape is unreachable for a `ColPath`, so the witness is the
    one-field u64 schema. No registered row takes this shape. Defined
    BEFORE the extension (the `mkRegistryExt` seed). -/
instance : Inhabited SomeUpdate :=
  ⟨{ fields := [{ name := "", ty := .u64 }]
   , field := { name := "", ty := .u64 }
   , update := { name := "", guard := .gt (.lit 0) (.lit 0)
               , value := .lit 0, writePath := .here } }⟩

/-- The update registry: append-only, replayed from oleans at import
    (the `CodegenCore.mkRegistryExt` semantics — a SEPARATE extension
    because `Item` cannot carry the VExpr family). -/
initialize updateItemExt :
    SimplePersistentEnvExtension SomeUpdate (List SomeUpdate) ←
  CodegenCore.mkRegistryExt `updateItemExt

/-- The registered update rows (the emission entry point). -/
def registeredUpdates (env : Environment) : List SomeUpdate :=
  updateItemExt.getState env

/-- Registered update names (dup detection). -/
def registeredUpdateNames (env : Environment) : List String :=
  (registeredUpdates env).map (fun u => u.update.name)

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

-- `schema_update <name> for <Record> <col> := <valueTerm>
--    where <guardTerm>` — the `where` clause is REQUIRED (no
-- literal-true in `VExpr .bool`; see the section header). The `set`
-- position is marked by `:=` alone — NOT by a `set` token: declaring
-- `" set "` in a syntax RESERVES the word globally (the lexer makes it
-- a keyword everywhere — identifiers named `set` stop parsing; the
-- WasmBackend do-block casualty that taught this trap, the `prefix`
-- lesson's class). Never declare common words as syntax tokens.
syntax (name := schemaUpdate) "schema_update " ident " for " ident
  ident " := " term " where " term : command

open Lean Elab Command Term in
@[command_elab SchemaLang.Meta.schemaUpdate]
unsafe def elabSchemaUpdate : CommandElab := fun (stx : Syntax) => do
  let uname := stx[1]!.getId.toString
  let recId := stx[3]!.getId
  -- the syntax layout ("set" dropped — the reserved-word trap): [4]=col,
  -- [5]=":=", [6]=value, [7]="where", [8]=guard
  let colId := stx[4]!.getId.toString
  let valueStx := stx[6]!
  let guardStx := stx[8]!
  let env ← getEnv
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
  -- the written FIELD, looked up by NAME: a misspelled column is a
  -- did-you-mean error (louder than the bare `HasCol` instance miss)
  let fieldNames := fields.map (·.name)
  let fVal : Field ←
    match fields.find? (fun fl => fl.name == colId) with
    | some f => pure f
    | none =>
        let cands := CodegenCore.didYouMean colId fieldNames
        let hint := if cands.isEmpty then ""
          else s!" — did you mean: {String.intercalate ", " cands}?"
        throwError s!"schema_update `{uname}`: `{colId}` is not a column of `{recordName}`{hint}"
  if (registeredUpdateNames env).contains uname then
    throwError s!"schema_update `{uname}`: duplicate update name"
  -- elaborate guard + value against the REAL fields, evaluate the GADT
  -- values, resolve the write path (the `VExpr.colOf` route, its `.col`
  -- path extracted) — all data by the time it registers
  let (row, instName, instTy, instVal) ← liftTermElabM do
    let fsList := fieldsToExpr fields
    let expectedFs : Q(Type) := q(List Field)
    let fsVal : List Field ← Meta.evalExpr (List Field) expectedFs fsList
    -- the value: against `VExpr <fields> f.ty` — the FIELD's OWN TYPE
    -- is the type gate (a u64 expr on a string column fails here)
    let expectedValue : Expr := vexprTyQ fsList (tyToExpr fVal.ty)
    let e ← elabTerm valueStx (some expectedValue)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- the TYPE GATE, stated loud: the value expression's `Ty` index must
    -- BE the written field's own type (a u64 expr on a string column
    -- fails HERE, with the two types named — the did-you-mean grade)
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
    -- the guard: against `VExpr <fields> .bool`
    let expectedGuard : Expr := vexprBoolTyQ fsList
    let g ← elabTerm guardStx (some expectedGuard)
    Term.synthesizeSyntheticMVarsNoPostponing
    let g ← instantiateMVars g
    if g.hasExprMVar then
      throwError s!"schema_update `{uname}`: unresolved metavariables in the guard"
    let guardVal : VExpr fsVal .bool ← Meta.evalExpr (VExpr fsVal .bool) expectedGuard g
    -- the DETERMINISM GATE (the armed `volatileInPureContext` diag's
    -- firing site): the value and guard terms may reference REGISTERED
    -- schema functions; a volatile one in this pure-context lane fails
    -- elaboration, naming the fn and the update. The scan is the
    -- post-elaboration constant walk of BOTH terms (`volatileSchemaFns`).
    let volatileHits :=
      (volatileSchemaFns env e ++ volatileSchemaFns env g).eraseDups
    unless volatileHits.isEmpty do
      throwError s!"schema_update `{uname}`: " ++
        String.intercalate "; " (volatileHits.map fun fn =>
          SchemaDiag.render (.volatileInPureContext fn s!"schema_update {uname}"))
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
    -- THE COMPOSABLE LOCK (the second layer — the scan above stays
    -- the first): the scan's decided fact is discharged as a PROOF.
    -- The command EMITS the `UpdatePure` instance for the registered
    -- update; its proof is `rfl` against the STORED `volatileRefs`
    -- data — if the gate ever stored a nonempty scan, this `rfl`
    -- FAILS to elaborate (the proof checks the gate). Downstream,
    -- `UpdateItem.cascade2` assembles legality by instance search —
    -- no re-scan at the consumer.
    -- the instance assembly, fully typed (Qq): the elaborated terms
    -- are passed to the typed-quotation helpers with their CHECKED
    -- types (the `VExpr`/`ColPath` gates above) — the `Q(_)` casts are
    -- `implicit_reducible` defeq, sound by the gates. The proof is
    -- `UpdatePure.emptyScan`, discharging `rfl` against the literal
    -- `[]` scan result — the kernel checks the gate (was: raw `mkAppN`
    -- assembly + runtime `elabTerm` of `⟨rfl⟩` + an "internal:
    -- unresolved metavariables" guard, all dead now that the instance
    -- is typed at construction)
    let instTy : Expr :=
      updatePureInstTyQ fsList (fieldToExpr fVal) (toExpr uname) g e pathE
    let pf : Expr :=
      updatePureInstPfQ fsList (fieldToExpr fVal) (toExpr uname) g e pathE
    pure ({ fields := fsVal, field := fVal
          , update := { name := uname, guard := guardVal
                      , value := valueVal, writePath := pathVal
                      , volatileRefs := volatileHits } : SomeUpdate },
      ((`SchemaLang).str "instUpdatePure").str uname, instTy, pf)
  modifyEnv fun env =>
    updateItemExt.addEntry env row
  -- the instance: a def with the instance attribute (4.33's `Declaration`
  -- has no `instanceDecl` constructor — the `instance` command's own
  -- route is defn + addInstance)
  -- KNOWN FALSE POSITIVE: `warn.classDefReducibility` flags these
  -- (`instUpdatePure.*` — Demo/Tests) as "semireducible" EVEN THOUGH the
  -- hints ARE `.abbrev` — the linter reads only attribute-site
  -- declarations, not the addDecl route. Accepted (documented), NOT
  -- silenced: `set_option ... false` would trip the noLinterDisable
  -- lint, and the instances resolve fine (the consumers prove it).
  liftTermElabM do
    Lean.addDecl (Declaration.defnDecl {
      name := instName, levelParams := [], type := instTy
      , value := instVal, hints := Lean.ReducibilityHints.abbrev
      , safety := Lean.DefinitionSafety.safe })
    Lean.Meta.addInstance instName .global 1000

end SchemaLang.Meta

/- The async boundary markers (WASI 0.3): the ONE copy. The reifier
    (`tyOfExpr?`) matches these BY NAME - do not move into a namespace. -/
namespace Async
def Future (a : Type) : Type := a
/- Same marker shape as `Future` (the boundary marker pair). -/
def Stream (a : Type) : Type := Future a
end Async
