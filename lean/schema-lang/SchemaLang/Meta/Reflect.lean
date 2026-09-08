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
                                 the body is irrelevant to emission)
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
import SchemaLang.Item

namespace SchemaLang.Meta

open Lean

/-- The registry: Lean declaration name ↦ schema item, append-only. -/
initialize schemaItemExt :
    SimplePersistentEnvExtension (Name × Item) (List (Name × Item)) ←
  registerSimplePersistentEnvExtension {
    name := `schemaItemExt
    addEntryFn := fun xs x => xs ++ [x]
    addImportedFn := fun ess => ess.foldl (fun acc arr => acc ++ arr.toList) []
  }

/-- Registered items from an environment (the emitter entry point). -/
def registeredItems (env : Environment) : List (Name × Item) :=
  schemaItemExt.getState env

/-- Register one reflected item (the attribute handler's write path). -/
def registerSchemaItem (leanName : Name) (item : Item) : CoreM Unit :=
  modifyEnv fun env =>
    schemaItemExt.addEntry env (leanName, item)

/-- The schema name for a reflected declaration (kebab at emission). -/
def schemaNameOf (leanName : Name) : String := leanName.toString

/-- The case name of a constructor: the inductive's full name stripped
    (`OrderError.invalidItem` → `invalidItem`; emission kebabs it).
    `splitOn` + `getLast!` is robust to namespaced ctors
    (`Foo.Role.admin` → `admin`). -/
def ctorNameOf (declName ctor : Name) : String :=
  (String.splitOn ctor.toString ".").getLast!

/-- Already-registered schema names (dup detection + did-you-mean space). -/
def registeredNames (env : Environment) : List String :=
  (schemaItemExt.getState env).map (fun (_, item) => item.name)

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

/-- The boundary fragment, enumerated (the error IS the documentation). -/
def boundaryFragment : String :=
  "boundary types are: Bool, UInt8..UInt64, Int8..Int64, Float32, Float, "
    ++ "String, ByteArray, List, Option, Sum (as result),"
    ++ " Async.Future, Async.Stream, or another `@[schema]` declaration"

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
            match tyOfExpr? env tE with
            | some t => .inr (fields ++ [{ name := f.toString, ty := t }])
            | none => .inl [SchemaDiag.unknownRef f.toString
                               (didYouMean f.toString known) known]
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
  | .inr fields => registerSchemaItem declName (.record (schemaNameOf declName) fields)

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
            match env.find? ctor with
            | none => .inl [SchemaDiag.noCtor caseName]
            | some (.ctorInfo ci) =>
                match ctorArgTypes ci.type with
                | [] => .inr (cases ++ [(caseName, none)])
                | [t] =>
                    match tyOfExpr? env t with
                    | some ty => .inr (cases ++ [(caseName, some ty)])
                    | none => .inl [SchemaDiag.unknownRef caseName
                                     (didYouMean caseName known) known]
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
  | .inr cases => registerSchemaItem declName (.variant (schemaNameOf declName) cases)

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
          | some ty => go (acc ++ [(name.stripPrefix "_".toList |>.getD name.toString, ty)]) b
          | none => throw s!"param `{name}` has non-boundary type: {d}"
        else go acc b
    | _ =>
        match tyOfExpr? env t with
        | some ret => pure { name := schemaNameOf declName, params := acc, ret := ret }
        | none => throw s!"return type not in the boundary fragment: {t}"
  go [] di.type

/-- Register one reflected function signature. -/
def registerSchemaFunc (declName : Name) : CoreM Unit := do
  let env ← getEnv
  match funcSignature env declName with
  | .error msg => throwError ("@[schema_fn] `" ++ declName.toString ++ "`: " ++ msg)
  | .ok sig => registerSchemaItem declName (.func sig)

/-- `@[schema_fn]` — reflect a function's SIGNATURE into the schema
    registry (params + return type; the body is not part of the spec). -/
initialize registerBuiltinAttribute {
  name := `schema_fn
  descr := "register a function signature as a schema func item"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (registerSchemaFunc decl : CoreM Unit)
}

/-! ## Resources — `@[schema_resource]` on an opaque type -/

/-- Register one reflected resource (an opaque handle: the name is the
    schema content; there is nothing to check). -/
def registerSchemaResource (declName : Name) : CoreM Unit :=
  registerSchemaItem declName (.resource (schemaNameOf declName))

/-- `@[schema_resource]` — register an opaque handle type as a schema
    resource item (its method surface arrives as `func` items referencing
    it in their first param). -/
initialize registerBuiltinAttribute {
  name := `schema_resource
  descr := "register an opaque type as a schema resource item"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (registerSchemaResource decl : CoreM Unit)
}

end SchemaLang.Meta
