/-
# SchemaLang.Meta.Reflect — `@[schema]`: native Lean structures as the spec

The authoring surface is PLAIN Lean structures. The `@[schema]`
attribute reflects them at elaboration time into registry items — the
author never writes `Ty` or `Item` by hand. This is the buf model with
the descriptor produced by the compiler itself.

Reifier scope (v1, honest limits):
- Scalars: Bool, UInt8..UInt64, Int8..Int64, Float32, Float — 1:1
- `String`, `ByteArray`, `List T`, `Option T`, `Sum T E` — recursive
- Fields whose head is ANOTHER `@[schema]` structure → `.ty` ref
  (forward references fail — register the referenced structure first)
- Everything else (Subtype, Nat, functions, opaque types) → a
  domain-voiced elaboration error enumerating the boundary fragment
- Inductives (variants) and funcs: pending — spec-as-data for now
- Flat structures only: no parent-structure subobjects, no typeclass
  fields (getStructureFields order must match ctor binder order)

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

/-- The schema name for a reflected structure (kebab at emission). -/
def schemaNameOf (leanName : Name) : String := leanName.toString

/-- Partial reifier: a Lean type expression → schema `Ty`, when the type
    is in the boundary fragment. `env` resolves references to previously
    reflected structures. -/
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
    | _, #[] =>
        -- a previously-reflected schema structure: a named reference
        match (schemaItemExt.getState env).find? (fun (ln, _) => ln == c) with
        | some (_, item) => some (.ty item.name)
        | none => none
    | _, _ => none
  | _ => none

/-- The boundary fragment, enumerated (the error IS the documentation). -/
def boundaryFragment : String :=
  "boundary types are: Bool, UInt8..UInt64, Int8..Int64, Float32, Float, "
    ++ "String, ByteArray, List, Option, Sum (as result), "
    ++ "or another `@[schema]` structure"

/-- The constructor's field types, in declaration order (flat
    structures: no subobject parents, no typeclass binders). -/
def ctorFieldTypes : Expr → List Expr
  | .forallE _ d b _ => d :: ctorFieldTypes b
  | .letE _ _ _ b _ => ctorFieldTypes b
  | _ => []

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
      let tys := ctorFieldTypes ci.type
      if tys.length != fieldNames.size then
        .inl [SchemaDiag.binderMismatch declName.toString]
      else
        let known := (schemaItemExt.getState env).map (fun (_, item) => item.name)
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
          let ns := (schemaItemExt.getState env).map (fun (_, item) => item.name)
          if ns.contains (schemaNameOf declName) then
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

/-- `@[schema]` — reflect a structure into the schema registry. -/
initialize registerBuiltinAttribute {
  name := `schema
  descr := "register a structure as a schema item (the boundary universe)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (registerSchemaStruct decl : CoreM Unit)
}

end SchemaLang.Meta
