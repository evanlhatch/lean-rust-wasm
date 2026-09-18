/-
# SchemaLang.Meta.Register.Provenance — doc strings + naming + reifier

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the provenance
registry (`schemaItemDocsExt`), the schema/ctor/param naming helpers,
and the partial reifier (`tyOfExpr?`) + `ctorArgTypes`.
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

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Provenance — doc strings for registered items (parallel registry)

The declaring Lean constant's doc string is stored in a SEPARATE
persistent extension, NOT on `Item` — `Item` is the closed boundary
universe, and a provenance field would poison its BEq/specEq/snapshot
surface (`FuncSig.body`'s precedent, extended to all item kinds). -/

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

end SchemaLang.Meta

end -- public meta section
