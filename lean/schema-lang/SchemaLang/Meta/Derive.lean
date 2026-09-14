/-
# SchemaLang.Meta.Derive — elab-time derivations from the registry

The shift-left module: anything that used to be hand-mirrored and
tie-checked at TEST time (`Faults.Spec.knownTypes`, `GuestImpl.
orderErrorCases`) is DERIVED here, at elaboration, from the registry
env extension. A wrong mirror is now UNWRITABLE, not a red suite.

The registry is a `SimplePersistentEnvExtension` — populated by the
`@[schema]` handlers as they elaborate, and PERSISTED across imports
(concatenate-on-import). So any module that imports the schema module
can read it HERE, at its own elaboration time, via `registeredItems`.

Ownership: schema-lang owns this file. Consumers: std (the derived
`orderErrorCases`), faults (the derived `knownTypes`). The runtime
tie-checks stay as regression controls (derived = derived now; the
negative controls keep them honest).
-/

import Lean
import SchemaLang.Meta.Reflect
import CodegenCore.Emit.Core

namespace SchemaLang.Meta

open Lean Elab Command

/-! ## Registry lookups (elab-time) -/

/-- The registered item for a Lean declaration name, if any. -/
def registeredItem? (env : Environment) (declName : Name) : Option Item :=
  (registeredItems env).find? (fun (ln, _) => ln == declName) |>.map (·.2)

/-- The registered VARIANT item for a Lean inductive name; a
    record/func/resource there is a wrong-kind reference. -/
def registeredVariant? (env : Environment) (declName : Name) :
    Except String (List VariantCase) :=
  match registeredItem? env declName with
  | some (.variant _ cases) => .ok cases
  | some it =>
      .error s!"`{declName}` is registered as `{it.name}`, not a variant"
  | none =>
      let cands := didYouMean declName.toString (registeredNames env)
      let hint := match cands with
        | [] => ""
        | cs => " — did you mean: " ++ String.intercalate ", " cs ++ "?"
      .error (s!"no schema item registered for `{declName}`" ++ hint)

/-! ## The term builders (the emitted literals, kebab-cased) -/

def tyTerm : Ty → CommandElabM Term
  | .bool => `(.bool) | .u8 => `(.u8) | .u16 => `(.u16) | .u32 => `(.u32)
  | .u64 => `(.u64) | .i8 => `(.i8) | .i16 => `(.i16) | .i32 => `(.i32)
  | .i64 => `(.i64) | .f32 => `(.f32) | .f64 => `(.f64)
  | .string => `(.string) | .bytes => `(.bytes)
  | .option a => do `(.option $(← tyTerm a))
  | .result o e => do `(.result $(← tyTerm o) $(← tyTerm e))
  | .list a => do `(.list $(← tyTerm a))
  | .tensor dims a => do
      let ds : Array Term := (dims.map (fun d => (⟨Syntax.mkNatLit d⟩ : Term))).toArray
      `(.tensor ([$ds,*] : List Nat) $(← tyTerm a))
  | .future a => do `(.future $(← tyTerm a))
  | .stream a => do `(.stream $(← tyTerm a))
  | .ty n => `(.ty $(quote n))

def variantCaseTerm : String × Option Ty → CommandElabM Term
  | (c, none) => `(( $(quote (CodegenCore.Emit.kebab c)), none ))
  | (c, some t) => do `(( $(quote (CodegenCore.Emit.kebab c)), some $(← tyTerm t) ))

def variantCasesTerm (cases : List VariantCase) : CommandElabM Term :=
  match cases with
  | [] => `([])
  | c :: rest => do
      let head ← variantCaseTerm c
      let tail ← variantCasesTerm rest
      `($head :: $tail)

/-! ## The derivations (commands) -/

/-- `derive_variant_cases targetName from InductiveName` — define
    `targetName : List SchemaLang.VariantCase` from the registry's
    registered variant, kebab-cased (the emitted spelling). Elaboration
    error (did-you-mean included) when the name is unregistered or not
    a variant: the mirror cannot drift because it is not written. -/
syntax (name := deriveVariantCases) "derive_variant_cases " ident " from " ident : command

@[command_elab deriveVariantCases]
def deriveVariantCasesImpl : CommandElab := fun stx => do
  let target := stx[1].getId
  let declName := stx[3].getId
  match registeredVariant? (← getEnv) declName with
  | .error msg => throwError msg
  | .ok cases =>
    let term ← variantCasesTerm cases
    elabCommand (← `(abbrev $(mkIdent target) : List SchemaLang.VariantCase := $term))

/-- `derive_schema_type_names targetName` — define `targetName : List
    String` from the registry's type-position items (records +
    variants — `Item.typeNames`' exact fold, snapshotted at elab). -/
syntax (name := deriveTypeNames) "derive_schema_type_names " ident : command

@[command_elab deriveTypeNames]
def deriveTypeNamesImpl : CommandElab := fun stx => do
  let target := stx[1].getId
  let names := Item.typeNames ((registeredItems (← getEnv)).map (·.2))
  let term : Term := quote names
  elabCommand (← `(abbrev $(mkIdent target) : List String := $term))

end SchemaLang.Meta
