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
`orderErrorCases`, `userSchema`/`userRow`), faults (the derived
`knownTypes`), Demo + feature-flags (the derived record fields + row
builders). The runtime tie-checks stay as regression controls
(derived = derived now; the negative controls keep them honest).
-/

module

public import Lean
public import SchemaLang.Meta.Reflect
public import CodegenCore.Emit.Core
public import CodegenCore.DidYouMean

public meta section

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
      let cands := CodegenCore.didYouMean declName.toString (registeredNames env)
      let hint := match cands with
        | [] => ""
        | cs => " — did you mean: " ++ String.intercalate ", " cs ++ "?"
      .error (s!"no schema item registered for `{declName}`" ++ hint)

/-- The registered RECORD item's fields for a Lean structure name; a
    variant/func/resource there is a wrong-kind reference. The
    did-you-mean pool is the registered records' LEAN names (the
    lookup key space). -/
def registeredRecord? (env : Environment) (declName : Name) :
    Except String (List Field) :=
  match registeredItem? env declName with
  | some (.record _ fields) => .ok fields
  | some it =>
      .error s!"`{declName}` is registered as `{it.name}`, not a record"
  | none =>
      let recordNames := (registeredItems env).filterMap fun (ln, it) =>
        match it with | .record _ _ => some ln.toString | _ => none
      let cands := CodegenCore.didYouMean declName.toString recordNames
      let hint := match cands with
        | [] => ""
        | cs => " — did you mean: " ++ String.intercalate ", " cs ++ "?"
      .error (s!"no schema record registered for `{declName}`" ++ hint)

/-! ## The term builders (the emitted literals, kebab-cased) -/

/-- THE `KeyTy` reifier at TERM level — the one walker, shared by
    every consumer (the derive commands, `Meta.Gen`,
    `Meta.EntityMachine`, the faults registry). The Expr-level core is
    the `ToExpr Ty` instance in `SchemaLang.Ty`; the drift-pin below
    makes the two agree. Fully `SchemaLang.`-qualified: generated text
    must not depend on the consumer's `open`s (the EntityMachine
    rule). A new `KeyTy` ctor extends THIS match or the build
    fails. -/
def keyTerm : KeyTy → CommandElabM Term
  | .bool => `(term| SchemaLang.KeyTy.bool)
  | .u8 => `(term| SchemaLang.KeyTy.u8)
  | .u16 => `(term| SchemaLang.KeyTy.u16)
  | .u32 => `(term| SchemaLang.KeyTy.u32)
  | .u64 => `(term| SchemaLang.KeyTy.u64)
  | .i8 => `(term| SchemaLang.KeyTy.i8)
  | .i16 => `(term| SchemaLang.KeyTy.i16)
  | .i32 => `(term| SchemaLang.KeyTy.i32)
  | .i64 => `(term| SchemaLang.KeyTy.i64)
  | .string => `(term| SchemaLang.KeyTy.string)

/-- THE `Ty` reifier at TERM level — the one walker, shared by every
    consumer (the derive commands, `Meta.Gen`, `Meta.EntityMachine`,
    the faults registry). The Expr-level core is the `ToExpr Ty`
    instance in `SchemaLang.Ty`; the drift-pin below makes the two
    agree on the full vocabulary. Fully `SchemaLang.`-qualified:
    generated text must not depend on the consumer's `open`s (the
    EntityMachine rule). A new `Ty` ctor extends THIS match or the
    build fails. -/
def tyTerm : Ty → CommandElabM Term
  | .bool => `(term| SchemaLang.Ty.bool)
  | .u8 => `(term| SchemaLang.Ty.u8)
  | .u16 => `(term| SchemaLang.Ty.u16)
  | .u32 => `(term| SchemaLang.Ty.u32)
  | .u64 => `(term| SchemaLang.Ty.u64)
  | .i8 => `(term| SchemaLang.Ty.i8)
  | .i16 => `(term| SchemaLang.Ty.i16)
  | .i32 => `(term| SchemaLang.Ty.i32)
  | .i64 => `(term| SchemaLang.Ty.i64)
  | .f32 => `(term| SchemaLang.Ty.f32)
  | .f64 => `(term| SchemaLang.Ty.f64)
  | .string => `(term| SchemaLang.Ty.string)
  | .bytes => `(term| SchemaLang.Ty.bytes)
  | .option a => do `(term| SchemaLang.Ty.option $(← tyTerm a))
  | .result o e =>
      do `(term| SchemaLang.Ty.result $(← tyTerm o) $(← tyTerm e))
  | .list a => do `(term| SchemaLang.Ty.list $(← tyTerm a))
  | .map k v =>
      do `(term| SchemaLang.Ty.map $(← keyTerm k) $(← tyTerm v))
  | .set k => do `(term| SchemaLang.Ty.set $(← keyTerm k))
  | .tensor dims a => do
      -- the dims as RAW nat literals (the `Syntax.mkNatLit` form —
      -- `quote` would elaborate to `OfNat.ofNat … instOfNatNat`, a
      -- different Expr shape than `ToExpr Ty`'s `.lit`; the drift-pin
      -- below enforces the literal form)
      let ds : Array Term :=
        (dims.map fun d => (⟨Syntax.mkNatLit d⟩ : Term)).toArray
      `(term| SchemaLang.Ty.tensor ([$ds,*] : List Nat) $(← tyTerm a))
  | .future a => do `(term| SchemaLang.Ty.future $(← tyTerm a))
  | .stream a => do `(term| SchemaLang.Ty.stream $(← tyTerm a))
  | .ty n => `(term| SchemaLang.Ty.ty $(quote n))

/-! ## The drift-class pin (the consolidation's evidence)

`tyTerm`/`keyTerm` (Term level) and `ToExpr Ty` (Expr level,
`SchemaLang.Ty`) are walks over ONE universe; the pin makes the Term
core AGREE with the Expr core on the full vocabulary: every fixture
elaborates through `tyTerm` to EXACTLY `toExpr`'s output (structural
`Expr` equality, checked at THIS module's compile — every build). A
new `Ty` ctor misses both walkers' exhaustive matches at once (the
build fails); the pin additionally catches shape drift that still
compiles (arity, literal form, namespace spelling). The consumers
(`Meta.Gen`, `Meta.EntityMachine`, the faults registry) share these
walkers, so the pin covers every path. -/

private def tyPinFixtures : List Ty :=
  [.bool, .u8, .u16, .u32, .u64, .i8, .i16, .i32, .i64, .f32, .f64,
   .string, .bytes,
   .option .u64, .result .u64 .string, .list .string,
   .map .u64 (.list .string), .set .i32,
   .future (.option .u64), .stream .string,
   .tensor [2, 3] .f32, .tensor [] .u8, .ty "User",
   .option (.result (.map .string .u64) (.set .bool))]

run_cmd do
  let tyT : Expr := .const ``SchemaLang.Ty []
  -- the elaboration helper: the RowIso.elabGen pattern (TermElabM.run'
  -- under MetaM.run' in CoreM — the one proven mvar-discipline here;
  -- elaborates + synthesizes + instantiates, then the mvar guard).
  -- Agreement is DEFINITIONAL equality (the byte-tie property: the
  -- same VALUE, e.g. a Nat dim either as a raw `.lit` or as
  -- `OfNat.ofNat … instOfNatNat` — both spellings, one value).
  let elabPinAgrees (stx : Term) (tyT? : Option Expr) (expected : Expr) :
      CoreM Bool :=
    Lean.Meta.MetaM.run' <| Lean.Elab.Term.TermElabM.run' do
      let goal ← Lean.Elab.Term.elabTerm stx tyT?
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let goal ← instantiateMVars goal
      if goal.hasExprMVar then
        throwError s!"drift-pin: internal: unresolved metavariables in `{goal}`"
      Lean.Meta.isDefEq goal expected
  for t in tyPinFixtures do
    let stx ← tyTerm t
    let ok ← liftCoreM <| elabPinAgrees stx (some tyT) (toExpr t)
    unless ok do
      throwError s!"drift-pin: `tyTerm` and `ToExpr Ty` disagree on \
        `{repr t}`"
  let keyArms : List (KeyTy × Name) :=
    [(.bool, ``SchemaLang.KeyTy.bool), (.u8, ``SchemaLang.KeyTy.u8),
     (.u16, ``SchemaLang.KeyTy.u16), (.u32, ``SchemaLang.KeyTy.u32),
     (.u64, ``SchemaLang.KeyTy.u64), (.i8, ``SchemaLang.KeyTy.i8),
     (.i16, ``SchemaLang.KeyTy.i16), (.i32, ``SchemaLang.KeyTy.i32),
     (.i64, ``SchemaLang.KeyTy.i64), (.string, ``SchemaLang.KeyTy.string)]
  for (k, nm) in keyArms do
    let stx ← keyTerm k
    let ok ← liftCoreM <| elabPinAgrees stx none (.const nm [])
    unless ok do
      throwError s!"drift-pin: `keyTerm` arm `{repr k}` does not \
        elaborate to `{nm}`"

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

/-- A record field → its `Field` literal term (`⟨"id", .u64⟩` — the
    anonymous-constructor spelling the hand mirrors used). -/
def fieldTerm (f : Field) : CommandElabM Term := do
  `((⟨$(quote f.name), $(← tyTerm f.ty)⟩))

/-- The `Value`-boxing term for one field-access term, per the field's
    schema type. The fragment is the flat scalars + `list string`
    (every in-tree consumer); a field outside it fails HERE, loudly —
    widening the fragment is a Derive change, not a hand mirror. -/
def fieldValueTerm (listHelper : Name) (access : Term) : Ty → CommandElabM Term
  | .bool => `(.bool $access)
  | .u8 => `(.u8 $access)
  | .u16 => `(.u16 $access)
  | .u32 => `(.u32 $access)
  | .u64 => `(.u64 $access)
  | .i8 => `(.i8 $access)
  | .i16 => `(.i16 $access)
  | .i32 => `(.i32 $access)
  | .i64 => `(.i64 $access)
  | .f32 => `(.f32 $access)
  | .f64 => `(.f64 $access)
  | .string => `(.string $access)
  | .list .string => `(.list ($(mkIdent listHelper) $access))
  | t => throwError
      "derive_schema_fields: no row-boxing for field type `{repr t}` — \
       the fragment is the flat scalars (bool/u8–u64/i8–i64/f32/f64/string) \
       + list string"

/-- The `.cons`-chain row literal over the record's projections
    (`.cons (.u64 (User.id u)) … .nil`), ending `.nil`. -/
def recordRowTerm (declName listHelper : Name) (u : Ident) :
    List Field → CommandElabM Term
  | [] => `(.nil)
  | f :: rest => do
      let access ← `($(mkIdent (declName.mkStr f.name)) $u)
      let v ← fieldValueTerm listHelper access f.ty
      `(.cons $v $(← recordRowTerm declName listHelper u rest))

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

/-- `derive_schema_fields fieldsName builderName from Record (using
    toVList)?` — from a registered `@[schema]` structure, emit:

    1. `abbrev fieldsName : List SchemaLang.Field` — the record's
       registered field list, snapshotted at elab (`abbrev`: the
       reducibility rule — instance search sees through).
    2. `def builderName (u : Record) : SchemaLang.RowVals fieldsName`
       — the row builder: one `.cons` per field, boxing each
       projection per its schema type.
    3. When the record carries a `list string` field, the element
       helper: `using h` names an EXISTING `List String →
       SchemaLang.VList .string` (std's guest-marked `toVList` — the
       compiled lane's authority, so the derived body can ride it);
       without a `using`, the command emits `builderName.toVList`.

    Wrong-kind or unregistered names are elaboration errors
    (did-you-mean included): the field/row mirror cannot drift because
    it is not written. No attributes are attached — the guest-mark
    lane applies `attribute [guest_std]` post-hoc where the MARK ORDER
    is artifact-visible (the wasm manifest folds the registry in
    marking order). -/
syntax (name := deriveSchemaFields)
  "derive_schema_fields " ident ident " from " ident (" using " ident)? : command

@[command_elab deriveSchemaFields]
def deriveSchemaFieldsImpl : CommandElab := fun stx => do
  let fieldsName := stx[1].getId
  let builderName := stx[2].getId
  let declName := stx[4].getId
  let using? : Option Name :=
    if stx[5].isNone then none else some stx[5][1].getId
  match registeredRecord? (← getEnv) declName with
  | .error msg => throwError msg
  | .ok fields => do
    let listHelper := using?.getD (builderName ++ `toVList)
    if using?.isNone && fields.any (·.ty == .list .string) then
      let helper := mkIdent listHelper
      elabCommand (← `(def $helper:ident : List String → SchemaLang.VList .string
        | [] => .nil
        | s :: ss => .cons (.string s) ($helper ss)))
    let fieldTerms ← fields.mapM fieldTerm
    elabCommand (← `(abbrev $(mkIdent fieldsName) : List SchemaLang.Field
      := [$fieldTerms.toArray,*]))
    let u := mkIdent `u
    let row ← recordRowTerm declName listHelper u fields
    elabCommand (← `(def $(mkIdent builderName) ($u : $(mkIdent declName)) :
        SchemaLang.RowVals $(mkIdent fieldsName) := $row))

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
