/- # SchemaLang.Meta.Mono — `schema_mono`: monomorphized parameterized
   types (W8.12, folded into W8.13's lane)

`Page<T>`-style types WITHOUT opening `Ty`: the runbook's default is
MONOMORPHIZATION (WIT has no generics; the canonical ABI doesn't
either) — each concrete instantiation registers a CONCRETE item; the
registry, the emitters, the snapshot, and the delta/Wf lanes see only
ordinary records. No type constructors exist in `Ty` (the closed
boundary universe is untouched — the 27-artifact byte-tie holds BY
CONSTRUCTION: nothing in the demo spec changes).

    schema_mono PairStringU64 := Pair String UInt64

The command: resolves the TEMPLATE (a plain Lean parameterized
structure — NOT registered, never reflected as an item), instantiates
its constructor with the given type arguments, reifies the fields
through the SAME `tyOfExpr?` boundary fragment the `@[schema]`
attribute uses (a non-boundary type arg = the `nonBoundaryType`
elaboration error, the negative control), checks the field idents and
the registry dup gate, and registers the concrete record under the
given name. A `Lean` `abbrev` of the instantiation is emitted too, so
downstream authors reference the instantiation as a Lean type and the
reifier resolves it as a `.ty` ref (the zero-arg-const arm over the
schema registry).

Deliberate exclusions (v1, conservative): positional type args only
(named `(α := …)` args are a parse away when needed); the template
must be a structure (variants are not parameterized shapes v1);
instances/derives are the author's business (the emitted `abbrev` is
plain). The emitted item is an ORDINARY record: `universeCheck` (with
W8.13's `InlineAcyclic` gate) applies unchanged.

Ownership: this module (the mono lane). No emitter reads it; the demo
spec does not use it (byte-tie neutral by construction).
-/

module

public import Lean
public import SchemaLang.Meta.Reflect

public meta section

namespace SchemaLang.Meta

open Lean Elab Command Meta Term

/-- `schema_mono <Name> := <Template> <TypeArg…>` — register the
    monomorphized instantiation of a parameterized structure as a
    concrete schema record (W8.12). The template stays unregistered. -/
syntax (name := schemaMono) "schema_mono " ident " := " ident ident* : command

@[command_elab schemaMono]
def schemaMonoImpl : CommandElab := fun stx => do
  let name := stx[1].getId
  let args := stx[4].getArgs
  let env ← getEnv
  -- the dup gate (the `@[schema]` registration ritual)
  if (registeredNames env).contains name.toString then
    throwError s!"schema_mono `{name}`: duplicate name `{name}` — names must be unique"
  -- resolve the template HEAD through the current namespace (the
  -- declaration lands in it too): elaborate the head as a TERM (an
  -- unapplied parameterized structure is a type CONSTRUCTOR, not a
  -- type — `elabType` would refuse it) and take its constant
  let headTerm ← liftTermElabM (elabTerm stx[3] none)
  let headFn := headTerm.getAppFn
  unless headFn.isConst do
    throwError s!"schema_mono `{name}`: the template must be a type constant"
  let head := headFn.constName!
  unless Lean.isStructure env head do
    throwError s!"schema_mono `{name}`: `{head}` is not a structure (the template is a plain Lean parameterized structure)"
  let some (.inductInfo ii) := env.find? head
    | throwError s!"schema_mono `{name}`: `{head}`: no inductive info"
  -- the registered Lean name = the DECL name (the namespace is part of
  -- it — the reifier's zero-const arm resolves the abbrev by this key)
  let declName := (← getCurrNamespace) ++ name
  -- the arg-count gate BEFORE the structure gate (UInt64 IS a Lean
  -- structure — the count error is the informative one)
  if args.size != ii.numParams then
    throwError s!"schema_mono `{name}`: `{head}` expects {ii.numParams} type argument(s), got {args.size}"
  unless ii.levelParams.isEmpty do
    throwError s!"schema_mono `{name}`: `{head}`: level-parameterized templates are outside the v1 fragment (Type-0 args only)"
  -- elaborate the type args (the same boundary reifier consumes them)
  let argExprs : List Expr ← args.toList.mapM fun a =>
    liftTermElabM (elabType a)
  -- instantiate the template's constructor with the args
  let ctor := Lean.getStructureCtor env head
  let argArr := argExprs.toArray
  let instantiated ← liftTermElabM do
    instantiateForall ctor.type argArr
  -- walk the field binders (the ctor's EXPLICIT args — the structure's
  -- params were implicit and are consumed by the instantiation)
  let fieldNames := (Lean.getStructureFields env head).toList
  let tys := ctorArgTypes instantiated
  if tys.length != fieldNames.length then
    throwError s!"schema_mono `{name}`: `{head}`: field/binder count mismatch — flat structures only (v1)"
  -- reify + ident-gate per field (the `checkStruct` ritual)
  let mut ds : List SchemaDiag := []
  let mut fields : List Field := []
  for ⟨f, tE⟩ in fieldNames.zip tys do
    if !ds.isEmpty then pure ()
    else match checkSchemaIdent s!"field of `{name}`" f.toString with
      | ds'@(_ :: _) => ds := ds'
      | [] =>
          match tyOfExpr? (← getEnv) tE with
          | some t => fields := fields ++ [{ name := f.toString, ty := t }]
          | none =>
              ds := [SchemaDiag.nonBoundaryType f.toString (toString tE)]
  unless ds.isEmpty do
    throwError ("schema_mono `" ++ name.toString ++ "`: "
      ++ String.intercalate "; " (ds.map SchemaDiag.render))
  -- register the CONCRETE item (the registry sees only this) + the
  -- Lean abbrev so later declarations reference the instantiation
  let argStx : TSyntaxArray `term := args.map (fun a => ⟨a⟩)
  elabCommand (← `(abbrev $(mkIdent name) := $(mkIdent head) $(argStx)*))
  liftCoreM (registerSchemaItem declName (.record name.toString fields))
  liftCoreM (registerSchemaItemDoc declName)

end SchemaLang.Meta
