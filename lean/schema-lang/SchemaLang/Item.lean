/-
# SchemaLang.Item — the item model and the universe

Records, variants, functions, resources — the schema vocabulary. The
universe (`List Item`) is the source the emitters fold and the
well-formedness predicate guards.

Well-formedness is RESOLUTION, not just syntax: a `.ty "user"` reference
is valid only if a record/variant named `user` exists in the same
universe, names are unique, and functions reference resolvable types.
This is the (c)-address reading (executable Bool; the Prop/proved readings
land with schema-indexed).

The items are a plain `def : List Item` in v1 (deterministic order,
flatland's staging discipline); attribute-first registration over
`mkRegistryExt` moves in when the authoring surface lands.
-/

import SchemaLang.Ty

namespace SchemaLang

/-! ## Items -/

/-- A record field: name + type. -/
structure Field where
  name : String
  ty : Ty
deriving Repr, BEq, Inhabited

/-- A function signature: params in order, one return type.
    Errors are `.result` constructors — no special error channel. -/
structure FuncSig where
  name : String
  params : List (String × Ty)
  ret : Ty
deriving Repr, BEq, Inhabited

/-- A variant case: name + optional payload type. -/
abbrev VariantCase := String × Option Ty

/-- The item kinds. `resource` is the opaque-handle seed — its method
    surface is `func` items referencing the resource name in their first
    param (the WIT lowering maps them onto the resource block). -/
inductive Item where
  | record (name : String) (fields : List Field)
  | variant (name : String) (cases : List VariantCase)
  | func (sig : FuncSig)
  | resource (name : String)
deriving Repr, BEq, Inhabited

/-- The identifying name of an item (records/variants/resources by their
    type name; funcs by their function name). -/
def Item.name : Item → String
  | .record n _ => n
  | .variant n _ => n
  | .func s => s.name
  | .resource n => n

/-- Type-position names only (what `.ty` references may resolve to). -/
def Item.typeNames : List Item → List String :=
  fun items =>
    items.filterMap fun it =>
      match it with
      | .record n _ => some n
      | .variant n _ => some n
      | _ => none

/-- References of a type, innermost-out (no dedup; the consumer sorts). -/
def Ty.tyRefs : Ty → List String
  | .option a => a.tyRefs
  | .result ok err => ok.tyRefs ++ err.tyRefs
  | .list a => a.tyRefs
  | .future a => a.tyRefs
  | .stream a => a.tyRefs
  | .ty n => [n]
  | _ => []

/-! ## Well-formedness — resolution over the universe -/

/-- Async types are banned in FIELD position (WIT grammar: records can't
    contain future/stream — they live in func signatures where `async`
    unwraps the future). Params/results keep them. -/
def Ty.banAsync : Ty → Bool
  | .option a => a.banAsync
  | .result ok err => ok.banAsync && err.banAsync
  | .list a => a.banAsync
  | .future _ | .stream _ => false
  | _ => true

mutual
/-- A type is well formed over `known` when every `.ty` reference
    resolves. -/
def Ty.wellFormed (known : List String) : Ty → Bool
  | .option a => a.wellFormed known
  | .result ok err => ok.wellFormed known && err.wellFormed known
  | .list a => a.wellFormed known
  | .future a => a.wellFormed known
  | .stream a => a.wellFormed known
  | .ty n => known.contains n
  | _ => true

def Ty.fieldsWellFormed (known : List String) : List Field → Bool
  | [] => true
  | f :: rest =>
      f.ty.banAsync && f.ty.wellFormed known && Ty.fieldsWellFormed known rest

def Ty.variantsWellFormed (known : List String) : List VariantCase → Bool
  | [] => true
  | (_, some t) :: rest => t.wellFormed known && Ty.variantsWellFormed known rest
  | (_, none) :: rest => Ty.variantsWellFormed known rest

def Ty.paramsWellFormed (known : List String) : List (String × Ty) → Bool
  | [] => true
  | (_, t) :: rest => t.wellFormed known && Ty.paramsWellFormed known rest
end

/-- An item is well formed when its types resolve against `known`.
    (Called with the FULL universe's type names — a record may reference
    a variant declared after it.) -/
def Item.wellFormed (known : List String) : Item → Bool
  | .record _ fields => Ty.fieldsWellFormed known fields
  | .variant _ cases => Ty.variantsWellFormed known cases
  | .func s => Ty.paramsWellFormed known s.params && s.ret.wellFormed known
  | .resource _ => true

/-- Names are unique (no two items share an identifying name). -/
def namesUnique (items : List Item) : Bool :=
  let ns := items.map Item.name
  ns.Nodup

/-- The whole universe: every item well formed against it, names unique. -/
def universeWellFormed (items : List Item) : Bool :=
  let known := Item.typeNames items
  items.all (Item.wellFormed known) && namesUnique items

/-- The `.ty` references of an item — used by the compat diff and by
    dependency-ordered emission. -/
def Item.tyRefs : Item → List String
  | .record _ fields => fields.map (·.ty) |>.flatMap Ty.tyRefs
  | .variant _ cases => cases.filterMap (·.2) |>.flatMap Ty.tyRefs
  | .func s => s.params.map (·.2) ++ [s.ret] |>.flatMap Ty.tyRefs
  | .resource _ => []

end SchemaLang
