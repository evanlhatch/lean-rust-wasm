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

import SchemaLang.DidYouMean
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

/-! ## Well-formedness — resolution over the universe, with designed errors

The universe check returns STRUCTURED diagnostics (TOOLKIT §11.1: errors
enumerate the valid space, did-you-mean everywhere, never a bare Bool).
`universeWellFormed` stays as the Bool projection for gates; `universeCheck`
is the diagnostic authority.

The closed-world superpower: `unknownRef` carries the closest matches AND
the full valid space — for an LLM, an error that lists the valid moves is
a self-correcting prompt. -/

/-- One well-formedness finding. -/
inductive SchemaDiag where
  | unknownRef (got : String) (candidates valid : List String)
  | dupName (name : String)
  | asyncField (item field : String)
  | notAStructure (name : String)
  | noCtor (name : String)
  | binderMismatch (name : String)
  | multiPayload (name : String)
deriving Repr, BEq, Inhabited

namespace SchemaDiag

def render : SchemaDiag → String
  | .unknownRef got cands valid =>
      let hint := match cands with
        | [] => ""
        | cs => " — did you mean: " ++ String.intercalate ", " cs ++ "?"
      s!"unknown type `{got}` — valid types: "
        ++ String.intercalate ", " valid ++ hint
  | .dupName n => s!"duplicate name `{n}` — names must be unique"
  | .asyncField item field =>
      s!"field `{field}` on `{item}`: future/stream cannot appear in field "
        ++ "position (WIT grammar) — move it to a function signature"
  | .notAStructure n => s!"`{n}` is not a structure — v1 reflects structures only"
  | .noCtor n => s!"`{n}`: no constructor found"
  | .binderMismatch n =>
      s!"`{n}`: field/binder count mismatch — flat structures without typeclass fields only (v1)"
  | .multiPayload n =>
      s!"`{n}`: variant cases carry at most one payload type (v1 — WIT case shape)"

end SchemaDiag

/-- Collect resolution diagnostics for one type against `known`.
    (Async-in-field-position is diagnosed at the FIELD level, where the
    item/field names are known — see `Item.check`.) -/
def Ty.check (known : List String) : Ty → List SchemaDiag
  | .option a => a.check known
  | .result ok err => ok.check known ++ err.check known
  | .list a => a.check known
  | .future a => a.check known
  | .stream a => a.check known
  | .ty n => if known.contains n then [] else [.unknownRef n (didYouMean n known) known]
  | _ => []

/-- Async types are banned in FIELD position (WIT grammar: records can't
    contain future/stream — they live in func signatures where `async`
    unwraps the future). Params/results keep them. -/
def Ty.banAsync : Ty → Bool
  | .option a => a.banAsync
  | .result ok err => ok.banAsync && err.banAsync
  | .list a => a.banAsync
  | .future _ | .stream _ => false
  | _ => true

/-! ## The diagnostic authority (supersedes the Bool) -/

/-- Collect ALL diagnostics for one item (async-in-field + unresolved
    refs), tagged with the item's name. -/
def Item.check (known : List String) : Item → List SchemaDiag
  | .record n fields =>
      fields.flatMap fun f =>
        (if f.ty.banAsync then [] else [.asyncField n f.name])
          ++ f.ty.check known
  | .variant _ cases =>
      cases.flatMap fun (_, payload) =>
        match payload with
        | some t => t.check known
        | none => []
  | .func s =>
      s.params.flatMap fun (_, t) => t.check known
        ++ s.ret.check known
  | .resource _ => []

/-- The universe check: ALL diagnostics. Empty list = well formed. -/
def universeCheck (items : List Item) : List SchemaDiag :=
  let known := Item.typeNames items
  let ns := items.map Item.name
  let dupNames := ns.filter (fun n => ns.countP (· == n) > 1)
  let dedupNames := SchemaLang.dedupStr dupNames
  let dupDiags := dedupNames.map SchemaDiag.dupName
  items.flatMap (Item.check known) ++ dupDiags

/-! ## The Bool projection (derived from the diagnostic authority) -/

/-- The whole universe is well formed iff the diagnostic authority emits
    NO findings — DERIVED from `universeCheck`, not a parallel fold. One
    authority, two readings; they cannot drift. (The `namesUnique` /
    `Item.wellFormed` / `Ty.wellFormed` folds that used to sit here were
    deleted — the diagnostic fold is the single source.) -/
def universeWellFormed (items : List Item) : Bool :=
  (universeCheck items).isEmpty

/-- The `.ty` references of an item — used by the compat diff and by
    dependency-ordered emission. -/
def Item.tyRefs : Item → List String
  | .record _ fields => fields.map (·.ty) |>.flatMap Ty.tyRefs
  | .variant _ cases => cases.filterMap (·.2) |>.flatMap Ty.tyRefs
  | .func s => s.params.map (·.2) ++ [s.ret] |>.flatMap Ty.tyRefs
  | .resource _ => []

instance : ToString SchemaDiag where
  toString := SchemaDiag.render

instance : ToString (List SchemaDiag) where
  toString ds := String.intercalate ";; " (ds.map toString)

end SchemaLang
