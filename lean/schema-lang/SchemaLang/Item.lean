/-
# SchemaLang.Item — the item model and the universe

Records, variants, functions, resources — the schema vocabulary. The
universe (`List Item`) is the source the emitters fold and the
well-formedness predicate guards.

Func items carry SEMANTIC FIELDS AS DATA (6.5.1): `FuncSem` = nullSem
(`strict | propagate | custom`) + determinism (`pure | stable |
volatile`), defaulted so existing items are unchanged. The volatile-
in-pure-context enforcement rule is armed (`SchemaDiag.
volatileInPureContext`) but unfired — no fold/reorder role exists in
the item algebra yet (see `Determinism`).

Well-formedness is RESOLUTION, not just syntax: a `.ty "user"` reference
is valid only if a record/variant named `user` exists in the same
universe, names are unique, and functions reference resolvable types.
This is the (c)-address reading (executable Bool; the Prop/proved readings
land with schema-indexed).

Registration is attribute-first (`@[schema]`/`@[schema_fn]`/
`@[schema_resource]` in `SchemaLang.Meta.Reflect`) over
`CodegenCore.mkRegistryExt`; the emitters read the replayed registry.
-/

import SchemaLang.Ty
import CodegenCore.Emit.Core
import CodegenCore.DidYouMean

namespace SchemaLang

/-! ## Items -/

/-- A record field: name + type. -/
structure Field where
  name : String
  ty : Ty
deriving Repr, BEq, DecidableEq, Inhabited

/-- Nullability semantics of a func item, AS DATA (refactor-guide
    6.5.1; flatland SPEC-core §2): how the fn treats null (`option`)
    arguments. `strict` = any null arg → error (the body never sees
    `none`); `propagate` = any null arg → null result (the body runs
    only when every arg is present); `custom` = the body owns null
    handling. Emitters and the wasm differential oracle may consume
    this later; today it is validated data. -/
inductive NullSem where
  | strict | propagate | custom
deriving Repr, BEq, DecidableEq, Inhabited

/-- Determinism of a func item, AS DATA (6.5.1; SPEC-core §11.5):
    `pure` = same args → same result, always (reorderable, memoizable);
    `stable` = pure within one run; `volatile` = may observe the world
    (clock, rng, host state). The enforcement rule: a `volatile` fn in
    a purity-required context (aggregation/reorderable operand) fails
    `universeCheck` — the diag ctor `volatileInPureContext` is armed,
    but NO such role exists in the item algebra yet, so nothing fires
    it today (v1: validated data + the armed diag; the firing site
    lands with the first pure-context consumer, e.g. an aggregation
    emitter or the wasm oracle). -/
inductive Determinism where
  | pure | stable | volatile
deriving Repr, BEq, DecidableEq, Inhabited

/-- The delivery contract of a func item: `once` = the result arrives
    as one value (a list result = ONE payload); `stream` = the host
    consumes the results INCREMENTALLY (the WASI 0.3 stream — the
    delta-shaped contracts on the wire). The default (`once`) keeps
    every existing item unchanged. -/
inductive Delivery where
  | once | stream
deriving Repr, BEq, DecidableEq, Inhabited

/-- Delivery tokens — the ONE spelling (snapshot + attr args). -/
def Delivery.toToken : Delivery → String
  | .once => "once" | .stream => "stream"

def Delivery.ofToken? : String → Option Delivery
  | "once" => some .once
  | "stream" => some .stream
  | _ => none

/-- The semantic contract fields of a func item (6.5.1): nullability +
    determinism + delivery, as DATA. The defaults (`propagate`, `pure`,
    `once`) keep every existing `@[schema_fn]` item unchanged; the
    attribute's optional ident args override per axis (`SchemaLang.Meta`). -/
structure FuncSem where
  nullSem : NullSem := .propagate
  determinism : Determinism := .pure
  delivery : Delivery := .once
deriving Repr, BEq, DecidableEq, Inhabited

/-- NullSem tokens — the ONE spelling, consumed by the snapshot codec
    (`Snapshot`) and the `@[schema_fn]` attr args (`Meta.Reflect`). -/
def NullSem.toToken : NullSem → String
  | .strict => "strict" | .propagate => "propagate" | .custom => "custom"

def NullSem.ofToken? : String → Option NullSem
  | "strict" => some .strict
  | "propagate" => some .propagate
  | "custom" => some .custom
  | _ => none

/-- Determinism tokens (closed set). -/
def Determinism.toToken : Determinism → String
  | .pure => "pure" | .stable => "stable" | .volatile => "volatile"

def Determinism.ofToken? : String → Option Determinism
  | "pure" => some .pure
  | "stable" => some .stable
  | "volatile" => some .volatile
  | _ => none

/-- A function signature: params in order, one return type.
    Errors are `.result` constructors — no special error channel.
    `sem` carries the semantic contract fields (defaulted — existing
    constructed and reflected items need no changes). -/
structure FuncSig where
  name : String
  params : List (String × Ty)
  ret : Ty
  sem : FuncSem := {}
  /-- The declaring Lean constant carrying the EXECUTABLE semantics
  (6.5.1's "unsigned code doesn't ship"): auto-filled by `@[schema_fn]`
  with the declaration itself, so downstream consumers (the wasm oracle,
  future emitters) can derive rows from items instead of hand-mirroring
  them. NOT part of the Snapshot wire format — it is registry metadata,
  not spec data (the default keeps every snapshot byte-identical). -/
  body : Lean.Name := Lean.Name.anonymous
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

/-- The SPEC-SURFACE equality: `FuncSig.body` (6.5.1) is registry
    metadata — the declaring constant, re-attached at `@[schema_fn]`
    time and reconstructed anonymous by the snapshot round-trip — so
    two items that agree on name/params/ret/sem ARE the same spec. The
    compat gate (`diff`) compares through this, not raw BEq. -/
def Item.specEq : Item → Item → Bool
  | .func a, .func b =>
      a.name == b.name && a.params == b.params && a.ret == b.ret
        && a.sem == b.sem
  | a, b => a == b

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
  | .tensor _ a => a.tyRefs
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
  | nonBoundaryType (name tyText : String)
  | notAStructure (name : String)
  | noCtor (name : String)
  | binderMismatch (name : String)
  | multiPayload (name : String)
  | reservedWord (name context : String)
  | volatileInPureContext (fn context : String)
deriving Repr, BEq, Inhabited

/-! ## Reserved words — the identifier gate (elab-time, via the
    registration handlers in `Meta.Reflect`; also enforced by the pure
    `Item.check` for hand-built universes)

A field/case named `u8` would emit INVALID WIT (`record user { u8: ... }`)
and invalid Rust; the collision is caught HERE — at registration —
not downstream at wit-parser time. The identifier is checked in its
EMITTED spellings (kebab for WIT, snake for Rust).
-/

/-- WIT's keyword set (wit-parser rejects these as identifiers). -/
def witReserved : List String :=
  ["any", "bool", "char", "enum", "f32", "f64", "flags", "float32", "float64",
   "future", "handle", "i8", "i16", "i32", "i64", "interface", "list",
   "option", "package", "record", "resource", "result", "s8", "s16", "s32",
   "s64", "service", "static", "stream", "string", "tuple", "type", "u8",
   "u16", "u32", "u64", "unit", "use", "variant", "world", "async"]

/-- Rust's reserved set (strict + reserved-suffix keywords). -/
def rustReserved : List String :=
  ["as", "async", "await", "become", "box", "break", "const", "continue",
   "crate", "do", "dyn", "else", "enum", "extern", "false", "final", "fn",
   "for", "if", "impl", "in", "let", "loop", "macro", "match", "mod",
   "move", "mut", "override", "priv", "pub", "ref", "return", "self",
   "static", "struct", "super", "trait", "true", "try", "type", "typeof",
   "union", "unsafe", "unsized", "use", "virtual", "where", "while", "yield"]

/-- One schema identifier (field/case/param name), checked in BOTH
    target spellings. Empty diagnostic list = usable. -/
def checkSchemaIdent (context : String) (name : String) : List SchemaDiag :=
  let witHit := witReserved.contains (CodegenCore.Emit.kebab name)
  let rustHit := rustReserved.contains (CodegenCore.Emit.snake name)
  if witHit || rustHit then [.reservedWord name context] else []

/-- The boundary fragment, enumerated (the error IS the documentation).
    The reifier's `nonBoundaryType` render appends this. -/
def boundaryFragment : String :=
  "boundary types are: Bool, UInt8..UInt64, Int8..Int64, Float32, Float, "
    ++ "String, ByteArray, List, Option, Sum (as result),"
    ++ " Async.Future, Async.Stream, or another `@[schema]` declaration"

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
  | .nonBoundaryType name tyText =>
      s!"`{name}`: `{tyText}` is not a boundary type — " ++ boundaryFragment
  | .notAStructure n => s!"`{n}` is not a structure — v1 reflects structures only"
  | .noCtor n => s!"`{n}`: no constructor found"
  | .binderMismatch n =>
      s!"`{n}`: field/binder count mismatch — flat structures without typeclass fields only (v1)"
  | .multiPayload n =>
      s!"`{n}`: variant cases carry at most one payload type (v1 — WIT case shape)"
  | .reservedWord name context =>
      s!"`{name}` is a reserved word in {context} — rename it (WIT/Rust "
        ++ "would reject the emitted identifier)"
  | .volatileInPureContext fn ctx =>
      s!"func `{fn}` is volatile but `{ctx}` requires purity — valid "
        ++ "determinisms in a pure context: pure, stable"

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
  | .tensor _ a => a.check known
  | .ty n =>
      if known.contains n then []
      else [.unknownRef n (CodegenCore.didYouMean n known) known]
  | _ => []

/-- Async types are banned in FIELD position (WIT grammar: records can't
    contain future/stream — they live in func signatures where `async`
    unwraps the future). Params/results keep them. -/
def Ty.banAsync : Ty → Bool
  | .option a => a.banAsync
  | .result ok err => ok.banAsync && err.banAsync
  | .list a => a.banAsync
  | .future _ | .stream _ => false
  | .tensor _ a => a.banAsync
  | _ => true

/-! ## The diagnostic authority (supersedes the Bool) -/

/-- Collect ALL diagnostics for one item (async-in-field + unresolved
    refs), tagged with the item's name. -/
def Item.check (known : List String) : Item → List SchemaDiag
  | .record n fields =>
      fields.flatMap fun f =>
        (if f.ty.banAsync then [] else [.asyncField n f.name])
          ++ checkSchemaIdent (s!"field of `{n}`") f.name
          ++ f.ty.check known
  | .variant n cases =>
      cases.flatMap fun (c, payload) =>
        match payload with
        | some t =>
            (if t.banAsync then [] else [.asyncField n c])
              ++ checkSchemaIdent (s!"case of `{n}`") c
              ++ t.check known
        | none => checkSchemaIdent (s!"case of `{n}`") c
  | .func s =>
      s.params.flatMap fun (_, t) => t.check known
        ++ s.ret.check known
  | .resource _ => []

/-- The universe check: ALL diagnostics. Empty list = well formed. -/
def universeCheck (items : List Item) : List SchemaDiag :=
  let known := Item.typeNames items
  let ns := items.map Item.name
  let dupNames := ns.filter (fun n => ns.countP (· == n) > 1)
  let dupDiags := dupNames.eraseDups.map SchemaDiag.dupName
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

/-- Render a diagnostic list — a FUNCTION, not an instance (core's
    generic `ToString (List α)` would make an instance here resolution
    roulette). -/
def SchemaDiag.renderList (ds : List SchemaDiag) : String :=
  String.intercalate ";; " (ds.map SchemaDiag.render)

end SchemaLang
