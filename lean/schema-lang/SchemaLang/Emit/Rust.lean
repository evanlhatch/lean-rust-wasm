/-
# SchemaLang.Emit.Rust — the Rust target

Fold `Item`s to the rich Rust domain crate. Records → structs, variants
→ enums; func signatures are NOT emitted here (they are the WIT world's
exports — the component-host glue consumes the WIT in Phase 5).

Lowering (target-neutral universe → Rust):
- scalars 1:1 (`bool`, `u8`…`u64`, `i8`…`i64`, `f32`, `f64`)
- `string` → `String`, `bytes` → `Vec<u8>`
- `option`/`result`/`list` → `Option`/`Result`/`Vec` (1:1)
- `map`/`set` → `BTreeMap`/`BTreeSet` (deterministic — the runbook
  default; `KeyTy` scalars are all `Ord`)
- `future`/`stream` unreachable in field position (wellFormed bans —
  the flatland audit doctrine: the emitter may assume checked input)
- `.ty n` → `Pascal n`

Derives come from `derivesFor`: `baseDerives` + conditional `Eq`
(f32/f64 don't implement Eq, and named refs are RESOLVED against the
universe — a float behind a `.ty` ref still blocks `Eq`; fast-observe,
bon, serde land with the faults/tabular packages). Names pre-mangled via
`Emit.pascal`/`rustIdent` — the AST never case-converts.
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx

@[expose] public section

namespace SchemaLang.Emit.Rust

open CodegenCore.Emit (pascal rustIdent)

/-- The base derives stamped on every generated type. Eq is added
    conditionally — f32/f64 don't implement Eq. -/
def baseDerives : List String := ["Clone", "Debug", "PartialEq"]

/-- Float check with a ref-semantics: structural on the Ty; refs
    consult `sem` (an already-resolved verdict per name). -/
def hasFloatWith (sem : String → Bool) : Ty → Bool
  | .f32 | .f64 => true
  | .option a => hasFloatWith sem a
  | .result ok err => hasFloatWith sem ok || hasFloatWith sem err
  | .list a => hasFloatWith sem a
  | .map _ v => hasFloatWith sem v  -- the key is a `KeyTy` scalar: float-free
  | .set _ => false                 -- a `KeyTy` scalar: float-free
  | .future a => hasFloatWith sem a
  | .stream a => hasFloatWith sem a
  | .ty n => sem n
  | _ => false

/-- The ref verdicts, fuel-bounded like `Vortex.Emit.refSem`: a name is
    float-CONTAINING unless resolvable-and-clean. The failure mode this
    conservatism prevents: a record deriving `Eq` while the type behind
    its named ref doesn't implement it (generated Rust that doesn't
    compile). Fuel exhaustion / unresolvable / non-type refs → `true`. -/
def floatRefs (items : List Item) : Nat → String → Bool
  | 0, _ => true
  | fuel + 1, n =>
      match items.find? (·.name == n) with
      | some (.record _ fields) =>
          fields.any fun f => hasFloatWith (floatRefs items fuel) f.ty
      | some (.variant _ cases) =>
          cases.any fun (_, payload) =>
            match payload with
            | some t => hasFloatWith (floatRefs items fuel) t
            | none => false
      | _ => true

/-- Check whether a Ty's Rust lowering contains a float type, resolving
    named refs against the universe (fuel-bounded; unresolvable or
    over-deep refs are conservatively float-CONTAINING). -/
def hasFloat (items : List Item) (t : Ty) (fuel : Nat := 8) : Bool :=
  hasFloatWith (floatRefs items fuel) t

/-- The derives for a type whose parts are `tys` (record fields or
    variant payloads): `Eq` joins the base derives iff NO part — refs
    resolved against the universe — contains a float. The ONE
    Eq-eligibility fold: the Rust emitter and the Delta change enums
    both consume it (single fix site for the `Eq`-behind-a-ref bug). -/
def derivesFor (items : List Item) (tys : List Ty) : List String :=
  if tys.any (hasFloat items) then baseDerives else baseDerives ++ ["Eq"]

/-- The map/set KEY rendering, DIRECT (the `KeyTy.toTy` indirection
    breaks `tyRust`'s structural recursion; the arms are exactly the
    scalar text `tyRust` gives the injected types). -/
def keyRust : KeyTy → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .string => "String"

/-- Lower a `Ty` to Rust type text. `future`/`stream` cannot reach this
    in field position (wellFormed bans them); if a func-signature
    emitter reuses this, the future unwraps at `async`. -/
def tyRust : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "String"
  | .bytes => "Vec<u8>"
  -- the flat form: `Vec<elem>` (row-major; the dims are schema
  -- metadata — a shape-bearing newtype is v2 with the derives work)
  | .tensor _ a => s!"Vec<{tyRust a}>"
  -- BTreeMap/BTreeSet, NOT HashMap/HashSet: deterministic iteration
  -- order (the runbook default — generated artifacts and any
  -- order-observing downstream code are stable). `KeyTy` scalars are
  -- all `Ord`, so the tree types' bounds hold by construction
  | .map k v => s!"BTreeMap<{keyRust k}, {tyRust v}>"
  | .set k => s!"BTreeSet<{keyRust k}>"
  | .option a => s!"Option<{tyRust a}>"
  | .result ok err => s!"Result<{tyRust ok}, {tyRust err}>"
  | .list a => s!"Vec<{tyRust a}>"
  | .future a | .stream a => tyRust a
  | .ty n => pascal n

/-- A record → `struct` item. -/
def recordItem (derives : List String) : Item → CodegenCore.Emit.Rust.Item
  | .record n fields =>
      .struct (pascal n) derives
        (fields.map fun f => { name := rustIdent f.name, ty := tyRust f.ty })
  | _ => .comment "recordItem: not a record"

/-- A variant → `enum` item (payload cases carry their type). -/
def variantItem (derives : List String) : Item → CodegenCore.Emit.Rust.Item
  | .variant n cases =>
      .enum (pascal n) derives
        (cases.map fun (c, payload) =>
          match payload with
          | some t => s!"{pascal c}({tyRust t})"
          | none => pascal c)
  | _ => .comment "variantItem: not a variant"

/-- A full universe → the Rust module items (types only; funcs are the
    WIT world's exports, not Rust-side types). Derives come from
    `derivesFor` — `Eq` exactly when the fields/payloads (refs resolved
    against `items`) are float-free. -/
def schemaItems (items : List Item) :
    List CodegenCore.Emit.Rust.Item :=
  items.filterMap fun it =>
    match it with
    | .record _ fields =>
        some (recordItem (derivesFor items (fields.map (·.ty))) it)
    | .variant _ cases =>
        some (variantItem (derivesFor items (cases.filterMap (·.2))) it)
    | _ => none

end SchemaLang.Emit.Rust

/-- The Rust emitter plugin: rich domain types. -/
def rustEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "rust"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../src/schema_generated.rs"]
  run ctx := [
    { path := "../../src/schema_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule (SchemaLang.Emit.Rust.schemaItems ctx.items) }
  ]
