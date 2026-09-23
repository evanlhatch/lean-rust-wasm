/-
# SchemaCore.Ty — the boundary universe (the C1 slice's closed `Ty`)

Owner: the SchemaCore agent (the macht tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §1 (Universe root: finite data,
closed codes + total denotation) + notes/v3/15-patterns.md #15 (the
closed-universe exhaustiveness discipline).

THE CLOSED-UNIVERSE DISCIPLINE (the slice's documented contract): `Ty`
is a CLOSED universe. A new constructor breaks every fold's
exhaustiveness (`renderTy` here; the reifier's match in
`SchemaCore.Register` reifies LEAN types — it grows only when an
AUTHORING surface consumes the new ctor; every consumer's match
downstream) and the compiler drives the extension — nobody "remembers"
to update a fold, because the build refuses to pass without it.

THE MEMBERS (the honest working size, mined toward legacy
`SchemaLang/Ty.lean`'s content, slice-sized):

- the four slice scalars: `bool`, `u64`, `i64`, `string`;
- `option`/`list` — free at this size: two folds of recursive
  structure, no extra machinery;
- `result (ok err : Ty)` — the legacy Ty's SUM-flavored ctor (the
  legacy tree carries it and its Value/defaultValue/toType lanes
  consume it). NO `prod` ctor exists in the legacy Ty — deliberately
  not invented here;
- `map (k : KeyTy) (v : Ty)` / `set (α : KeyTy)` — keys ride the
  CLOSED scalar sub-universe `KeyTy` (bool | u64 | i64 | string, the
  slice's scalars): a non-scalar key is UNREPRESENTABLE — in the type,
  not a checker pass (a predicate field on `Ty.map` would forfeit the
  derived `DecidableEq`). Rendering routes key positions through
  `KeyTy.toTy` — below the first fold a key position is a plain `Ty`
  again;
- `bounded (cap : Nat)` — the bounded-Nat lane's base type: the cap
  lives IN the type (the lane's well-formedness is the type; a value
  of `.bounded cap` cannot exceed the cap — see `SchemaCore.Value`'s
  `Fin cap` payload).

DELIBERATELY EXCLUDED from the legacy Ty's ctor list (each names its
reason — the leftover rule: nothing lands without a consumer):

- `u8/u16/u32/i8/i16/i32` — no current-tree lane consumes them; the
  slice's scalars stay the four the Example exercises. They extend
  `KeyTy` first when a lane needs them;
- `f32/f64` — floats out (legacy W8.1: NaN breaks the total order a
  canonical map form needs); no lane;
- `bytes`, `future`, `stream`, `tensor` — no current-tree consumer;
- `ty (name : TyRef)` — named references are OPEN-world (they need
  the wellFormed resolution lane); the slice has no second registered
  item to reference.

The five questions (01-core's acceptance test): root = Universe (data);
carrier = the DataRegistry's nodup-in-type (Kit.Registry); spine
reading = Registry → Interpretation → artifact (Kit.Emit); ladder rung
= `decide`/`decidableNow` for every checkable fact over concrete
values; gate row = the byte-tie (`gates gen-check`) + the axiom report.

Core-only (imports Kit only — the cone rule).
-/

import Kit

namespace SchemaCore

/-- The hashable/comparable SCALAR sub-universe: map keys and set
    elements. A non-scalar key is UNREPRESENTABLE — in the type, not a
    checker pass. Sized to the slice's scalars (see the module header).
    Every key injects into `Ty` via `KeyTy.toTy`. -/
inductive KeyTy where
  | bool
  | u64
  | i64
  | string
deriving Repr, BEq, DecidableEq, Inhabited

/-- The boundary universe: every schema field's type IS one of these.
    CLOSED — see the module header. -/
inductive Ty where
  | bool
  | u64
  | i64
  | string
  | option (α : Ty)
  | list (α : Ty)
  | result (ok err : Ty)
  | map (k : KeyTy) (v : Ty)
  | set (α : KeyTy)
  | bounded (cap : Nat)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The key sub-universe INJECTS into `Ty`: every key is a scalar
    type. Emitters/codecs route key rendering through this — below the
    first fold a key position is a plain `Ty` again. -/
def KeyTy.toTy : KeyTy → Ty
  | .bool => .bool
  | .u64 => .u64
  | .i64 => .i64
  | .string => .string

/-- The key's Lean reification, DIRECT (not `toTy`-routed — the
    indirection breaks `toType`'s structural recursion). -/
abbrev KeyTy.toType : KeyTy → Type
  | .bool => Bool
  | .u64 => UInt64
  | .i64 => Int64
  | .string => String

/-- Reify a schema type as a Lean type. No named references in the
    slice's universe (`Ty` is first-order here), so the semantics is
    total with no `TySem` parameter. -/
abbrev Ty.toType : Ty → Type
  | .bool => Bool
  | .u64 => UInt64
  | .i64 => Int64
  | .string => String
  | .option a => Option a.toType
  | .list a => List a.toType
  | .result ok err => Sum ok.toType err.toType
  -- the map/set Lean payload is the ASSOCIATION-LIST / element-list
  -- form (the wire shape — BTreeMap/BTreeSet are a Rust emitter's
  -- rendering, not the reification's)
  | .map k v => List (k.toType × v.toType)
  | .set k => List k.toType
  | .bounded cap => Fin cap

/-- The two key reifications agree (the direct one is the structural
    recursion's; the injected one is the emitters'). -/
theorem KeyTy.toType_toTy (k : KeyTy) : k.toTy.toType = k.toType := by
  cases k <;> rfl

/-- The key position's rendering. Key positions route through the
    scalar sub-universe (never a full `Ty` fold below it) — a plain
    leaf fold, so `renderTy`'s own recursion stays STRUCTURAL (a
    `k.toTy`-routed recursive call defeats the size check; wf-recursion
    would make `renderTy` kernel-opaque). Coherent with the injection:
    `renderKeyTy k = renderTy k.toTy` (proved below). -/
def renderKeyTy : KeyTy → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"

/-- The WIT lowering (the emitter's spelling; 07 R1's lowering over the
    closed `Ty` — ONE fold, TOTAL, so exhaustiveness IS the
    change-management system: a new constructor refuses to compile until
    this match grows an arm). The correspondence grade per row:

    LOSSLESS — the rendering determines the type:
    `bool`/`u64`/`i64`/`string` are WIT's own scalars;
    `option`/`list`/`result` recurse over their payloads.

    RETRACTION-WITH-NOTE — the lossy rows (13-interfaces' rule: the WIT
    view is the lossy one, never the baseline; the loss is DECLARED
    here, not silent):
    - `map k v` → `list<tuple<K, V>>`: WIT has no map. The
      association-list form is the nearest shape; key uniqueness and
      canonical key order are payload invariants the WIT type cannot
      carry (a duplicate-key list is WIT-valid, schema-invalid).
    - `set k` → `list<K>`: WIT has no set. BYTE-COLLIDES with
      `.list k.toTy` (pinned: `renderTy_set_list_collision`); element
      uniqueness is a payload invariant.
    - `bounded cap` → `u64`: WIT has no bounded integers — the cap is
      schema metadata the WIT boundary cannot carry. BYTE-COLLIDES with
      `.u64` (pinned: `renderTy_bounded_u64_collision`); `bounded c1`
      and `bounded c2` conflate, and a wire value over the cap becomes
      representable.

    Key positions route through `renderKeyTy` (the sub-universe fold). -/
def renderTy : Ty → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"
  | .option t => s!"option<{renderTy t}>"
  | .list t => s!"list<{renderTy t}>"
  | .result ok err => s!"result<{renderTy ok}, {renderTy err}>"
  | .map k v => s!"list<tuple<{renderKeyTy k}, {renderTy v}>>"
  | .set k => s!"list<{renderKeyTy k}>"
  | .bounded _ => "u64"

/-! ## The lossless fragment (the correspondence row, 07 R1 step 3) -/

/-- The lossless FRAGMENT: `t.witLossless = true` iff `renderTy t`
    determines `t`. The map/set/bounded rows are OUT (the lossy
    lowerings above — each names its loss); the scalars and the three
    wrappers recurse over their payloads. -/
def Ty.witLossless : Ty → Bool
  | .bool => true
  | .u64 => true
  | .i64 => true
  | .string => true
  | .option a => a.witLossless
  | .list a => a.witLossless
  | .result ok err => ok.witLossless && err.witLossless
  | .map _ _ => false
  | .set _ => false
  | .bounded _ => false

/-- THE NAMED COLLISION (the lossy `set` row): a set's lowering is
    byte-identical to the plain list over the same key type — the
    collision is the declared loss, pinned here as data. -/
theorem renderTy_set_list_collision (k : KeyTy) :
    renderTy (.set k) = renderTy (.list k.toTy) := by cases k <;> rfl

/-- THE NAMED COLLISION (the lossy `bounded` row): every cap lowers to
    `u64` — caps conflate with each other and with plain `u64`. -/
theorem renderTy_bounded_u64_collision (cap : Nat) :
    renderTy (.bounded cap) = renderTy .u64 := rfl

/-- Pairwise surface distinctness over a CONCRETE type list (decidable;
    the lossless injectivity PIN at the slice's granularity — the
    fragment's lowerings are pairwise distinct on the ctor sample,
    `decide`-checked, not asserted). A `false` verdict names a surface
    collision; the named ones are the lossy rows' pins. -/
def witSurfaceDistinct : List Ty → Bool
  | [] => true
  | t :: rest =>
      rest.all (fun t' => renderTy t != renderTy t') && witSurfaceDistinct rest

/-- THE PIN: the lossless ctor sample's lowerings are pairwise distinct
    (kernel `decide` over the one fold). -/
example : witSurfaceDistinct
    [.bool, .u64, .i64, .string, .option .u64, .list .string,
     .result .u64 .string] = true := by decide

/-- The lossy rows' fragment verdicts (the flagged exclusions). -/
example : (Ty.map .string .u64).witLossless = false := rfl
example : (Ty.set .u64).witLossless = false := rfl
example : (Ty.bounded 42).witLossless = false := rfl
example : (Ty.result .u64 .string).witLossless = true := rfl

theorem renderKeyTy_toTy (k : KeyTy) : renderKeyTy k = renderTy k.toTy := by
  cases k <;> rfl

example : witSurfaceDistinct [.list .string, .set .string] = false := by decide
example : witSurfaceDistinct [.u64, .bounded 42] = false := by decide

end SchemaCore
