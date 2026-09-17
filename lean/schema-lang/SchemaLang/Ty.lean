/-
# SchemaLang.Ty — the schema language's type universe

Target-NEUTRAL by design (the schema-lang rule): option/result/map/set/
future/stream are constructors HERE; how each target renders them is the
target lowering's job (WIT: option<T>/result<T,E>/list<tuple<K,V>>/
future<T>/stream<T>; Rust: BTreeMap/BTreeSet; OpenAPI: nullable +
oneOf; Vortex: nullable flag). No wire knowledge lives in this module.
Map/set KEYS ride the `KeyTy` scalar sub-universe — a non-scalar key is
unrepresentable (enforcement in the type; W8.1's default).

Type-driven surfaces, per the four-addresses axis (TOOLKIT Part 1):

- (a) data: `Ty` is a first-order inductive — emitters fold it, the oracle
  reads it, it serializes.
- (b) type-level: `Value : Ty → Type` — a value payload INDEXED by the
  type (a `.bool` value cannot carry a string). This is the bridge that
  later gives schema-typed validators and test-vector generation for free;
  Lean forbids Σ/nested-inductive under GADT params, so nothing here needs
  the wrapper (flatland's AnyExpr lesson — no heterogeneous lists yet).
- (c) proposition: `Ty.wellFormed` over a universe of known names.
- (d) instance: `EqAns` — DIRECTED, proof-carrying equality (`.yes h` /
  `.no`, no `Decidable` instance needed for open terms; the flatland
  Typed/Schema pattern). The `.yes` proof is what makes compat evidence
  and reindexing compositional downstream.

Deliberately omitted (containment, lean-v3 Part 10): nullability (WIT
`option<T>` IS the nullability; targets that use flags derive it),
generics (WIT has none — monomorphization is the emitters' job),
refinement predicates (the schema-indexed package owns `{x // P x}`;
v1 payloads are plain types).
-/


module

public import Lean

@[expose] public section
open Lean

namespace SchemaLang

/-! ## The universe -/

/-- A named type reference: must resolve to a record/variant in the item
    universe (checked by `wellFormed`, not by this type). -/
abbrev TyRef := String

/-- The hashable/comparable SCALAR sub-universe: map keys and set
    elements (W8.1's default — keys/elements are scalars). Floats are
    OUT (NaN breaks the total order a canonical map form needs);
    `bytes`, composites and named refs are OUT (no canonical hash).
    A non-scalar key is UNREPRESENTABLE — enforcement in the type, not
    a checker pass (the `RowVals` wrong-shape discipline; a predicate
    field on `Ty.map` would forfeit the derived `DecidableEq`/`BEq`).
    Every key injects into `Ty` via `KeyTy.toTy` (below, once `Ty`
    exists). -/
inductive KeyTy where
  | bool
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | string
deriving Repr, BEq, DecidableEq, Inhabited

/-- The schema type universe. -/
inductive Ty where
  | bool
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | f32 | f64
  | string
  | bytes
  | option (α : Ty)
  | result (ok err : Ty)
  | list (α : Ty)
  /-- A map with SCALAR keys (the `KeyTy` sub-universe) and arbitrary
      values. Boundary rendering is the TARGET's job (the tensor
      precedent): WIT `list<tuple<K,V>>` (WIT has no map — the
      association-list form, key uniqueness a documented invariant);
      Rust `BTreeMap<K,V>` (deterministic iteration — the runbook
      default, NOT `HashMap`); snapshot `map(K,V)`; Vortex a list of
      key/value structs (the parquet convention); the wire a
      length-prefixed entry list. The payload (`VMap` below) is an
      INSERTION-ORDERED association list — the `list` discipline:
      order is payload data, canonicalization (sort/dedup) is the
      emitter boundary's job. W8.2's declared-keys work is the first
      consumer of the key story. -/
  | map (k : KeyTy) (v : Ty)
  /-- A set of SCALAR elements (the `KeyTy` sub-universe, same row as
      map keys). WIT `list<T>` (uniqueness a documented invariant);
      Rust `BTreeSet<T>`; snapshot `set(T)`; the wire a
      length-prefixed element list. The payload rides `VList` —
      insertion-ordered, the `list` discipline. -/
  | set (α : KeyTy)
  | future (α : Ty)
  | stream (α : Ty)
  /-- A dense row-major tensor: static DIMS (outermost first, the
      TorchLean `Tensor α [dims…]` convention) over an element type.
      Boundary rendering is the TARGET's job (WIT: `list<elem>` — the
      flat form, dims dropped; Rust: `Vec<elem>`; snapshot: the paren
      encoding `tensor(dims…,elem)`); the dims are VERIFIED data — the
      payload constructor (TVal.tensor below) cannot hold a wrong-shape
      value, the `RowVals` discipline.

      THE LAYOUT LAYER (not built — no consumer yet): when a tensor
      first crosses the WASM memory boundary (a tensor field in a
      record = addressed offsets, not the self-describing wire lists
      this codec uses), the blueprint is flatland's
      `Flatland/Flatland/Tensor.lean`: `CoordsOf` (typed coordinates
      `Fin d₀ × Fin d₁ × …`), `flatIdxT` (the total row-major offset,
      the bound carried by types — the same telescope as
      `Layout.go_pairwise`), and `dot_inj` (the write-safety theorem —
      scatter through a view cannot alias). The ingress-validates-once
      bridge (`Coords.ofList?` + `flatIdxT_ofList`) is the pattern this
      codec's shape gate already mirrors at the value level. For the
      WIRE FORMAT of tensor DATA (bytes, not values): NumPy's `.npy`
      (header + raw row-major bytes) is the proven shape — see also
      leanprover/TensorLib (the NumPy engine model: unitStrides/
      startIndex zero-copy views, Dtype.itemsize, the LOrd
      NaN-excluded Float32 order) — an engineering reference, not a
      dependency (its shapes are runtime data; ours are indices). -/
  | tensor (dims : List Nat) (α : Ty)
  | ty (name : TyRef)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The key sub-universe INJECTS into `Ty`: every key is a scalar
    type. Emitters/codecs route key rendering through this — below the
    first fold a key position is a plain `Ty` again. -/
def KeyTy.toTy : KeyTy → Ty
  | .bool => .bool
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64
  | .string => .string

/-- The key's Lean reification, DIRECT (not `toTy`-routed — the
    indirection breaks `toType`'s structural recursion). Coherent with
    the injection by `toType_toTy`. -/
def KeyTy.toType : KeyTy → Type
  | .bool => Bool
  | .u8 => UInt8 | .u16 => UInt16 | .u32 => UInt32 | .u64 => UInt64
  | .i8 => Int8 | .i16 => Int16 | .i32 => Int32 | .i64 => Int64
  | .string => String

/-- The partial inverse: the scalar `Ty`s that ARE map/set keys
    (the snapshot parser's key gate — `map(f32,u64)` is a parse
    error, the type-level negative control). -/
def Ty.toKeyTy? : Ty → Option KeyTy
  | .bool => some .bool
  | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32
  | .u64 => some .u64
  | .i8 => some .i8 | .i16 => some .i16 | .i32 => some .i32
  | .i64 => some .i64
  | .string => some .string
  | _ => none

/-- `toKeyTy?` undoes `toTy` (the snapshot round trip's key arm). -/
theorem Ty.toKeyTy?_toTy (k : KeyTy) : Ty.toKeyTy? k.toTy = some k := by
  cases k <;> rfl

/-- `ReflBEq`/`LawfulBEq` for the derived structural `BEq` (core's
    `DecidableEq → LawfulBEq` instance is tied to the decidable-equality
    `BEq`, not the derived one — so the instances are discharged here
    with Init's own deriving tactics, `Init.LawfulBEqTactics`). -/
instance : ReflBEq KeyTy where
  rfl := by deriving_ReflEq_tactic

instance : LawfulBEq KeyTy where
  eq_of_beq := by deriving_LawfulEq_tactic

instance : ReflBEq Ty where
  rfl := by deriving_ReflEq_tactic

instance : LawfulBEq Ty where
  eq_of_beq := by deriving_LawfulEq_tactic

/-! ## Value payloads, indexed by type ((a) → (b) bridge)

A `Value t` can only hold data of type `t` — test vectors, fuzz corpora
and validators consume these; a mismatched payload is unconstructible. -/

mutual
inductive Value : Ty → Type where
  | bool : Bool → Value .bool
  | u8 : UInt8 → Value .u8
  | u16 : UInt16 → Value .u16
  | u32 : UInt32 → Value .u32
  | u64 : UInt64 → Value .u64
  | i8 : Int8 → Value .i8
  | i16 : Int16 → Value .i16
  | i32 : Int32 → Value .i32
  | i64 : Int64 → Value .i64
  | f32 : Float32 → Value .f32
  | f64 : Float → Value .f64
  | string : String → Value .string
  | bytes : List UInt8 → Value .bytes
  | some : {t : Ty} → Value t → Value (.option t)
  | none : {t : Ty} → Value (.option t)
  | ok : {ok err : Ty} → Value ok → Value (.result ok err)
  | err : {ok err : Ty} → Value err → Value (.result ok err)
  | list : {t : Ty} → VList t → Value (.list t)
  | map : {k : KeyTy} → {v : Ty} → VMap k v → Value (.map k v)
  | set : {k : KeyTy} → VList k.toTy → Value (.set k)
  | future : {t : Ty} → Value t → Value (.future t)
  | stream : {t : Ty} → VList t → Value (.stream t)
  /-- A tensor payload: shape-indexed by construction (the TVal
      family — a value for `.tensor [2, 3] t` cannot have the wrong
      shape, the `RowVals` discipline). -/
  | tensor : {t : Ty} → {dims : List Nat} → TVal t dims → Value (.tensor dims t)

/-- A value list. Nested inductives (`List (Value t)` inside the GADT)
    are forbidden by the kernel — the flatland `AnyExpr` lesson — so the
    list shape is its own sibling inductive in the mutual block. -/
inductive VList : Ty → Type where
  | nil : {t : Ty} → VList t
  | cons : {t : Ty} → Value t → VList t → VList t

/-- The map payload: an association list (the `VList` sibling rule —
    a nested `List (Value k.toTy × Value v)` under the GADT is
    kernel-forbidden). INSERTION-ORDERED, duplicate keys
    REPRESENTABLE: the `list` discipline — canonical form is the
    emitter boundary's concern (Rust's `BTreeMap` sorts, last-wins on
    duplicates; the wire preserves order) and the codec's round trip
    is per-payload. A consumer needing map EQUALITY canonicalizes
    first (none does yet — W8.2). -/
inductive VMap : KeyTy → Ty → Type where
  | nil : {k : KeyTy} → {v : Ty} → VMap k v
  | cons : {k : KeyTy} → {v : Ty} → Value k.toTy → Value v → VMap k v → VMap k v

/-- The shape-indexed tensor payload (the TorchLean `View` shape —
    `scalar`/`dim` over static dims). The outer dimension's slices ride
    the LENGTH-INDEXED `TSlices` sibling (not a `Fin n →` function — the
    list form is what the codecs build from flat wire data). The kernel
    trap is only NESTED type constructors over the GADT family (the
    `VList` sibling rule); length-indexed siblings are fine. The
    tensor's ELEMENTS are full `Value t`s — a `.tensor [2] .u64`
    element is a `Value .u64`. -/
inductive TVal : Ty → List Nat → Type where
  | scalar : {t : Ty} → Value t → TVal t []
  | dim : {n : Nat} → {t : Ty} → {dims : List Nat} →
      TSlices t dims n → TVal t (n :: dims)

/-- The length-indexed slice list under a `TVal.dim` (the `VList`
    pattern: a sibling per index shape). -/
inductive TSlices : Ty → List Nat → Nat → Type where
  | nil : {t : Ty} → {dims : List Nat} → TSlices t dims 0
  | cons : {t : Ty} → {dims : List Nat} → {m : Nat} →
      TVal t dims → TSlices t dims m → TSlices t dims (m + 1)
end

/-! ## Proof-carrying directed equality

`EqAns` is LOCAL (the demotion: the template's core is substrait-free —
substrait is the OPT-IN expression layer, and `Bridge` is the only
substrait consumer). The original lives in `Substrait.Typed.Schema`
(same `.yes h` / `.no` shape, proof-carrying directed equality); the
Bridge maps between the two copies, and their agreement is the bridge's
test.

`Ty` derives `DecidableEq` (first-order inductive — the flatland
`SType`/`SParam` mutual-block trap doesn't apply here), so the decision
is one `dite` and the proof rides the branch. The wrapper exists only
because `Option` cannot carry a `Prop`. -/

/-- The directed answer: a proven-or-not answer, `Prop`-safe (`Option`
    cannot hold a `Prop`). LIFTED from Substrait.Typed.Schema (verbatim
    shape) at the substrait demotion — the bridge maps the copies. -/
inductive EqAns (a b : α) : Type where
  | yes (h : a = b)
  | no

/-- The directed decision: kernel-derived decidability, proof in the
    `.yes` branch. -/
def Ty.eqAns (a b : Ty) : EqAns a b :=
  if h : a = b then .yes h else .no

/-- Boolean projection of the directed answer — the surface `Diff`
    routes its field comparison through. Callers that reindex keep
    `eqAns` itself (the `.yes` proof); the Bool is for verdicts. -/
def Ty.eqViaAns (a b : Ty) : Bool :=
  match Ty.eqAns a b with | .yes _ => true | .no => false

/-- The proof-carrying decision AGREES with derived `BEq` — routing the
    diff through `eqViaAns` changes no verdict (the Diff.lean comment's
    claim, discharged). -/
theorem Ty.eqViaAns_beq (a b : Ty) : Ty.eqViaAns a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [Ty.eqViaAns, Ty.eqAns]
  · have hno : Ty.eqViaAns a b = false := by simp [Ty.eqViaAns, Ty.eqAns, h]
    rw [hno]
    cases hb : a == b with
    | true => exact absurd (eq_of_beq hb) h
    | false => rfl

/-! ## Reification: the schema universe as Lean types

`toType` turns data-describing-types into TYPES. Named references are
open-world: one `RefTy` instance per schema type; an unresolved
reference fails at ELABORATION TIME the moment `toType` is used - the
universe check becomes a type-class check, strictly stronger than the
runtime `wellFormed` scan.

`future`/`stream` erase to their payload: the async wrapping is an
emission concern (WASI 0.3 future/stream at the boundary), not a Lean
type-level one. -/

/-- Open-world semantics for named type references: a function from
    schema type names to Lean types. Provided per schema; v1 universes
    are acyclic (self-reference needs depth fuel). -/
abbrev TySem : Type 1 := String → Type

/-- Reify a schema type as a Lean type. Unresolved references become
    whatever `sem` says (typically `Empty`) — and if `sem` is total over
    the universe, the wellFormed scan is SUPERSEDED by the kernel:
    unresolved refs are elaboration errors at the use site. -/
def Ty.toType : Ty → TySem → Type
  | .bool, _ => Bool
  | .u8, _ => UInt8
  | .u16, _ => UInt16
  | .u32, _ => UInt32
  | .u64, _ => UInt64
  | .i8, _ => Int8
  | .i16, _ => Int16
  | .i32, _ => Int32
  | .i64, _ => Int64
  | .f32, _ => Float32
  | .f64, _ => Float
  | .string, _ => String
  | .bytes, _ => List UInt8
  | .option a, sem => Option (a.toType sem)
  | .result ok err, sem => Sum (ok.toType sem) (err.toType sem)
  | .list a, sem => List (a.toType sem)
  -- the map/set Lean payload is the ASSOCIATION-LIST / element-list
  -- form (the wire shape — BTreeMap/BTreeSet are the Rust emitter's
  -- rendering, not the reification's)
  | .map k v, sem => List (k.toType × v.toType sem)
  | .set k, _ => List k.toType
  | .future a, sem => a.toType sem
  | .stream a, sem => a.toType sem
  -- the tensor's Lean payload is the ROW-MAJOR FLAT form (the dims are
  -- static verified data — TVal carries them; the Lean reading flattens)
  | .tensor _ a, sem => List (a.toType sem)
  | .ty n, sem => sem n

/-- The two key reifications agree (the direct one is the structural
    recursion's; the injected one is the emitters'). -/
theorem KeyTy.toType_toTy (k : KeyTy) (sem : TySem) :
    k.toTy.toType sem = k.toType := by
  cases k <;> rfl

/-- The `ToExpr` instance: a hand-written walk of the `Ty` universe
    (the deriving handler is unavailable because `ToExpr` lives in the
    `Lean` package, not in the prelude — Ty.lean is a pure universe
    definition with no prior ``Lean`` import; importing `Lean` is
    intentional, not incidental, to own the single canonical walk). -/
instance : ToExpr Ty where
  toTypeExpr := .const ``Ty []
  toExpr := go
where
  keyExpr : KeyTy → Expr
    | .bool => .const ``KeyTy.bool []
    | .u8 => .const ``KeyTy.u8 []
    | .u16 => .const ``KeyTy.u16 []
    | .u32 => .const ``KeyTy.u32 []
    | .u64 => .const ``KeyTy.u64 []
    | .i8 => .const ``KeyTy.i8 []
    | .i16 => .const ``KeyTy.i16 []
    | .i32 => .const ``KeyTy.i32 []
    | .i64 => .const ``KeyTy.i64 []
    | .string => .const ``KeyTy.string []
  go : Ty → Expr
    | .bool => .const ``Ty.bool []
    | .u8 => .const ``Ty.u8 []
    | .u16 => .const ``Ty.u16 []
    | .u32 => .const ``Ty.u32 []
    | .u64 => .const ``Ty.u64 []
    | .i8 => .const ``Ty.i8 []
    | .i16 => .const ``Ty.i16 []
    | .i32 => .const ``Ty.i32 []
    | .i64 => .const ``Ty.i64 []
    | .f32 => .const ``Ty.f32 []
    | .f64 => .const ``Ty.f64 []
    | .string => .const ``Ty.string []
    | .bytes => .const ``Ty.bytes []
    | .option a => .app (.const ``Ty.option []) (go a)
    | .result ok err =>
        .app (.app (.const ``Ty.result []) (go ok)) (go err)
    | .list a => .app (.const ``Ty.list []) (go a)
    | .map k v => .app (.app (.const ``Ty.map []) (keyExpr k)) (go v)
    | .set k => .app (.const ``Ty.set []) (keyExpr k)
    | .future a => .app (.const ``Ty.future []) (go a)
    | .stream a => .app (.const ``Ty.stream []) (go a)
    | .tensor dims a =>
        let dimsE := dims.foldr (fun d acc =>
          .app (.app (.app (.const ``List.cons [0]) (.const ``Nat []))
            (.lit (.natVal d))) acc)
          (.app (.const ``List.nil [0]) (.const ``Nat []))
        .app (.app (.const ``Ty.tensor []) dimsE) (go a)
    | .ty n => .app (.const ``Ty.ty []) (.lit (.strVal n))

end SchemaLang
