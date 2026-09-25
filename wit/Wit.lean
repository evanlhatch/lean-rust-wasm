/-
# Wit — the typed WIT AST (the target-side carrier)

Owner: the Wit agent (the mandate tree, `wit/`).
Driving decisions: notes/v3/07-extensibility.md R1 (a typed target AST
where the target supports it — misrendering unconstructible) +
notes/v3/05-codegen.md §2 (the emitter spine: the lowering produces
THIS carrier, the ONE renderer prints it) + notes/v3/13-interfaces.md
(the WIT worlds row: the emitter, the guest adapter generation, the
host skew check and the witness verification surface all speak WIT —
today through string templates with no AST; this is the carrier they
share).

## COVERAGE — exactly the subset the toolkit emits

The AST is the MINIMAL honest shape over the committed artifact of
record (`gen/schema-slice.wit`) and the mandate tree's WIT emitter:

- a `Package` (the id line, `package mandate:slice;`);
- `Interface`s (the emitter emits one, `items`);
- `Record`s of named fields (one per registered item);
- the type grammar the lowering actually produces: the four scalar
  atoms (`bool`, `u64`, `i64`, `string`), `option`, `list`,
  `result` (both summands — the emitted form), and the 2-`tuple`
  (the map lowering's `list<tuple<K, V>>` shape).

## EXCLUSIONS — each named with its consumer (the leftover rule)

- **variants / funcs / worlds / resources / `use`** — the mandate
  emitter emits NONE of them today (the item model is records-only,
  SchemaCore.Item's honest gap; the mined legacy surface lives at
  legacy/lean/schema-lang/SchemaLang/Emit/Wit.lean). They land with
  their consumers: variant items port (the `variant` decl), guest
  adapter generation (funcs + worlds), the skew check (its parser).
  Growing the closed `Ty`/item grammars is compiler-driven (every
  fold's exhaustiveness). PARTIAL GROWTH LANDED: the world carrier
  (`Wit.World` — funcs + worlds as data over the records-only item
  model) rides the component lane's emission (`Guest.Component`);
  variants/resources/`use` are still out, with the same named
  consumers.
- **no parser** — `Wit.Render` is ONE-directional (AST → text, total).
  Text → AST (the skew-check's parser; the round-trip law) is a LATER
  order — no round-trip claim is made here.
- **the `i64` spelling** — the artifact of record renders `i64` (WIT's
  canonical spelling is `s64`); the byte-tie is the proof, and a
  renaming is a byte-breaking event (the breaking gate), not taken
  here. The ctor keeps the artifact's spelling.
- **no n-tuples** — WIT's tuples are n-ary; the toolkit emits only the
  pair, so `Ty.tuple` is binary. Larger arities land with a consumer.
- **no single-summand `result`** — WIT allows `result<T>` and
  `result<_, E>`; the toolkit always emits both summands, so both are
  required — the one-summand forms are UNCONSTRUCTIBLE.
- **no name mangling** — record/field names arrive pre-mangled (the
  kebab lane lives upstream, target-specific by doctrine); the AST
  carries the wire spellings as strings.

## THE TYPING DISCIPLINE — what WIT makes invalid is unconstructible

- The type grammar is CLOSED (`Ty`): an arbitrary type string is not
  constructible; the wrappers are arity-exact by construction.
- `Record.fields_nodup` / `Interface.records_nodup` — duplicate field
  (resp. record) names are IN THE TYPE (the `DataRegistry` pattern,
  Kit.Registry): a duplicate-named literal fails to elaborate (the
  `by decide` default fires the kernel on concrete literals), and the
  runtime route is a decided refusal, never a silent acceptance (the
  construction boundary lives with the consumer — SchemaCore.Emit's
  `witCheckedOfReg`).
- `Package.interfaces` is a plain list (one interface today; interface
  name collisions are not yet a reachable shape — noted, grown with
  the multi-interface consumer).

Core-only (no imports — the cone root of the WIT lane).

The five questions (notes/v3/01-core.md):
- root: Crossing — the WIT target grammar the toolkit's lowerings
  produce (the typed face of notes/v3/13's WIT worlds row).
- carrier grade: the nodup facts ride the TYPE (`fields_nodup`,
  `records_nodup` — the DataRegistry pattern one level down); the
  renderer is total over well-formed ASTs by construction.
- spine reading: the Interpretation stage's target half — the
  lowering (upstream, per target lane) produces the AST; `Wit.Render`
  is the ONE text mechanics module (05 §2: the byte-tie is the
  correspondence evidence).
- ladder rung: rung 1 — closed data + decided nodup defaults; every
  checkable fact over concrete ASTs is a `decide`.
- gate row: gen-check (the byte-tie over `gen/schema-slice.wit` — the
  renderer's artifact-side proof) + the axiom report (the `Wit` root).
-/

namespace Wit

/-- The scalar atoms the toolkit's WIT lowerings produce. CLOSED —
    a new atom lands with the upstream `Ty` ctor that needs it (the
    exhaustiveness discipline drives both folds). The `i64` spelling
    is the artifact of record's (see the module header). -/
inductive Scalar where
  | bool
  | u64
  | i64
  | string
deriving Repr, BEq, DecidableEq, Inhabited

/-- The WIT type grammar: closed over exactly the shapes the
    toolkit's lowerings produce — the four atoms, the three unary
    wrappers, the two-summand `result`, the pair `tuple`. An arbitrary
    type text is UNCONSTRUCTIBLE (that is the point): every malformed
    WIT type shape fails here, at the carrier, before any renderer
    runs. -/
inductive Ty where
  | atom (s : Scalar)
  | option (α : Ty)
  | list (α : Ty)
  | result (ok err : Ty)
  | tuple (a b : Ty)
deriving Repr, BEq, DecidableEq, Inhabited

/-- One record field: the wire name + the WIT type. -/
structure Field where
  name : String
  ty : Ty
deriving Repr, BEq, Inhabited

/-- A WIT record: the field names are distinct IN THE TYPE (the
    `DataRegistry` pattern — a duplicate-named literal fails to
    elaborate through the `by decide` default; a runtime constructor
    decides the same fact and refuses loudly). WIT rejects duplicate
    record fields; here the rejection is the elaborator/kernel, not a
    renderer concern. -/
structure Record where
  name : String
  fields : List Field
  fields_nodup : (fields.map Field.name).Nodup := by decide
deriving Repr, Inhabited

/-- A WIT interface: the record names are distinct IN THE TYPE (the
    same discipline — WIT rejects duplicate record names in an
    interface). -/
structure Interface where
  name : String
  records : List Record
  records_nodup : (records.map Record.name).Nodup := by decide
deriving Repr, Inhabited

/-- A WIT package: the id (the `mandate:slice` form) + its interfaces.
    The emitter emits one interface today; the list is the honest
    growth surface (multi-interface packages land with the consumer
    that needs the split — the exclusions note in the header). -/
structure Package where
  id : String
  interfaces : List Interface
deriving Repr, Inhabited

end Wit
