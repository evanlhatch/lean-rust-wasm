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

- **variants / funcs / worlds / `use`** — the mandate
  emitter emits NONE of them today (the item model is records-only,
  SchemaCore.Item's honest gap; the mined legacy surface lives at
  legacy/lean/schema-lang/SchemaLang/Emit/Wit.lean). They land with
  their consumers: variant items port (the `variant` decl), guest
  adapter generation (funcs + worlds), the skew check (its parser).
  Growing the closed `Ty`/item grammars is compiler-driven (every
  fold's exhaustiveness). PARTIAL GROWTH LANDED: the world carrier
  (`Wit.World` — funcs + worlds as data over the records-only item
  model) rides the component lane's emission (`Guest.Component`);
  variants/`use` are still out, with the same named consumers.
  THE D2 GROWTH LANDED (the honest narrowing): the resource rows —
  `Resource` (the interface-level declaration), `Ty.own`/`Ty.borrow`
  (the handle refs, the component-model's own/borrow spellings) +
  `Ty.stream`/`Ty.future` (the waitable rows) + the `result` face's
  one-summand completeness (`Ty.resultOk`/`Ty.resultErr`) — with the
  RENDERER extended over all of them (`Render.ty` stays total over
  the closed grammar) and the RESOURCE DECLARATIONS parsing (the
  engine-level `resourceLineG` rows, the round-trip laws extended —
  Wit.Parse's header). THE DEFERRED REMAINDER'S WALL WAS A
  CARRIER-CHOICE MISTAKE, now dissolved: the ty-level rows
  (`stream`/`future`/`resultOk`/`resultErr`/`own`/`borrow`) PARSE —
  the D2 finisher read `Kit.Codec.decode_encode`'s UNCONDITIONAL
  obligation against a ty-unconstrained carrier, but `WitOk`'s
  per-field `tyPre` conjunct IS the fragment gate riding the payload
  subtype (the WireTarget `conditionalRetraction` discipline: the
  law's domain narrowed by the carrier, never by a premise), so the
  rows land as parser arms + an honest `tyPre` shrink — every
  round-trip law extends as an instance. The fragment's residual
  gate is the handle refs' NAME discipline (`own<9bad>` refuses —
  the maximal-munch name run's head need not be alpha). Malformed
  stream/result/handle syntax refuses with the structured
  `ParseError` (the WitTests teeth). The lifecycle discipline rides
  the effects lane's resource split (`Wit.Resource`); the
  world-as-session reading is
  `Wit.Session`.
- **no parser** — `Wit.Render` is ONE-directional (AST → text, total).
  Text → AST (the skew-check's parser; the round-trip law) is a LATER
  order — no round-trip claim is made here.
- **the `i64` spelling** — the artifact of record renders `i64` (WIT's
  canonical spelling is `s64`); the byte-tie is the proof, and a
  renaming is a byte-breaking event (the breaking gate), not taken
  here. The ctor keeps the artifact's spelling.
- **no n-tuples** — WIT's tuples are n-ary; the toolkit emits only the
  pair, so `Ty.tuple` is binary. Larger arities land with a consumer.
- **the single-summand `result`** — the toolkit always emits both
  summands, so the D2 growth is the EMITTER's only consumer: the
  one-summand forms landed as `Ty.resultOk`/`Ty.resultErr` (the fault
  channel's faces; the D2 rows above). The bare parameterless `result`
  stays out (no consumer; its spelling would collide with a resource
  handle named `result`).
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
  | stream (α : Ty)
  | future (α : Ty)
  | result (ok err : Ty)
  | resultOk (ok : Ty)
  | resultErr (err : Ty)
  | tuple (a b : Ty)
  | own (name : String)
  | borrow (name : String)
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

/-- A WIT resource declaration (the interface-level row: `resource r;`).
    The handle's lifecycle discipline is `Wit.Resource`'s — the
    declaration is the NAME's row; the handle refs (`Ty.own`/`Ty.borrow`)
    name it. The decl-name and ref-name agreement is the consumer's
    check (the name-mangling precedent: the AST carries wire spellings). -/
structure Resource where
  name : String
deriving Repr, BEq, Inhabited

/-- A WIT interface: the record names AND the resource-declaration
    names are distinct IN THE TYPE (the same discipline — WIT rejects
    duplicate record names / duplicate resource declarations in an
    interface). The `resources` default keeps every pre-D2 literal
    constructing identically (the byte-tie's surface unchanged). -/
structure Interface where
  name : String
  records : List Record
  resources : List Resource := []
  records_nodup : (records.map Record.name).Nodup := by decide
  resources_nodup : (resources.map Resource.name).Nodup := by decide
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
