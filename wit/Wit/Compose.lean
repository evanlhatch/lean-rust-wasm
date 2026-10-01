/-
# Wit.Compose — the wac composition as a relation (wave-30 D4)

Owner: the composition lane (the mandate tree, `wit/` — the Wit lib's
newest module; the component graph rides the LANDED WIT carrier, never
a second type grammar).

Driving decisions: notes/design-wave-30.md D4 (the component graph =
nodes + typed edges; interface compatibility = a join; unresolved
imports = a negation query; the composition spec in Lean → the
generated wac file; the interposition/DI seam — middleware as
component composition) + notes/v3/08-capabilities.md §30-31 (the
middleware chain; the provider DAG, acyclicity as a Statement) +
notes/v3/02-data-plane.md §2 (the negation boundary: "no import is
unresolved" is the empty-list reading over the CLOSED artifact set —
the named semantics, never a blanket claim) + the legacy audit's
splicer-mw mining (legacy/crates/splicer-mw/ — the passthrough splice
+ the counting middleware over wac; the interposer's shape is THIS
file's `interpose`).

## The graph discipline

- `Node` — a component: the kebab instance name + the package id +
  its `Wit.World` (the contract the D2 extension landed — the
  resources/streams rows render AND parse (`Wit.Parse`'s package +
  world faces): the composition's fixtures still ride the scalar
  fragment, honestly).
- `Wire` — one TYPED edge: the consumer's import item (the wired id)
  ← the provider's export item. The wire carries NAMES; the TYPES
  ride the items through `SigEquiv` (the join).
- `CompGraph` — the nodes + the wires, both nodup IN THE TYPE (the
  `DataRegistry` pattern; the runtime route is `mkChecked`'s decided
  refusal, never a silent acceptance).

## The verdicts (ctors, never strings)

- THE JOIN: `SigEquiv` — an import edge resolves iff a provider
  export's interface matches: funcs by (params, result, async),
  interfaces by name. The executable face is `sigAgree` (decide); the
  session duality reading (the world as the session type, the
  mismatch as a duality failure) is `Wit.Session`'s named remainder —
  the join here is its signature-level fragment (the async conjunct
  is that bridge's first face: a sync import must NOT join an async
  export — the call sessions disagree, `Wit.Session.exportTape`).
- `unresolved` — THE NEGATION QUERY, honestly named (02 §2): an
  import is unresolved when NO export in the graph's closed export
  pool joins it; "no import is unresolved" is the empty-list reading.
  Decidable over the finite graph, so the boundary does not bite —
  but the semantics is the closed world of the artifact set, nothing
  more.
- `Skew` — the version-skew witness: a WIRE whose endpoints exist,
  whose items exist, and whose signatures DISAGREE (matched by name,
  mismatched in shape).
- `findCycle` — the provider-DAG discipline (08 §31): the
  consumer→provider dependency walk, fuel-bound, the cycle's PATH as
  data (the witness carries the repeated head — the closure).
- `Verdict`/`check` — `.ok` / `.unresolved` / `.skew` / `.cycle`, in
  that priority.

## The interposition seam

`interpose` — the edge (host → guest) becomes (host → mw) ++ (mw →
guest): the middleware is a node interposed ON the edge (the
passthrough splice's Lean model). The middleware's world: import what
it exports (the splicer-mw v1 shape: count → delegate → return
unchanged — the counter is the mw's own state, outside the signature
relation). THE LAW: `passthrough_id` — a passthrough middleware's two
edges compose to the direct edge's compatibility (the honest Lean-side
claim: the end-to-end SIGNATURE is preserved; the faults/
observability middlewares land their implementation faces when the
wasm face exists — the named remainder).

## The wac emitter

`wacFile` — the checked composition's artifact: the wac text through
the Kit.Emit discipline's shape (a pure total function spec → file,
the 2-line GENERATED header, the content hash = `String.hash` — the
byte-tie's contract, tied in WitTests against the committed fixture).
THE HONEST TIER: `wasm-tools` is absent in this env (checked), so the
validation tier is the Lean-side check (`check`) + the artifact's
byte-tie; the wac grammar's accepted subset (package line, component
decls, `new` instantiations with `import` wirings) is the artifact of
record's shape, and the tool's validation is the named follow-up.

Cone: imports `Wit` + `Wit.World` only (the WIT lane's core face;
`Wit.Parse`'s Kit import is the precedent — this module needs none).

The five questions (notes/v3/01-core.md):
- root: Crossing — the component graph read as data over the WIT
  worlds (the composition's contract side).
- carrier grade: the nodup facts ride the TYPE (`nodes_nodup`,
  `wires_nodup`); the join is a Prop with a decide evaluator.
- spine reading: the Interpretation stage's composition face — the
  graph folds the worlds; `wacFile` is its text face.
- ladder rung: rung 1 — closed data + decided defaults + one hand
  theorem (the passthrough law).
- gate row: the axiom report (the `Wit` root's sweep) + the WitTests
  byte-tie (the artifact face).
-/
module


public import Wit
public import Wit.World


@[expose] public section
namespace Wit.Compose

/-! ## the graph -/

/-- One component node: the kebab instance name, the package id (the
    wiring's namespace face), the world (the contract). -/
structure Node where
  name : String
  pkg : String
  world : Wit.World
deriving Repr, Inhabited

/-- One typed edge: the CONSUMER's import item (the wired id) served
    by the PROVIDER's export item. The types ride the items (the
    join); the wire carries the names. -/
structure Wire where
  consumer : String
  imp : String
  provider : String
  exp : String
deriving Repr, Inhabited, DecidableEq

/-- The wire's uniqueness key: the (consumer, import id) pair — a
    consumer's import id is wired once. -/
def Wire.key (w : Wire) : String := w.consumer ++ "." ++ w.imp

/-- The component graph over the WIT worlds: the nodes, the typed
    edges, both nodup IN THE TYPE (the `DataRegistry` pattern — a
    duplicate-named literal fails to elaborate through the `by decide`
    default; the runtime route is `mkChecked`'s decided refusal). -/
structure CompGraph where
  id : String
  nodes : List Node
  wires : List Wire
  nodes_nodup : (nodes.map Node.name).Nodup := by decide
  wires_nodup : (wires.map Wire.key).Nodup := by decide
deriving Repr, Inhabited

/-- The runtime route of the in-type nodup (the constructor's decided
    refusal — a graph built from runtime names either carries the
    facts or is not constructed). -/
def CompGraph.mkChecked (id : String) (nodes : List Node) (wires : List Wire) :
    Option CompGraph :=
  if h : (nodes.map Node.name).Nodup ∧ (wires.map Wire.key).Nodup then
    some ⟨id, nodes, wires, h.1, h.2⟩
  else none

/-- The node's export item by name. -/
def Node.export? (n : Node) (item : String) : Option Item :=
  n.world.exports.find? (·.name == item)

/-- The node's import item by name. -/
def Node.import? (n : Node) (item : String) : Option Item :=
  n.world.imports.find? (·.name == item)

/-! ## the join (the compatibility check) -/

/-- THE JOIN — the two items' interface compatibility, at the Prop
    level: funcs by (params, result, async), interfaces by name (the
    by-name form's body check is `Wit.Session`'s named remainder —
    the duality reading's fragment). Mixed shapes never join; the
    async flag is part of the signature (a sync import's call session
    closes at the result; an async export's appends the lift's two
    moves — `Wit.Session.exportTape`). -/
def SigEquiv : Item → Item → Prop
  | .func f, .func g =>
      f.params = g.params ∧ f.result = g.result ∧ f.async = g.async
  | .iface i, .iface j => i.name = j.name
  | _, _ => False

-- The join's decidability (the executable face needs it).
deriving instance DecidableEq for Field

instance itemSigDecidable (a b : Item) : Decidable (SigEquiv a b) := by
  cases a <;> cases b <;> simp only [SigEquiv] <;> infer_instance

/-- The join's executable face: `decide` over the Prop — the two
    faces agree by construction (`sigAgree_iff`). -/
def sigAgree (a b : Item) : Bool := decide (SigEquiv a b)

theorem sigAgree_iff (a b : Item) : sigAgree a b = true ↔ SigEquiv a b :=
  decide_eq_true_iff

/-- The join is transitive (the passthrough law's engine). -/
theorem sigEquiv_trans {a b c : Item}
    (h1 : SigEquiv a b) (h2 : SigEquiv b c) : SigEquiv a c := by
  cases a <;> cases b <;> cases c <;> simp_all [SigEquiv]

/-- One wire's RESOLUTION: both endpoints exist as nodes, both items
    exist as declared world items, and the items JOIN. -/
def wireResolves (g : CompGraph) (w : Wire) : Bool :=
  match g.nodes.find? (·.name == w.consumer) with
  | none => false
  | some c =>
    match c.import? w.imp with
    | none => false
    | some i =>
      match g.nodes.find? (·.name == w.provider) with
      | none => false
      | some p =>
        match p.export? w.exp with
        | none => false
        | some e => sigAgree i e

/-! ## the verdicts -/

/-- One unresolved import, as data (the witness names the consumer +
    the wired id). -/
structure Unresolved where
  consumer : String
  imp : String
deriving Repr, Inhabited, DecidableEq

/-- THE UNRESOLVED-IMPORTS QUERY — the negation, honestly named (02
    §2's boundary): an import is unresolved when NO export in the
    graph's CLOSED export pool joins it; "no import is unresolved" is
    the empty-list reading. The pool is the composition's own artifact
    set — the claim reaches exactly that far, never a blanket
    open-world statement. -/
def unresolved (g : CompGraph) : List Unresolved :=
  g.nodes.flatMap fun n =>
    n.world.imports.filterMap fun i =>
      if g.nodes.any fun p => p.world.exports.any fun e => sigAgree i e
        then none else some ⟨n.name, i.name⟩

/-- The version-skew witness: a wire matched by name, mismatched in
    shape. -/
structure Skew where
  consumer : String
  provider : String
  imp : String
  exp : String
deriving Repr, Inhabited, DecidableEq

/-- THE VERSION-SKEW CHECK: a wire whose endpoints and items exist
    but whose signatures DISAGREE. (An import with NO agreeing export
    anywhere is `unresolved`'s row — the skew needs the pool to have
    a match the wire missed.) -/
def skews (g : CompGraph) : List Skew :=
  g.wires.filterMap fun w =>
    match g.nodes.find? (·.name == w.consumer) with
    | none => none
    | some c =>
      match c.import? w.imp with
      | none => none
      | some i =>
        match g.nodes.find? (·.name == w.provider) with
        | none => none
        | some p =>
          match p.export? w.exp with
          | none => none
          | some e => if sigAgree i e then none else some ⟨w.consumer, w.provider, w.imp, w.exp⟩

/-- The node's providers (the dependency edge's direction: the
    consumer depends on the provider — 08 §31's DAG). -/
def providersOf (g : CompGraph) (n : String) : List String :=
  (g.wires.filter (·.consumer == n)).map (·.provider)

/-- The cycle walk: fuel-bound DFS over the provider relation. `some
    path` = the cycle's path as data (the repeated head is the
    closure); `none` = exhausted without repeat. -/
def cycleDfs (g : CompGraph) : Nat → List String → String → Option (List String)
  | 0, _, _ => none
  | fuel + 1, stack, cur =>
      if stack.contains cur then some (cur :: stack).reverse
      else
        match (providersOf g cur).filterMap
            (fun p => cycleDfs g fuel (cur :: stack) p) with
        | [] => none
        | c :: _ => some c

/-- THE CYCLE DISCIPLINE: the first cycle's path, or [] (the fuel =
    the node count + 1 bounds every simple path plus its closing
    repeat — a cycle must repeat a node within it, so the bound cannot
    mask a cycle). -/
def findCycle (g : CompGraph) : List String :=
  match g.nodes.filterMap (fun n => cycleDfs g (g.nodes.length + 1) [] n.name) with
  | [] => []
  | c :: _ => c

/-- The composition's verdict — ctors, never strings; the priority is
    unresolved, then skew, then cycle (each verdict's witness list is
    computed once). -/
inductive Verdict where
  | ok : Verdict
  | unresolved (us : List Unresolved) : Verdict
  | skew (ss : List Skew) : Verdict
  | cycle (path : List String) : Verdict
deriving Repr, Inhabited, DecidableEq

/-- The graph check: the verdicts in priority order. -/
def check (g : CompGraph) : Verdict :=
  match unresolved g with
  | _u :: _ => .unresolved (unresolved g)
  | [] =>
    match skews g with
    | _s :: _ => .skew (skews g)
    | [] =>
      match findCycle g with
      | [] => .ok
      | c => .cycle c

/-! ## the interposition seam -/

/-- THE INTERPOSITION SEAM: the wire (host → guest) becomes (host →
    mw) ++ (mw → guest) — the middleware is a node interposed ON the
    edge, REPLACING it (the passthrough splice's Lean model,
    legacy/crates/splicer-mw). `mwImport`/`mwExport` name the
    middleware's inner (imported) and served (exported) items. Refuses
    (none) on a name or wire-key collision — the runtime route of the
    in-type nodup. The middleware's OWN state (the counters, the
    spans) is outside the signature relation — the seam contract's
    honest boundary. -/
def interpose (g : CompGraph) (w : Wire) (mw : Node) (mwImport mwExport : String) :
    Option CompGraph :=
  let hostMw : Wire :=
    { consumer := w.consumer, imp := w.imp
      provider := mw.name, exp := mwExport }
  let mwGuest : Wire :=
    { consumer := mw.name, imp := mwImport
      provider := w.provider, exp := w.exp }
  CompGraph.mkChecked g.id (mw :: g.nodes)
    (hostMw :: mwGuest :: g.wires.filter (·.key != w.key))

/-- THE PASSTHROUGH MIDDLEWARE's executable test: it imports AND
    exports the item, and the two sides JOIN (the splicer-mw v1
    shape: count → delegate → return unchanged). -/
def passthrough (mw : Node) (item : String) : Bool :=
  match mw.import? item, mw.export? item with
  | some i, some e => sigAgree i e
  | _, _ => false

/-- THE PASSTHROUGH-IS-IDENTITY LAW: a passthrough middleware's two
    edges compose to the direct edge's compatibility — the interposed
    composition preserves the edge's end-to-end signature (the honest
    Lean-side claim: the SIGNATURE is what the graph discipline
    carries; the faults/observability middlewares' implementation
    faces land with the wasm face — the named remainder). -/
theorem passthrough_id {imp mwImp mwExp exp : Item}
    (h1 : SigEquiv imp mwImp) (hp : SigEquiv mwImp mwExp)
    (h2 : SigEquiv mwExp exp) : SigEquiv imp exp :=
  sigEquiv_trans (sigEquiv_trans h1 hp) h2

/-! ## the wac emitter (the artifact's text face) -/

/-- One wiring line: `import "<wired-id>": <provider>.<export>`. -/
def wacWiring (w : Wire) : String :=
  "    import \"" ++ w.imp ++ "\": " ++ w.provider ++ "." ++ w.exp ++ "\n"

/-- One instantiation block: the `new` over the node's incoming
    wires (wire order — the graph's declaration order). -/
def wacInst (g : CompGraph) (n : Node) : String :=
  "  new " ++ n.name ++ " {\n"
    ++ String.intercalate "" ((g.wires.filter (·.consumer == n.name)).map wacWiring)
    ++ "  }\n"

/-- The component declarations (node order). -/
def wacDecls : List Node → String
  | [] => ""
  | n :: ns => n.name ++ ": component;\n" ++ wacDecls ns

/-- The composition body: the package line, the component decls, then
    one `new` per node that has incoming wires (node order). Total;
    deterministic; the byte-tie's render face. -/
def wacBody (g : CompGraph) : String :=
  "package " ++ g.id ++ ";\n\n"
    ++ wacDecls g.nodes
    ++ "\ncomposition: component {\n"
    ++ String.intercalate ""
        ((g.nodes.filter (fun n => g.wires.any (·.consumer == n.name))).map (wacInst g))
    ++ "}\n"

/-- THE ARTIFACT: the wac text under the 2-line GENERATED header (the
    Kit.Emit discipline's text face at the Wit cone root — the header
    layout is `Kit.Emit.header`'s, the content hash is `String.hash`,
    the byte-tie's contract). The honest tier: `wasm-tools` is absent
    in this env — the validation is the Lean-side `check` + this
    byte-tie; the tool's validation is the named follow-up. -/
def wacFile (g : CompGraph) : String :=
  let body := wacBody g
  "// GENERATED by Wit.Compose.wacFile (the composition lane's wac emitter) — DO NOT EDIT\n"
    ++ "// spec compose-graph | " ++ toString g.nodes.length
      ++ " item(s) | content hash " ++ toString body.hash
      ++ " | regen: Wit.Compose.wacFile (byte-tied in WitTests); drift fails CI\n"
    ++ body

end Wit.Compose

end -- public section

