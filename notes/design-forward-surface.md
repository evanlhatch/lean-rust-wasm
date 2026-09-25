# The Forward Surface — making new targets marginal-cost

Owner's goal: "vortex fleshing-out, additional codegen targets besides
Rust, more Lean DSLs like qlang, more wire targets — isomorphic,
shared-foundation, straightforward to add." This note designs the four
target families' interfaces against the code AS IT STANDS (mandate
branch), with a census per family, the landing sequence, and the honest
gaps.

Doctrine slots this note names (per the diff rule): 05 §1–2 (grammar,
emitters), 07 R1/R4 (target/DSL recipes), 13 (the interface index),
15 #2/#10/#17/#18 (codec law, emitter spine, recursion wall, streaming
codec), 16 §2 (the compile-to rule) + §4.6 (typed contexts ride with
the first real language).

---

## 0. The census method

Every claim below is measured over the live tree. The four surfaces
share one observation: **the shared foundation already exists and is
good** — `Kit.Emit`'s plugin model, `Fold.lean`'s one walk, `Kit.Mangle`,
`Kit.Varint`, `TextKit.Grammar`, `Kit.Correspondence`'s grades,
`Kit.Duel`. What does NOT exist is the last factoring that turns
"the Rust emitter" into "the spine, parameterized" — target #1 and the
spine are still one module. Everything else in this note is that
factoring, stated per family.

---

## 1. The target-parameterized emitter spine

### 1.1 Census: `SchemaCore.Emit.Rust` (1,333 LOC)

Measured by section (schemacore/SchemaCore/Emit/Rust.lean):

| LOC band | Section | Class |
|---|---|---|
| 1–143 | header, imports, `descrOfTy`/`itemDescr` (:144,:152) | GENERIC (the description lift is target-independent) |
| 175–289 | `tyRust` (:175), `keyEncAlg` (:204), `encAlg` (:216), `keyDecAlg` (:246), `decAlg` (:258) | TARGET (the type map + the wire's Rust statement templates) |
| 298–483 | `libPrelude` (:298) | TARGET (the Rust runtime helpers: varint/bool/zigzag/string/bounded + the typestate markers) |
| 490–743 | `rustStrLit`, `universeTypesRust` (:515), `renderKeyLookup` (:562), `renderFinder` (:577), `renderBuilder` (:597), `renderSerde` (:675) | TARGET (the API discipline faces) |
| 745–958 | `renderRecord` (:745), `valueRust` (:803), the migration face (:794–943), `libRope` (:945) | MIXED — `libRope`'s section walk is generic; every leaf is target |
| 960–1270 | the duel: `goldenExample`/`atomGoldens`/`tamperVectors`/`duelVectors` (:983–1060) | GENERIC (the vector bytes are `SchemaCore.Codec.encVal`'s — wire data, not Rust data); `differentialRope` (:1071) is TARGET (the Rust test consumer) |
| 1273–1333 | `rustEmitter` (:1259), the consumer-suite pins | TARGET (pins) + one more generic emitter row |

**The split: ~94% target-specific / ~6% generic inside the module.**
But the honest denominator is not the module — it is what a second
target must re-derive vs re-ride. The generic machinery the Rust target
CONSUMES lives already-shared outside it:

- the plugin model + one-writer + certified lane: `Emitter` structure,
  `outputs_nodup` in the type (`kit/Kit/Emit.lean:209`),
  `runCertified`, `outputsDisjoint` (:279), the driver loop
  `runEmitters` (:331) + the binary twin (:374), the ledger rows;
- the item walk: `foldTy`/`TyAlg`/`KeyTyAlg`
  (`schemacore/SchemaCore/Fold.lean:101–146`) — the enc/dec templates
  are ALREADY algebras, not hand walks (the module header records the
  migration);
- the mangler: `Kit.Mangle`'s ONE word split + per-target conventions
  (`kit/Kit/Mangle.lean:36–85`: `camel`/`pascal`/`snake`/`kebab`/
  `rustIdent`) + the post-mangle uniqueness bridge;
- the rope: `Kit.Text` (`cat`/`sepBy`, proved render laws);
- the byte-tie: `Kit.Emit.tieText`/`tieBytes`
  (`kit/Kit/Emit.lean:195`) + the goldens channel
  (`SchemaCore.Emit.lean`'s `goldensBody`);
- the duel: `Kit.Duel`'s vector-set convention (`duelVectors` is 27 LOC
  of pure rows).

**The finding:** the spine is NOT in `Emit/Rust.lean` — it is in Kit
and healthy. What keeps target #2 at ~1,300 LOC today is that the
section ORDER (prelude → universe faces → records → migration), the
record block assembly (`renderRecord`), and the file list are
hardwired with Rust leaves interpolated. The seam is `renderRecord` +
`libRope`, not the plugin model.

### 1.2 The design: `CodeTarget` — the spine parameterized over one structure

07 R1 already prescribes the pieces (a lowering over the closed `Ty`,
a typed target AST, a correspondence row, an Emitter row). This
names the structure they fold into:

```lean sketch
/-- ONE codegen target. The spine (walk registry → assemble sections →
    emitter rows → byte-tie) is THIS structure's single consumer; a
    target lands as rows, never as a new walk. -/
structure CodeTarget where
  /-- The typed TARGET AST (07 R1 step 2: misrendering unconstructible).
      The WIT migration (Emit.lean's `witTy` + `Wit.Render`) is the
      precedent: the AST carries the nodup/well-formedness facts in the
      type; the renderer is the ONE total fold AST → text. -/
  AST  : Type
  /-- The lowering instance over the closed universe — leaves +
      wrappers, NEVER a new universe (07 R1 step 1). Total; the sum
      case refuses curatively until the target's sum spelling lands. -/
  tyOf : Ty → Except Diag AST
  /-- The ONE renderer (the WIT precedent: `Wit.Render.ty`). -/
  renderTy : AST → Text
  /-- The identifier conventions: the registry name → the target's
      spelling per position, all through the ONE word split
      (Kit.Mangle.words). Rides the post-mangle uniqueness bridge. -/
  identTy : String → String          -- types (pascal)
  identVal : String → String         -- values/fields (camel/snake)
  /-- The wire's statement templates: the SAME `TyAlg (…)` algebras
      `encAlg`/`decAlg` are today — the wire is SchemaCore.Codec's,
      the templates are its target face. The append-form law holds
      Lean-side ALREADY; these rows render it. -/
  encAlg : TyAlg (String → String)
  decAlg : TyAlg (String → String)
  /-- The literal face (the migration lane's `valueRust` — total over
      the closed universe; `option` on the retype gap). -/
  litOf : (t : Ty) → Value t → Option Text
  /-- The runtime prelude: the helpers the templates call. -/
  prelude : Text
  /-- The API discipline faces, as DATA over each item (07's "rows +
      instances" rule): a face = a name + a render function over the
      item's (name, field types). The builder / lookups / serde faces
      become `faceRows` entries; a target opts in per face. -/
  faces : List (TargetFace)
  /-- The keyword/comment/escape lane (today: `rustIdent`,
      `CommentStyle`). -/
  escape : String → String
  style : CommentStyle
```

`TargetFace`:

```lean sketch
structure TargetFace where
  name : String                       -- "builder" | "keyLookup" | "serde" | …
  render : Item → Text                -- the face's template over one item
  /-- The face's behavior pins, the emitter renders verbatim (the
      commit-slice emitter's hand-authored-pin discipline). -/
  tests : List String
```

**What moves into the generic spine** (a new `SchemaCore.Emit.Spine`
— the leftover rule's consumer is target #2 itself):

- the section assembly now hardcoded in `libRope`
  (`Emit/Rust.lean:945`): `prelude ++ universeFaces ++ (records sepBy
  "\n\n") ++ lanes ++ "\n"` — parameterized over `CodeTarget`;
- `renderRecord`'s SKELETON (decl block → encode → decode →
  decode_full → faces), with the leaves from `encAlg`/`decAlg`/faces;
- the universe-faces slot (`universeTypesRust`'s position — a target
  may emit none);
- the emitter rows (`rustEmitter`'s shape is target #N's shape);
- the duel's vector computation + the emitter-with convention
  (`duelVectors`/`duelEmitter` — generic today already, just co-located).

**What stays target fields:** `tyOf`/`AST`/`renderTy`, the two algs,
`litOf`, `prelude`, the face list, `escape`, and the generated-test
consumer text.

**The WIT lane joins the same spine.** `SchemaCore.Emit.witEmitter` is
already the typed-AST shape (the `Wit.Ty` carrier, `witTy` :78–96,
`witTy_tie` :123). After the seam, `wit` is a `CodeTarget` row and
`regen`'s file list is `spineEmitters (targets := [wit, rust, …])` —
one regen, N renderings, the byte-tie unchanged (Emit.lean's `regen`
is already the ONE copy, :310–330).

**Success metric (07's growth number):** target #2 = AST type + ~8
`tyOf` arms + ~10 `TyAlg` rows + prelude + face opts ≈ **≤150 LOC of
target-specific code** (plus the target's test pins, which are
authoring, not machinery). Today's cost: ~1,300.

### 1.3 What target #2 must NOT get for free

The Rust module's honest notes are target-specific judgments that do
NOT belong to the spine: the map→`Vec<(K,V)>` order-preserving
divergence, the strum/newtype dep judgments, the typestate builder.
The `TargetFace` indirection is exactly so these stay Rust rows — the
spine must not grow a `features : List Feature` enum (that is the
parallel-table anti-pattern 15's meta-pattern forbids).

---

## 2. The wire-target family

### 2.1 Census: what the existing formats share

| Format | LOC | Law form | Shared substrate |
|---|---|---|---|
| `SchemaCore.Codec` (the binary wire) | 1,113 | append-form per atom (`decBool?_encBool_append` :178 et al.) + exact-image inversion | `Kit.Varint` (THE one LEB128, 198 LOC), `Kit.Correspondence.Codec` grade |
| `Substrait.Text` | 638 | round-trip at fuel, scalar fragment (`parseScalarGo_typeChars`), the recursive `list` arm honestly DEFERRED (pattern #17's wall) | token tables as prefix↔ctor bijections, `TextKit` parsers |
| `SchemaCore.Snapshot` | 1,501 | the Grammar value's laws (`Grammar.print_parse`, `run_print_fixFree`) — generated | `TextKit.Grammar` (the ONE bidirectional grammar engine) |
| `Wit.Parse` | (grammar values :1316–1350) | the layered composition (pattern #17: the recursive `tyAtom` hand zone, ONE induction) | `TextKit.Grammar` + the guarded-lexeme leaf |
| `Vortex.Codecs` | 771 | pattern #18: append-form + `inDomain` + the off-domain negative control | `Kit.Varint`, its own LSB-first bit-stream layer |
| `Kit.Json` | DELETED (wave-30 A6) | — | trigger never fired: the tree's one manifest stays tab-delimited by design (07's parked table) |

**What they already share:** the varint (one copy — the consolidation
is recorded in `SchemaCore.Codec`'s header), the law's APPEND FORM
(patterns #2/#18 — byte codecs), the Grammar value + generated laws
(text codecs), the grade vocabulary (`Kit.Correspondence`: `Iso` :49 >
`Retraction` :92 > `Codec` :167 > `Normalization` :323 > `Simulation`
:377 / `Abstraction` :434), the duel vector-set, the byte-tie.

**What they do NOT share:** there is no single "wire target" row —
each format re-states its entourage (vectors, gates, 13-interfaces
row, E-codes) ad hoc. The checklist lives in prose (05 §5's acceptance
gate, 13's row rule) but not as a structure the gate can scan.

### 2.2 The design: `WireTarget` — the format's checklist as a structure

```lean sketch
/-- ONE wire format: the grammar/codec + the law + the entourage tier.
    The 07-recipe row (R7, proposed) and the 13-interfaces row are
    GENERATED from this row (the docs-check reads it). -/
structure WireTarget (A : Type) where
  /-- The bytes (binary) or the Grammar value (text) — one of the two
      proven carriers, never a third. -/
  carrier : WireCarrier A          -- .bytes | .grammar (TextKit.Grammar A)
  /-- THE law, in the form the carrier forces:
      binary  — pattern #2/#18 append form, dec (enc a ++ rest) = some (a, rest),
                admissibility gated by inDomain at the emission boundary;
      text    — parse (print x) = ok x + print (parse t) = canonicalize t (05 §1).
      The statement lives in the structure; a format whose law is
      deferred carries the DEFERRED ROW here (Substrait.Text's list
      arm is the precedent) — never a missing field. -/
  law : LawStatement
  /-- The admissible subdomain (binary lane) + its mandatory negative
      control vectors (pattern #5): the off-domain loss PINNED. -/
  inDomain : A → Bool := fun _ => true
  offDomainControls : List (Σ a, ¬ inDomain a) := []
  /-- The correspondence grade — the strongest honest one
      (Kit.Correspondence). A lossy codec keeps the conditional form
      and cites the byte layer (pattern #18's honesty rule). -/
  grade : GradeStatement
  /-- The entourage tier (16 §3's weakest-sufficient): which evidence
      the format owes — vectors, golden module, duel, 13-row. -/
  entourage : Entourage
```

```lean sketch
/-- The evidence entourage, as data (16 §3's computed tiers). -/
structure Entourage where
  vectors : Option Kit.Duel.VectorSet   -- the differential's bytes
  goldens : Bool                        -- the goldens-module channel
  byteTie : { text, bytes, sidecar }    -- the gate's channel
  ifaceRow : String                     -- the 13-interfaces.md row id
```

**What a NEW wire format provides** (e.g. protobuf for the substrait
port, arrow-ipc for vortex): carrier row (a byte codec per message —
the proto wire is varint tags + field ordinals, so `Kit.Varint` is
already the shared atom), the append law per message (protobuf's
non-self-delimiting fields compose exactly this way), the
`inDomain`/controls for the narrowed fragment (the typed layer's
refusals — `u64` has no substrait spelling — ARE the inDomain
boundary, `Substrait/Typed.lean:316`), the grade (`Retraction` for a
lossy fragment), the entourage rows. **No new law machinery, no new
gate, no new vector convention.**

**Census conclusion:** the shared fraction is ~70% (varint, law form,
grades, duel, byte-tie, Grammar engine). The missing 30% is purely the
`WireTarget` row making the checklist SCANABLE — worth landing WITH
the first new format, not before (the leftover rule).

---

## 3. The DSL pattern: qlang

A Lean-embedded query language lowering to substrait, then to the
query lane's evaluation.

### 3.1 What exists (the free foundation)

- **The typed core**: `Query.Q fs gs` (`query/Query/Expr.lean:104`) —
  the typed fragment with the COMPUTED result schema; `QSat` (:140) is
  the spec of record; `evalQ_true_iff` (`Query/Eval.lean:464`) is the
  eval bridge; the key-backed join's determinacy rides the Keys lane
  (`keyJoinRows_atMostOne`).
- **The substrait lowering discipline**: `Substrait.Typed` — `Expr`/
  `Rel` over SchemaCore's closed `Ty`, `HasCol` with the `resolves`
  proof field, and TWO pinned bridge theorems: `Expr.toProto_ords`
  (:441, the wire ordinal IS the instance's index) and
  `Rel.toProto_width` (:641).
- **The typechecker**: SchemaCore's closed `Ty` + `Value` GADT — a
  mistyped literal is unconstructible; `Pred` is the selection
  fragment qlang shares.
- **The entourage**: 16 §3's computed tiers; the duel convention; the
  E-code registry.

### 3.2 The shape

Three layers, each riding an existing spine:

**Surface** — the `qlang!` macro over the two-idiom vocabulary (16
§2's `query Pending := Orders where state = .pending` spelling). The
honest gap: `dsl!` does not exist yet — the grammar engine does
(`TextKit.Grammar`, with the Snapshot and Wit.Parse instances; the
Check module already speaks of "build-time errors (dsl!/the …)" at
`TextKit/Grammar/Check.lean:298`). 05 §1 + 07 R4's rule is
"third-or-later DSL MUST use dsl!" — qlang is the third surface in
tree terms (snapshot grammar, WIT grammar precede), so **qlang is the
consumer that lands `dsl!`**, per the leftover rule. Until `dsl!`
lands, a hand term-elaborator would be R4's forbidden trio.

**Typed core** — qlang's elaborated form IS `Query.Q` (+ `Pred`
selections), with the term-elab precedents: by-name column references
resolve through instance search exactly as `Substrait.Typed`'s `HasCol`
does — the misspelled column fails at elaboration, and the resolution
proof rides the term. Q's second index (the computed result schema) is
the typechecker qlang gets free; no new universe.

**Lowering** — `qlangToRel : Q fs gs → Except Diag (Typed.Rel fs gs)`:
a `CodeTarget` instance in §1's sense (the query lane's target), with
the correspondence row stated ONCE at the structure: the lowered rel's
evaluated rows = the Q's `QSat` rows. The two disciplines to cite:
`Substrait.Typed`'s ordinal/width bridges (the wire faces), and
`Query.Eval`'s `evalQ_true_iff` (the semantic face). The duel is
free: the vectors are `evalQ`'s outputs vs the substrait evaluator's
(`Substrait/Eval.lean`), the sabotage control mandatory (pattern #5).

**What qlang gets FREE:** the typechecker (the GADTs + `HasCol`
elaboration-time resolution), the entourage (tiers, duel, codes), the
duel + negative-control discipline, the determinacy typing (the
Option-vs-collection shape rides the Keys lane, not qlang), the
substrait lowering's two bridge theorems. **What it must build:** the
`dsl!` grammar spec + the `Q → Typed.Rel` bridge module (the honest
gap below). Estimated: grammar rows ~60, elaborator glue ~50
(via `dsl!`), lowering ~120, ties ~60 ≈ **~300 LOC**, of which the
bridge is permanent shared surface.

### 3.3 The qlang gap that is NOT free

`Query.Q` indexes over `List Field` schemas; `Substrait.Typed.Rel`
indexes over `Schema = List (String × Ty × Bool)` (nullability). The
bridge must reconcile the two schema spellings — ONE `PartialIso`
(`Col → Field` + the nullability-face note), proved once, cited by
both lanes. 16 §4.6's typed-context substrate also parks until qlang
(or the guest language) needs scoped binding — aggregation does
(`Expr.lean`'s honest boundary: no aggregation/negation/ordering yet);
qlang v0 is the projection/select/join/union fragment, honestly.

---

## 4. Vortex fleshing-out

`vortex/` is 1.7k: `Encoding.lean` (406: the pure selection), `Codecs.lean`
(771: the byte codecs), `Emit.lean` (120: the layout emitter). Pattern
#18 (streaming/append-form codec) just landed WITH FoR/constant as the
canonical pair.

### 4.1 The marginal-encoding checklist (what the next encoding provides)

From the FoR/constant template (`Vortex/Codecs.lean` + `Encoding.lean`):

1. **Vocabulary row**: an `EncodingSpec` ctor + its applicability
   predicate + its `select` guard row (constant → sequence → dict →
   FoR → fallback; `Encoding.lean`'s locked order) + `select_
   applicable`'s new case (~15 LOC).
2. **The codec**: append-form law `dec (enc xs ++ rest) = some (xs, rest)`,
   composed through the varint/bit-stream layers (the compound laws are
   one-line instances chained through the varint's law — #18's whole
   point) (~60–100 LOC).
3. **The admissible subdomain**: `inDomain`-shaped width/range gate +
   the off-domain loss PINNED in `VortexTests` (pattern #5; constant's
   non-constant-column loss is the template) (~20 LOC).
4. **The semantic grade**: a `Kit.Correspondence` instance — `Codec`
   grade where lossless; the conditional form where lossy, citing the
   byte layer (never lying about the grade) (~15 LOC).
5. **The emitter row is FREE**: `layoutOf` picks it up through the
   selection function; `renderEncoding` grows one string row;
   `layoutLaw_discharged` stays a one-citation theorem
   (`Vortex/Emit.lean:78–83`).
6. **Negative control + golden pins** in the test lane (~30 LOC).

**Estimated: ~150–200 LOC per encoding**, all rows + instances.

### 4.2 The queue, with each exclusion's named trigger (from `Encoding.lean`'s header)

- `runEnd` — needs DATA facts (runs/cardinality): the data-dependent
  half discharges on the obligation ladder's `oracleSwept` tier. First
  consumer: any measured-column lane. The `ShapeFacts` structure grows
  a data-facts variant — the one structural change in the queue.
- the container level (framing/metadata/flatbuffers) — explicitly
  parked at `Vortex.Codecs.lean`'s boundary note; lands with the write
  path (the named follow-up). Arrow-ipc as a `WireTarget` (§2) is its
  natural form.
- `ALP` — blocked on floats: 16 §4.5's semantic-profiles lane is the
  honest route (`Float Deterministic` codec-legal), never a silent
  wire row.

---

## 5. The marginal-target scoreboard

| Target | Today (no shared foundation) | With the foundations landed | ≤150 rule |
|---|---|---|---|
| New codegen target (TS/Go/C) | ~1,300 LOC (copy `Emit/Rust.lean` and edit leaves) | **~120–150** target rows (`tyOf` arms + `TyAlg` rows + prelude + face opts); test pins extra | MET if prelude ≤80 and faces are opted-in rows; the spine + byte-tie + duel ride free |
| New wire format (protobuf, arrow-ipc) | ~400–1,100 (per-atom laws + entourage re-stated ad hoc) | **~150–250** per-message codec rows + entourage ROW (the `WireTarget` structure makes the rest generated/scanned) | MET for a fragment-narrowed format; a full-format port is a PORT (mined content), not a marginal target — name it as such |
| New DSL (qlang) | first-of-kind: no `dsl!`, no Q→Rel bridge | **~300** (grammar rows via `dsl!` + the bridge + ties); typechecker/entourage/duel/determinacy free | NOT met at v0 — qlang lands `dsl!` + the bridge (permanent shared surface); the SECOND DSL after qlang is the one that measures ≤150 |
| New vortex encoding | (first-of-kind was FoR/constant: the discipline's cost) | **~150–200** per encoding (the #18 checklist) | MET |

Cross-family amortization: `Kit.Varint`, the append-form law,
`Kit.Correspondence`'s grades, `Kit.Duel`, the byte-tie, `TextKit.
Grammar`, `Kit.Mangle`, and the closed-`Ty` folds are shared by ALL
four families — each new target strengthens every other's evidence
base for free.

---

## 6. The landing sequence

1. **The `CodeTarget` seam** (§1.2): extract `SchemaCore.Emit.Spine`
   from `renderRecord`/`libRope`'s skeleton; Rust + WIT become the
   first two rows. Gate: `just gen` byte-identical (the gen-check IS
   the migration's proof — the WIT AST migration set this precedent).
   *Everything in family 1 rides this; nothing else is blocked.*
2. **The `WireTarget` row** (§2.2) lands WITH the first new wire
   format (protobuf for substrait is the likely first: the typed
   layer's refusal fragment already names its `inDomain`). 07 grows
   recipe R7; 13's row points at the structure.
3. **`dsl!` + the Q→Rel bridge**, then qlang (§3): the bridge is
   pure surface-free work (startable immediately); `dsl!` lands with
   qlang as its consumer per the leftover rule.
4. **Vortex encodings** (§4): independent of 1–3; the #18 discipline
   is landed. `runEnd`'s data-facts variant is the only sequencing
   constraint (it wants the obligation-lane's oracle tier).

## 7. The honest gaps (where the shared foundation does NOT exist yet)

| Gap | Costs | Blocks |
|---|---|---|
| `dsl!` does not exist (only prose + the Grammar engine) | a real macro layer (~200–400 LOC of elab machinery), the doctrine's own acceptance test for it | qlang's surface; any fourth DSL |
| The Q↔Typed.Schema bridge (Field vs Col spellings) | one `PartialIso` + proofs (~60 LOC) | qlang's lowering |
| The binary byte-tie's gate wiring (`Kit.Emit.tieBytes` is built; the gen-check wiring for binary artifacts is the named follow-up — `Emit/Rust.lean`'s duel header) | small gate row | any binary wire format's committed-artifact channel |
| `runEnd`'s data-facts tier (oracleSwept discharge) | an obligation-lane instance, not new machinery | runEnd, ALP-adjacent encodings |
| Aggregation in the Q fragment (02 §2's named boundary) | new semantics with named laws — deliberately out | qlang v1+ |
| The Rust lane's identifier-cleanliness gap (uncompilable generated code on non-clean names — `Emit/Rust.lean`'s header) | the mangle-uniqueness bridge already exists in Kit; wiring it as an emitter-law conjunct is ~20 LOC | target #2 (fix it in the SPINE during step 1, so every target inherits it) |
| 16 §4.5 semantic profiles (the float route) | a whole lane, deliberately parked | ALP, any float-bearing target |

## 8. The acceptance test for this note

Each design above is accepted iff it is rows + instances of an
existing recipe (07 R1/R4 + this note's new rows enter 07 WITH their
first consumer), names its doctrine slot, and its "free" claims cite
landed theorems (`evalQ_true_iff`, `toProto_ords`, `foldTy_unique`,
`witTy_tie`, the append-form laws) rather than hopes. The scoreboard's
≤150 numbers are the phase gates' growth metric — reviewed at each
phase boundary per 07.
