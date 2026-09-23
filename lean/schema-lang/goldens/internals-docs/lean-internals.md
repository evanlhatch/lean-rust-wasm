# Lean internals — module documentation

Generated from the elaborated environment (`Lean.getModuleDoc?`) at the
build of `SchemaLang.ModuleDocs`: the module manifest (`internalsModules`)
is data, the docstrings are VERBATIM environment replay. DO NOT EDIT:
regenerate with `just gen`.

## SchemaLang.Item

## Items 

## Well-formedness — resolution over the universe, with designed errors

The universe check returns STRUCTURED diagnostics (TOOLKIT §11.1: errors
enumerate the valid space, did-you-mean everywhere, never a bare Bool).
`universeWellFormed` stays as the Bool projection for gates; `universeCheck`
is the diagnostic authority.

The closed-world superpower: `unknownRef` carries the closest matches AND
the full valid space — for an LLM, an error that lists the valid moves is
a self-correcting prompt. 

## Reserved words — the identifier gate (elab-time, via the
    registration handlers in `Meta.Reflect`; also enforced by the pure
    `Item.check` for hand-built universes)

A field/case named `u8` would emit INVALID WIT (`record user { u8: ... }`)
and invalid Rust; the collision is caught HERE — at registration —
not downstream at wit-parser time. The identifier is checked in its
EMITTED spellings (kebab for WIT, snake for Rust).


## The diagnostic authority (supersedes the Bool) 

The dup-scan idiom, shared by the item / key / table-invariant
    lanes: the duplicated names of `ns`, ONE each, plus the lemmas the
    Prop-side bridges reduce through (`dupNames_eq_nil_iff`,
    `dupNamesDiags_eq_nil_iff` — one proof, every dup lane). 

## The Bool projection (derived from the diagnostic authority) 

## SchemaLang.Diff

## Field-level compat evidence (EqAns-based: WHICH fields moved) 

## SchemaLang.Validate

## The value-aligned row 

## The field path — the resolution's RUNTIME half 

## The cast kit (the TorchLean castShape suite, on GADT indices)

The registry's existential wrappers (`SomeUpdate.applyRow`,
`InvariantItem.checkOn`) transport a row across a DATA-equality of the
field list with raw `▸`. The named cast + its four lemmas make the
transport GREPPABLE and the proof-irrelevance usable: two consumers that
derived the same equality differently share a lemma (the cast does not
depend on which proof is used), and `▸`-inserted rewrites are the same
function (the bridge lemma keeps simp firing on elaborator-produced
goals).


## The indexed expression 

## The evaluators 

## Phase 3 — the variant family (the second indexed-expr family)

The honest-skip's scope, RESOLVED at the spec level. The second
family's full inventory, as predicted: its own variant-row type, its
own resolution classes, its own expression level, its own evaluator —
and the pin.

THE COMPILED-LANE DECISION (the strlen precedent, applied): the VCase
family is SPEC-LEVEL ONLY. `evalCase` constructs `Value` boxes (the
boxed reading — `evalV`'s reason, unmarked), and a RAW variant
evaluator would need the discr + joined-payload scalar level the
backend does not emit (the canonical ABI's f64→i64 payload join makes
the slot non-scalar — the demo's f64 arm is deliberately UNREAD). So
the registered variant validator (`GuestImpl.orderErrorValid`) KEEPS
the hand `match` — the tag case + the payload sproj is the shape the
backend already emits — and the VCase form (`orderErrorSpecValid`)
rides beside it, eval-tested against the mirrored case list in the
schema-lang tests.

Payload-access rules, BY CONSTRUCTION:
- SOME-payload cases get the arm-typed accessor (`payload`, its type
  index = the case's payload type); a NONE-payload case has NO
  accessor (`CasePath.here` exists only over `some t` heads) — the
  read fails at ELABORATION, never at runtime.
- The MISS case (the row's fired tag is NOT the queried arm) yields
  the 0-analog (`HasPayload.miss`) — an unfired slot's read is
  meaningless, so the guarded-usage pattern (`isCase` ∧ `payload`)
  discards it. The 0-analog exists for the valueable scalar fragment
  (u64/f64/bool/string); other payload types get no accessor yet
  (additive — the instances extend, the universe stays closed).
- `.ty`-ref payloads: a named ref has NO `Value` ctor (the boxed lane
  cannot value it), so those arms get no instance — the honest skip.


### The variant expression 

## The `[inv| …]` surface syntax — the DSL embedding (the ch. 8 pattern)

The Metaprogramming-in-Lean book's chapter 8 ("Embedding DSLs by
Elaboration"), IMP shape: a `declare_syntax_cat` for the invariant
language + a RECURSIVE elaborator into the `VExpr` constructors + a
`term`-level quoter. ADDITIVE: the `VExpr` ctors and the evaluators
above are untouched — this section only SPELLS them.

- The field-ref leaf rides `VExpr.colOf` — the `HasCol` instance
  search happens at the elaboration site, so the MISSPELLED field is a
  BUILD error (the same gate the hand spelling has, now through the
  syntax).
- Precedence: the book's `:50/:40` shape — `&&` binds tighter than
  `||`, the comparisons (`>`, `==`) tighter than both; the right
  operand parses at prec+1 (left associativity, the `infixl` recipe).
- `||` has NO VExpr constructor — it elaborates to the De Morgan form
  `not (and (not a) (not b))` (exact on Bool; no ctor added, the
  universe stays closed). `!` is the `not` node's spelling — it exists
  so the unexpanders (below) can round-trip EVERY tree the syntax can
  build.
- The unexpanders are the book's Pretty Printing pattern: per-ctor
  `@[app_unexpander]`, each matching the delaborated form INSIDE the
  pattern (the children arrive already unexpanded to `[inv| … ]`
  terms — the inner syntax is unwrapped and re-spliced, parenthesized
  when the child's top node binds looser than the operand position
  demands — the tree parses back to the SAME constructor tree).

No `set_option hygiene false`: the book's `myid` case is about a macro
EXPOSING a local name through hygiene marks; the unexpanders here run
at pp-time and construct RAW syntax (no marks), and every other name
is a global constant (resolved through marks).


### The unexpanders — a VExpr pretty-prints back to `[inv| … ]` 

## SchemaLang.Session

## The gateway instance, typed 

## Machines.Session

## Protocols 

## Payload-TYPED steps — generic over the payload universe (the CORE) 

## The session machine (Label = the script's indices) 

### Peer agreement as a TYPE — the elaboration-error property

`IsDualOf theirs mine` is inhabited EXACTLY when `theirs` is the typed
dual of `mine`. The generic instance is the only witness, so the peer's
script is COMPUTED by the unifier (deriving, not stating): a
hand-written script that disagrees — a direction that doesn't flip, or
a payload that differs at any position — fails definitional equality
at ELABORATION time. This is the type-level check the runtime cannot
skip: the mismatched conversation does not compile. 

## Machines.Sim

## The model: components + in-flight messages + clock 

## The step — deterministic by construction 

## (a) Schedule determinism 

## (b) No loss — queue conservation 

## (c) No deadlock — the non-stuck states are steppable 

## The queue diamond — two deliveries, either order 

## The demo — the CRDT point: schedule-independence 

## SchemaLang.Witness

## The claim language (design §2.1 — the first-order VExpr mirror) 

## The wire tags (ctor order — the EnumWire wire-breaking rule) 

## Encoders (structural on the data) 

## The flat decoders (WU64, WStep) 

## The tree decoders (depth-capped — see the module header) 

## The proof-term decoder 

## The claim decoder 

## The witness family as `LawfulCodec` instances (additive)

The round-trip theorems above, re-stated once as `Codec.LawfulCodec`
instances (the class lives in SchemaLang.Codec — qualified here, this
module's namespace is `SchemaLang.Witness`). Entry-point decoders only
— `decWBoolExpr?`/`decWProof?` ALREADY carry the depth cap's
sufficiency (fuel = bytes + 1, the `*_depth_le_length_enc` lemmas), so
their append laws are honest whole-value laws. `Witness` itself has NO
instance: its wire is the versioned envelope + a trailing-garbage
reject (not append-form) — `decWitness?_encWitness` below still rides
the class through the payload's four fields. 

## The witness wire (design §1: envelope + label + claim + proof + fuel) 

## Field resolution (design §2.1): names checked against the record 

## SchemaLang.WitnessCheck

## The mirror evaluators (the guest lane — `@[guest_std]`-gated)

Name-based field lookup over the decoded row (the wire carries NAMES;
the guest resolves them against the record's decoded field list). The
box match is `match h : f.ty with` + `h ▸ v` — matching `Value f.ty`
at an ABSTRACT `f.ty` does not elaborate (the index is a variable),
and splitting the tag in the LHS pattern makes the catch-all's
equation CONDITIONAL (a negative HEq side condition simp cannot
discharge); the equality-refined scrutinee compiles to ONE clean
equation (verified against the equation lemmas). The cast is
proof-irrelevant — identity at runtime. First-hit on duplicate names,
and a wrong-typed name-hit is `none`, not a skip — loud; the tie
theorems carry the uniqueness hypothesis (the header). 

## The checker (design §2.2–2.3) 

## The reasoning authority (design §2.4 — the Wf.lean template) 

## Soundness (the deliverable) 

## The fuel discipline (the substrait `parseType_mono` precedent) 

## The CheckedProp pack (the canon row — gaps LOUD) 

## The semantic tie to the compiled reading (design §2.4)

The mirror reflects a `VExpr` when field names resolve to paths; under
name uniqueness the name-based guest reading IS the path-based
compiled reading. 

## The W9.5 seam (the W9.6 mount point) 

## The fuel classifier (the apply-gate's refusal classes, made exact) 

## SchemaLang.WitnessSpec

> (no module docstrings in the environment — the header is a plain block comment, or the module has none)

## SchemaLang.Update2

## The v2 data 

## The semantics 

## The membership kit (derived sets earn the premises) 

## Law 1 — clause-order freedom WITHIN one update 

## Law 2 — neutrality under the multi-write 

## Law 3 — two write folds with disjoint columns commute 

## Laws 4/5 — the two-update order-freedom 

## Law 6 — the lowering to THE SHARED DELTA (R1 consolidation) 

### The keyed table semantics + the table-level correspondence 

### The lawful key kit (R5) — the `nodup2` family retired

`FieldVal.beq` IS equality on codec-closed keys (Keys.lean's
`beq_eq_true_iff_eq`, riding the codec's decode-encode round trip), so
the correspondence's key premises speak CORE `List.Nodup` and `≠`: the
hand-rolled `nodup2` def, its append decomposition, and the
`A ++ k :: B` both-direction inversion pack are gone. The honest price
is the closure of the key images (`CodecClosed` — key types are `KeyTy`
scalars, the W8.1 discipline): ONE closed type fact
(`keyFieldType` — the key column's own type) seeds ALL of them, because
the key projection's TYPE is determined by the field list + column
name — never by the row. 

### The applicator bridge (R1: ONE delta, ONE keyed reading)

The update lane's keyed applicator (`applyRowDelta`: update REPLACES
every key-matching row, remove DROPS them, insert APPENDS) and the
event-sourcing lane's (`EventSourced.apply`: insert/update UPSERT the
first match, remove erases the first) are the SAME keyed reading on
key-unique tables — the correspondence the W8.3 lowering law rides:
one shared Delta, two equivalent applicators. 

## The obligation view (W7.1's substrate, the keys-lane shape) 

## SchemaLang.Refine

## The range 

## The obligation tier (W7.1p2's decidableNow backend) 

## The word lane (the order's bv_decide backend) 

## The validator lane (the generated boundary check) 

## The monus tie (the canon row) 

## SchemaLang.PrePost

## The contract 

## The caller's boundary — the typed refusal 

## The post = the contract the correctness story cites 

## The obligation view (W7.1's substrate, the keys-lane shape) 

### The decidableNow backend (the uncited post's rung) 

## SchemaLang.TableInvariant

## The aggregation shapes 

## The item 

## The elaboration-gate checker (String diagnostics — the `checkCitation?` precedent) 

## The reasoning authority + the bridge (the Wf lane's table sibling)

The `Keys.lean` family, mirrored rung for rung: the checker's String
rungs get Prop mirrors (`TableAggFieldOk` ← `TableAgg.fieldDiags`,
`TableInvOk` ← `TableInvItem.diags`), each with its `_eq_nil_iff`
bridge, packed under `TableInvsWellFormed` and bridged to the Bool
gate by `tableInvWellFormed_iff` (the `universeWellFormed_iff` shape).


## The obligation view (what a table invariant MEANS, as data)

The substrate is the kit's `Obligation` (`SchemaLang.Keys`' sibling
lane): a table-invariant declaration produces ONE obligation; the
computed tier is `decidableNow`; the discharge's evidence is the
kernel's decide over a PROVIDED materialized table. 

## SchemaLang.Commands

## The declaration data 

## The well-formedness lane (the Keys shape: checker + relation + bridge) 

## The derived session — commands out, events in 

### The session row's laws — CITED, not re-proved

Every theorem below is the generic `Machines.Session` fact instantiated
at the derived protocol. The mechanism (duality, mid-protocol
deadlock-freedom, termination) is proved ONCE, generically; a world
declaration INHERITS the laws by composition — the session row's
inheritance rule. 

### The WIT view — the ONE renderer 

## SchemaLang.EntityMachine

## The declaration data 

## The legality relation (the canon: DFA membership) 

## The journal: the event log as deltas — the antijoin check, replay 

## The typestate hook (the Emit/Typestate projection, generalized) 

### The Rust items (the hook's emission shape) 

## The obligation view 

## The transition delta 

## SchemaLang.Meta.EventSourced

## The term builders (CoreM; the `Meta.Derive`/`Meta.Gen` builders
    are CommandElabM-typed and cannot ride an attribute handler — the
    shapes are theirs, the monad is the difference. The row-bridge
    builders — field literal, toRow cons-chain, ofRow nested match —
    live in `Meta.RowIso` now; only the `FieldsClosed` witness is
    event-sourcing-specific.) 

## SchemaLang.Meta.Keys

> (no module docstrings in the environment — the header is a plain block comment, or the module has none)

## SchemaLang.Meta.WireCodec

## The codec-supported atom instances (Codec.lean's atoms, once each) 

## SchemaLang.Meta.TableInvariant

> (no module docstrings in the environment — the header is a plain block comment, or the module has none)

## SchemaLang.Meta.Mono

> (no module docstrings in the environment — the header is a plain block comment, or the module has none)

## Machines.Fusion

## Bridge 1 — the D/I pair as a Kit Iso 

## Bridge 2 — the convergence bridge (cascade settle = machine
termination = dbsp fixpoint) 

## Bridge 3 — bisimulation as stream equality 
