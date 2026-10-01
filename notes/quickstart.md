# The quickstart — one table, the whole spine

The 10-minute path: write a `table!`, get the Rust/TS/WIT/wasm faces,
persist, query, observe, evolve, and let the gates judge. The running
example IS the dogfood: every command below was run against this tree
(the observed outputs are quoted; a step that fails here is a tree
finding, not your error).

Why the tree is shaped this way: [`notes/v3/README.md`](v3/README.md)
(the two sentences) → [`notes/architecture.md`](architecture.md) (the
map). The full concepts: [`notes/guide.md`](guide.md).

## Prerequisites

- **Lean + lake**: the pinned toolchain (`lean-toolchain`:
  `leanprover/lean4:v4.33.0` — elan picks it up on first `lake` call).
- **just**: the recipe runner (`nixpkgs#just`; the recipes are thin
  wrappers over `lake`/`cargo` — read the `justfile`, it is the recipe
  surface's spec, `notes/v3/09-gates-ops.md` §3).
- **Nightly Rust + cargo** (step 5 only): `crates/rust-toolchain.toml`
  pins `nightly` — fast-observe's generated fault surface needs
  `error_generic_member_access` (the honest cost, surfaced in the
  toolchain note; a nix-pinned nightly works without rustup).

## 1. Build

```
just build
```

## 2. Declare a table

Write a scratch file anywhere OUTSIDE the tree (it needs no lakefile
row — `lake env lean` compiles it against the built env):

```lean sketch
import SchemaCore

table! Invoice where
  key: id
  id : UInt64
  customer : String
  total : UInt64
  rule: PositiveTotal := .u64GtLit "total" 0
```

```
lake env lean /tmp/mandate-qs/First.lean    # silence = elaborated
```

That ONE declaration bought the whole entourage (what each clause
expands to: `schemacore/SchemaCore/Surface.lean`'s module header):

- the plain structure + the `@[schema]` mount — the SAME registration
  the attribute face uses; the ONE reflection path
  (`Describe.reflectItemViaDescr`) is fed, never bypassed;
- `key:` — the `KeyDecl` row into the keys lane, at the declaration
  (no second module, no string record-ref);
- `rule:` — the `CheckItem` row into the check lane (the violating
  rows are the payload — `notes/v3/02-data-plane.md` §1);
- the codecs — `deriving WireCodec, row_bridge` INJECTED by default
  (the derivation stays lazy; an explicit `deriving:` clause
  overrides);
- nothing emitted on refusal: every analysis (types, refs, versions,
  the diff) runs BEFORE the first emission.

A verbatim in-tree example (the ref target first — a `ref:` needs its
target registered WITH a key):

```lean
table! Customer where
  key: id
  id : UInt64
  name : String
```

(`schemacore/SchemaTests/SurfaceV1.lean` — the migration fixture's
old face.)

**The refusal is curated.** Typo a clause and the elaborator refuses
with the legal vocabulary + the did-you-mean (observed output):

```
error: [SR0001] error: table!: unknown clause `ky` — the clause list
is a closed world (field lines are `name : type`) (got: ky) — valid:
key:, ref:, rule:, deriving:, name : type — did you mean: key:?
```

The E-codes are registry-allocated, never hand-strung
(`notes/code-registry.txt`).

## 3. Get the faces (Rust + TS + WIT + wasm)

```
just gen           # the schema slice's writers
just wasmgen       # the binary lane
just componentgen  # the component lane
```

Observed (the writers announce every path): `gen/schema-slice.wit`,
`gen/schema-slice.ts` (the JSON interop face — the wire of record is
the byte codec), `crates/schema-generated/src/lib.rs` + its test/bench
suite, the duel vectors under `crates/*/tests/duel/*.bin`,
`gen/wasm-slice.{wat,wasm}` + the `.hdr` sidecar, the 38-vector wasm
duel set, `gen/component-*.{wit,wasm}`.

**The byte-tie**: these paths have exactly ONE writer each (the exes
above); a hand edit fails the gate. Check it:

```
lake exe gates gen-check
# gen-check: clean — 88 artifact(s) byte-tied (text + binary lanes; ...)
```

Re-running the writers is always safe — drift-free regen is the
gate's law (`notes/v3/13-interfaces.md`).

## 4. Persist (the delta log)

The host's persistence lane is the hand-written Rust crate
`crates/mandate-delta` — it invents NO format: every byte it writes
is a byte `SchemaCore` emits (the frame is `encDelta`: one tag byte
in ctor order + the self-delimiting payload; atoms are
canonical-minimal varints, zigzag i64, char-varint strings — the map:
`crates/mandate-delta/README.md`).

The duel vectors were written by step 3's `just gen`
(`crates/mandate-delta/tests/duel/*.bin`): Lean computed every byte
through the landed journal codec; the crate must decode, re-encode
byte-identical, and refuse the four tamper splices. Run it:

```
cd crates/mandate-delta && cargo test
```

Observed: green (the duel rows + the torn-tail recovery's sweep — a
torn snapshot at every offset falls back and reports).

## 5. Query (qlang!)

`qlang!{ … }` is a Lean QUOTATION, elaborating directly to the typed
`Q` — columns resolve BY NAME at elaboration, and the term is
SELF-TYPED (a mis-typed query fails at elaboration, never at
evaluation). Verbatim from the tree (`query/QueryTests/QLangSpecs.lean`,
over the worked 3-column schema):

```lean
def qBig := qlang!{ from bFields then select (total > 100) }
def qAnnIds := qlang!{ from bFields then select (name == "ann") then project [.id] }
def qUnion := qlang!{ from bFields then select (id > 2)
  then union qlang!{ from bFields then select (name == "bob") } }
```

The stage pipe is `then`; the refusals are QL0002–QL0005 (a column
miss carries the did-you-mean; a projection's columns must be
distinct; a union branch must read and yield the same schema). The
end-to-end tooth: the elaborated query ≡ the hand-written `Q`, both
evaluators agree:

```
lake exe QueryTests
# [qlang] ok the qlang! surface: elaboration ≡ the hand-written Q,
#         both evaluators agree: PASS ... 8/8 specs passed
```

## 6. Observe (faults + the E-codes)

Every curated refusal in the tree is the ONE `Kit.Diag` envelope with
a registry-allocated code — you met SR0001 in step 2, QL0002–0005 in
step 5. The Rust fault face is GENERATED, not hand-rolled:

```
lake exe faultsgen
# faultsgen: 4 fault(s) rendered — crates/mandate-faults/src/lib.rs written
```

The rendered file is the typed-error enum in fast-observe's `error!`
syntax — the macro generates `code()`/`category()`/`advice()` + the
registry entries; the codes map onto `#[code]` verbatim (ONE registry,
two faces). It is a byte-tied artifact like every other (step 3's
gen-check covers it); the nightly requirement is step 0's note.

## 7. Evolve (the v2 discipline)

The first declaration of a name IS v1. Evolution is a version BUMP —
`table! Account v2 where …` — and the registry (which IS the
accumulated event log) diffs v1→v2 and DERIVES the upcaster; the
unsupported shapes refuse AT ELABORATION (removals, unremedied
retypes, reorders, key moves, additions without a default).

The version chain rides imports — the registry's rows replay per
module — so the tree's fixture is TWO modules
(`schemacore/SchemaTests/SurfaceV1.lean` declares `Account` v1;
`schemacore/SchemaTests/Surface.lean` bumps it):

```lean
-- `limit` added at the END with the type's default (the fill's source);
-- the key carried UNCHANGED (stable identities).
table! Account v2 where
  key: id
  id : UInt64
  owner : String
  limit : UInt64
```

A versioned declaration with no prior version in a fresh process
refuses (observed):

```
error: [SR0005] error: table! Widget: versioned declaration with no
prior version in the registry — the first declaration of a name is v1
(no `v<N>` spelling); a version rides the registry's OWN event log
(got: Widget)
```

Run the evolution teeth:

```
lake exe SchemaTests
# the v1→v2 plan's key-stability, the removal-direction control,
# the negative controls (SR0001/SR0003/SR0005 ×4) ... 58/58 specs passed
```

## 8. The gates' discipline

```
just check   # the fast tier: build + the light gates + lint
just gates   # the full battery: axioms, coverage, kernel-check included
```

The closed run order is `Gates.gateNames` (14 rows:
`notes/architecture.md` §3). The rules you just lived under: the
byte-tie (step 3), the persisted E-code registry (steps 2/6), the
snapshot baseline (the evolution face reads it), the loud `--write`
re-baseline discipline (NEVER hand-edit a baseline; drift is
reported, the INTEGRATOR re-baselines). A red gate names the gate +
the divergence — never a bare failure.

## 9. Where to go next

- [`notes/guide.md`](guide.md) — the user guide (the concepts, in the
  order a user meets them).
- [`notes/architecture.md`](architecture.md) — the map of every
  library, surface, and gate row.
- The scaffolder: an application skeleton from a declarative AppSpec —
  `scaffold/Scaffold/Specs.lean` (the adopted specs) +
  `lake exe scaffoldgen <Name>`; the adopted skeletons live in
  `DemoApp/` + `LedgerApp/` (the fill obligations land in each hand-
  owned `Flow.lean`).
- The six-word vocabulary's honest boundary: `table!` lands
  `table`/`key`/`ref`/`rule`/`deriving:` today; `state` and `event`
  are the NAMED next rows (`SchemaCore.Surface`'s module header —
  the gaps are declared, not hidden).
