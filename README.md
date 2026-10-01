# mandate

The formally-modeled application toolkit: model an application in Lean —
data, changes, behavior, protocols, obligations — and generate its
Rust/WASM/WIT/vortex surfaces with the correctness flowing down by
construction.

**The architecture in two sentences.** Structure composes;
interpretations preserve structure; proofs compose through explicit
relations. Every crossing declares the strongest honest law and reports
what survives — wrongness does not elaborate, does not synthesize, does
not typecheck.

## Start here

- **The quickstart** — [`notes/quickstart.md`](notes/quickstart.md):
  write a `table!`, get the Rust/TS/WIT/wasm faces, persist, query,
  observe, evolve — every step verified against this tree.
- **The user guide** — [`notes/guide.md`](notes/guide.md): the concepts
  in the order a user meets them.
- **The architecture map** — [`notes/architecture.md`](notes/architecture.md):
  every library, surface, and gate row, with its owner.
- **The doctrine** — [`notes/v3/README.md`](notes/v3/README.md): the
  why of the shape (reading order: 01-core first; everything else is
  an instance).

## The gates' discipline

Correctness here is enforced, not claimed. A closed registry of 14
gates (`gates/Gates.lean`) reads the tree after every change: the axiom
sweep (zero `sorry`/`axiom` outside a disclosed allowlist), the
byte-tie (every generated artifact has exactly one writer; a hand edit
fails CI), the pure-kernel replay, the docs fence check, coverage,
breaking-change detection. You never hand-edit a generated path or a
gate baseline — regen is mechanical, re-baselining is a deliberate
loud act. Run:

```
just check   # the fast tier: build + the light gates + lint
just gates   # the full battery: axioms, coverage, kernel-check
just ci      # CI runs EXACTLY this (build + tests + gates + rust)
```

A red gate names the gate + the divergence — never a bare failure.

## The honest status

What works end-to-end is named in the quickstart and the map; the
OPEN gaps are declared where they live, never hidden: the `table!`
vocabulary's `state`/`event` words are named next rows
(`schemacore/SchemaCore/Surface.lean`'s header), the query join
carries a named refusal (`QL0001`), and the remaining wave rows are
the plan (`notes/design-wave-30.md`). The build process and the
port/rework map: [`notes/v3/14-build-map.md`](notes/v3/14-build-map.md).

The pre-v3 tree is preserved under [`legacy/`](legacy/README.md) as the
read-only mining source — port content, never migrate in place.
