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

## The docs

The doctrine lives in [`notes/v3/`](notes/v3/README.md) — start at its
reading order (01-core first; everything else is an instance). The
build process and the port/rework map: [`notes/v3/14-build-map.md`](notes/v3/14-build-map.md).
The pre-v3 tree is preserved under [`legacy/`](legacy/README.md) as the
read-only mining source.

## Build

```
just build   # lake build (the root package)
just test    # the package's tests
just gates   # the gate spine (byte-tie, axiom gate, lints)
```

The scaffold is the first commit of the fresh v3 build (see
`notes/v3/14-build-map.md` §4); libraries arrive with their first
content, cone-ordered (C0 machinery → C1 cores → C2 theory → C3 apps).
