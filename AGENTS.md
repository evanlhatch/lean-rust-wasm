# macht — agent instructions

## The doctrine (the contract)

The governing doctrine is `notes/v3/` — read in this order:
`notes/v3/README.md` (index + execution protocol) →
`notes/v3/01-core.md` (three roots, one carrier, one spine) →
`notes/v3/02-data-plane.md` (the relational center; §2's cone rule) →
then the file your change touches (03–15). Every claim in a diff must
name its doctrine slot; a change that names none is a design failure.

## Hard rules

- **Zero `sorry`/`axiom`** in anything that lands; the axiom gate
  enforces (core triple + disclosed native_decide only). A missing
  theorem is information; a stub is a lie.
- **Byte-tie**: the spec of record is the COMMITTED generated universe;
  never hand-edit generated files; one writer per artifact path.
- **The leftover rule**: nothing lands without a consumer — no lib
  targets, directories, or files ahead of their first content. Applies
  at every phase boundary.
- **The patterns catalog** (`notes/v3/15-patterns.md`): land new shapes
  as instances of a cataloged pattern or extend the catalog
  deliberately — never invent a parallel table.
- **The cone rule** (`notes/v3/02` §2, `06` §8): kernel cones C0/C1
  stay mathlib-free; a cone-low module importing cone-high is a gate
  failure.
- Compile after every declaration; tests live in `<Package>/Tests/`;
  negative controls are mandatory for property sweeps.

## Build

```
just build   # lake build (the root package)
just test    # the package's tests
just gates   # the gate spine (byte-tie, axiom gate, lints)
```

The scaffold is honest emptiness: `just gates` prints "the scaffold:
nothing to gate yet" until the first gate rows land.

## Version control (jj)

The working copy IS a commit — small atomic changes, `jj describe` once
the change is known. NEVER `git checkout/reset/stash` — use `jj undo` /
`jj new`. Do not run `jj git push` from an agent session.

## The legacy tree

`legacy/` is the pre-v3 mining source: read-only reference; its builds
run only from its own history (`jj log`/`jj evolog`). Mine per
`notes/v3/14-build-map.md` — port content, never migrate in place.
