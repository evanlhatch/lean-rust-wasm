---
title: Getting Started
description: The 30-second quickstart — scaffold a Lean-spec'd WASM project.
---

Mirror of the [root README's quickstart](https://github.com/evanlhatch/lean-rust-wasm#30-second-quickstart).

## Prerequisites

- [Nix](https://nixos.org) with [devenv](https://devenv.sh)
- [elan](https://lean-lang.org/lean4/doc/setup/) — the toolchain is pinned
  at Lean 4.33.0

## 30 seconds

```sh
git clone <this-repo> && cd lean-rust-wasm
devenv shell --profile wasm     # wasm toolchain + wasip3 guest linking
just new-project my-thing       # scaffold lean/my-thing from template/
```

## The loop

```sh
# edit lean/my-thing/MyThing.lean (spec) and MyThingFn.lean (bodies)
just gen            # regenerate every artifact from the spec
just wasm-compile   # LCNF → WAT → component; regenerates the oracle manifest
just gates          # the full lean↔rust drift check, one shot
```

`new-project` auto-registers the package in the gate loops and prints the
manual follow-ups (the WIT world's fold, the gen driver, the lint row).
The recipe self-verifies via `just scaffold-test`.

## What you get for free

- **Proved schemas** — the spec of record is kernel-checked Lean; the
  registry reflects it; no hand-maintained type list survives.
- **Byte-tied codegen** — every artifact is committed and drift fails CI.
- **The breaking gate** — schema evolution is diffed against a committed
  snapshot; breaking changes fail unless a registered migration remediates.
- **CI that means it** — `just gates`: axiom check, byte-tie, wit-parser
  round-trip, differential replay, lint, compat diff — all green or the
  build fails.
