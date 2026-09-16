# lean-sys-v433

> **Provenance (see NOTICE):** vendored fork of
> [digama0/lean-sys](https://github.com/digama0/lean-sys) @ `cb1a8e4`
> (crate v0.0.9, pinned to Lean 4.23), MIT OR Apache-2.0. This fork targets
> **leanprover/lean4 v4.33.0**; drift fixes + the lean.h surface consumed are
> in [lean-compat.md](lean-compat.md) — toolchain bump means re-diff lean.h.

[![lean version](https://img.shields.io/badge/lean-4.33.0-lightgray.svg)](#lean-version-requirements)

Rust bindings to [Lean 4](https://github.com/leanprover/lean4)'s C API

Functions and comments manually translated from those in the [`lean.h` header](https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h) provided with Lean 4
