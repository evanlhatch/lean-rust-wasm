# AGENTS.md — working agreements for coding agents (and humans).

## Version control: jj

- Working copy IS a commit. Small atomic commits, `jj describe` once the
  change is known. Never `git checkout/reset/stash` — `jj undo`/`jj new`.
- Bookmark before risky operations.

## Verification (every change)

`just check` — tests (nextest + doctests), clippy, fmt must be green
before declaring done. Dependency/config changes also: `just deny`.

## Errors

fast-observe is the error tool. No thiserror/anyhow/eyre — define faults
with fast-observe, flow with `?`. Never double-log an error, never
collapse failure into `None`/0/"" — read paths return real `Result`s.

## Lints

Clippy runs pedantic. `panic!`/`unwrap`/`expect` denied in library code —
tests use `assert!` with messages and `let … else { unreachable!(…) }`.
No `#[allow]` without `reason = "…"`.

## Comments

A comment describing a mechanism names its file/symbol. Found drift gets
fixed in the same change, never later.

## Design notes

Design decisions live in `notes/` — one file per decision, dated, with
the rejected alternatives. Code comments point at the note; notes are
authoritative when they disagree with stale comments.
