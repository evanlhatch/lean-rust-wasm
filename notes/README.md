# notes/

Design decisions, spikes, and post-mortems — one file per decision, dated.

Code comments point here; when a note disagrees with a stale code comment,
the note wins (then fix the comment). Format that's worked: context →
options considered → decision → rejected alternatives with reasons.

## Index (the living docs)

- `lean-doctrine.md` — the enforcement ladder, the dependency policy,
  the design rules (the spec of record for HOW we Lean).
- `lean-refactor-guide.md` — the work ledger (the phases + the status).
- `seam-contract.md` — the Rust↔Lean seam inventory + the proof list.
- `reuse-map.md` — every package's modules + their reuse stories + the
  project-instantiation checklist.
- `full-remaining-work.md` — the original goals + the stage history.
- `execution-guide.md` — the build/test commands + the stage demos.
- `async-wrpc-oci-plan.md` — the async-ABI/wRPC/OCI plan (mostly landed).
