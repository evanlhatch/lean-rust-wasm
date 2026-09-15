# notes/

Design decisions, studies, and the work plan. Code comments point here;
when a note disagrees with a stale code comment, the note wins (then fix
the comment). Format: context → options → decision → rejected
alternatives with reasons.

## Reading order (agents and humans)

1. `vision.md` — what this is, the seven-concept kernel, scope locks.
2. `canon.md` — what everything IS (the isomorphism table). Binding:
   name your row; no row = a finding.
3. `lean-doctrine.md` — the rules, each with its enforcement level
   (convention → lint → structural → gate).
4. `runbook-2026-09-15.md` — THE work plan: agent primer, global
   protocol, 40+ prescriptive work orders, dispatch order.
5. `lean-cohesion-plan.md` + `code-review-2026-09-15.md` — the
   analysis + evidence behind the plan.
6. `studies/` — external evidence (cedar-spec, verified-ledger).
   Read the one your work order cites.
7. `seam-contract.md` — the Rust↔Lean seam inventory + proof status.
8. `reuse-map.md` — every module's purpose + status (loadbearing /
   seed).
9. `execution-guide.md` — build/test commands; `async-wrpc-oci-plan.md`
   + `decision-wasip3-linking.md` — the runtime linking decisions.
10. `archive/` — superseded docs, kept for lineage. Never cite from
    here in new work.

## House rules for notes

- Long beats vague. A work order or rule must be executable without
  the conversation that produced it.
- Dated docs are snapshots; vision/doctrine/canon/reuse-map are LIVING
  (update in the same commit as the change they describe).
- A note referenced from code must exist (the stale-path lint covers
  `*.lean`; notes referencing notes is review's job).
