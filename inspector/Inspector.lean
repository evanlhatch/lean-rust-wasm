/-
# Inspector umbrella — the evidence-chain inspector's import point

Owner: the Inspector agent (the mandate tree, `inspector/`).

Root-module imports are NOT re-exported — this module re-exports by
importing:

- `Inspector.Obligations` — the uniform obligation row + the closed
  discharge state + the trust axes + the acceptance-shape defects.
- `Inspector.Why` — the why-answer + the sweep report (pure).
- `Inspector.Replay` — the lanes' env-extension replay (host side).
- `Inspector.LedgerView` — the provenance ledger's queries rendered
  (backward / forward / the orphans; 09 §4).
- `Inspector.Cites` — the proof-coverage row: who cites a theorem, off
  LintKit.Citations' census (consumed, project modules only).
- `Inspector.Trust` — the trust report: the axiom surface, the tiers'
  distribution, the kernel-check coverage, the duel rows' status.
- `Inspector.WhatIf` — the what-if inspector: rewind/replay-with-
  modification over the journal (08 #20 — the divergence as data).

The five questions: answered per submodule; the umbrella answers none —
it is the import point.
-/

import Inspector.Obligations
import Inspector.Why
import Inspector.Replay
import Inspector.LedgerView
import Inspector.Cites
import Inspector.Trust
import Inspector.WhatIf
