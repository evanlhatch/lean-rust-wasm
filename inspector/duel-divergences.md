# Duel divergences ledger — the committed duel vectors' Lean replay vs the committed expectations

One row per observed disagreement between a committed duel set's
manifest expectation (the generator-computed pin, emitted through the
byte-tie) and the Lean replay's observation (the landed engine — the
executor, the codec, the checker — re-run over the committed bytes by
`lake exe inspector duel`). Policy (the notes/divergences.md
discipline, the duel lanes' face): **a divergence is investigated
before the replay is trusted again; an empty ledger = we looked.**

The replay is the regression discipline — a divergence names its
witness (the vector + BOTH sides' rendered values, never a bare
"behavior changed"); the row below is what the `duel` command's
report renders, ready to paste. The resolution column records the
adjudication: the root cause, the fix, and which side moved.

| date | duel | vector | divergence | resolution |
|---|---|---|---|---|

## First full replay — 2026-09-28: zero divergences

All four committed duel sets replayed green (the wasm execution duel
`gen/wasm-duel` — 6 rows; the codec differential
`crates/schema-generated/tests/duel` — 10 rows; the journal duel
`crates/mandate-delta/tests/duel` — 9 rows; the commit slice
`crates/schema-generated/tests/duel-commit` — 5 rows): every committed
byte re-ran through the Lean engine and matched its committed
expectation, including the negative controls (the tamper shapes
refused; the invalid module was refused by the validator; the trap
module trapped). The replay is tested agreement, never a theorem
(notes/v3/04-verification.md §6) — this ledger is where the next
divergence lands, with its adjudication.
