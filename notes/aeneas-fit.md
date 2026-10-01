# Aeneas fit — where the Rust→Lean extraction lands on this tree

**Status: analysis, with a verdict.** The question: Aeneas (Rust → Lean/OCaml
extraction, `mvcgen` for the proof obligations) — where does it fit a tree
whose Rust is GENERATED from Lean, whose hand-written zones are deliberately
simple, and whose Lean↔Rust agreement is carried by duels, never proofs? The
probe found the env wall (no OCaml in the devenv; the wall falls only if the
fit is real). This note decides against the fit's zones, honestly.

The reading basis: `notes/v3/03-bidirectional.md` (the discipline), the
hand-written zones themselves (`mandate-delta/src/log.rs`,
`mandate-host/src/live.rs`), `notes/v3/04-verification.md` §3/§7 (the
certificate pattern; the portable verifier), `machines/Machines/Crash.lean`
(the crash/recovery refinement — the model face of recovery), and
`notes/design-flatland-rewrite.md` (the inheritance case).

---

## 1. The generated Rust (`crates/schema-generated/`): POINTLESS

The verdict is total and needs one sentence per face:

- **Proved at the source.** The generated Rust is emitted from the checked
  model — its correctness is the generator's correctness, discharged in Lean
  where the model lives. Aeneas extracts Rust → Lean; running it on code that
  was emitted FROM Lean produces a Lean image of a Lean artifact. The
  round-trip adds no evidence: the source of record was already a theorem.
- **A second semantic authority, forbidden.** 03 §1: "Generated Rust is never
  a second specification." An extracted Lean copy of the generated codecs
  would be exactly that — a parallel encoding the gates would have to keep
  from drifting. 04 §3's rule names it: no duplicate semantic authority.
- **The byte-tie inverts the tool.** The spec of record is the COMMITTED
  generated universe. Aeneas's premise is that the Rust is the thing needing
  verification; here the Rust is the THING VERIFIED-BY-CONSTRUCTION. The
  tool answers a question this zone does not ask.

No slice, no experiment, no deferral — this zone is closed.

## 2. The hand-written Rust (`mandate-delta`, `mandate-host`, `mandate-rt`, `mandate-store`): the real fit — and the real costs

This is where Aeneas's premise holds: code the model does not generate,
carrying behavior the model DOES specify.

**What would be proved.** The hand-written zones carry the tree's
Rust-side disciplines, and their crown jewels have landed Lean models to
prove against:

- **Crash recovery** — `log.rs`'s torn-tail classification, the recovery
  cut, the snapshot alignment rules A/B, the `retain_from` scratch + rename
  dance. The model exists: `machines/Machines/Crash.lean` (`CrashMachine`,
  `crashStep`, `up`, `FaithfulAt`, the two-directional `Refines`). Today the
  Rust recovery is DUELED against this model (the crash-recovery
  differential); Aeneas + mvcgen would lift the evidence from "tested
  executions agree" to 03 §3's top rung — "verified
  implementation/refinement" — the Rust `recover` proved faithful to the
  model's `up ∘ crashStep` closure.
- **The propose/check/commit loop** — `live.rs`'s mirror of
  `Proposal.deltas` / `checkDelta` / `Proposal.commit`. The module header is
  the honest confession: the checker stays Lean-side because the guest
  cannot compile it, so the mirror is DUEL-BOUND to the committed duel
  vectors — 03 §3's DIFFERENTIAL level, "tested agreement, never a
  theorem." Aeneas is the only tool on the table that could prove the
  mirror, and it would retire the mirror's one known drift class (the
  pinned self-transfer divergence) by construction rather than by a pinned
  tooth.
- **The runtime-checked laws** — `log.rs`'s rewind-to law (the two
  independent computations must agree; disagreement is the typed refusal)
  is the runtime shadow of a theorem. Aeneas would let the shadow retire:
  the agreement proved once, not recomputed per replay.

**The costs — read off the crates, not imagined:**

- **Fragment restrictions vs the crates' shapes.** Aeneas's comfortable
  fragment is pure, terminating, monomorphic-with-enums code. The zones:
  `log.rs` is trait-dispatched I/O (`Backend` with the `&mut B` blanket
  impl), `std::fs` with `?` propagation, the TWO-file rename compaction,
  `usize::try_from` clamps, `sync_data` before return — the interesting 20%
  of the recovery logic is exactly the part extraction handles worst. The
  pure core (`FrameWalk`'s span classification, the rule A/B predicate over
  hashes) extracts cleanly; the monad lifting for the I/O skin is heavy,
  per-call-site work. `live.rs` is iterator-closure shaped (`iter().find()`,
  `map().collect()`, keyed folds) — extractable, but each closure becomes
  monadic code mvcgen then must reason over; the `ViolationRow`/`LiveVerdict`
  enums and the pure folds are the clean part.
- **The OCaml dependency.** Aeneas is OCaml-toolchain-native (opam, its
  own runtime). The devenv addition is real and permanent: a second
  build-world beside Lean and Rust, with its own version skew against
  rustc (Aeneas tracks rustc versions; every toolchain bump is a
  re-extraction event).
- **The maintenance of the evidence.** 03 §5: evidence binds to exact
  implementation dependencies. An Aeneas theorem over `log.rs` names the
  extraction identity (tool version, rustc version, the extracted
  function's exact shape) — and every edit to the hand-written zone
  re-runs extraction and re-discharges obligations. The crates are ~2.3k +
  ~2.4k + rt/store and deliberately simple; the duel suite re-runs in
  seconds and needs no toolchain. The marginal rung (differential → proved)
  is bought with a standing toolchain tax on a codebase whose size is the
  point.
- **The gate face.** 04 §2's Tier and Evidence kinds are CLOSED. Proved
  agreement via extraction is a new evidence kind — adoption means
  deliberately extending the tier set (07's extensibility path), a new
  gates row, and a disclosure discipline for the extraction identity. Not
  forbidden; not free.

**Zone verdict: the fit is real but the price exceeds the marginal gain
today.** The hand-written zones are small BY POLICY (no unsafe, minimal
deps, typed refusals everywhere); the duel discipline plus the
runtime-checked laws already pin them at the level below proved. The one
zone where the marginal rung is worth real money — crash recovery against
`Crash.lean` — is also the one where extraction fights the code shape
hardest.

## 3. The pre-existing-codebase case: the fit Aeneas was built for

The owner's framing: "in the event we have to write code that isn't well
supported by our model." Two concrete instances:

- **Flatland's inheritance.** `notes/design-flatland-rewrite.md` plans the
  absorb of flatland's EXISTING Rust — the cursor (`cursor.rs` 1,446 LOC
  collapsing to `RawParts` ≤300), the dispatch/absorb paths (1,334 LOC),
  the hand-synced mirrors. Aeneas here is the ONBOARDING discipline for
  Rust the tree did not write and did not generate: extract before/while
  absorbing, read what the extraction says the code DOES (not what its
  author said), surface the mismatches against the mandate models as the
  rewrite's work list. This is translation validation in 04 §3's
  certificate shape — untrusted producer (the legacy code), checked
  claims.
- **The honest limit.** The rewrite plan already deletes most of what
  Aeneas would on-board: the five hand-synced mirrors die into one
  generated spec, the journal dies into the proved delta log, the
  defensive layers die at M6. Extracting a proof from code scheduled for
  deletion is waste. Aeneas earns its place on the inheritance only for
  the RESIDUAL — the code that survives the rewrite hand-written (the
  cursor-on-RawParts, the absorb discipline) — and there its output is
  primarily a READING tool (what does this do?), secondarily a proof.

**Zone verdict: real, conditional on the inheritance actually landing, and
there Aeneas is onboarding, not a landing discipline.**

## 4. The bidirectionality's honest map

What each evidence level buys, on 03 §3's own table:

| Mechanism | Evidence level | Coverage | Failure mode |
|---|---|---|---|
| the commit duel (`commitDuel` + `run_commit_duel`) | differential — tested executions agree | the pinned vectors, verdict-for-verdict | a behavior no vector exercises (the pinned self-transfer drift — the duel CANNOT see it) |
| the runtime laws (`reverse_inv` two-computation agreement) | runtime checked transition | every replayed execution, per-run | a wrong law checked against itself (both computations share the Rust encoding) |
| Aeneas + mvcgen over the hand-written zone | verified implementation/refinement — ALL executions of the covered fragment | the extraction's fragment only | a behavior outside the fragment (I/O skin, trait dispatch) silently uncovered |

The map: **the duel = tested agreement; Aeneas = proved agreement for the
covered fragment.** Aeneas does not replace the duel — the duel's observer
(04 §4) covers the whole surface including what extraction cannot carry,
and the duel survives when the toolchain bumps. Aeneas strengthens ONE
cell of the table and costs a standing dependency. And 03 §6's warning
binds in both directions: extracting a description from Rust does not
prove the description matches the intent — Aeneas proves the Rust matches
the EXTRACTED spec, which is why mvcgen's obligations must aim at the
LEAN model's declarations (`Crash.lean`'s, `Proposal`'s), never at
specifications reconstructed from the extraction. That aiming is the
whole game, and it is manual per-slice work.

## 5. Verdict: DEFERRED, with named triggers and the adoption shape recorded

**The verdict: not now.** The generated zone is closed (pointless). The
hand-written zones are where Aeneas is genuinely additive — and today the
duel discipline plus the runtime laws plus the deliberately small crate
sizes make the standing cost (OCaml world, rustc-skew maintenance,
per-change re-extraction, the closed-tier extension) larger than the
marginal rung. The honest deferral is not "no" — it is a trigger contract:

**Trigger 1 — the crash-recovery proof debt.** If the crash-recovery duel
suite ever misses a shipped failure (a recovery bug the vectors did not
pin, found in the fault lane or the field), the marginal rung becomes
worth the tax, and the model to prove against is already landed
(`Crash.lean`). This is the highest-value slice and the hardest extraction
— the monad lifting of the `FsBackend` rename dance — so it is the trigger
most likely to fire late rather than early.

**Trigger 2 — the flatland inheritance.** When the rewrite lands residual
hand-written Rust the tree did not generate and cannot regenerate (the
cursor, the absorb), Aeneas becomes the onboarding read: extract,
diff-against-model, work list. Cheaper than Trigger 1 (reading, not
proving) and independent of it.

**The adoption shape, when a trigger fires** (recorded so the deferral is
executable, not vague):

1. **The devenv addition first**: OCaml + opam + the Aeneas/mvcgen pin,
   one profile, version-locked to the rustc pin in
   `crates/rust-toolchain.toml`.
2. **The slice discipline — one function**: `FrameWalk`'s classification
   and the rule A/B predicate in `log.rs` (the purest extractable core
   with real content — byte spans, hash equality, the torn/torn-at
   decision), NOT `retain_from` first. Prove the pure core; measure the
   monad-lifting cost of the I/O skin before committing to it.
3. **The aims**: mvcgen obligations at the landed Lean declarations
   (`Machines.Crash`, `SchemaCore.Proposal`/`Violate`), never at
   extraction-reconstructed specs (03 §6's trap, named in §4 above).
4. **The gates' face**: a new Evidence kind (extracted-refinement) added
   deliberately per 07, a gates row pinning the extraction identity
   (Aeneas version, rustc version, the extracted symbol) per 03 §5, and
   the tier disclosure in the artifact headers. Negative control: one
   deliberately-wrong mirror variant must FAIL the obligation sweep
   before the first positive lands.
5. **The leftover rule respected**: the OCaml profile, the extraction
   artifacts, and the gate row land WITH the first proved slice or not at
   all — no toolchain ahead of its consumer.

One line of honesty to close: the tree's discipline was designed so that
"we did not prove the Rust" is a STATEMENT, never a silence — the duel
rows and the runtime laws say exactly what is and is not proved. Aeneas
would buy the top rung for one cell of that table. The deferral says: the
table is honest as it stands, the price is known, and the triggers are
named.
