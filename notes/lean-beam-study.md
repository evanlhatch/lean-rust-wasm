# lean-beam study — the mandate tree + agent workflows

Source: cloned `leanprover/lean-beam` (default branch, Oct 2025) to `/tmp/lean-beam`, read-only. Nothing in the tree touched; no jj/git state changed anywhere.

## 1. What lean-beam IS

A preview project from Lean FRO for "efficient interaction with Lean from AI agents." Architecture: a Lean-side **LSP plugin** (`$/lean/runAt`, `$/lean/todo`, etc.) + a thin local **broker daemon** + three clients: `lean-beam` (CLI), `lean-beam-search` (shell search loops), `lean-beam-mcp` (stdio MCP). It wraps **the Lean LSP server with the Beam plugin loaded inside a Lake workspace** — i.e. the real elaborator, with the real module environment — not `lake build`. Implemented in Lean itself.

**State it keeps:** one foreground `lean-beam serve` owner process per (canonical project root × session dir); the owner runs a daemon that holds Lean LSP sessions, a document mirror, sync/save history, handles, and metrics. Descriptor at `<root>/.beam/beam-daemon.json` (mode 0700 dir, 0600 file, capability token per request). Runtime bundles are toolchain-keyed, cached under `~/.local/share/beam` (installed) with fallback `<root>/.beam/bundles`. Cache discipline: warm server across commands, `lean-beam save` writes a **zero-build .olean checkpoint** of the server's accepted environment (structured Lake options, dynamic libs, plugins included).

**Exact CLI** (from `Beam/Cli/Usage.lean` — every subcommand):

```
lean-beam --version | version
lean-beam [--root PATH] [--session-dir DIR] serve [lean|rocq]
lean-beam [--root PATH] status | stats | doctor [lean|rocq] | open-files
lean-beam --root PATH stop | recover --generation ID | --force
lean-beam [--root PATH] cancel <request-id>
lean-beam [--root PATH] update <path>                 # open/refresh mirror, returns doc version
lean-beam [--root PATH] sync <path> [+all-diagnostics]     # diagnostics/readiness barrier
lean-beam [--root PATH] refresh <path> [+all-diagnostics]  # close + sync
lean-beam [--root PATH] save <path> [+all-diagnostics]     # sync + zero-build checkpoint
lean-beam [--root PATH] close <path> | close-save <path> [+all-diagnostics]
lean-beam [--root PATH] run-at <path> <ver> <line> <char> (--stdin|--text-file F|-- <text>|<text>)
lean-beam [--root PATH] run-at-handle <...>            # speculative probe returning a handle
lean-beam [--root PATH] run-with <path> <handle> <text>     # continue from handle (branch)
lean-beam [--root PATH] run-with-linear <path> <handle> <text>
lean-beam [--root PATH] release <path> <handle>
lean-beam [--root PATH] hover | signature-help | definition | references
          <path> <ver> <line> <char>   # references: [--include-declaration|--exclude-declaration]
lean-beam [--root PATH] document-symbols <path> <ver>
lean-beam [--root PATH] workspace-symbols <query...>
lean-beam [--root PATH] goals before|after <path> <ver> <line> <char>
lean-beam [--root PATH] todo <path> <ver> <sl> <sc> <el> <ec> [--kind <k>...] [--suggest none|basic]
lean-beam [--root PATH] rocq-goals-after | rocq-goals-prev ...
lean-beam [--root PATH] feedback-report --stdin|--input F [--bundle none|dir|zip] [--output-dir P] [--no-redact]
lean-beam prune [--apply] [--bundles] | validated-toolchains | compatible-release-lines
```

Output shape: completed broker ops print final JSON `{"ok": true, "result": ...}` (typed semantic failures also JSON, `ok: false`); selector/transport failures exit nonzero with human stderr and **no JSON** — check exit status first. Positions are LSP coordinates (0-based line, UTF-16 char). Sync/save results carry `result.readiness.saveReady`, `blockingErrorCount`, and on `syncBarrierIncomplete` failure: `error.data.staleDirectDeps`, `saveDeps`, `recoveryPlan`, `completionBlockingDiagnostics`. Version-bound ops fail `contentModified` with `error.data.acceptedVersion` for retry. Ships its own agent skill (`skills/lean-beam/SKILL.md`) installable via `./scripts/install-beam.sh --pi` — pi is a first-class target.

## 2. Workflow mapping — the session's pain → the feature

**(a) Full-lake-build inner loop → beam-fixes (the core win).** The lean-beam README contains the owner's exact framing verbatim: "make that loop cheaper and more structured than repeatedly creating scratch files or using full `lake build` runs as the inner loop." `lean-beam sync <file>` gives per-file elaboration with a diagnostics/readiness barrier against the **warm server** — no full build, no full `lake build` re-elaboration of the import cone per iteration. `lean-beam save` then checkpoints the accepted module env zero-build. Escalation contract is explicit: `lake build` only for dependency-cone validation and clean CI / final batch validation (`stop` → `lake clean` → `lake build` once).

**(b) Scratch-file probes → beam-fixes.** The skill's "Agent Cost Model" section addresses this head-on: a scratch file has a high fixed cost (detached module, re-imports, simplified context that may not match the real position); `run-at` has low marginal cost against the real module environment and exact source position. The skill's policy: scratch files only for context-free syntax checks or Beam incident isolation. Multiline probes via `--stdin`/`--text-file`; parallel independent probes encouraged.

**(c) Root-cause finding → beam-partial.** `sync` streams diagnostics (errors by default, `+all-diagnostics` to widen) and reports `blockingErrorCount` — so you get the current file's blocking errors without the flood from dependents, because nothing downstream is elaborated until you ask. `lean-beam todo` enumerates sorries, holes, diagnostics, code actions, and incomplete proofs per range. But Beam does **not** rank errors or compute a minimal failing set, and it does not hide the cascade *within* one file — one bad declaration still yields its own multiple errors. What it does fix is the *cross-file amplification*: dependent files simply aren't re-elaborated in the loop.

**(d) Proof-debugging (trace_state / pp.all scratch loops) → beam-fixes.** `goals before|after <file> <ver> <l> <c>` gives the proof state at a tactic position directly; `hover`/`signature-help` replace `#check` probes; `run-at` tries the replacement tactic in place. The handle API (`run-at-handle` → `run-with`/`run-with-linear`/`release`) supports branching search from exact speculative state — the mcts-search reference documents tree/linear playout patterns. No more tactic-state archaeology via inserted `example`/`trace_state` lines.

**(e) Multi-agent collisions → beam-partial, and the honest answer is mixed.** Beam never applies source edits and is safe for concurrent *read/probe* load (parallel probes explicitly supported). Isolation model: session selector = canonical root + session dir; `--session-dir DIR` or `BEAM_SESSION_ROOT` gives each agent a **separate daemon namespace over the same tree** — that isolates broker/server state, mid-edit red-servers, and sync barriers per agent. But it does **not** isolate the working copy itself: agents sharing one tree still collide on disk bytes. The discipline that actually fixes the (e) pain is jj-side (`jj workspace add` per agent) with lean-beam per workspace — beam makes that cheap because each workspace root gets its own session and the bundle cache is shared, so workspace #N is warm immediately. Also relevant: `syncBarrierIncomplete` + `staleDirectDeps`/`recoveryPlan` is exactly the structured answer to "another agent saved my dependency, my file is now red" — the error names the stale direct deps and the recovery plan instead of a 90-error flood.

## 3. Framework integration (the mandate tree's own tooling)

- **Gates / `just check` vs `just gates`:** the tree already splits a light tier (`check`) from the heavy battery (`gates`, env-replay shards, ~24GB kernel-check node). lean-beam is a **third tier below `check`**: the per-declaration inner loop. But the gates themselves are batch programs (`lake exe gates ...`) — they should NOT ride the beam daemon; batch-only `moreLeanArgs` even fail `save` with `saveUnsupportedSetup`. Honest fit: gates unchanged; add a `just beam` recipe (serve lifecycle) + documentation of the loop discipline.
- **The axiom gate's shard discipline** (`notes/v3/09-gates-ops.md`, per-package env replay): this is batch env loading by design, re-baselined via `axiom-report.md`. lean-beam cannot replace it (env replay ≠ server session), but the *authoring* loop that produces axiom candidates — iterating one file until `native_decide` closes — is exactly the `run-at`/`sync`/`save` loop. beam-partial.
- **Inspector / query / scaffold:** `lean-beam definition`, `references`, `document-symbols`, `workspace-symbols`, `hover` are usable directly as the human/agent query surface over the tree without building anything. The scaffolder's "does the generated module compile" check could use `sync` on the new file instead of a package build — beam-fixes, but only as an agent-loop habit, not by rewiring the scaffold exe.
- **Test harnesses (`<Lib>Tests` exes):** irrelevant — those are batch executables; keep `just test`. beam-irrelevant.
- **Byte-tie / gen:** the regen lane (`just gen`) is a batch writer; unaffected. One real integration point: the "after editing a lakefile/lean-toolchain, `lean-beam stop` then re-`serve`" rule must be taught, because this tree regenerates and re-baselines often.
- **Cone rule compliance:** lean-beam is host tooling (the `inspector` slot in the placement table) — CLI-side, no new Lean library, no lakefile row, no cone-table impact. It installs via `./scripts/install-beam.sh --pi`; nothing enters the tree but a justfile recipe and this note.

## 4. Agent-workflow discipline (the owner's waves)

Per-agent loop, in order:

1. **Setup (once):** `./scripts/install-beam.sh --pi` from a lean-beam checkout; `lean-beam doctor` in the tree root. v4.33.0 is prebuilt/validated (see §5).
2. **Serve (once per working session):** one `lean-beam serve` holder in the agent's long-lived shell. Per-agent isolation: `BEAM_SESSION_ROOT=/abs/writable/base` (sandbox convenience, per-root hashed dirs) or explicit `--session-dir`; pair with one `jj workspace` per agent for the collision-free wave.
3. **Check-before-build:** never `lake build` to learn whether a file elaborates. `update <file>` → version → probe (`run-at`, `goals`, `hover`, `todo`) → real edit → `update` again → `sync <file>` for the readiness verdict. Prefer many small `run-at` probes over one big experiment.
4. **Checkpoint per file:** `save <file>` after a green sync; do **not** clean-build after checkpoints.
5. **Escalation ladder (stop conditions, from the skill):** repeated `run-at` no longer clarifying → real edit + sync. Dependency edited / `syncBarrierIncomplete` → save the listed `staleDirectDeps`, `refresh` importers per `recoveryPlan`, and if it spans multiple hops → `lake build` (this is where the cascade is real). Lakefile/toolchain touched → `--root stop` + new serve. End of task → one batch validation (`lake build` / clean CI), never per loop.
6. **Token arithmetic:** the session's waste pattern was (i) full `lake build` per edit — each re-elaborating the import cone of touched modules, minutes of wall time and thousands of tokens of error spam per iteration, (ii) scratch files — re-imports from a detached module plus context drift, and (iii) cross-file error floods. The beam-shaped loop replaces (i) and (ii) with warm-server calls whose steady-state marginal cost is one file's elaboration delta, and returns *typed verdicts* (`saveReady`, `blockingErrorCount`, `staleDirectDeps`) instead of prose error walls an agent re-reads. Honest unknown: no measured token numbers exist for either loop here; the tree's own justfile data (`check` = "seconds", full battery 2:34–4:34) bounds where the savings live — in the per-iteration elaboration cone, not in the gates.

## 5. Honest limits

- **Does not fix:** the kernel-check's ~24GB replay, the gates' shard runs, `just test`'s exe builds, `cargo` builds, the byte-tie regen lane. All batch by design. Also: `save` does not validate downstream importers; servers don't see Lake config changes (stop/serve after lakefile edits); if a dependency is edited, downstream probes are stale until rebuild — the exact case where a full build is still the truth.
- **Status:** explicitly "experimental beta… interfaces may change"; handles and `lean-beam-search` are pre-stable support APIs; distribution is checkout + local installer, no registry.
- **Toolchain compat — verified:** the tree pins `leanprover/lean4:v4.33.0`; lean-beam's `validated-lean-toolchains` lists `leanprover/lean4:v4.33.0` exactly, and `v4.33` is a compatible release line. So the tree's pin is a **fully validated, prebuilt-by-default-eligible** toolchain: no fallback bundle build, no compat risk today. One caveat: Beam requires `-Dexperimental.module=true` for plugin loading and is toolchain-keyed; a future tree re-pin must land in Beam's validated list (currently v4.28.0–v4.34.0-rc1) or trigger a local fallback-bundle build on first use.
- **Preference match:** owner prefers CLI over MCP — the CLI is the complete surface here (MCP only adds structured live progress/diagnostic streaming); nothing in this report requires MCP.

---

**Headline answers.** (1) lean-beam is a per-project warm Lean-LSP daemon + plugin with a typed JSON CLI; full subcommand surface above. (2) Pain mapping: (a) full-build loop — beam-fixes; (b) scratch files — beam-fixes; (c) root-cause — beam-partial (kills cross-file cascades, not intra-file floods; `staleDirectDeps`/`recoveryPlan` names the failing set for stale-dep cases); (d) proof-state loops — beam-fixes (`goals`, `run-at`, handles); (e) collisions — beam-partial (per-agent session namespaces; pair with jj workspaces for byte isolation). (3) Framework: gates/tests/gen untouched (batch by design); beam slots as the inner-loop tier below `just check`, host-tooling placement, no lakefile/cone impact. (4) Discipline: serve once, update→probe→edit→update→sync→save, escalate to `lake build` only on the skill's named stop conditions. (5) Compat: v4.33.0 is on Beam's validated list — clean; the rest is batch machinery beam doesn't touch.
