# design-debloat — the DEBLOAT + NON-ACCUMULATION discipline

The contract: NON-ACCUMULATION + minimal project size — NOT artifact
location. Artifacts are prevented from accumulating (the ignore wall,
the shared cargo target); they are never swept after the fact, so no
`clean` recipe exists in the justfile. The census is the READ-ONLY
audit (`just size`); when its numbers climb, the answer is a
prevention piece. No gate row: the gates run in CI where the
environment is fresh — the justfile and this note are the discipline.

## The census (2026-10-06, the before numbers)

| zone | before | after | disposition |
|---|---|---|---|
| `.lake/` (root) | 6.3G | 6.2G | kept; 409 stale oleans of deleted modules removed (the deleted-module remnants) |
| `.tools/` (nanoda lane) | 1.1G | 1.1G | kept — `just tools-nanoda` is the recipe; rebuilding needs one online fetch |
| six per-crate `target/` | ~26.4G | gone | shared root `target/` landed; the stale per-crate dirs removed after the green rebuilds |
| shared `target/` (root) | — | 6.1G | every crate's deps build once (mandate-host alone was 22G) |
| `legacy/.lake/` | 30M | gone | untracked build state, skipped by the legacy-hash gate |
| `legacy/crates/guestlang-rt/target/` | 988M | gone | untracked cargo build residue; the legacy-hash skip list gained `target` (the drift below) |
| `legacy/docs-site/node_modules/` | 252M (12,621 files) | gone | untracked, already in the gate's skip list; gate green after |
| `/tmp` finished scratch | ~6G (llvm-spike 4.7G, nanoda-spike 1.0G, mprobe 138M, lrw-grind 95M, aeneas-spike 4.3M, + the small probe dirs) | gone | probes finished; their notes remain (`llvm-backend-spike.md`, `nanoda-probe.md`, `mvcgen-probe.md`) |
| `/tmp/lean-beam` | 176M | kept | ACTIVE — the daemon's session state |
| `/tmp/mw-baseline` | 261M | kept | a full tree snapshot — a bench/compare baseline; not a finished probe; re-census at the next wave |

Net: ~35G reclaimed (20G in-tree, ~6G in /tmp, ~10G legacy artifacts).

## The prevention pieces (the whole answer)

1. **The ignore wall** (`.gitignore`, the tracked config): `/.lake/`,
   `/.tools/`, `/target/`, `/crates/*/target/`, `node_modules/`,
   `/.beam/` — the build-artifact zones are invisible to git AND to
   jj (jj honors gitignore). The earlier incident (jj snapshotting
   186MB of target files) cannot recur: the zones never enter the
   snapshot surface. No `.jjignore` exists or is needed — one wall,
   two consumers.
2. **The shared cargo target** (`.cargo/config.toml`, the tracked
   config): `build.target-dir = "target"`. The crates are standalone
   (no root workspace), so cargo would otherwise give each its own
   `target/` — six copies of the same dep closure (measured: six
   per-crate dirs, ~26.4G, one crate 22G). The relative target-dir
   resolves against the config's parent, so every crate builds into
   the root `target/` — the deps build ONCE. CI's cache path was
   already the root `target/` (ci.yml), so CI and local agree. The
   wasm-dual row's explicit `CARGO_TARGET_DIR` still overrides per
   invocation. Verified: `cargo test` green in all six crates after
   the switch, each rebuilding into the shared dir.
3. **The legacy no-build-side-effects rule** (AGENTS.md): legacy/'
   gets no in-place builds — its builds run only from its own
   history, so no NEW build residue can appear under legacy/; the
   residue that existed was untracked, regenerable, and outside the
   frozen surface (see the drift note below).
4. **The /tmp scratch rule** (AGENTS.md): scratch lives in /tmp and
   is deleted when its probe finishes (the notes remain). Never
   delete the active daemon (`/tmp/lean-beam`) or a bench baseline
   while its pair is live (`/tmp/mw-baseline`).
5. **The audit**: `just size` — the per-zone du report, read-only;
   a bounded footprint claim needs the numbers, and a climbing number
   means land a prevention piece, never a sweep.

## The legacy-hash drift (reported for the INTEGRATOR's re-baseline)

The first cut deleted `legacy/crates/guestlang-rt/target` (988M of
untracked cargo/fuzz build residue) while the legacy-hash gate's walk
hashed EVERY file under legacy/ except its skip list — `"target"` was
missing, and 1,669 of the baseline's 2,419 rows were that dir's
cargo residue. Regeneration is impractical (multi-target fuzz build
artifacts). The INTEGRATOR ruled the rows were build residue, never
the frozen surface: `target` now joins
`Gates.LegacyHash.skipDirNames` (the gate's own docstring discipline:
untracked scratch is named-and-skipped, never silent), and the
committed `notes/legacy-surface.txt` awaits the INTEGRATOR's
deliberate re-baseline (`--write --accept-drift` at the wave's
commit). Until then the gate reads DRIFTED — the honest state.
