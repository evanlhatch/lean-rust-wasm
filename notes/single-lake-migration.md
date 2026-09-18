# Single-lakefile migration — spike verdict + migration plan

Status: SPIKE + PILOT COMPLETE (2026-09-19). Pilot = `edgepython` absorbed
into a root lakefile; old package lakefile dead; build/tests/lint/axiom/
native-policy shards green. This doc is the plan for the FULL migration
(15 packages remaining). Owner approval was for spike+pilot only — do not
start the phases below without it.

## 1. Verdict

**GO.** No Lake wall found. Every mechanism the consolidation needs is
supported by Lake 4.33 (verified in the toolchain's own Lake sources,
`~/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean/lake/`, and
empirically in the pilot):

| Need | Lake 4.33 answer | Evidence |
|---|---|---|
| One root lakefile, many libs/exes | `[[lean_lib]]`/`[[lean_exe]]` repeated freely; per-target `srcDir` + `roots` on BOTH libs (`Lake/Config/LeanLibConfig.lean`: `srcDir : FilePath := "."`, `roots : Array Name := #[name]`) and exes (`LeanExeConfig extends LeanConfig` — inherits `srcDir`) | pilot `lakefile.toml` builds 3 libs + 2 exes, all sources staying in `lean/edgepython/` + one `srcDir`-mount of `lean/wasm-backend` |
| Lib restricted to a subdir | `srcDir` (the `-R` root per target) + `roots`/`globs`; nothing outside roots is built | pilot: lib `EdgeWat` mounts `WasmBackend.Wat` from `lean/wasm-backend` without dragging wasm-backend's dep cone (this pattern predates the pilot — the old `lean/edgepython/lakefile.toml` did the same with `srcDir = "../wasm-backend"`) |
| Tests | `testDriver` is PACKAGE-level (one per package — `Lake/CLI/Actions.lean: Package.test` resolves exactly one driver). Per-library testing = each test exe is a target: `lake build <Pkg>Tests` + run, or `lake run <Pkg>Tests` | pilot: `lake test` ran `EdgePythonTests` (testDriver); `#guard` suites gate at build time, the exe run is the driver's exit code |
| Downstream of the root | A path `[[require]]` of the root exposes ALL its libs; importing any module makes Lake resolve the owning lib and build it in the ROOT's build dir (`LEAN_PATH=<root>/.lake/build/lib/lean:...` — observed in the build trace). No per-lib `require` selection (`@[...]`/moreDeps) exists or is needed | pilot scratch package `lean/spike-downstream` (created, built green, deleted — recreate below) imported `EdgePython` + `EdgePython.Parity` across the require |
| Gates sharding → per-library | The axiom/native-policy sweeps load envs by module ROOTS (`Gates.Packages.PkgSpec.roots`, `importModules` + own-dir-first LEAN_PATH); a lib = its roots, so the mapping is a PATH swap, not a redesign. `PkgSpec` gained `oleanDir`/`srcDir`/`leanPath` override fields (defaults preserve the old layout); edgepython's row points at the root build dir; `--package edgepython` shards stay green and the committed `notes/axiom-report.md` section stays in sync (section key = `dir`, unchanged) | `lake exe gates axioms --package edgepython`: 582 decls, 0 violations, "section in sync"; `gates native-policy --package edgepython`: 582 decls, 32 grandfathered — clean |

The cone-duplication goal is met: the pilot package's modules now build in
ONE build dir (`/home/evan/lean-rust-wasm/.lake/build/lib/lean`); a second
package absorbing on top of it reuses every shared olean (TestKit, LSpec,
plausible oleans already shared through the existing path-require tree;
the win compounds as mathlib-bearing packages merge — dbsp/Machines build
once instead of once per dependent package dir).

## 2. Pilot evidence (reproducible)

From the repo root, toolchain bin on PATH (elanc shims broken — invoke
`~/.elan/toolchains/leanprover--lean4---v4.33.0/bin/` directly):

1. `/home/evan/lean-rust-wasm/lakefile.toml` (NEW — root package
   `LeanRoot`; libs `EdgePython` (roots `EdgePython`, `EdgePython.Parity`,
   `srcDir = "lean/edgepython"`), `EdgeWat` (`srcDir = "lean/wasm-backend"`,
   roots `WasmBackend.Wat`), `EdgeGen` (roots `GenMain`); exes
   `EdgePythonTests` (root `Tests.Main`) + `py-gen`; `testDriver =
   "EdgePythonTests"`; NO requires).
2. `/home/evan/lean-rust-wasm/lean-toolchain` (NEW,
   `leanprover/lean4:v4.33.0`).
3. `lean/edgepython/lakefile.toml` + `lake-manifest.json` DELETED (the
   honest-pilot rule: no thin re-export). `lean/edgepython/lean-toolchain`
   kept (editor toolchain pin for the remaining sources).
4. `lake build` — 22 jobs green; `lake test` —
   `edgepython: structural + negative controls green (Lean engine)`, exit 0.
5. `py-gen` run from `lean/edgepython` (root-built exe) rewrote
   `target/py.wat` byte-identical (1183 bytes, 5 fns, 28 instrs).
6. Downstream proof: scratch `lean/spike-downstream` package —
   `[[require]] name = "LeanRoot", path = "../.."` + module importing
   `EdgePython` and `#check (EdgePython.Parity.parity_adder_40_2)` —
   `lake build` green (LEAN_PATH trace shows root build dir first).
   DELETED after the evidence run (it tripped `lean-pkg-inventory`, as it
   should). Recreate verbatim if re-proving.
7. Gates: `PkgSpec` overrides landed (`lean/gates/Gates/Packages.lean` —
   `oleanDir`/`srcDir`/`leanPath : Option String := none`, helpers
   `PkgSpec.oleanDirOf`/`PkgSpec.srcDirOf`); consumers
   `Gates/Axioms.lean`, `Gates/NativePolicy.lean`, `Gates/KernelCheck.lean`
   route through them. NOTE (Lean gotcha): the helpers MUST be named
   `Gates.PkgSpec.<name>` (projection-style defs) — dot-notation
   `pkg.oleanDirOf` did NOT fall back to a plain `Gates.oleanDirOf`
   definition across the module boundary ("Invalid field" error).
8. justfile: `edgepython` dropped from `lean_pkgs`; `lean-build` builds the
   root package first; `lean-lint` replaces the `run edgepython` line with
   a root-package `lake env guestlang-lint EdgePython Tests.Main`.
   `lean-pkg-inventory` + `lean-proof-roots` green after scratch removal.

## 3. Lint discipline in one package (spec — NOT built)

Today core-only-ness is a lakefile boundary: `codegen-core`, `substrait`,
`TestKit`, `LintKit` require no mathlib/Dbsp, so nothing under their
module roots CAN import a heavy dep. In one package imports become free;
the rule becomes a LINT OWNED BY LINTKIT AS DATA.

**Observed (LintKit sources):** env-linters see declarations, not import
statements; text lints (`LintKit/TextLints.lean`) are pure `String →
Array TextFinding` scanners over source files, already path-scoped
(`testImportDiscipline` scopes to `/Tests/`, `noReprInEmit` to `/Emit/`).

**Spec: `linter.guestlang.importBan` (text lint).**
- Data table in `LintKit` (the `partialAllowance` pattern):
  `(dirPrefix : String, bannedRoots : List Name, reason : String)` rows:
  - `("lean/codegen-core/", [Mathlib, Dbsp, Machines, Substrait, SchemaLang, GuestlangStd, ...])` — core imports NOTHING above TestKit/LintKit/LSpec
  - `("lean/substrait/", [Mathlib, Dbsp, Machines, ...])` — core-only
  - `("lean/TestKit/", [Mathlib, ...])`, `("lean/LintKit/", [Mathlib, TestKit, ...])`
  - rows added as each former package's discipline is ratcheted in
- Check (the `checkTestImportDiscipline` shape): for a file under the
  dirPrefix, an `import` line whose first token after `import` is or
  starts with a banned root → finding.
- Default-on. Negative controls: fixtures under `LintKit.TestFixtures`
  (a violating import + a clean import), replayed by `Tests/Main.lean`
  per the TestKit.PropSpec rule.
- Migration coupling: when a package is ABSORBED, its row's `dirPrefix`
  stays `lean/<dir>/` (the physical layout does not move), so the ban
  survives the lakefile's death — the rule fires from the first absorbed
  commit, before any drift can land.

**Second spec (pilot gap, must ship in phase 1): text-lint src-root
resolution.** `runTextLintsOnModules` resolves sources cwd-relative
(`modToFilePath cwd m "lean"`) — correct when cwd is the package dir,
wrong for the root package (absorbed modules are `lean/<dir>/…` under the
root). Observed: `warning: no source file found for module
`EdgePython.Parity` — text lints skipped` (env-lints still ran, clean).
Spec: add repeatable `--src-root=<module-root>=<dir>` flags to
`LintMain.Cli.parse`; `runTextLintsOnModules` tries each mapping before
the cwd fallback. The lint driver in the justfile passes one flag per
absorbed lib (`--src-root=EdgePython=lean/edgepython`, ...). Until this
ships, TEXT lints are silently unenforced for absorbed packages — do not
absorb package #2 before it lands.

## 4. Gates remapping (mechanical, proven)

For EACH absorbed package, flip its `gatedPackages` row:
```lean
{ dir := "ledger", roots := #[`Ledger, `LedgerFn, `Tests.Main],
  oleanDir := some "../../.lake/build/lib/lean",
  srcDir := some "../../lean/ledger",
  leanPath := some "../../.lake/build/lib/lean" },
```
- `dir` stays the `## <dir>` section key in `notes/axiom-report.md` —
  the committed baseline NEVER changes shape (verified: `--package
  edgepython` reports "section in sync").
- `leanPath` override matters: an absorbed package has no lakefile, so
  `KernelCheck.leanPathOf` must not `lake env` in its dir (it would
  crash). The root build dir carries the whole dep closure.
- `gates gen-check`/`coverage`/`manifest-check` consume REGISTRIES
  in-process (module imports), not package dirs — unaffected by
  absorption; only the row flips.
- Kernel-check is UNSHARDED (`gates kernel-check` loops all packages in
  one run; a full run exceeded 30 min on this box — timed out). The
  migration plan should add a `--package` flag to kernel-check (it has
  the `PkgSpec` filter pattern from `NativePolicy.run` to copy) BEFORE
  absorbing the mathlib-bearing packages; until then `just gates` cost
  grows with each absorption.

## 5. Test-driver collision rule (the one real refactor per absorption)

Every package names its test modules `Tests.*` (`Tests.Main`,
`Tests/Axioms.lean`). In one package those names collide. Rule: when
absorbing package N, move `lean/N/Tests/` → `lean/N/NTests/` (module root
`NTests`, files `NTests/Main.lean`, `NTests/Axioms.lean`), update the
test exe root to `NTests.Main`, and update in-file `import Tests.X` lines
to `import NTests.X`. Update:
- `just lean-proof-roots` (its grep expects `import Tests\.$mod` — make
  the pattern per-package `<pkg>Tests\.`),
- `Gates.Packages` roots (`Tests.Main` → `NTests.Main`),
- `just lean-lint`'s root list.
(The pilot did NOT rename — edgepython is alone so far; its rename happens
when package #2 lands. Keep it in the same commit as that absorption.)
Also dedupe `Tests/Axioms.lean` naming at the same time (standalone entry
point, excluded from lean-proof-roots — keep that exclusion).

## 6. The full migration, in order

Absorb in DEPENDENCY order (a package's requires die as its deps merge
into the root; each step keeps every gate green):

1. **Phase 0 (prereqs):** the `importBan` text lint (§3) + the
   `--src-root` driver flag (§3) + kernel-check `--package` (§4) land in
   LintKit/gates FIRST. All three are small, testable, and the negative
   controls are mandatory.
2. **Phase 1:** rename pilot tests (`EdgePython.Tests.Main` per §5 —
   edgepython included now that #2 approaches). Absorb `ledger` next
   (deps: SchemaLang, CodegenCore, TestKit, GuestlangStd, Machines — all
   still path requires, now `path = "lean/X"`); flip its gates row; drop
   its `[[require]]`s as its deps absorb in later phases (a require of a
   still-standing package stays a require — the root builds it once for
   everyone).
3. **Phase 2 (leaves, no interdeps):** `feature-flags`, `proofkit`,
   `qlang` (each: lakefile dies, modules stay, tests renamed, gates row
   flipped, justfile `lean_pkgs` entry dropped, lint roots line merged
   into the root run).
4. **Phase 3 (mid-tree):** `substrait`, `faults`, `std`, `schema-lang`
   (schema-lang brings the `Demo` lib + `schema`/`snapshot-fixtures`
   exes — move them as root `[[lean_lib]] Demo` / `[[lean_exe]]` with
   `srcDir = "lean/schema-lang"`; the justfile `check-schema`/`breaking`/
   `snapshot-fixtures` recipes change from `cd lean/schema-lang && lake
   exe …` to `lake exe schema …` from the root).
5. **Phase 4 (heavy cone):** `dbsp`, `Machines`, `codegen-core`,
   `TestKit`, `LintKit` — the mathlib cone builds ONCE here. LintKit
   last-but-one (its `guestlang-lint` exe becomes a root exe; the
   `lean-lint` recipe's LK path shortens to `.lake/build/bin/
   guestlang-lint`).
6. **Phase 5:** `wasm-backend` (brings `WasmBackend.Wat` in-place — the
   pilot's `EdgeWat` srcDir mount becomes a plain root lib; delete the
   mount), then `gates` LAST (its requires all dead; `Gates` lib + `gates`
   exe become root targets; `gates all --full`'s `just` shell-outs get
   their `cd` removed).
7. **Phase 6 (cleanup):** delete empty `lean/` package scaffolding
   (lean-toolchain files may remain for editor pins or go — owner call);
   `lean_pkgs` and `lean-pkg-inventory` retire (nothing left to inventory
   — the root lakefile is the inventory); `lean-build`/`lean-test` collapse
   to root `lake build`/`lake test` + a per-test-exe loop; update
   `notes/README.md` + `notes/canon.md` rows that say "package".

Per-absorption checklist (every phase 1–5 step, in this order):
1. Move `Tests/` → `<Pkg>Tests/` (§5) + fix imports inside.
2. Copy the package's `[[lean_lib]]`/`[[lean_exe]]` blocks into the root
   `lakefile.toml` with `srcDir = "lean/<dir>"`; add its still-external
   `[[require]]`s (paths now `lean/X`) if the root lacks them.
3. Delete `lean/<dir>/lakefile.toml` + `lake-manifest.json`.
4. Root: `lake build` && `lake run <Pkg>Tests` (or `lake test` if it is
   the testDriver).
5. Flip the `Gates.Packages` row (§4); `lake exe gates axioms --package
   <dir>` from `lean/gates` must report "section in sync"; run
   `gates native-policy --package <dir>`.
6. justfile: drop from `lean_pkgs`; move its `lean-lint` roots into the
   root run; update any `cd lean/<dir>` recipe (schema-lang's three,
   LintKit's artifact-headers, wasm-backend's WasmBackendTests build).
7. `just lean-pkg-inventory && just lean-proof-roots` green.

## 7. Known traps for this migration (do not re-pay)

- Dot-notation helpers for `PkgSpec` must be `PkgSpec.<name>` defs (§2.7).
- The 07:53-mtime incident: `lake` skipped rebuilding `Gates.Packages`
  despite changed content (mtime-based hash cache). If a build insists an
  edited module is fresh, `touch` the source or delete the olean + trace
  before concluding anything else.
- `lake exe gates kernel-check` has no sharding — full runs exceed 30 min;
  never put it in a phase gate without the `--package` flag (§4).
- `py-gen` (and every absorbed gen exe) writes CWD-relative paths
  (`target/py.wat`). From the repo root, `target/` is the CARGO dir —
  always run gen exes from their package dir (or give them a flag) — the
  justfile recipes must keep their `cd lean/<dir>` for gen exes even after
  absorption (observed byte-identical output when run from the package
  dir; untested from root BY DESIGN — do not "fix" this silently).
- `lake test` runs exactly ONE driver (the root package's) — per-library
  test runs go through `lake run <Pkg>Tests`; the `lean-test` recipe loops
  them.
- The lean-lint failure in `schema-lang` (`Register/Provenance.lean:107`,
  `Register/Updates.lean:125` — `partial def` beyond allowance) PRE-EXISTS
  this spike (files dated before the pilot session; not caused by it).
  Resolve before Phase 2 reaches schema-lang.
