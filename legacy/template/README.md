# The scaffold — a new project's spec + impl layer

This package was instantiated by `just new-project <name>` (the
template/ skeleton at the repo root). The spec + impl modules below are
the ONLY code a new project writes — the harnesses, gates, emitters,
and proofs come from the layers (notes/reuse-map.md).

## What is here (the instantiation checklist, steps 1–2)

- `<Name>.lean` — the spec module: `@[schema]` records + `@[schema_fn]`
  functions. The SSOT every artifact generates from. The header explains
  each attribute's role — do not trim it.
- `<Name>Fn.lean` — the impl module: `@[guest_std]` bodies (the elab-time
  runtime ban). The header explains the `guest`/`guest_std` split.
- `project.json` — the codegen manifest: `spec-modules` + `impl-modules`
  (the renamed skeleton already names YOUR modules). The wasm backend's
  compile-set + the world's exports fold from it (see follow-up 3) —
  there is no hand-list to maintain.
- `Tests/Main.lean` + `Tests/Axioms.lean` — the minimal gate files
  (`just lean-axioms` runs every package's `Tests/Axioms.lean`).
- `lake-manifest.json` — the pinned dep closure (faults' shape). gonzalgo
  resolves from the VENDORED bundle `vendor/gonzalgo.bundle` (the pinned
  rev was rewritten upstream — the GitHub URL serves it to no one). The
  manifest's url and the `[[require]]` rows in dbsp/Machines point at
  the bundle, so a fresh clone resolves with no sibling-build
  dependency. The justfile's hardlink-seed from
  `lean/faults/.lake/packages` is only the fallback for prebuilt oleans.
  If the manifest drifts: `lake update` in this package (it rewrites
  the gonzalgo row from the lakefile's `git = ` — keep that on the
  bundle).

## Already registered for you (the recipe did it)

- `lean_pkgs` in the justfile — the build/test/axiom gate loop.
- The `packagePrefixes` rows in
  `lean/LintKit/LintKit/PackageNamespace.lean` (the `lean_pkgs` mirror —
  one row per module root: `<Name>` and `<Name>Fn`).

## Manual follow-ups (the world's fold + the lint row)

1. The WIT world: `lean/schema-lang/SchemaLang/Emit/Wit.lean` — the
   `witEmitter` row (`worldOf "demo:gateway" "gateway" items`) is the
   demo world's fold pattern. Add YOUR emitter module (one module +
   one line in the `emitters` list in
   `lean/schema-lang/SchemaLang/Emit/Registry.lean` — no driver
   changes) folding your registry into your world.
2. The gen driver: `lean/schema-lang/GenMain.lean` imports `Demo` and
   replays `#[`Demo]` — point it at your spec module (or copy the
   driver into this package; it is 30 lines).
3. The compiled world: DONE by the manifest — `project.json` (written
   beside this README) is the compile-set's single source:
   `lean/wasm-backend/GenMain.lean` loads the manifest's modules and
   folds the compile roots from the `@[guest]`/`@[guest_std]` marks
   (`targetDeclsOf` — the guest-mark registry in
   `lean/codegen-core/CodegenCore/GuestGate.lean`) and the exports from
   the schema registry (`worldExportsOf`). Every `@[guest_std]`-marked
   def in your impl module is a compile root automatically; the
   registered `@[schema_fn]` items whose body is a compile root are the
   world's exports. To run the backend over YOUR world, copy the
   wasm-gen driver into this package (`lakefile.toml` exe + the
   `project.json` beside it — the driver reads the manifest, no edits).
4. The lint row: a `run <Name> <Name> <Name>Fn` line in the `lean-lint`
   recipe (justfile) — the linter then sweeps this package's roots.
5. Then `just gen` (the artifacts, all byte-tied) and `just gates`.

## Verify

    just lean-pkg-inventory   # the registration landed
    just lean-build           # this package + its requires
    just lean-axioms          # the axiom gate covers this package
