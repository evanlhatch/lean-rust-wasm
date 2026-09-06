# rust-devenv-template

Devenv-based Rust project starter. The repo itself is the documentation —
read `devenv/` for how things are wired.

## New project

```sh
gh repo create myproj --template evanlhatch/rust-devenv-template --clone
direnv allow        # or: devenv shell
just check
```

## Conventions (short version)

- **Errors**: fast-observe only — no thiserror/anyhow/eyre.
- **Lang toggles**: opt-in languages live in `devenv/lang/`, gated by
  `templateConfig.toggles.<name>.enable` (set in `devenv.local.nix`).
- **Per-machine overrides**: `devenv.local.nix` (gitignored).
- **wasm**: `just check-wasip3` / `just check-wasm`; needs the vendored
  getrandom patch (see Cargo.toml `[patch.crates-io]`).
