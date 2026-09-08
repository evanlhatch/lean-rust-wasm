# Verification recipes

# Full check: tests, clippy, fmt, typos, secrets.
check: test clippy fmt typos secrets

# nextest is the default runner. nextest does not run doctests —
# they run separately (flatland pattern).
test:
	cargo nextest run && cargo test --doc

clippy:
	cargo clippy --all-targets
	cargo clippy --all-targets --all-features

fmt:
	cargo fmt --check

# Everything formatter: rustfmt + dprint (treefmt.toml + .dprint.json).
format:
	treefmt

# Spell-check (typos.toml).
typos:
	typos

# Secret scanner (ripsecrets).
secrets:
	ripsecrets

# Auto-fix lint/format findings (separate target dir, no -Zthreads).
fix:
	cargo-clippy-fix
	cargo fmt

clippy-fix:
	cargo-clippy-fix

# Dependency hygiene
deny:
	cargo deny check

outdated:
	cargo outdated

machete:
	cargo machete

# Mutation testing (pass a module name: just mutants foo)
mutants name:
	cargo mutants -f {{name}}

# ── Codegen loop (buf-style: watched = same command, wrapped) ────────
# `gen`/`check`/`breaking` run identically in CI and in watchers. The
# watcher never changes what runs, only when.

# Fast type-check only, no emission (buf lint analog).
check-schema:
	@echo "TODO: guestlangc check"

# Schema-compat diff vs last released schema (buf breaking analog).
breaking:
	@echo "TODO: schema diff"

# Watchers — watchexec wraps the SAME commands, no redefinition.
# --restart: kill in-flight gen on new save (codegen is idempotent).
watch-gen:
	watchexec -r -w lean -e lean -- just gen

# Host restart on generated OUTPUTS + host code (not lean/ — the gen
# write into src/generated is what triggers this, one write per change).
watch-host:
	watchexec -r -w src -w wit -- cargo run

# Fast schema check without emission.
watch-check:
	watchexec -w lean -e lean -- just check-schema

# Property/fuzz ingress boundary tests (bolero). Corpora live in
# devenv state (DEVENV_STATE/bolero-corpus).
fuzz name:
	cargo bolero run {{name}}

# ── WASM compile checks (nightly + rust-src required) ────────────────
# RUSTFLAGS_WASIP3/RUSTFLAGS_WASM32 strip host-only flags (target-cpu=native,
# -Z*); these are the real gates for "does it build for wasm" without a link.
check-wasip3:
	RUSTFLAGS="$RUSTFLAGS_WASIP3" cargo check --target wasm32-wasip3 -Z build-std=std,panic_abort

check-wasm:
	RUSTFLAGS="$RUSTFLAGS_WASM32" cargo check --target wasm32-unknown-unknown

# ── Lean workspace (packages in dependency order) ────────────────────
# elan shims broken — invoke toolchain bin directly.
lean_tc := home_dir() / ".elan" / "toolchains" / "leanprover--lean4---v4.33.0" / "bin"
lean_pkgs := "TestKit Machines codegen-core schema-lang faults dbsp"

lean-build:
	#!/usr/bin/env bash
	set -euo pipefail
	for p in {{lean_pkgs}}; do
	  (cd lean/$p && PATH="{{lean_tc}}:$PATH" {{lean_tc}}/lake build)
	done

lean-test: lean-build

# Codegen pipeline shim — all logic lives in the forge crate.
gen:
	cargo run -p forge -- gen

gen-check:
	cargo run -p forge -- gen --check

# ── Cloudflare Pages (devenv/dev/cloudflare.nix) ─────────────────────
# Pages as static host: no wrangler.toml, token via secretspec at
# runtime (never the shell env). Project name/dist from the nix module.

# One-time setup (interactive, browser OAuth — no token needed):
#   npx wrangler pages project create $CLOUDFLARE_PAGES_PROJECT

# Local serve of dist/ (deploy-parity: prod caching ships as dist/_headers).
serve:
	miniserve --interfaces 0.0.0.0 -p 8080 --hidden --header "Cache-Control: no-cache" $CLOUDFLARE_DIST_DIR

# Deploy dist/ to Pages. Token from secretspec (dotenv today, infisical
# later — consumers unchanged). CI passes CLOUDFLARE_* as repo secrets
# instead; see .github/workflows/deploy.yml.
deploy:
	secretspec run -- wrangler pages deploy "$CLOUDFLARE_DIST_DIR" --project-name="$CLOUDFLARE_PAGES_PROJECT"

# ── Docs (Astro Starlight; docs profile) ─────────────────────────────
doc-dev:
	cd docs-site && bun run dev

doc-build:
	cd docs-site && bun run build

# ── Gates: every lean↔rust drift check in one shot ───────────────────
# wit-check: the canonical parser (wasm-tools) must accept our emitted
# WIT — it, not our printer, is the correctness authority.
wit-check:
	wasm-tools component wit wit/gateway.wit > /dev/null

# Full gate: builds lean first (no stale oleans), then all drift checks.
gates: lean-build gen-check wit-check lean-axioms
	@echo "gates: clean"

# Axiom gate: sorryAx or an unexpected axiom fails the build (the allowed
# set is the core triple + native_decide's disclosed trust base).
lean-axioms:
	#!/usr/bin/env bash
	set -euo pipefail
	for p in {{lean_pkgs}}; do
	  out=$(cd lean/$p && PATH="{{lean_tc}}:$PATH" {{lean_tc}}/lake env lean Tests/Axioms.lean 2>&1)
	  if echo "$out" | grep -q "sorryAx"; then echo "FAIL: sorryAx in $p"; exit 1; fi
	  bad=$(echo "$out" | grep -v "does not depend" | sed "s/.*depends on axioms: //" | tr -d "[]" | tr "," "\n" \
	    | sed "s/^ *//;s/ *$//" \
	    | grep -vE "^(propext|Classical.choice|Quot.sound|.*native_decide..*|)$" || true)
	  if [ -n "$bad" ]; then echo "FAIL: $p unexpected axioms:"; echo "$bad"; exit 1; fi
	  echo "$p: axioms clean"
	done
