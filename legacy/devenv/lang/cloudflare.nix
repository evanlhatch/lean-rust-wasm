# Cloudflare Pages deploy tooling — OPT-IN via profile (extends js for
# the jco/npm browser stack): devenv --profile cloudflare
#
# Model (from wasmtron, verified): Cloudflare Pages as pure static host —
# NO wrangler.toml/jsonc, no Workers, no bindings. wrangler is a CLI:
#   secretspec run -- wrangler pages deploy dist --project-name=<name>
# Token runtime-loaded via secretspec (never the shell env). CI passes
# CLOUDFLARE_API_TOKEN/CLOUDFLARE_ACCOUNT_ID as repo secrets instead.
#
# Secrets: declared in secretspec.toml [profiles.default]; provider is
# dotenv today, swap [providers] to infisical when the team needs it —
# consumers (this module's recipes) never change.
{ pkgs, ... }:
{
  packages = with pkgs; [
    wrangler # pages deploy CLI (alternative: `npx --yes wrangler` on demand)
    miniserve # local static serve of dist/ (prod caching via dist/_headers)
    bore-cli # dev TCP tunnel via bore.pub (share local serve externally; no
             # TLS/auth — demos only, use cloudflared for anything real)
  ];

  # Wrangler reads the token from env; secretspec injects it at run time.
  env.CLOUDFLARE_PAGES_PROJECT = "lean-rust-wasm";
  env.CLOUDFLARE_DIST_DIR = "dist";
}
