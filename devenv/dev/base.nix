# Core development module — always on.
# Shell init lives in this file (no background tasks; those are
# devenv processes).
{ pkgs, lib, config, inputs, ... }:
let
  caches = import ../_caches.nix;
  cacheList = caches.upstreams ++ [ caches.project ];
  substituters = lib.concatStringsSep " " (map (c: c.url) cacheList);
  pubkeys = lib.concatStringsSep " " (map (c: c.publicKey) cacheList);
in
{
  packages = with pkgs; [
    jujutsu
    just
    ripgrep
    yek # repo → LLM context packer (respects yek.yaml + .gitignore)
    difftastic
    watchexec # file-watcher wrapper for codegen loops (just watch-gen et al)
    elan # Lean toolchain manager (lean.nix also uses it)
  ];

  difftastic.enable = true;
  dotenv.enable = false;

  # ── Multiple binary caches (single source: _caches.nix) ─────────
  env.NIX_CONFIG = ''
    connect-timeout = 2
    substituters = ${substituters}
    trusted-public-keys = ${pubkeys}
    experimental-features = nix-command flakes ca-derivations
  '';
  env.NIXPKGS_ALLOW_UNFREE = "1";

  enterShell = ''
    echo "🦀 devenv ready"
  '';
}
