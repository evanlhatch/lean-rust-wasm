# Lean 4 — compile-time authoring frontend.
#
# Lean is build-time ONLY: it emits whatever plan/spec the downstream
# compiler consumes; nothing Lean touches the runtime. This module provides
# the toolchain (elan + a pinned Lean toolchain via `lean-toolchain` in the
# Lean package) plus the libraries the authoring surface builds on.
{ pkgs, ... }:
{
  # devenv's built-in Lean 4 module (defaults to pkgs.lean4).
  languages.lean4.enable = true;

  packages = [
    pkgs.elan # toolchain manager — reads the lake package's lean-toolchain
    pkgs.leanPackages.batteries # std4: data structures, tactics, serde helpers
    pkgs.leanPackages.plausible # property-based testing
    pkgs.leanPackages.Qq # quoted-term metaprogramming
    pkgs.leanPackages.Cli # CLI for the emitter binary
    pkgs.leanPackages.aesop # automation for routine obligations
  ];
}
