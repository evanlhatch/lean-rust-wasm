# Shell entrypoint — sheath pattern.
#
# Base (always on): dev/* helpers + lang/rust + lang/lean.
# Opt-ins are devenv PROFILES (devenv --profile <name>):
#   js, python, wasm, docs, cloudflare (extends js for jco).
# See the profiles block below and devenv/local.nix.example.
{ pkgs, lib, config, inputs, ... }:
let
  # Auto-discover devenv modules.
  findModules =
    dir:
    let
      entries = builtins.readDir dir;
      processEntry =
        name: type:
        if lib.hasPrefix "_" name then
          [ ]
        else if type == "directory" then
          findModules (dir + "/${name}")
        else if lib.hasSuffix ".nix" name then
          [ (dir + "/${name}") ]
        else
          [ ];
    in
    lib.flatten (lib.mapAttrsToList processEntry entries);
in
{
  imports =
    findModules ./devenv/dev
    ++ [
      ./devenv/lang/rust.nix # always on
      ./devenv/lang/lean.nix # always on
    ];

  profiles = {
    js.module = import ./devenv/lang/js.nix;
    python.module = import ./devenv/lang/python.nix;
    wasm.module = import ./devenv/lang/wasm.nix;

    cloudflare = {
      extends = [ "js" ]; # jco/npm browser stack
      module = import ./devenv/lang/cloudflare.nix;
    };
  };
}
