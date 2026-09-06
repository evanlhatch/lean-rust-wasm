# Shared helpers for devenv modules (same `_` prefix rule as _caches.nix).
# Import with `import ./_lib.nix { inherit pkgs lib config; }`.
#
# NOTE: helpers return ATTRSETS, never module-functions — a module file
# must eval to one lambda (args → attrset). Passing config/lib here and
# producing attrsets directly avoids the "does not look like a module"
# trap.
{ pkgs, lib, config }:
let
  # Hook entry that prepends a PATH of tool bins. git-hooks run from the
  # raw `git commit` env — nothing from the shell is on PATH — so every
  # hook that dispatches by name (treefmt→rustfmt/dprint, clippy→cc/lld)
  # needs this wrap.
  #
  #   mkHook {
  #     command = "cargo-clippy";         # name or abs path
  #     bins = [ pkgs.gcc ];              # packages whose bin/ goes on PATH
  #     paths = [ "${root}/.devenv/profile/bin" ]; # extra PATH entries
  #     args = "clippy --all-targets";    # appended verbatim
  #   }
  mkHook = { command, bins ? [ ], paths ? [ ], args ? "" }: pkgs.writeShellScript "hook-${builtins.baseNameOf command}" ''
    export PATH="${lib.makeBinPath bins}:${lib.concatStringsSep ":" paths}:$PATH"
    exec ${command} ${args}
  '';

  # Toggle builder for opt-in sub-modules. Generates an option
  # `templateConfig.toggles.<name>.enable` + a lib.mkIf dispatch, and
  # returns the module ATTRSET (not a function).
  #
  #   mkToggle {
  #     name = "wasm";
  #     description = "wasm component tooling";
  #     mod = { config, lib, ... }: { packages = [ ... ]; };
  #   }
  mkToggle =
    { name, description ? name, mod }:
    {
      options.templateConfig.toggles.${name}.enable = lib.mkEnableOption description // {
        default = false;
      };
      config = lib.mkIf config.templateConfig.toggles.${name}.enable (mod {
        inherit config lib pkgs;
      });
    };
in
{
  inherit mkHook mkToggle;
}
