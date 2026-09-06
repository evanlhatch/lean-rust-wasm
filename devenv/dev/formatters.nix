# Formatters and linters config (sheath formatters.nix pattern).
# Tool installation + the manual treefmt.toml wiring. Everything gated
# by options so a project can trim without deleting files.
{
  pkgs,
  lib,
  config,
  ...
}:
let
  cfg = config.templateConfig.formatters;
  mkHook = (import ../_lib.nix { inherit pkgs lib config; }).mkHook;
in
{
  options.templateConfig.formatters = {
    enable = lib.mkEnableOption "formatters and linters" // {
      default = true;
    };

    enableDprint = lib.mkOption {
      type = lib.types.bool;
      default = true;
      description = "Enable dprint (JSON/TOML/YAML/MD via .dprint.json plugin URLs).";
    };

    enableTypos = lib.mkOption {
      type = lib.types.bool;
      default = true;
      description = "Enable typos spell-checker.";
    };

    enableRipsecrets = lib.mkOption {
      type = lib.types.bool;
      default = true;
      description = "Enable ripsecrets secret scanner.";
    };
  };

  config = lib.mkIf cfg.enable {
    packages =
      (with pkgs; [
        # Core formatters (used by treefmt.toml)
        treefmt
        rustfmt
      ])
      ++ lib.optionals cfg.enableDprint [
        pkgs.dprint # reads .dprint.json (plugin URLs, shadow-empire pattern)
      ]
      ++ lib.optionals cfg.enableTypos [
        pkgs.typos
      ]
      ++ lib.optionals cfg.enableRipsecrets [
        pkgs.ripsecrets
      ];

    # ── Manual treefmt config (repo root), not treefmt-nix generation ──
    # Point treefmt at it and disable devenv's auto-generated task.
    enterShell = ''
      export TREEFMT_CONFIG="$DEVENV_ROOT/treefmt.toml"
    '';
    tasks."devenv:treefmt:run".before = lib.mkForce [ ];

    # git-hooks (devenv 2.x first-class): format + hygiene.
    # Hooks run from the raw `git commit` env (not the devenv shell), so
    # treefmt can't find rustfmt/dprint by name — wrap via mkHook.
    git-hooks.hooks = {
      treefmt = {
        enable = true;
        settings.fail-on-change = true;
        entry = ''
          ${mkHook {
            command = "${pkgs.treefmt}/bin/treefmt";
            bins = with pkgs; [ treefmt rustfmt dprint typos ];
            args = "--fail-on-change --no-cache";
          }}
        '';
      };
      typos.enable = true;
      ripsecrets.enable = true;
    };
  };
}
