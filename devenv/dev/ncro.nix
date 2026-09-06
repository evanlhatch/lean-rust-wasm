# ncro — Nix Cache Route Optimizer (devenv process, OPT-IN).
#
# Races upstream caches in parallel on localhost:8080.
#   nix build/develop -> http://localhost:8080 -> ncro -> upstream caches
#
# To use: set templateConfig.ncro.enable = true in devenv/local.nix and
# add `http://localhost:8080` to substituters (see dev/base.nix).
{
  pkgs,
  lib,
  config,
  ...
}:
let
  cfg = config.templateConfig.ncro;

  # Upstream caches to race (trim/add per project).
  allCaches = [
    {
      url = "https://cache.nixos.org";
      publicKey = "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=";
      priority = 10;
    }
    {
      url = "https://nix-community.cachix.org";
      publicKey = "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs=";
      priority = 15;
    }
    {
      url = "https://cache.numtide.com";
      publicKey = "niks3.numtide.com-1:DTx8wZduET09hRmMtKdQDxNNthLQETkc/yaX7M4qK0g=";
      priority = 18;
    }
    {
      url = "https://cache.flox.dev";
      publicKey = "flox-cache-public-1:7F4OyH7ZCnFhcze3fJdfyXYLQw/aV7GEed86nQ7IsOs=";
      priority = 20;
    }
    {
      url = "https://nixpkgs-unfree.cachix.org";
      publicKey = "nixpkgs-unfree.cachix.org-1:hqvoInulhbV4nJ9yJOEr+4wxhDV4xq2d1DK7S6Nj6rs=";
      priority = 25;
    }
  ];

  upstreamBlocks = builtins.concatStringsSep "\n" (map (c: ''
    [[upstreams]]
    url = "${c.url}"
    priority = ${toString c.priority}
    public_key = "${c.publicKey}"
  '') allCaches);

  # Static config, @DEVENV_STATE@ replaced at runtime.
  ncroConfigStatic = pkgs.writeText "ncro-config.toml" ''
    server.listen = ":8080"

    ${upstreamBlocks}

    [cache]
    db_path = "@DEVENV_STATE@/ncro/routes.db"
    max_entries = 100000
    ttl = "1h"
    latency_alpha = 0.3

    [logging]
    level = "info"
    format = "json"
  '';
in
{
  options.templateConfig.ncro.enable = lib.mkEnableOption "ncro cache proxy process" // {
    default = false;
  };

  config = lib.mkIf cfg.enable {
    packages = [ pkgs.ncro ];

    processes.ncro = {
      exec = ''
        mkdir -p "$DEVENV_STATE/ncro"
        sed "s|@DEVENV_STATE@|$DEVENV_STATE|g" ${ncroConfigStatic} > "$DEVENV_STATE/ncro/config.toml"
        exec ${pkgs.ncro}/bin/ncro --config "$DEVENV_STATE/ncro/config.toml"
      '';
      restart.on = "on_failure";
    };
  };
}
