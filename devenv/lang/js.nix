# JavaScript (node + bun) — OPT-IN via profile: devenv --profile js
# Consumed by: cloudflare profile (jco transpile), docs profile (astro).
{ pkgs, ... }:
{
  languages.javascript = {
    enable = true;
    package = pkgs.nodejs-slim;

    # Bun as the primary JS runtime + package manager
    bun = {
      enable = true;
      package = pkgs.bun;
      install.enable = false;
    };

    npm.enable = false;
    pnpm.enable = false;
    yarn.enable = false;
    corepack.enable = false;
  };
}
