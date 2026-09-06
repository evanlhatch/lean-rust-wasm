# Single source of truth for binary caches (sheath _binary-caches.nix
# pattern). Consumed by base.nix (NIX_CONFIG substituters) and ncro.nix
# (upstream list). The `_` prefix excludes this from auto-discovery.
{
  # Cache for the project's own deps — swap in your cachix when publishing.
  project = {
    url = "https://nix-community.cachix.org";
    publicKey = "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs=";
  };

  # Upstream caches to race (ncro) or trust (NIX_CONFIG).
  upstreams = [
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
}
