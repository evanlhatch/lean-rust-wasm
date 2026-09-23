# Process examples (devenv 2.0) — gated off by default.
# Enable per-project by setting templateConfig.processes.enable = true
# and uncommenting the processes you need. See:
#   https://devenv.sh/processes/ (watchers, ports, sockets, watchdog)

{ lib, config, ... }:
{
  options.templateConfig.processes.enable = lib.mkEnableOption "example processes block" // {
    default = false;
  };

  config = lib.mkIf (config.templateConfig.processes.enable) {
    # Watcher: long-running processes restart on change; one-shot commands
    # re-run. `paths` are resolved relative to the project root (devenv.nix)
    # — use path literals, not strings.
    # processes.dev = {
    #   exec = "cargo run";
    #   watch = {
    #     paths = [ ./src ];
    #     extensions = [ "rs" "toml" ];
    #     ignore = [ "target" "*.log" ];
    #   };
    # };

    # Auto port allocation (strict mode: strict_ports in devenv.yaml).
    # processes.server = {
    #   exec = ''myserver --port ${toString config.processes.server.ports.http.value}'';
    #   ports.http.allocate = 8080;
    # };

    # Socket activation (zero-downtime restarts, systemd-compatible).
    # processes.api = {
    #   exec = "myserver";
    #   listen = [ { name = "http"; kind = "tcp"; address = "127.0.0.1:8080"; } ];
    # };
  };
}
