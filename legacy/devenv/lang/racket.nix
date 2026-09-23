# Racket — OPT-IN via profile: devenv --profile racket
# `languages.racket.enable` defaults to false (upstream devenv default);
# this module only flips it on when the racket profile is active.
{ pkgs, ... }:
{
  languages.racket.enable = true;
}
