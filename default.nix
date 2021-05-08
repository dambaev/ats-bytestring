let
  pkgs0 = (import <nixpkgs> {}); # first, load the nixpkgs with system-wide overlays
  pkgs = pkgs0 // (import ./overlay-set.nix { pkgs = pkgs0; }); # second, add local packages into the scope of pkgs

in pkgs.ats-bytestring
