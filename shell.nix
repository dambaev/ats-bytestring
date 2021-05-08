let
  pkgs0 = (import <nixpkgs> {}); # first, load the nixpkgs with system-wide overlays
  pkgs = pkgs0 // (import ./overlay-set.nix { pkgs = pkgs0; }); # second, add local packages into the scope of pkgs
  shell = pkgs.mkShell {
    buildInputs = pkgs.ats-bytestring.buildInputs ++ [ pkgs.valgrind pkgs.gdb ];
  };

in shell
