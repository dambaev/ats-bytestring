let
#  nixpkgs = import <nixpkgs>;
  pkgs = import <nixpkgs> {
    config = {};
    overlays = [
      (import ./overlay.nix)
    ];
  };
  shell = pkgs.mkShell {
    buildInputs = pkgs.ats-bytestring.buildInputs ++ [ pkgs.valgrind pkgs.gdb ];
  };

in shell
