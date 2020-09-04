{ nixpkgs ? import <nixpkgs> { }}:
let
  inherit (nixpkgs) pkgs;
  project = import ./release.nix {};
in
project.env
