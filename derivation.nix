{ stdenv, pkgs, fetchzip, fetchpatch, fetchgit, fetchurl }:
stdenv.mkDerivation {
  name = "ats-bytestring";

  src = ./. ;
  buildInputs = with pkgs;
  [ ats2
  ];

}
