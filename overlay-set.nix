{pkgs ? {}}:
{
  ats-bytestring = pkgs.callPackage ./derivation.nix {};
}