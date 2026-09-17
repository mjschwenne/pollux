{ lib, buildGoModule, ... }:
let
  name = "pollux";
  version = "latest";
in
buildGoModule {
  inherit name version;
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.difference ./. (lib.fileset.fileFilter (f: f.hasExt "nix") ./.);
  };
  vendorHash = "sha256-lYCZAUit96cvXrbCnoDQxFwyCIGv6sEcEAVBI9G1DJ4=";
}
