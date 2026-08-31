{buildGoModule, ...}: let
  name = "pollux";
  version = "latest";
in
  buildGoModule {
    inherit name version;
    src = ./.;
    vendorHash = "sha256-lYCZAUit96cvXrbCnoDQxFwyCIGv6sEcEAVBI9G1DJ4=";
  }
