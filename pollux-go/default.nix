{buildGoModule, ...}: let
  name = "pollux";
  version = "latest";
in
  buildGoModule {
    inherit name version;
    src = ./.;
    vendorHash = "sha256-6DzOOFGg3qARoLjuhalzJoAnQ3RGCdYjlxsc/8QUviU=";
  }
