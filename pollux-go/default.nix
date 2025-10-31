{buildGoModule, ...}: let
  name = "pollux";
  version = "latest";
in
  buildGoModule {
    inherit name version;
    src = ./.;
    vendorHash = "sha256-OUYycxoljD7wyqTYdoxD8dTgMJRYERXhQMkFa6breVU=";
  }
