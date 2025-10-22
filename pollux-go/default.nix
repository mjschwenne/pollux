{buildGoModule, ...}: let
  name = "pollux";
  version = "latest";
in
  buildGoModule {
    inherit name version;
    src = ./.;
    vendorHash = "sha256-6P6nxbe1gxlJQgB2cLEC/6nvv8MnyNwW0JGEFxGi5UU=";
  }
