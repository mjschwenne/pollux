{buildGoModule, ...}: let
  name = "pollux_varint_conversion";
  version = "latest";
in
  buildGoModule {
    inherit name version;
    src = ./../go_varint_conversion;
    vendorHash = "sha256-k4HZj2GxcIowPDJWFPKbFHg97XHE9GDgMLIZUolargA=";
  }
