{
  lib,
  fetchFromGitHub,
  buildDunePackage,
  ocaml,
  pkg-config,
  protobuf,
  ocamlPackages,
  ...
}: let
  omd = ocamlPackages.omd.overrideAttrs (final: prev: {
    version = "2.0.0-alpha4";
    src = fetchFromGitHub {
      owner = "ocaml-community";
      repo = "omd";
      rev = "373e3f80e48001a62daf4072373ad3aa589ca65f";
      hash = "sha256-5eZitDaNKSkLOsyPf5g5v9wdZZ3iVQGu8Ot4FHZZ3AI=";
    };
    buildInputs = with ocamlPackages; [dune-build-info uucp uunf uutf];
  });
in
  buildDunePackage rec {
    pname = "ocaml-protoc-plugin";
    version = "2025-07-09-main";

    minimalOcamlVersion = "4.14";

    src = fetchFromGitHub {
      owner = "andersfugmann";
      repo = pname;
      rev = "27b7eda3c775dc5a140cec0f57bd7e1ba3410152";
      hash = "sha256-JKhzAZYnXu17v4LGkiXGNH2G5cxnXrPKtfEtZmkGbBw=";
    };

    checkInputs = with ocamlPackages; [dune-configurator yojson];
    buildInputs = with ocamlPackages;
      [
        base64
        omd
        ppx_expect
        ppx_deriving
        ptime
        uucp
        uunf
        uutf
      ]
      ++ [protobuf];
    nativeBuildInputs = [pkg-config protobuf];

    doCheck = lib.versionAtLeast ocaml.version "4.14";
  }
