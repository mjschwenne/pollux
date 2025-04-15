{
  fstar,
  karamel,
  fetchFromGitHub,
  gnused,
  ocamlPackages,
  removeReferencesTo,
  stdenv,
  symlinks,
  which,
  z3_4_8_5,
}: let
  pname = "everparse";
  version = "v2025.04.01";
  propagatedBuildInputs = with ocamlPackages; [
    batteries
    stdint
    ppx_deriving_yojson
    zarith
    pprint
    menhirLib
    sedlex
    process
    fix
    wasm
    ctypes
    visitors
    uucp
    hex
    sexplib
    re
    sha
    karamel.passthru.lib
  ];
  nativeBuildInputs = [fstar removeReferencesTo symlinks which z3_4_8_5 gnused] ++ (with ocamlPackages; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit version pname propagatedBuildInputs nativeBuildInputs;

    src = fetchFromGitHub {
      owner = "project-everest";
      repo = "everparse";
      rev = "d9283b5bd8f2fa78f1ed0cee11ecf5a71be589e4";
      hash = "sha256-oJg4ONYYQ/8f8DWevr47fkz8Aniz64kIOTl6//QiX64=";
    };

    outputs = ["out"];

    KRML_HOME = karamel;
    enableParallelBuilding = true;

    configurePhase = ''
      export FSTAR_EXE=${fstar}/bin/fstar.exe
      patchShebangs --build ./src/3d/version.sh
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp -r ./bin/* $out/bin
      mkdir -p $out/lib
      mkdir -p $out/lib/lowparse
      cp -r ./src/lowparse/* $out/lib/lowparse
      mkdir -p $out/lib/3d/prelude
      cp ./src/3d/EverParseEndianness.h $out/lib/3d
      cp -r ./src/3d/prelude $out/lib/3d/
      mkdir -p $out/lib/asn1
      cp -r ./src/ASN1/*.fst $out/lib/asn1
      cp -r ./src/ASN1/*.fsti $out/lib/asn1
      cp -r ./src/ASN1/*.checked $out/lib/asn1
    '';
    postInstall = ''
      # OCaml leaves its full store path in produced binaries
      # Thus we remove every reference to it
      for binary in $out/bin/*
      do
        remove-references-to -t '${ocamlPackages.ocaml}' $binary
      done
    '';

    dontFixup = true;
  }
