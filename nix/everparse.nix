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
  pname = "everpase";
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
    karamel.passthru.lib
  ];
  nativeBuildInputs = [fstar removeReferencesTo symlinks which z3_4_8_5 gnused] ++ (with ocamlPackages; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit version pname propagatedBuildInputs nativeBuildInputs;

    src = ./.;
    # src = fetchFromGitHub {
    #   owner = "project-everest";
    #   repo = "everparse";
    #   rev = "d9283b5bd8f2fa78f1ed0cee11ecf5a71be589e4";
    #   hash = "sha256-oJg4ONYYQ/8f8DWevr47fkz8Aniz64kIOTl6//QiX64=";
    # };

    outputs = ["out" "home"];

    KRML_HOME = karamel;
    enableParallelBuilding = true;

    configurePhase = ''
      export FSTAR_EXE=${fstar}/bin/fstar.exe
      patchShebangs --build ./src/3d/version.sh
    '';

    preInstall = ''
      export PREFIX=$out
    '';

    postInstall = ''
      # OCaml leaves its full store path in produced binaries
      # Thus we remove every reference to it
      for binary in $out/bin/*
      do
        remove-references-to -t '${ocamlPackages.ocaml}' $binary
      done

      cp -r ./. $home
    '';

    # passthru = {
    #   lib = ocamlPackages.buildDunePackage {
    #     GIT_REV = version;
    #     inherit version propagatedBuildInputs;
    #     nativeBuildInputs = with ocamlPackages; [menhir];
    #     pname = "qd";
    #     src = ./.;
    #   };
    # };
    #
    dontFixup = true;
  }
