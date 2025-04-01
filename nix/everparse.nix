{
  fstar,
  karamel,
  ocamlPackages,
  removeReferencesTo,
  stdenv,
  symlinks,
  version,
  which,
  z3,
}: let
  pname = "everpase";
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
    karamel.passthru.lib
  ];
  nativeBuildInputs = [fstar removeReferencesTo symlinks which z3] ++ (with ocamlPackages; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit version pname propagatedBuildInputs nativeBuildInputs;

    src = ./.;

    outputs = ["out" "home"];

    KRML_HOME = karamel;

    # GIT_REV = version;

    # configurePhase = "export KRML_HOME=$(pwd)";

    enableParallelBuilding = true;

    # preBuild = "mkdir -p krmllib/hints";

    preInstall = "export PREFIX=$out";
    postInstall = ''
      # OCaml leaves its full store path in produced binaries
      # Thus we remove every reference to it
      for binary in $out/bin/*
      do
        remove-references-to -t '${ocamlPackages.ocaml}' $binary
      done

      cp -r ./. $home
    '';

    passthru = {
      lib = ocamlPackages.buildDunePackage {
        GIT_REV = version;
        inherit version propagatedBuildInputs;
        nativeBuildInputs = with ocamlPackages; [menhir];
        pname = "qd";
        src = ./.;
      };
    };

    dontFixup = true;
  }
