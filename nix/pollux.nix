{
  fstar,
  ocaml-ng,
  stdenv,
  protobuf,
  system,
  ocaml-protoc-plugin,
  ...
}: let
  pname = "pollux";
  version = "latest";
  fstar-pkg = fstar.packages.${system}.default;
  propagatedBuildInputs = with ocaml-ng.ocamlPackages_4_14; [
    base64
    batteries
    pprint
    ppx_deriving_yojson
    ppx_expect
    ptime
    qcheck-core
    stdint
    stdio
    zarith
  ];
  nativeBuildInputs =
    [fstar-pkg protobuf ocaml-protoc-plugin]
    ++ (with ocaml-ng.ocamlPackages_4_14; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit pname version nativeBuildInputs propagatedBuildInputs;

    src = ./..;
    configurePhase = ''
      export OCAMLPATH=$OCAMLPATH:${fstar-pkg}/lib
    '';
    makeFlags = ["PREFIX=$(out)"];
    enableParallelBuilding = true;
  }
