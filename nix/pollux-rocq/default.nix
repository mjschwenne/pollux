{
  stdenv,
  rocq-core,
  rocqPackages,
  coqPackages,
  perennial,
  ...
}:
stdenv.mkDerivation {
  pname = "pollux-rocq";
  version = "unstable";

  src = ../../.;

  nativeBuildInputs = [
    rocq-core
  ];
  propagatedBuildInputs = [
    coqPackages.equations
    perennial
    coqPackages.flocq
    rocqPackages.stdlib
  ];

  enableParallelBuilding = true;

  buildPhase = ''
    export OCAMLPATH=${coqPackages.equations}/lib/ocaml/4.14.2/site-lib/
    make -j$NIX_BUILD_CORES
  '';

  installPhase = ''
    mkdir -p $out/lib/coq/${rocq-core.rocq-version}/user-contrib
    cp -r src $out/lib/coq/${rocq-core.rocq-version}/user-contrib/Pollux
  '';
}
