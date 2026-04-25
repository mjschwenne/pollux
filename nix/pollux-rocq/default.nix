{
  stdenv,
  perennial,
  perennialPkgs,
  ...
}:
stdenv.mkDerivation {
  pname = "pollux-rocq";
  version = "unstable";

  src = ../../.;

  nativeBuildInputs = with perennialPkgs; [
    rocq-runtime
    rocq-stdlib
  ];
  propagatedBuildInputs = with perennialPkgs; [
    coq-coqutil
    coq-record-update
    rocq-stdpp
    rocq-iris
    iris-named-props
    perennial
  ];

  enableParallelBuilding = true;

  buildPhase = ''
    export ROCQPATH=$COQPATH
    unset COQPATH
    make -j$NIX_BUILD_CORES
  '';

  installPhase = ''
    mkdir -p $out/lib/coq/9.1.0/user-contrib
    cp -r src $out/lib/coq/9.1.0/user-contrib/Pollux
  '';
}
