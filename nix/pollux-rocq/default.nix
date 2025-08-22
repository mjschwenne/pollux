{
  stdenv,
  rocq-core,
  rocqPackages,
  perennial,
  flocq,
  ...
}:
stdenv.mkDerivation {
  pname = "pollux-rocq";
  version = "unstable";

  src = ../../.;

  nativeBuildInputs = [
    rocq-core
  ];
  buildInputs = [
    perennial
    flocq
    rocqPackages.stdlib
  ];

  enableParallelBuilding = true;

  buildPhase = ''
    make -j$NIX_BUILD_CORES
  '';

  installPhase = ''
    mkdir -p $out/lib/coq/${rocq-core.rocq-version}/user-contrib
    cp -r src $out/lib/coq/${rocq-core.rocq-version}/user-contrib/Pollux
  '';
}
