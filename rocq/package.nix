{
  lib,
  stdenv,
  perennial,
  perennialPkgs,
  ...
}:
stdenv.mkDerivation {
  pname = "pollux-rocq";
  version = "unstable";

  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.difference ./. (
      # Tests.v doesn't build in the nix sandbox for some wierd memory layout bug with 
      # vm_compute. Builds find locally.
      lib.fileset.fileFilter (f: f.hasExt "nix" || f.hasExt "md" || f.name == "Tests.v") ./.
    );
  };

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
    runHook preBuild
    export ROCQPATH=$COQPATH
    unset COQPATH
    make -j$NIX_BUILD_CORES
    runHook postBuild
  '';

  installPhase = ''
    mkdir -p $out/lib/coq/9.1.0/user-contrib/Pollux
    cp -r . $out/lib/coq/9.1.0/user-contrib/Pollux
  '';
}
