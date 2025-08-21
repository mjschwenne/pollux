{
  bash,
  autoconf,
  rocq-core,
  rocqPackages,
  version ? null,
  ...
}:
rocqPackages.mkRocqDerivation {
  pname = "flocq";
  owner = "flocq";
  domain = "gitlab.inria.fr";

  inherit version;
  defaultVersion = "4.2.1";
  release."4.2.1".sha256 = "sha256-W5hcAm0GGmNsvre79/iGNcoBwFzStC4G177hZ3ds/4E=";
  releaseRev = v: "flocq-${v}";

  COQC = "${rocq-core}/bin/rocq compile";
  COQDEP = "${rocq-core}/bin/rocq dep";

  nativeBuildInputs = [
    bash
    autoconf
  ];

  mlPlugin = true;
  useMelquiondRemake.logpath = "Flocq";

  propagatedBuildInputs = [rocqPackages.stdlib];
}
