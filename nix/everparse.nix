{
  callPackage,
  installShellFiles,
  lib,
  makeWrapper,
  buildDunePackage,
  version,
  z3,
  bash,
  batteries,
  menhir,
  menhirlib,
  pprint,
  ppx_deriving,
  ppx_deriving_yojson,
  ppxlib,
  process,
  sedlex,
  stdint,
  yojson,
  zarith,
  memtrace,
  mtime,
  ...
}:
buildDunePackage {
  pname = "everparse";
  version = "v2023.01.23";
}
