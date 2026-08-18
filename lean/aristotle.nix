{
  lib,
  buildPythonPackage,
  fetchurl,
  setuptools,
  pydantic,
  httpx,
  pathspec,
}:

buildPythonPackage rec {
  pname = "aristotlelib";
  version = "2.1.0";
  format = "wheel";

  src = fetchurl {
    url = "https://files.pythonhosted.org/packages/c5/63/1d25b34c331deee0e667881f81b5760d4d9c10f4f787cb8c6e0992ed5c16/aristotlelib-2.1.0-py3-none-any.whl";
    hash = "sha256-8pDI4LdLFbW1tDLbbdeRWtyPSf6D7+8P0vLqU7XDNVU=";
  };

  build-system = [ setuptools ];

  dependencies = [
    pydantic
    httpx
    pathspec
  ];

  pythonImportsCheck = [ "aristotlelib" ];

  meta = {
    description = "Python library for automated theorem proving with Lean";
    homepage = "https://aristotle.harmonic.fun";
    license = lib.licenses.unfree;
    mainProgram = "aristotle";
  };
}
