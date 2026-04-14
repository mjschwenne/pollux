{
  lib,
  buildPythonPackage,
  fetchPypi,
  setuptools,
  pydantic,
  httpx,
  pathspec,
}:

buildPythonPackage rec {
  pname = "aristotlelib";
  version = "1.0.1";
  pyproject = true;

  src = fetchPypi {
    inherit pname version;
    hash = "sha256-FON0tngCWoCbLOJPAxD9uOo1WZFg22M51cnmKwRMlho=";
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
