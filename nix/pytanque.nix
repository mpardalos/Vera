{ lib, buildPythonPackage, fetchFromGitHub, setuptools, requests, typing-extensions }:

buildPythonPackage rec {
  pname = "pytanque";
  version = "0.2.2";
  pyproject = true;

  src = fetchFromGitHub {
    owner = "LLM4Rocq";
    repo = "pytanque";
    tag = "v${version}";
    hash = "sha256-1Hae21BuMdE6MjRdiBO7fcsuS4HzahOdLLhynAUox3I=";
  };

  # No [build-system] in pyproject.toml -> PEP 517 default backend.
  build-system = [ setuptools ];

  dependencies = [ requests typing-extensions ];

  pythonImportsCheck = [ "pytanque" ];

  meta = {
    description = "Python client for the petanque (pet) Rocq interaction protocol";
    homepage = "https://github.com/LLM4Rocq/pytanque";
    license = lib.licenses.asl20;
  };
}
