# rocq-mcp: an MCP server that lets an LLM agent compile, query and step Rocq
# proofs via `coqc` and `pet` (coq-lsp).  Built the standard nixpkgs way.
#
# `pytanque` (its Python client for `pet`) is not in nixpkgs, so it lives in a
# small sibling derivation.  The `pet` binary itself comes from coq-lsp.
{ lib
, python3Packages
, fetchFromGitHub
, makeWrapper
, coq        # provides `coqc`
, coq-lsp    # provides `pet`
, dune_3     # rocq-mcp runs `dune coq top` for workspace detection
}:

python3Packages.buildPythonApplication {
  pname = "rocq-mcp";
  version = "0.3.1";
  pyproject = true;

  src = fetchFromGitHub {
    owner = "LLM4Rocq";
    repo = "rocq-mcp";
    # 0.3.1 is unreleased/untagged; pin the exact commit.
    rev = "d92fa9eaab78230a8b81f37b3a605672076ca22c";
    hash = "sha256-qus34UYvNRIt2MYZp34t/i4SIHyK0etlvtOIWS3+jrA=";
  };

  build-system = [ python3Packages.setuptools ];

  dependencies = [
    python3Packages.fastmcp
    python3Packages.psutil
    (python3Packages.callPackage ./pytanque.nix { })
  ];

  nativeBuildInputs = [ makeWrapper ];

  pythonImportsCheck = [ "rocq_mcp" ];

  # rocq-mcp resolves coqc / pet / dune from PATH at runtime; bake them in so
  # the server works regardless of how the MCP client launches it.
  postFixup = ''
    wrapProgram $out/bin/rocq-mcp \
      --prefix PATH : ${lib.makeBinPath [ coq coq-lsp dune_3 ]}
  '';

  meta = {
    description = "MCP server for Rocq/Coq proof development";
    homepage = "https://github.com/LLM4Rocq/rocq-mcp";
    license = lib.licenses.asl20;
    mainProgram = "rocq-mcp";
  };
}
