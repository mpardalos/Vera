{
  description = "A verified verilog equivalence checker (minimum viable product)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        coq = pkgs.coq_8_18;
        coqPackages = pkgs.coqPackages_8_18;
      in {
        devShells.default = pkgs.mkShell {
          packages =
            [
              coq
              coqPackages.coq-ext-lib

              coq.ocaml
              coq.ocamlPackages.findlib
              coq.ocamlPackages.ocaml-lsp
              coq.ocamlPackages.dune_3
              coq.ocamlPackages.utop
              coq.ocamlPackages.ocamlformat
              coq.ocamlPackages.z3

              pkgs.sv-lang
              pkgs.verible
              pkgs.z3
            ];
        };
      }
    );
}
