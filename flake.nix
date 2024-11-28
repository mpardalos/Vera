{
  description = "A verified verilog equivalence checker (minimum viable product)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        coq = pkgs.coq_8_19;
        coqPackages = pkgs.coqPackages_8_19;
      in {
        devShells.default = pkgs.mkShell {
          packages =
            [
              coq
              coqPackages.ExtLib
              coqPackages.equations
              coqPackages.smtcoq

              coq.ocaml
              coq.ocamlPackages.findlib
              coq.ocamlPackages.ocaml-lsp
              coq.ocamlPackages.dune_3
              coq.ocamlPackages.utop
              coq.ocamlPackages.ocamlformat
              coq.ocamlPackages.z3
              coq.ocamlPackages.menhir
              coq.ocamlPackages.ppx_deriving
              coq.ocamlPackages.ppxlib

              pkgs.sv-lang
              pkgs.verible
              pkgs.surelog
              pkgs.z3
            ];
        };
      }
    );
}
