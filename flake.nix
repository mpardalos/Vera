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
        coq-nbits = coqPackages.mkCoqDerivation {
          pname = "coq-nbits";
          owner = "fmlab-iis";
          version = "2022-11-28";
          release = {
            "2022-11-28" = {
              rev = "c360c35bd263807d0f960f4edfac713b1257ea80";
              sha256 = "sha256-eeF1HouyyPxZG8wdEtxQP1daO7taxNVGzMyWv7UkE0k=";
            };
          };
          propagatedBuildInputs = [
            coqPackages.mathcomp.ssreflect
            coqPackages.mathcomp.algebra
          ];
        };
      in {
        devShells.default = pkgs.mkShell {
          packages =
            [
              coq
              coqPackages.coq-ext-lib
              coqPackages.equations
              coq-nbits

              coq.ocaml
              coq.ocamlPackages.findlib
              coq.ocamlPackages.ocaml-lsp
              coq.ocamlPackages.dune_3
              coq.ocamlPackages.utop
              coq.ocamlPackages.ocamlformat
              coq.ocamlPackages.z3
              coq.ocamlPackages.menhir

              pkgs.sv-lang
              pkgs.verible
              pkgs.surelog
              pkgs.z3
            ];
        };
      }
    );
}
