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

        deps = [
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
          coq.ocamlPackages.menhir
          coq.ocamlPackages.ppx_deriving
          coq.ocamlPackages.ppxlib
          coq.ocamlPackages.yojson

          pkgs.sv-lang
          pkgs.z3
        ];

        dev-deps = [
          pkgs.abc-verifier
          pkgs.bitwuzla
          pkgs.cvc4
          pkgs.cvc5
          pkgs.yosys
          pkgs.iverilog
          (pkgs.python3.withPackages (ps: with ps; [ networkx pygraphviz ]))
        ];
      in {
        devShells.default = pkgs.mkShell {
          packages = deps ++ dev-deps;
        };

        packages.default = pkgs.stdenv.mkDerivation {
          pname = "vera";
          version = "0.1.0"; # Replace with your actual version

          src = self; # This assumes the source is in the current directory

          buildInputs = deps ++ [ pkgs.makeWrapper ];

          buildPhase = ''
            dune build
          '';

          installPhase = ''
            mkdir -p $out/bin
            cp _build/default/bin/main.exe $out/bin/vera

            # Wrap the binary to add slang to PATH
            wrapProgram $out/bin/vera \
              --prefix PATH : ${pkgs.sv-lang}/bin \
              --prefix PATH : ${pkgs.z3}/bin
          '';

          meta = with pkgs.lib; {
            description = "Verified Verilog Equivalence Checker";
            homepage = ""; # Add your project homepage if available
            license = licenses.mit; # Replace with your actual license
            platforms = platforms.unix;
          };
        };
      }
    );
}
