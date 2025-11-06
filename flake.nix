{
  description = "A verified verilog equivalence checker (minimum viable product)";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    nixpkgs-stable.url = "github:nixos/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, nixpkgs-stable, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        stable-pkgs = import nixpkgs-stable { inherit system; };

        coq = pkgs.coq;
        coqPackages = pkgs.coqPackages;

        deps = [
          coq
          coqPackages.stdlib
          coqPackages.ExtLib
          coqPackages.equations

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
          coq.ocamlPackages.cmdliner

          stable-pkgs.sv-lang
        ];

        dev-deps = [
          pkgs.abc-verifier
          pkgs.bitwuzla
          pkgs.cvc4
          pkgs.cvc5
          pkgs.yosys
          pkgs.iverilog
          (pkgs.python3.withPackages (ps: with ps; [ networkx pygraphviz ]))
          pkgs.z3
          pkgs.cvc5
	  coqPackages.coq-lsp
        ];
      in {
        devShells.default = pkgs.mkShell {
          packages = deps ++ dev-deps;
          shellHook = ''
            # Set ROCQPATH for Rocq 9.0+ (keep COQPATH for backwards compatibility with dune)
            if [ -n "$COQPATH" ]; then
              export ROCQPATH="$COQPATH"
            fi
          '';
        };

        packages.default = pkgs.stdenv.mkDerivation {
          pname = "vera";
          version = "0.1.0"; # Replace with your actual version

          src = self; # This assumes the source is in the current directory

          buildInputs = deps ++ [ pkgs.makeWrapper ];

          buildPhase = ''
            # Set ROCQPATH for Rocq 9.0+ (keep COQPATH for backwards compatibility with dune)
            if [ -n "$COQPATH" ]; then
              export ROCQPATH="$COQPATH"
            fi
            dune build
          '';

          installPhase = ''
            mkdir -p $out/bin
            cp _build/default/bin/main.exe $out/bin/vera

            # Wrap the binary to add slang to PATH
            wrapProgram $out/bin/vera \
              --prefix PATH : ${stable-pkgs.sv-lang}/bin
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
