{
  description = "A verified verilog equivalence checker (minimum viable product)";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    coqhammer = {
        url = "github:wrsturgeon/coqhammer-nix";
        inputs.src.url = "github:lukaszcz/coqhammer/coq8.19";
    };
  };

  outputs = { self, nixpkgs, flake-utils, coqhammer }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        coq = pkgs.coq_8_19;
        coqPackages = pkgs.coqPackages_8_19;

        smtcoq-api = coqPackages.mkCoqDerivation {
          pname = "smtcoq-api";
          repo = "smtcoq-api";
          owner = "smtcoq";
          branch = "correctness";

          version = "2024-12-12-correctness";
          release = {
            "2022-12-11" = {
              rev = "1368e5d443677723f1ede70caedd392d0800c6a6";
              sha256 = "sha256-rZcxUwtf8i70QNYuXctGufhI5+53yFBxRz2k6uA4gxo=";
            };
            "2024-12-12-correctness" = {
              rev = "1f2e2169a74539ded2db50ae2161d666768388c5";
              sha256 = "sha256-1Q/dXVXgYAn0MPJ/MdFRwB8jZkC76bACjmagZN9l08Q=";
            };
          };
        };

        smtcoq-api-bitvectors = coqPackages.mkCoqDerivation {
          pname = "smtcoq-api";
          repo = "smtcoq-api";
          owner = "mpardalos";
          branch = "extras";

          version = "extras";
          release = {
            "extras" = {
              rev = "793f1d4f4b0667927badfd000d3feefe65a35b25";
              sha256 = "sha256-MN5NRSUHrBT7m/yjWey1BRmbI3X4MOaVXZeE3cYrE4g=";
            };
          };
          nativeBuildInputs = [ coq.ocaml coqPackages.smtcoq ];
        };

        deps = [
          coq
          coqPackages.ExtLib
          coqPackages.equations
          coqPackages.smtcoq
          # smtcoq-api
          smtcoq-api-bitvectors

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

          pkgs.sv-lang
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
          (coqhammer.lib.with-pkgs pkgs coqPackages).tactics
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
              --prefix PATH : ${pkgs.sv-lang}/bin
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
