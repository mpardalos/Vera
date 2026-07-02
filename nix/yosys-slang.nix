{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  pname = "yosys-slang";
  version = "unstable";
  plugin = "slang";

  src = pkgs.fetchFromGitHub {
    owner = "povik";
    repo = "yosys-slang";
    rev = "b08e87ca0de19490f98f5c2937fd933c55cbfc30";
    hash = "sha256-lQaMyl5wD1jg2WvJnwiMYhvLAK70M7UINcXtR2XnmLU=";
    fetchSubmodules = true;
  };

  nativeBuildInputs = with pkgs; [ cmake python3 ];
  buildInputs = with pkgs; [ yosys ];

  installPhase = ''
    mkdir -p $out/share/yosys/plugins
    cp slang.so $out/share/yosys/plugins/
  '';
}
