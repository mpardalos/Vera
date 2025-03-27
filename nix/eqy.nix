{
  lib,
  stdenv,
  fetchFromGitHub,
  yosys,
  symbiyosys,
  makeWrapper ? null,
}:

stdenv.mkDerivation rec {
  pname = "eqy";
  version = "0.51"; # Replace with the specific version or date of the commit

  src = fetchFromGitHub {
    owner = "YosysHQ";
    repo = "eqy";
    rev = "93bf4dfb8b19c0f1e9d472fd8421cdfdc4fe85a0";
    sha256 = "sha256-5LvOebOJiG775Xb4+rvOvd+MUq3ACI2JGJfbpGaPrRE=";
  };

  buildInputs = [ yosys symbiyosys ];
  nativeBuildInputs = [ makeWrapper ];

  buildPhase = ''
    make
  '';

  installPhase = ''
    mkdir -p $out/bin
    make install PREFIX=$out
    wrapProgram $out/bin/eqy \
      --prefix PATH : "${lib.makeBinPath [ yosys symbiyosys ]}"
  '';

  meta = with lib; {
    description = "Equivalence checking tool for Yosys";
    homepage = "https://github.com/YosysHQ/eqy";
    license = licenses.isc; # Verify the actual license
    platforms = platforms.unix;
    maintainers = with maintainers; [ ]; # Add maintainers if applicable
  };
}
