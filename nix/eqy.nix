{
  lib,
  stdenv,
  fetchFromGitHub,
  yosys,
  sby,
  makeWrapper ? null,
}:

stdenv.mkDerivation (finalAttrs: {
  pname = "eqy";
  version = yosys.version;

  src = fetchFromGitHub {
    owner = "YosysHQ";
    repo = "eqy";
    rev = "v${finalAttrs.version}";
    sha256 = "sha256-7OwtyV3+9vZhTD0Ur8Dhd39xNtqNs2M5XETBN1F6Xb0=";
  };

  buildInputs = [ yosys sby ];
  nativeBuildInputs = [ makeWrapper ];

  enableParallelBuilding = true;

  installPhase = ''
    mkdir -p $out/bin
    make install PREFIX=$out
    wrapProgram $out/bin/eqy \
      --prefix PATH : "${lib.makeBinPath [ yosys sby ]}"
  '';

  meta = with lib; {
    description = "Equivalence checking tool for Yosys";
    homepage = "https://github.com/YosysHQ/eqy";
    license = licenses.isc; # Verify the actual license
    platforms = platforms.unix;
    maintainers = with maintainers; [ ]; # Add maintainers if applicable
  };
})
