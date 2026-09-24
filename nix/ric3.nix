{ lib, rustPlatform, fetchFromGitHub, clang, cmake, makeWrapper, coreutils, procps }:

rustPlatform.buildRustPackage {
  pname = "ric3";
  version = "1.5.1-hwmcc25";

  src = fetchFromGitHub {
    owner = "gipsyh";
    repo = "rIC3";
    # Pin the hwmcc25 branch for reproducible builds.
    rev = "52535208f5d35b5706f331883dcd1f023c3e827e";
    hash = "sha256-NaKMSpC8v2V4GICxIbYoW6rfSt5teLG2DLl6XG4bojo=";
    fetchSubmodules = true;
  };

  # Upstream's competition branch does not commit a lockfile.
  cargoLock.lockFile = ./ric3-Cargo.lock;

  postPatch = ''
    cp ${./ric3-Cargo.lock} Cargo.lock
  '';

  nativeBuildInputs = [ clang cmake makeWrapper ];

  # This competition branch uses unstable Rust features. Enable them with
  # nixpkgs' compiler rather than introducing a separate nightly toolchain.
  env.RUSTC_BOOTSTRAP = "1";

  # CMake is used by the SAT solver's Cargo build script, not at the root.
  dontUseCmakeConfigure = true;

  postFixup = ''
    wrapProgram "$out/bin/rIC3" \
      --prefix PATH : ${lib.makeBinPath [ coreutils procps ]}
  '';

  meta = {
    description = "Hardware model checker for AIGER and BTOR2 models";
    homepage = "https://github.com/gipsyh/rIC3";
    license = lib.licenses.gpl3Only;
    mainProgram = "rIC3";
    platforms = lib.platforms.linux;
  };
}
