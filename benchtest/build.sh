#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

mkdir -p .shake/ghc
ghc --make Shakefile.hs -O2 -threaded -rtsopts \
    -with-rtsopts=-I0 \
    -odir .shake/ghc -hidir .shake/ghc -stubdir .shake/ghc \
    -o .shake/ghc/Shakefile && \
    .shake/ghc/Shakefile +RTS -s -N -RTS "$@"
