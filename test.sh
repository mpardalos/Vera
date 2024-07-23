#!/usr/bin/env bash

dune build

for f in $(find test/ -type f); do
    echo "=== $(basename $f) ==="
    cat "$f"
    echo '---'
    dune exec -- bin/main.exe "$f"
    echo "======"
    echo
done
