#!/usr/bin/env bash

dune build

run_test() {
    test_type="$1"
    f="$2"
    echo "=== $f ==="
    cat "$f"
    echo '---'
    dune exec -- bin/main.exe "$test_type" "$f"
    echo "======"
    echo
}

for f in $(find test/module_items -type f); do
    run_test module_item "$f"
done

# for f in $(find test/expressions -type f); do
#     run_test expression "$f"
# done
