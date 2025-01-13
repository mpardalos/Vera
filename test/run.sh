#!/bin/bash

VERA_TIMEOUT=1h
YOSYS_TIMEOUT=1m

set -euo pipefail

testfilter="$@"

testdir="$(git rev-parse --show-toplevel)/test"

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[0;33m'
NC='\033[0m' # No Color

info() {
    echo -e "${YELLOW}${@}${NC}" >&2
}

assert_dir() {
    if [ ! -d "$testdir" ]; then
        echo "$testdir does not exist or is not a directory!"
        exit 1
    fi
}

get_inputs() {
    slang -q --ast-json - "$1" \
        | jq -r '.members[1].body.members[] | select(.kind == "Port" and .direction == "In") | .name' \
        | sort
}

get_outputs() {
    slang -q --ast-json - "$1" \
        | jq -r '.members[1].body.members[] | select(.kind == "Port" and .direction == "Out") | .name' \
        | sort
}

gen_verafile() {
    paste -d' ' <(get_inputs $1) <(get_inputs $2) | sed 's/^/IN /'
    echo
    paste -d' ' <(get_outputs $1) <(get_outputs $2) | sed 's/^/OUT /'
}

out="$testdir/out/"

setup() {
    rm -rf "$out"
    mkdir "$out"
}

veratest() {
    name="$1"
    verilog="$2"
    blif="$3"

    if [[ "$name" =~ $testfilter ]]; then
        printf "[ %-10s ]\n" "$name"
        mkdir -p "$out/$name"

        ret=0
        (
            cd $out/$name
            blif_as_verilog=$out/$name/$(basename $blif).v
            verafile=$out/$name/verafile
	    info "Slang-parse verilog"
            slang -q --ast-json ./$(basename $verilog).json $verilog
            timeout $YOSYS_TIMEOUT yosys --commands "read_blif $blif; write_verilog $blif_as_verilog" \
                > ./yosys_stdout \
                2> ./yosys_stderr
	    info "Slang-parse blif-as-verilog"
            slang -q --ast-json $blif_as_verilog.json $blif_as_verilog
	    info "gen-verafile"
            gen_verafile "$verilog" "$blif_as_verilog" > "$verafile"
	    info "vera compare"
            start=$(date +%s)
            timeout $VERA_TIMEOUT vera compare "$verafile" "$verilog" "$blif_as_verilog" \
                > ./vera_stdout \
                2> ./vera_stderr
            ret=$?
            end=$(date +%s)
            runtime_sec=$((end-start))
            echo "${runtime_sec}" > ./runtime
            exit $ret
        ) || ret=$?

        vera_out=$(cat $out/$name/vera_stdout)

        printf "(%ds) " $(cat $out/$name/runtime)
        case $ret in
            0) if [[ "$vera_out" =~ ^Equivalent ]]; then
                   printf "${GREEN}OK${NC}\n"
               else
                   printf "${RED}FAIL (not equivalent)${NC}\n"
               fi ;;
            124) printf "${RED}TIMEOUT (124)${NC}\n";;
            *) printf "${RED}FAIL ($ret)${NC}\n";;
        esac
    fi
}

epfl="$testdir/EPFL-benchmarks"

assert_dir "$epfl"

setup

veratest adder-depth       "$epfl/arithmetic/adder.v"         "$epfl/best_results/depth/adder_depth_2021.blif"
veratest bar-depth         "$epfl/arithmetic/bar.v"           "$epfl/best_results/depth/bar_depth_2015.blif"
veratest div-depth         "$epfl/arithmetic/div.v"           "$epfl/best_results/depth/div_depth_2021.blif"
veratest hyp-depth         "$epfl/arithmetic/hyp.v"           "$epfl/best_results/depth/hyp_depth_2021.blif"
veratest log2-depth        "$epfl/arithmetic/log2.v"          "$epfl/best_results/depth/log2_depth_2022.blif"
veratest max-depth         "$epfl/arithmetic/max.v"           "$epfl/best_results/depth/max_depth_2021.blif"
veratest multiplier-depth  "$epfl/arithmetic/multiplier.v"    "$epfl/best_results/depth/multiplier_depth_2022.blif"
veratest sin-depth         "$epfl/arithmetic/sin.v"           "$epfl/best_results/depth/sin_depth_2021.blif"
veratest sqrt-depth        "$epfl/arithmetic/sqrt.v"          "$epfl/best_results/depth/sqrt_depth_2021.blif"
veratest square-depth      "$epfl/arithmetic/square.v"        "$epfl/best_results/depth/square_depth_2022.blif"
veratest arbiter-depth     "$epfl/random_control/arbiter.v"   "$epfl/best_results/depth/arbiter_depth_2021.blif"
veratest cavlc-depth       "$epfl/random_control/cavlc.v"     "$epfl/best_results/depth/cavlc_depth_2018.blif"
veratest ctrl-depth        "$epfl/random_control/ctrl.v"      "$epfl/best_results/depth/ctrl_depth_2017.blif"
veratest dec-depth         "$epfl/random_control/dec.v"       "$epfl/best_results/depth/dec_depth_2018.blif"
veratest i2c-depth         "$epfl/random_control/i2c.v"       "$epfl/best_results/depth/i2c_depth_2022.blif"
veratest int2float-depth   "$epfl/random_control/int2float.v" "$epfl/best_results/depth/int2float_depth_2018.blif"
veratest mem_ctrl-depth    "$epfl/random_control/mem_ctrl.v"  "$epfl/best_results/depth/mem_ctrl_depth_2018.blif"
veratest priority-depth    "$epfl/random_control/priority.v"  "$epfl/best_results/depth/priority_depth_2022.blif"
veratest router-depth      "$epfl/random_control/router.v"    "$epfl/best_results/depth/router_depth_2021.blif"
veratest voter-depth       "$epfl/random_control/voter.v"     "$epfl/best_results/depth/voter_depth_2021.blif"

veratest adder-size       "$epfl/arithmetic/adder.v"         "$epfl/best_results/size/adder_size_2022.blif"
veratest bar-size         "$epfl/arithmetic/bar.v"           "$epfl/best_results/size/bar_size_2015.blif"
veratest div-size         "$epfl/arithmetic/div.v"           "$epfl/best_results/size/div_size_2021.blif"
veratest hyp-size         "$epfl/arithmetic/hyp.v"           "$epfl/best_results/size/hyp_size_2021.blif"
veratest log2-size        "$epfl/arithmetic/log2.v"          "$epfl/best_results/size/log2_size_2021.blif"
veratest max-size         "$epfl/arithmetic/max.v"           "$epfl/best_results/size/max_size_2018.blif"
veratest multiplier-size  "$epfl/arithmetic/multiplier.v"    "$epfl/best_results/size/multiplier_size_2022.blif"
veratest sin-size         "$epfl/arithmetic/sin.v"           "$epfl/best_results/size/sin_size_2021.blif"
veratest sqrt-size        "$epfl/arithmetic/sqrt.v"          "$epfl/best_results/size/sqrt_size_2021.blif"
veratest square-size      "$epfl/arithmetic/square.v"        "$epfl/best_results/size/square_size_2021.blif"

veratest arbiter-size     "$epfl/random_control/arbiter.v"   "$epfl/best_results/size/arbiter_size_2022.blif"
veratest cavlc-size       "$epfl/random_control/cavlc.v"     "$epfl/best_results/size/cavlc_size_2018.blif"
veratest ctrl-size        "$epfl/random_control/ctrl.v"      "$epfl/best_results/size/ctrl_size_2017.blif"
veratest dec-size         "$epfl/random_control/dec.v"       "$epfl/best_results/size/dec_size_2018.blif"
veratest i2c-size         "$epfl/random_control/i2c.v"       "$epfl/best_results/size/i2c_size_2018.blif"
veratest int2float-size   "$epfl/random_control/int2float.v" "$epfl/best_results/size/int2float_size_2020.blif"
veratest mem_ctrl-size    "$epfl/random_control/mem_ctrl.v"  "$epfl/best_results/size/mem_ctrl_size_2021.blif"
veratest priority-size    "$epfl/random_control/priority.v"  "$epfl/best_results/size/priority_size_2021.blif"
veratest router-size      "$epfl/random_control/router.v"    "$epfl/best_results/size/router_size_2018.blif"
veratest voter-size       "$epfl/random_control/voter.v"     "$epfl/best_results/size/voter_size_2022.blif"

for f in $epfl/random_control/*.v; do
    name=$(basename $f .v)
    veratest "$name" "$epfl/random_control/$name.v" "$epfl/random_control/$name.blif"
done

for f in $epfl/arithmetic/*.v; do
    name=$(basename $f .v)
    veratest "$name" "$epfl/arithmetic/$name.v" "$epfl/arithmetic/$name.blif"
done

