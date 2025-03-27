#!/bin/env python3
import os
import re
import shutil
import subprocess
import time
import traceback
import shutil
import json
import sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock

DEBUG = '-v' in sys.argv
VERA_TIMEOUT = 300  # 5m
YOSYS_TIMEOUT = 60  # 1m
MAX_CONCURRENT_TESTS = 16  # Configurable concurrency limit
testdir = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()) / "test"
out = testdir / "out"
testfilter = re.compile(".*")  # Match all tests by default
running_tests = set()
running_tests_lock = Lock()

def output(test_name, msg):
    with running_tests_lock:
        running_tests_str = " , ".join('{:>10}'.format(t) for t in running_tests)
    # print(f"[ {running_tests_str:>align_length} ] [{test_name}] {msg}")
    print(f"[ {running_tests_str} ] [{test_name}] {msg}")

def msg(test_name, msg):
    output(test_name, f"\033[0;32m{msg}\033[0m")

def error(test_name, msg):
    output(test_name, f"\033[0;31m{msg}\033[0m")

def info(test_name, msg):
    output(test_name, f"\033[0;33m{msg}\033[0m")

def debug(test_name, msg):
    if not DEBUG:
        return
    info(test_name, msg)

def assert_dir():
    if not testdir.is_dir():
        print(f"{testdir} does not exist or is not a directory!")
        exit(1)

def setup():
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)

def run_command(test_name, cmd, timeout, cwd):
    debug(test_name, cmd)
    return subprocess.run(
        cmd,
        shell=True, cwd=cwd, text=True, timeout=timeout,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )

def get_ports(verilog_file, direction):
    """Extract input or output ports from a Verilog file using slang."""
    result = subprocess.run(["slang", "-q", "--ast-json", "-", verilog_file],
                            capture_output=True, text=True, check=True)
    ast = json.loads(result.stdout)
    return [
        member["name"]
        for member in ast["members"][1]["body"]["members"]
        if member["kind"] == "Port" and member["direction"] == direction
    ]

def replace_ports(test_name, verilog, blif):
    """Replace input/output names in the BLIF file to match the Verilog file."""
    debug(test_name, f"replace_ports({verilog}, {blif})")
    blif_path = Path(blif)
    mapping_file = blif_path.parent / f"{blif_path.name}_mapping.csv"

    inputs_verilog = get_ports(verilog, "In")
    inputs_blif = get_ports(blif, "In")
    outputs_verilog = get_ports(verilog, "Out")
    outputs_blif = get_ports(blif, "Out")

    mapping_entries = []
    blif_text = blif_path.read_text()

    for in_verilog, in_blif in zip(inputs_verilog, inputs_blif):
        blif_text = re.sub(rf'\b{re.escape(in_blif)}\b', f'\\\\{in_verilog} ', blif_text)
        mapping_entries.append(f"{in_blif},{in_verilog}\n")

    for out_verilog, out_blif in zip(outputs_verilog, outputs_blif):
        blif_text = re.sub(rf'\b{re.escape(out_blif)}\b', f'\\\\{out_verilog} ', blif_text)
        mapping_entries.append(f"{out_blif},{out_verilog}\n")

    blif_path.write_text(blif_text)
    mapping_file.write_text("".join(mapping_entries))

def veratest(testname, verilog, blif, rename_interface=True):
    name = f'vera-{testname}'
    if not testfilter.search(name):
        return

    with running_tests_lock:
        running_tests.add(name)

    try:
        info(name, "Begin")
        test_out = out / name
        test_out.mkdir(parents=True, exist_ok=True)

        shutil.copy(verilog, test_out / verilog.name)

        run_command(name, f"slang -q --ast-json {test_out}/{Path(verilog).name}.json {verilog}", None, test_out)

        blif_as_verilog = test_out / f"{Path(blif).name}.v"
        ret = run_command(name, f"yosys --commands 'read_blif {blif}; write_verilog {blif_as_verilog}'", YOSYS_TIMEOUT, test_out).returncode
        if ret != 0:
            error(name, f"FAIL (yosys error {ret})")
            return (name, 0, f'FAIL (yosys error {ret})')
        if rename_interface:
            replace_ports(name, verilog, blif_as_verilog)

        run_command(name, f"slang -q --ast-json {blif_as_verilog}.json {blif_as_verilog}", None, test_out)

        start_time = time.time()
        timed_out = False
        try:
            result = run_command(name, f"vera compare {verilog} {blif_as_verilog}", VERA_TIMEOUT, test_out)
            (test_out / 'vera_stdout').write_text(result.stdout)
            (test_out / 'vera_stderr').write_text(result.stderr)
            runtime_sec = int(time.time() - start_time)
            if 'Equivalent (UNSAT)' in result.stdout:
                msg(name, f"OK ({runtime_sec}s) (ret {result.returncode})")
                return (name, runtime_sec, 'OK')
            elif 'Non-equivalent (SAT)' in result.stdout:
                message = f"FAIL (not equivalent)"
                error(name, message)
                return (name, runtime_sec, message)
            else:
                output = result.stdout.splitlines()
                if len(output) >= 1:
                    message = f"FAIL ('{output}')"
                else:
                    message = "FAIL"
                error(name, message)
                return (name, runtime_sec, message)
        except subprocess.TimeoutExpired:
            error(name, "TIMEOUT")
            return (name, VERA_TIMEOUT, "TIMEOUT")
        except subprocess.CalledProcessError as e:
            message = f"FAIL ({e.returncode})"
            error(name, message)
            return (name, 0, message)
    finally:
        with running_tests_lock:
            running_tests.remove(name)

def eqytest(testname, verilog, blif, rename_interface=True):
    name = f'eqy-{testname}'
    if not testfilter.search(name):
        return

    with running_tests_lock:
        running_tests.add(name)

    try:
        info(name, "Begin")
        test_out = out / name
        test_out.mkdir(parents=True, exist_ok=True)

        shutil.copy(verilog, test_out / verilog.name)

        run_command(name, f"slang -q --ast-json {test_out}/{Path(verilog).name}.json {verilog}", None, test_out)

        blif_as_verilog = test_out / f"{Path(blif).name}.v"
        ret = run_command(name, f"yosys --commands 'read_blif {blif}; write_verilog {blif_as_verilog}'", YOSYS_TIMEOUT, test_out).returncode
        if ret != 0:
            error(name, f"FAIL (yosys error {ret})")
            return (name, 0, f'FAIL (yosys error {ret})')
        if rename_interface:
            replace_ports(name, verilog, blif_as_verilog)

        start_time = time.time()
        timed_out = False
        try:
            (test_out / 'compare.eqy').write_text(f"""
[gold]
read_verilog {verilog}
prep -auto-top
rename -top top

[gate]
read_verilog {blif_as_verilog}
prep -auto-top
rename -top top

[strategy sby]
use sby
engine smtbmc z3
""")
            result = run_command(name, "eqy -f compare.eqy", VERA_TIMEOUT, test_out)
            (test_out / 'eqy_stdout').write_text(result.stdout)
            (test_out / 'eqy_stderr').write_text(result.stderr)
            runtime_sec = int(time.time() - start_time)
            if 'Successfully proved designs equivalent' in result.stdout:
                msg(name, f"OK ({runtime_sec}s) (ret {result.returncode})")
                return (name, runtime_sec, 'OK')
            else:
                output = result.stdout.splitlines()
                if len(output) >= 1:
                    message = f"FAIL ('{output}')"
                else:
                    message = "FAIL"
                error(name, message)
                return (name, runtime_sec, message)
        except subprocess.TimeoutExpired:
            error(name, "TIMEOUT")
            return (name, VERA_TIMEOUT, "TIMEOUT")
        except subprocess.CalledProcessError as e:
            message = f"FAIL ({e.returncode})"
            error(name, message)
            return (name, 0, message)
    finally:
        with running_tests_lock:
            running_tests.remove(name)

assert_dir()
setup()

epfl = testdir / "EPFL-benchmarks"

test_cases = []
for category in ["random_control", "arithmetic"]:
    for verilog_file in (epfl / category).glob("*.v"):
        name = verilog_file.stem
        test_cases.append((name, verilog_file, epfl / category / f"{name}.blif", False))

depth = epfl / "best_results" / "depth"
size = epfl / "best_results" / "size"
arithmetic = epfl / "arithmetic"
random_control = epfl / "random_control"

test_cases += [
    ("adder-depth",       arithmetic/"adder.v",         depth/"adder_depth_2021.blif"),
    ("bar-depth",         arithmetic/"bar.v",           depth/"bar_depth_2015.blif"),
    ("div-depth",         arithmetic/"div.v",           depth/"div_depth_2021.blif"),
    ("hyp-depth",         arithmetic/"hyp.v",           depth/"hyp_depth_2021.blif"),
    ("log2-depth",        arithmetic/"log2.v",          depth/"log2_depth_2022.blif"),
    ("max-depth",         arithmetic/"max.v",           depth/"max_depth_2021.blif"),
    ("multiplier-depth",  arithmetic/"multiplier.v",    depth/"multiplier_depth_2022.blif"),
    ("sin-depth",         arithmetic/"sin.v",           depth/"sin_depth_2021.blif"),
    ("sqrt-depth",        arithmetic/"sqrt.v",          depth/"sqrt_depth_2021.blif"),
    ("square-depth",      arithmetic/"square.v",        depth/"square_depth_2022.blif"),
    ("arbiter-depth",     random_control/"arbiter.v",   depth/"arbiter_depth_2021.blif"),
    ("cavlc-depth",       random_control/"cavlc.v",     depth/"cavlc_depth_2018.blif"),
    ("ctrl-depth",        random_control/"ctrl.v",      depth/"ctrl_depth_2017.blif"),
    ("dec-depth",         random_control/"dec.v",       depth/"dec_depth_2018.blif"),
    ("i2c-depth",         random_control/"i2c.v",       depth/"i2c_depth_2022.blif"),
    ("int2float-depth",   random_control/"int2float.v", depth/"int2float_depth_2018.blif"),
    ("mem_ctrl-depth",    random_control/"mem_ctrl.v",  depth/"mem_ctrl_depth_2018.blif"),
    ("priority-depth",    random_control/"priority.v",  depth/"priority_depth_2022.blif"),
    ("router-depth",      random_control/"router.v",    depth/"router_depth_2021.blif"),
    ("voter-depth",       random_control/"voter.v",     depth/"voter_depth_2021.blif"),

    ("adder-size",       arithmetic/"adder.v",         size/"adder_size_2022.blif"),
    ("bar-size",         arithmetic/"bar.v",           size/"bar_size_2015.blif"),
    ("div-size",         arithmetic/"div.v",           size/"div_size_2021.blif"),
    ("hyp-size",         arithmetic/"hyp.v",           size/"hyp_size_2021.blif"),
    ("log2-size",        arithmetic/"log2.v",          size/"log2_size_2021.blif"),
    ("max-size",         arithmetic/"max.v",           size/"max_size_2018.blif"),
    ("multiplier-size",  arithmetic/"multiplier.v",    size/"multiplier_size_2022.blif"),
    ("sin-size",         arithmetic/"sin.v",           size/"sin_size_2021.blif"),
    ("sqrt-size",        arithmetic/"sqrt.v",          size/"sqrt_size_2021.blif"),
    ("square-size",      arithmetic/"square.v",        size/"square_size_2021.blif"),

    ("arbiter-size",     random_control/"arbiter.v",   size/"arbiter_size_2022.blif"),
    ("cavlc-size",       random_control/"cavlc.v",     size/"cavlc_size_2018.blif"),
    ("ctrl-size",        random_control/"ctrl.v",      size/"ctrl_size_2017.blif"),
    ("dec-size",         random_control/"dec.v",       size/"dec_size_2018.blif"),
    ("i2c-size",         random_control/"i2c.v",       size/"i2c_size_2018.blif"),
    ("int2float-size",   random_control/"int2float.v", size/"int2float_size_2020.blif"),
    ("mem_ctrl-size",    random_control/"mem_ctrl.v",  size/"mem_ctrl_size_2021.blif"),
    ("priority-size",    random_control/"priority.v",  size/"priority_size_2021.blif"),
    ("router-size",      random_control/"router.v",    size/"router_size_2018.blif"),
    ("voter-size",       random_control/"voter.v",     size/"voter_size_2022.blif"),
]

results = []
# Vera
with ThreadPoolExecutor(max_workers=MAX_CONCURRENT_TESTS) as executor:
    futures = {executor.submit(veratest, *args): args[0] for args in test_cases}
    for future in as_completed(futures):
        if exc := future.exception():
            traceback.print_exception(exc)
        elif result := future.result():
            results.append(result)
 
# EQY
with ThreadPoolExecutor(max_workers=MAX_CONCURRENT_TESTS) as executor:
    futures = {executor.submit(eqytest, *args): args[0] for args in test_cases}
    for future in as_completed(futures):
        if exc := future.exception():
            traceback.print_exception(exc)
        elif result := future.result():
            results.append(result)

for name, runtime_sec, message in results:
    print(f'{name},{runtime_sec},{message}')
