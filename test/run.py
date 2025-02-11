#!/bin/env python3
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock

DEBUG = True
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
    return subprocess.run(
        cmd,
        shell=True, cwd=cwd, text=True, timeout=timeout,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).returncode

def veratest(name, verilog, blif):
    if not testfilter.match(name):
        return

    with running_tests_lock:
        running_tests.add(name)

    try:
        info(name, "Begin")
        test_out = out / name
        test_out.mkdir(parents=True, exist_ok=True)

        blif_as_verilog = test_out / f"{Path(blif).stem}.v"
        debug(name, "Slang-parse verilog")
        run_command(name, f"slang -q --ast-json {test_out}/{Path(verilog).name}.json {verilog}", None, test_out)

        debug(name, "Yosys processing")
        ret = run_command(name, f"yosys --commands 'read_blif {blif}; write_verilog {blif_as_verilog}'", YOSYS_TIMEOUT, test_out)
        if ret != 0:
            error(name, "FAIL (yosys error)")
            return

        debug(name, "Slang-parse blif-as-verilog")
        run_command(name, f"slang -q --ast-json {blif_as_verilog}.json {blif_as_verilog}", None, test_out)

        start_time = time.time()
        debug(name, "Vera compare")
        timed_out = False
        try:
            run_command(name, f"vera compare {verilog} {blif_as_verilog}", VERA_TIMEOUT, test_out)
            runtime_sec = int(time.time() - start_time)
            msg(name, f"OK ({runtime_sec}s)")
        except subprocess.TimeoutExpired:
            error(name, "TIMEOUT")
        except subprocess.CalledProcessError as e:
            error(name, f"FAIL ({e.returncode})")
        except e:
            print(e)
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
        test_cases.append((name, verilog_file, epfl / category / f"{name}.blif"))

best_results = epfl / "best_results"
for metric in ["depth", "size"]:
    for category in ["arithmetic", "random_control"]:
        for verilog_file in (epfl / category).glob("*.v"):
            name = verilog_file.stem
            blif_file = best_results / metric / f"{name}_{metric}_2022.blif"
            if blif_file.exists():
                test_cases.append((f"{name}-{metric}", verilog_file, blif_file))
            else:
                print(f"Skipping {name}-{metric}")

with ThreadPoolExecutor(max_workers=MAX_CONCURRENT_TESTS) as executor:
    futures = {executor.submit(veratest, *args): args[0] for args in test_cases}
    for future in as_completed(futures):
        if exc := future.exception():
            print("==> ERROR <==")
