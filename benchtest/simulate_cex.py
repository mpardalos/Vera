#!/usr/bin/env python3
"""Simulate a Verilog module on an SMT counterexample and report discrepancies.

Feeds the module's inputs with the values from the SMT model, simulates with
iverilog, and prints every variable whose simulated value differs from what the
model claims it should be.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

DEFINE_FUN = re.compile(
    r"""\(define-fun \s+
        (?: \| (?P<bname>[^|]*) \| | (?P<name>[^\s()|]+) ) \s+
        \(\) \s+
        (?P<sort>\(_ \s+ BitVec \s+ (?P<width>\d+)\) | [^\s()]+ ) \s+
        (?P<value>\#b[01]+ | \#x[0-9a-fA-F]+ | [^\s()]+ ) \s*
        \)""",
    re.VERBOSE,
)


def parse_value(s):
    """#b0101 -> ("4'b0101", 4); #xff -> ("8'hff", 8); true/false -> ("1'b1", 1)."""
    if s.startswith("#b"):
        bits = s[2:]
        return f"{len(bits)}'b{bits}", len(bits)
    if s.startswith("#x"):
        digits = s[2:]
        return f"{len(digits) * 4}'h{digits}", len(digits) * 4
    if s in ("true", "false"):
        return f"1'b{int(s == 'true')}", 1
    return s, None


def parse_model(text):
    """Return {name: (verilog_literal, width)} for every define-fun in the model."""
    model = {}
    for m in DEFINE_FUN.finditer(text):
        name = m.group("bname") if m.group("bname") is not None else m.group("name")
        value, width = parse_value(m.group("value"))
        if m.group("width"):
            width = int(m.group("width"))
        model[name] = (value, width)
    return model


def filter_prefix(model, prefix):
    """Keep only names starting with `prefix`, with the prefix stripped off."""
    return {
        name[len(prefix):]: v
        for name, v in model.items()
        if name.startswith(prefix)
    }


def expected_bits(literal, width):
    """Turn a Verilog literal back into a plain bit string of the given width."""
    _, _, digits = literal.partition("'")
    base, digits = digits[0], digits[1:]
    bits = bin(int(digits, 2 if base == "b" else 16))[2:]
    return bits.zfill(width)


# --- Verilog elaboration (via slang) --------------------------------------

RANGE = re.compile(r"\[\s*(\d+)\s*:\s*(\d+)\s*\]")


def escape(name):
    """Wrap a name in a Verilog escaped identifier if it isn't a plain one."""
    if re.fullmatch(r"[A-Za-z_$][\w$]*", name):
        return name
    return "\\" + name + " "


def type_width(type_str):
    """`logic[7:0]` -> 8, `logic` -> 1."""
    m = RANGE.search(type_str)
    if not m:
        return 1
    return abs(int(m.group(1)) - int(m.group(2))) + 1


def elaborate(verilog_path):
    """Run slang and return (module_name, {signal: (width, is_input)})."""
    out = subprocess.run(
        ["slang", "--quiet", "--ast-json", "-", verilog_path],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    design = json.loads(out)["design"]

    instances = [m for m in design.get("members", []) if m["kind"] == "Instance"]
    if not instances:
        raise SystemExit(f"slang found no top-level module in {verilog_path}")
    body = instances[0]["body"]

    inputs = {
        m["name"]
        for m in body.get("members", [])
        if m["kind"] == "Port" and m.get("direction") == "In"
    }
    signals = {
        m["name"]: (type_width(m.get("type", "logic")), m["name"] in inputs)
        for m in body.get("members", [])
        if m["kind"] in ("Net", "Variable")
    }
    return instances[0]["name"], signals


# --- Testbench generation -------------------------------------------------


def make_testbench(module, signals, model):
    """Build a testbench driving the inputs and printing every checked signal."""
    inputs = [n for n, (_w, is_input) in signals.items() if is_input]
    checked = [n for n in model if n in signals and not signals[n][1]]

    lines = ["`timescale 1ns/1ps", "module tb;"]
    for name in inputs:
        lines.append(f"  reg [{signals[name][0] - 1}:0] {escape(name)};")
    # Only the inputs need connecting; outputs are read hierarchically like
    # every other internal signal.
    ports = ", ".join(f".{escape(n)}({escape(n)})" for n in inputs)
    lines.append(f"  {module} dut({ports});")
    lines.append("  initial begin")
    for name in inputs:
        lines.append(f"    {escape(name)} = {model[name][0]};")
    lines.append("    #1;")
    for name in checked:
        lines.append(f'    $display("VAL {name} %b", dut.{escape(name)});')
    lines.append("    $finish;")
    lines.append("  end")
    lines.append("endmodule")
    return "\n".join(lines) + "\n", inputs, checked


def simulate(verilog_path, testbench):
    """Compile and run the testbench, returning {name: simulated bit string}."""
    with tempfile.TemporaryDirectory() as tmp:
        tb_path = os.path.join(tmp, "tb.v")
        exe_path = os.path.join(tmp, "sim")
        with open(tb_path, "w") as f:
            f.write(testbench)

        subprocess.run(
            ["iverilog", "-g2012", "-o", exe_path, tb_path, verilog_path],
            check=True,
        )
        out = subprocess.run(
            ["vvp", exe_path], check=True, capture_output=True, text=True
        ).stdout

    values = {}
    for line in out.splitlines():
        if line.startswith("VAL "):
            _, name, value = line.split(" ", 2)
            values[name] = value.strip()
    return values


def main():
    if len(sys.argv) != 4:
        print(
            f"usage: {sys.argv[0]} <verilog> <smt-model> <smt-prefix>",
            file=sys.stderr,
        )
        return 1

    verilog_path, model_path, prefix = sys.argv[1:]

    for tool in ("slang", "iverilog", "vvp"):
        if shutil.which(tool) is None:
            print(f"{tool} not found on PATH", file=sys.stderr)
            return 1

    with open(model_path) as f:
        model = filter_prefix(parse_model(f.read()), prefix)
    module, signals = elaborate(verilog_path)

    missing = [n for n, (_w, is_input) in signals.items() if is_input and n not in model]
    if missing:
        print(f"inputs missing from the model: {', '.join(missing)}", file=sys.stderr)
        return 1

    testbench, inputs, checked = make_testbench(module, signals, model)
    values = simulate(verilog_path, testbench)

    mismatches = 0
    for name in checked:
        literal, width = model[name]
        expected = expected_bits(literal, width)
        got = values.get(name, "<not printed>").zfill(width)
        if got != expected:
            mismatches += 1
            print(f"{name}: model says {expected}, simulation gives {got}")

    print(
        f"-- module {module}: {len(inputs)} inputs driven, "
        f"{len(checked)} signals checked, {mismatches} mismatches",
        file=sys.stderr,
    )
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
