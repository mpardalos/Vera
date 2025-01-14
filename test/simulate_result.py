#!/usr/bin/env python3

from pathlib import Path
from pprint import pprint
import json
import logging
import subprocess
import re
import sys
import argparse
import networkx as nx
import pygraphviz as pgv
import csv
from io import StringIO

def parse_args():
    parser = argparse.ArgumentParser(description='Process some arguments.')

    # Adding required string arguments
    parser.add_argument('--verilog', required=Path, type=str, help='Path to the verilog file')
    parser.add_argument('--verilog-module', required=True, type=str, help='Verilog module name')
    parser.add_argument('--model', required=True, type=Path, help='Path to the model file')
    parser.add_argument('--model-module', required=True, type=str, help='Model module name')

    # Parse the arguments
    return parser.parse_args()

logging.basicConfig(
    level=logging.DEBUG,
    format='[%(levelname)s : %(asctime)s] %(message)s'
)

def get_inputs(verilog_text):
    logging.info("Parsing verilog inputs using slang")
    verilog_inputs = set()
    pattern = r'^\s*input\s+\\?([^;]+)\s*;'
    for line in verilog_text.splitlines():
        if m := re.match(pattern, line):
            verilog_inputs.add(m.group(1).strip())
    return verilog_inputs

def parse_model(vera_output):
    logging.info("Parsing model (vera output)")
    model = dict()
    # Create regex pattern - matches module_name followed by ## then captures everything until =
    # and captures everything after = until end of line
    pattern = rf"^{smt_module_name}##([^=]+)\s*=\s*(.+)$"
    for line in model_file.read_text().splitlines():
        if m := re.match(pattern, line.strip()):
            # Part after ## before =
            key = m.group(1).strip()
            # Part after =. Remove the '#' to get a verilog value
            value = m.group(2).strip().replace('#', '')
            model[key] = value
    return model

def find_symbols(d: dict):
    symbols = []

    if isinstance(d, dict):  # Check if the value is a dictionary
        if 'symbol' in d:
            symbols.append(d['symbol'].split(' ')[1])
        for value in d.values():
            symbols.extend(find_symbols(value))  # Recur
    elif isinstance(d, list):  # Check if the value is a list
        for item in d:
            symbols.extend(find_symbols(item))

    return symbols

def verilog_to_graph(verilog_path):
    json_text = subprocess.run(
        ['slang', '-q', '--ast-json', '-', verilog_path],
        stdout=subprocess.PIPE,
        text=True
    ).stdout

    verilog_json = json.loads(json_text)

    instance = next(m for m in verilog_json['members'] if m['kind'] == 'Instance')
    members = instance['body']['members']
    continuous_assignments = (m['assignment'] for m in members if m['kind'] == 'ContinuousAssign')

    G = nx.DiGraph()
    for assignment in continuous_assignments:
        lhs_name = assignment['left']['symbol'].split(' ')[1]
        rhs_symbols = find_symbols(assignment['right'])
        # edges.extend((lhs_name, rhs_symbol)
        for rhs_symbol in rhs_symbols:
            G.add_edge(rhs_symbol, lhs_name)

    return G

def mk_testbench(verilog_file, verilog_module_name, verilog_inputs, model):
    logging.info(f"Creating testbench file for {verilog_file.absolute()}")
    input_values = { n: model[n] for n in verilog_inputs }
    read_signals = { n: model[n] for n in model if n not in verilog_inputs }

    tb = ""

    tb += f"`include \"{verilog_file.absolute()}\"\n"
    tb += f'module {verilog_module_name}_tb;\n'
    tb += f'  {verilog_module_name} dut (\n'
    tb += ',\n'.join(
        f'    .\\{name} ({value})'
        for name, value in input_values.items()
    )
    tb += f'\n'
    tb += f'  ); // dut\n'

    tb += f'  initial #2 begin\n'
    for name, value in read_signals.items():
        tb += f'    if (dut.\\{name} !== {value}) $display( "FAIL,{name},{value},%d ", dut.\\{name} );\n'
    tb += f'  end\n'
    tb += f'endmodule // {verilog_module_name}_tb\n'

    testbench_file = verilog_file.with_suffix(".tb.v")
    testbench_file.write_text(tb)
    logging.info(f"Wrote testbench to {testbench_file.absolute()}")
    return testbench_file

def run_verilog(verilog_path):
    logging.info(f"Running {verilog_path} with iverilog")
    vvp_path = verilog_path.with_suffix('.vvp')
    subprocess.run(['iverilog', verilog_path, '-o', vvp_path ])
    return subprocess.run(['vvp', vvp_path], stdout=subprocess.PIPE, text=True).stdout

args = parse_args()
verilog_module_name = args.verilog_module
smt_module_name = args.model_module
verilog_file = Path(args.verilog)
model_file = Path(args.model)

model = parse_model(model_file.read_text())
inputs = get_inputs(verilog_file.read_text())

verilog_graph = verilog_to_graph(verilog_file)

for nodename in verilog_graph.nodes:
    verilog_graph.nodes[nodename]['correct'] = True

testbench_file = mk_testbench(verilog_file, verilog_module_name, inputs, model)
testbench_out = run_verilog(testbench_file)
for (_,name,expected,got) in csv.reader(StringIO(testbench_out)):
    verilog_graph.nodes[name]['correct'] = False

for node in verilog_graph.nodes:
    if not verilog_graph.nodes[node]['correct']:
        if all(verilog_graph.nodes[prev]['correct'] for (prev, _) in verilog_graph.in_edges(node)):
            print(f'{node} ({[prev for (prev, _) in verilog_graph.in_edges(node)]})')

