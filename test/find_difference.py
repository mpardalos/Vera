#!/bin/env python3

from pprint import pprint
import sys

def parse_smt_file(filename):
    result = {}
    current_name = None

    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if 'define-fun' in line:
                name = line.split()[1].strip('|')
                current_name = name
            elif '#b' in line and current_name:
                value = line.strip().strip(')')
                result[current_name] = value
                current_name = None

    return result


def find_differences(mapping):
    # Group by base name (removing left/right prefix and pipes)
    pairs = {}
    for name, value in mapping.items():
        # Remove pipes and left/right prefix
        clean_name = name.strip('|')
        if clean_name.startswith('left__'):
            base_name = clean_name[6:]
            pairs.setdefault(base_name, {})['left'] = value
        elif clean_name.startswith('right__'):
            base_name = clean_name[7:]
            pairs.setdefault(base_name, {})['right'] = value

    # Find differences
    differences = {}
    for base_name, values in pairs.items():
        if 'left' in values and 'right' in values:  # only compare when both exist
            if values['left'] != values['right']:
                differences[base_name] = values

    return differences

mapping = parse_smt_file(sys.argv[1])
diffs = find_differences(mapping)
pprint(diffs)
# for name, values in diffs.items():
#     print(f"{name}: left={values['left']}, right={values['right']}")
