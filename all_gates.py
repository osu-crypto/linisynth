#!/usr/bin/env python2

from linismt import all_gates, print_truth_table

import argparse

def get_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('num_inputs',  nargs='?', type=int, default=2, help='number of inputs')
    parser.add_argument('num_outputs', nargs='?', type=int, default=1, help='number of outputs')
    args = parser.parse_args()
    return args

if __name__ == "__main__":
    args = get_args()
    for gate in all_gates(args.num_inputs, args.num_outputs):
        print_truth_table(gate, args.num_inputs, args.num_outputs)
