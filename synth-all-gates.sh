#!/bin/bash

# exit if any command fails
set -e
# split on newlines
IFS=$'\n'

NUM_INS=$1
NUM_OUTS=$2
shift 2

for GATE in $(./all_gates.py $NUM_INS $NUM_OUTS); do
    echo $GATE | ./linismt.py -G $@
done;
