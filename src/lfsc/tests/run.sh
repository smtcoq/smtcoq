#!/bin/bash
set -e
find work -name "*.smt2" -exec sh -c "./wrapper_cvc4tocoq.sh {} " \;
mv work/*.result work/results/
#exit 0
