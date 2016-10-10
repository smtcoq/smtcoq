#!/bin/bash
set -e
find work -name "*.smt2" -exec sh -c "./wrapper_cvc4tocoq.sh {} " \;
mv work/*.result work/results/
mv work/*.lfsc work/lfsc/
mv work/*.smt2 work/smt2/
rm work/*.v
rm work/*.glob
rm work/*.vo
#exit 0
