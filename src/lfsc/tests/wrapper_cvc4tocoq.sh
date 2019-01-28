#!/bin/bash
set -e
OUTPUT_FOLDER=/home/burak/Desktop/smtcoq/src/lfsc/tests/results/
CVC4TOCOQ_HOME=/home/burak/Desktop/smtcoq/src/lfsc/tests/

${CVC4TOCOQ_HOME}/cvc4tocoq $1 &> $1.result
#exit 0
# exit'e gerek var mi emin degilim abi
#${CVC4TOCOQ_HOME}/cvc4tocoq $1 &> ${OUTPUT_FOLDER}$1.result
