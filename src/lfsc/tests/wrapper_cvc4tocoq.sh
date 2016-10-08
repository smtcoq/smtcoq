#!/bin/bash
set -e
OUTPUT_FOLDER= ... /smtcoq/src/lfsc/tests/results/ #make sure to complete the path
CVC4TOCOQ_HOME=... /smtcoq/src/lfsc/tests/ #make sure to complete the path

${CVC4TOCOQ_HOME}/cvc4tocoq $1 &> $1.result

