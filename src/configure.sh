#!/bin/sh

set -e

if [ $@ -a $@ = -native ]; then
    cp versions/native/Makefile Makefile
    cp versions/native/smtcoq_plugin_native.ml4 smtcoq_plugin.ml4
else
    cp versions/standard/Makefile Makefile
    cp versions/standard/smtcoq_plugin_standard.ml4 smtcoq_plugin.ml4
    cp versions/standard/Int63/Int63_standard.v versions/standard/Int63/Int63.v
    cp versions/standard/Int63/Int63Lib_standard.v versions/standard/Int63/Int63Lib.v
    cp versions/standard/Int63/Cyclic63_standard.v versions/standard/Int63/Cyclic63.v
    cp versions/standard/Int63/Ring63_standard.v versions/standard/Int63/Ring63.v
    cp versions/standard/Int63/Int63Native_standard.v versions/standard/Int63/Int63Native.v
    cp versions/standard/Int63/Int63Op_standard.v versions/standard/Int63/Int63Op.v
    cp versions/standard/Int63/Int63Axioms_standard.v versions/standard/Int63/Int63Axioms.v
    cp versions/standard/Int63/Int63Properties_standard.v versions/standard/Int63/Int63Properties.v
    cp versions/standard/Array/PArray_standard.v versions/standard/Array/PArray.v
fi
