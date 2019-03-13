#!/bin/sh

pre=$(echo $0 | sed "s,\(\([^/]*/\)*\)[^/]*,\1,")

rm -f ${pre}_CoqProject
rm -f ${pre}Makefile
rm -f ${pre}Makefile.conf
rm -f ${pre}smtcoq_plugin.ml4
rm -f ${pre}versions/native/Structures.v
rm -f ${pre}g_smtcoq.ml4
rm -f ${pre}smtcoq_plugin.mlpack
rm -f ${pre}versions/standard/Int63/Int63.v
rm -f ${pre}versions/standard/Int63/Int63Native.v
rm -f ${pre}versions/standard/Int63/Int63Op.v
rm -f ${pre}versions/standard/Int63/Int63Axioms.v
rm -f ${pre}versions/standard/Int63/Int63Properties.v
rm -f ${pre}versions/standard/Array/PArray.v
rm -f ${pre}versions/standard/Structures.v

set -e
if [ $@ -a $@ = -native ]; then
    cp ${pre}versions/native/Makefile ${pre}Makefile
    cp ${pre}versions/native/smtcoq_plugin_native.ml4 ${pre}smtcoq_plugin.ml4
    cp ${pre}versions/native/Structures_native.v ${pre}versions/native/Structures.v
else
    cp ${pre}versions/standard/_CoqProject ${pre}_CoqProject
    cp ${pre}versions/standard/g_smtcoq_standard.ml4 ${pre}g_smtcoq.ml4
    cp ${pre}versions/standard/smtcoq_plugin_standard.mlpack ${pre}smtcoq_plugin.mlpack
    cp ${pre}versions/standard/Int63/Int63_standard.v ${pre}versions/standard/Int63/Int63.v
    cp ${pre}versions/standard/Int63/Int63Native_standard.v ${pre}versions/standard/Int63/Int63Native.v
    cp ${pre}versions/standard/Int63/Int63Op_standard.v ${pre}versions/standard/Int63/Int63Op.v
    cp ${pre}versions/standard/Int63/Int63Axioms_standard.v ${pre}versions/standard/Int63/Int63Axioms.v
    cp ${pre}versions/standard/Int63/Int63Properties_standard.v ${pre}versions/standard/Int63/Int63Properties.v
    cp ${pre}versions/standard/Array/PArray_standard.v ${pre}versions/standard/Array/PArray.v
    cp ${pre}versions/standard/Structures_standard.v ${pre}versions/standard/Structures.v
    coq_makefile -f _CoqProject -o CoqMakefile
    sed -i CoqMakefile -e "s/ocamldep/ocamldep -native/" -e "s/	\$(HIDE)\$(MAKE) --no-print-directory -f \"\$(SELF)\" post-all//"
fi
