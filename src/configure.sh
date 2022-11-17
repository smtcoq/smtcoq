#!/bin/bash

coq_makefile -f _CoqProject -o Makefile
if [[ $OSTYPE == 'darwin'* ]]
then
    sed -i '' 's/^CAMLDONTLINK=unix,str$/CAMLDONTLINK=num,str,unix,dynlink,threads/' Makefile
else
    sed -i 's/^CAMLDONTLINK=unix,str$/CAMLDONTLINK=num,str,unix,dynlink,threads/' Makefile
fi
