#!/bin/sh

coq_makefile -f _CoqProject -o Makefile
sed -i 's/^CAMLDONTLINK=unix,str$/CAMLDONTLINK=num,str,unix,dynlink,threads/' Makefile
