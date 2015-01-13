#!/bin/sh

set -e

if [ $@ -a $@ = -standard ]; then
    cp Makefile.standard Makefile
else
    cp Makefile.native Makefile
fi
