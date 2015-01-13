#!/bin/sh

set -e

if [ $@ -a $@ = -standard ]; then
    cp versions/standard/Makefile Makefile
else
    cp versions/native/Makefile Makefile
fi
