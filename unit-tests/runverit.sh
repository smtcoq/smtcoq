#!/usr/bin/env bash

count=1
i=$1
file=$(echo "$i" | sed "s/.smt2/.vtlog/")

veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=$file $i
