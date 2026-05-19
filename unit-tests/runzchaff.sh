#!/usr/bin/env bash

count=1
i=$1
file=$(echo "$i" | sed "s/.cnf/.zlog/")

zchaff $i
mv resolve_trace $file
