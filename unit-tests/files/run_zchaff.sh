#!/usr/bin/env bash

INPUT=$2
OUTPUT=$3

(
  flock -x 100 || exit 1

  zchaff "${INPUT}"
  mv resolve_trace "${OUTPUT}"
) 100>.smtcoq_zchaff_lock
