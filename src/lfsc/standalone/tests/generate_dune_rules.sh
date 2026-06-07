#!/usr/bin/env bash

set -e

TARGET=$1

shift 1
DEPS=$@

echo "From Stdlib Require Import Bool List."
echo "From SMTCoq Require Import BVList FArray Tactics."

for SMTFILE in $DEPS
do
    [[ "${SMTFILE}" == "array_bv3.smt2" ]] && continue
    [[ "${SMTFILE}" == "array_ext.smt2" ]] && continue
    [[ "${SMTFILE}" == "array_ext2.smt2" ]] && continue
    [[ "${SMTFILE}" == "array_incompleteness1.smt2" ]] && continue
    [[ "${SMTFILE}" == "bv_mult10.smt2" ]] && continue
    [[ "${SMTFILE}" == "bvneg0_32.smt2" ]] && continue
    [[ "${SMTFILE}" == "bvult.smt2" ]] && continue
    [[ "${SMTFILE}" == "dead_dnd001.smt2" ]] && continue
    [[ "${SMTFILE}" == "dead_dnd001_and.smt2" ]] && continue
    [[ "${SMTFILE}" == "eq_diamond37.smt2" ]] && continue
    [[ "${SMTFILE}" == "lia1.smt2" ]] && continue
    [[ "${SMTFILE}" == "simple.smt2" ]] && continue
    [[ "${SMTFILE}" == "swap1.smt2" ]] && continue
    [[ "${SMTFILE}" == "swap3.smt2" ]] && continue
    [[ "${SMTFILE}" == "trans.smt2" ]] && continue
    [[ "${SMTFILE}" == "uf5.smt2" ]] && continue

    LFSCFILE="${SMTFILE%.smt2}.lfsc"

    cvc4 --proof --dump-proof --fewer-preprocessing-holes \
         --no-bv-eq --no-bv-ineq --no-bv-algebraic \
         --allow-empty-dependencies "${SMTFILE}" > "${LFSCFILE}"

    echo "Section File."
    echo "  Lfsc_Checker \"src/lfsc/standalone/tests/${SMTFILE}\" \"src/lfsc/standalone/tests/${LFSCFILE}\"."
    echo "End File."

done
