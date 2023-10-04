# Detailed use of SMTCoq

<!--- Extraction is probably broken
SMTCoq also provides an extracted version of the checker, that can be
run outside Coq.
--->

<!--- The current stable version is version 1.3. --->

Examples are given in the file examples/Example.v. They are meant to be
easily re-usable for your own usage.


## Overview

After installation, the SMTCoq module can be used in Coq files via the
`Require Import SMTCoq.SMTCoq.` command. For each supported solver, it
provides:

- a vernacular command to check answers: `XXX_Checker "problem_file"
  "witness_file"` returns `true` only if `witness_file` contains a proof
  of the unsatisfiability of the problem stated in `problem_file`;

- a vernacular command to safely import theorems:
  `XXX_Theorem theo "problem_file" "witness_file"` produces a Coq term
  `theo` whose type is the theorem stated in `problem_file` if
  `witness_file` is a proof of the unsatisfiability of it, and fails
  otherwise.

- safe tactics to try to solve a Coq goal using the chosen solver (or a
  combination of solvers).

<!--- Extraction is probably broken
The SMTCoq checker can also be extracted to OCaml and then used
independently from Coq.
--->

With cvc5, SMTCoq provides the ability to ask the solver for facts that 
would entail otherwise failing goals. It does this via cvc5's capability 
for abductive reasoning.

We now give more details for each solver.

<!--- Extraction is probably broken
We now give more details for each solver, and explanations on
extraction.
--->


## zChaff

Compile and install zChaff as explained in the installation
instructions. In the following, we consider that the command `zchaff` is
in your `PATH` environment variable.


### Checking zChaff answers of unsatisfiability and importing theorems

To check the result given by zChaff on an unsatisfiable dimacs file
`file.cnf`:

- Produce a zChaff proof witness: `zchaff file.cnf`. This command
  produces a proof witness file named `resolve_trace`.

- In a Coq file `file.v`, put:
```coq
Require Import SMTCoq.SMTCoq.
Zchaff_Checker "file.cnf" "resolve_trace".
```

- Compile `file.v`: `coqc file.v`. If it returns `true` then zChaff
  indeed proved that the problem was unsatisfiable.

- You can also produce Coq theorems from zChaff proof witnesses: the
  commands
```coq
Require Import SMTCoq.SMTCoq.
Zchaff_Theorem theo "file.cnf" "resolve_trace".
```
will produce a Coq term `theo` whose type is the theorem stated in
`file.cnf`.


### zChaff as a Coq decision procedure

The `zchaff` tactic can be used to solve any goal of the form:
```coq
forall l, b1 = b2
```
where `l` is a quantifier-free list of terms and `b1` and `b2` are
expressions of type `bool`.

A more efficient version of this tactic, called `zchaff_no_check`,
performs only the check at `Qed`. (Thus it is safe, but a proof may fail
at `Qed` even if everything went through during proof elaboration.)


## veriT

Compile and install veriT as explained in the installation instructions.
In the following, we consider that the command `veriT` is in your `PATH`
environment variable.


### Checking veriT answers of unsatisfiability and importing theorems

To check the result given by veriT on an unsatisfiable SMT-LIB2 file
`file.smt2`:

- Produce a veriT proof witness:
```coq
veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-e --disable-ackermann --input=smtlib2 --proof=file.log file.smt2
```
This command produces a proof witness file named `file.log`.

- In a Coq file `file.v`, put:
```coq
Require Import SMTCoq.SMTCoq.
Section File.
  Verit_Checker "file.smt2" "file.log".
End File.
```

- Compile `file.v`: `coqc file.v`. If it returns `true` then veriT
  indeed proved that the problem was unsatisfiable.

- You can also produce Coq theorems from veriT proof witnesses: the
  commands
```coq
Require Import SMTCoq.SMTCoq.
Section File.
  Verit_Theorem theo "file.smt2" "file.log".
End File.
```
will produce a Coq term `theo` whose type is the theorem stated in
`file.smt2`.

The theories that are currently supported by these commands are `QF_UF`
(theory of equality), `QF_LIA` (linear integer arithmetic), `QF_IDL`
(integer difference logic), and their combinations.


### veriT as a Coq decision procedure

The `verit_bool [h1 ...]` tactic can be used to solve any goal of the form:
```coq
forall l, b1 = b2
```
where `l` is a quantifier-free list of terms and `b1` and `b2` are
expressions of type `bool`. This tactic **supports quantifiers**: it takes
optional arguments which are names of universally quantified
lemmas/hypotheses that can be used to solve the goal. These lemmas can
also be given once and for all using the `Add_lemmas` command (see
[examples/Example.v](https://github.com/smtcoq/smtcoq/blob/master/examples/Example.v)
for details).

In addition, the `verit` tactic applies to Coq goals of sort `Prop`: it
first converts the goal into a term of type `bool` (thanks to the
`reflect` predicate of `SSReflect`), and then calls the previous tactic
`verit_bool`.

The theories that are currently supported by these tactics are `QF_UF`
(theory of equality), `QF_LIA` (linear integer arithmetic), `QF_IDL`
(integer difference logic), and their combinations.

A more efficient version of this tactic, called `verit_no_check`,
performs only the check at `Qed`. (Thus it is safe, but a proof may fail
at `Qed` even if everything went through during proof elaboration.)


## CVC4

Compile and install `CVC4` as explained in the installation
instructions. In the following, we consider that the command `cvc4` is
in your `PATH` environment variable.


### Checking CVC4 answers of unsatisfiability and importing theorems

To check the result given by CVC4 on an unsatisfiable SMT-LIB2 file
`name.smt2`:

- Produce a CVC4 proof witness:

```bash
cvc4 --dump-proof --no-simplification --fewer-preprocessing-holes --no-bv-eq --no-bv-ineq --no-bv-algebraic name.smt2 > name.lfsc
```

This set of commands produces a proof witness file named `name.lfsc`.

- In a Coq file `name.v`, put:
```coq
Require Import SMTCoq.SMTCoq Bool List.
Import ListNotations BVList.BITVECTOR_LIST FArray.
Local Open Scope list_scope.
Local Open Scope farray_scope.
Local Open Scope bv_scope.

Section File.
  Lfsc_Checker "name.smt2" "name.lfsc".
End File.
```

- Compile `name.v`: `coqc name.v`. If it returns `true` then the problem
  is indeed unsatisfiable.

NB: Use `cvc4tocoq` script in `src/lfsc/tests` to automatize the above steps.

- Ex: `./cvc4tocoq name.smt2` returns `true` only if the problem
  `name.smt2` has been proved unsatisfiable by CVC4.

The theories that are currently supported by these commands are `QF_UF`
(theory of equality), `QF_LIA` (linear integer arithmetic), `QF_IDL`
(integer difference logic), `QF_BV` (theory of fixed-size bit vectors),
`QF_A` (theory of arrays), and their combinations.


### CVC4 as a Coq decision procedure

The `cvc4_bool` tactic can be used to solve any goal of the form:
```coq
forall l, b1 = b2
```

where `l` is a quantifier-free list of terms and `b1` and `b2` are
expressions of type `bool`.

In addition, the `cvc4` tactic applies to Coq goals of sort `Prop`: it
 first converts the goal into a term of type `bool` (thanks to the
 `reflect` predicate of `SSReflect`), it then calls the previous tactic
 `cvc4_bool`, and it finally converts any unsolved subgoals returned by
 CVC4 back to `Prop`, thus offering to the user the possibility to solve
 these (usually simpler) subgoals.

The theories that are currently supported by these tactics are `QF_UF`
(theory of equality), `QF_LIA` (linear integer arithmetic), `QF_IDL`
(integer difference logic), `QF_BV` (theory of fixed-size bit vectors),
`QF_A` (theory of arrays), and their combinations.

A more efficient version of this tactic, called `cvc4_no_check`,
performs only the check at `Qed`. (Thus it is safe, but a proof may fail
at `Qed` even if everything went through during proof elaboration.)


## The smt tactic

The more powerful tactic `smt` combines all the previous tactics: it
first converts the goal to a term of type `bool` (thanks to the
`reflect` predicate of `SSReflect`), it then calls a combination of the
`cvc4_bool` and `verit_bool` tactics, and it finally converts any
unsolved subgoals back to `Prop`, thus offering to the user the
possibility to solve these (usually simpler) subgoals.

A more efficient version of this tactic, called `smt_no_check`,
performs only the check at `Qed`. (Thus it is safe, but a proof may fail
at `Qed` even if everything went through during proof elaboration.)


## Abduction

Using abduction requires to compile and install both `cvc4` and `cvc5`
as explained in the installation instructions. In the following, we
consider that the commands `cvc4` and `cvc5` are in your `PATH`
environment variable.


### Asking cvc5 for abducts that entail the goal
When an external solver finds that a goal doesn't hold (via one of the
previous tactics, say) the `abduce` tactic can be used to ask cvc5 for
*abducts* - facts that when provided to the solver, would allow it to
prove the goal. It is useful to discover missing hypotheses.

Within the proof of a goal of type
```coq
forall l, b1 = b2
```
`abduce n` asks cvc5 for `n` abducts, each of which will
independently entail the goal. A successful invocation of
`abduce` will result in a Coq failure with a failure message
that begins with:
```coq
The solver cannot prove the goal, but one of the following hypotheses would
make it provable:
```
and is followed by `n` abducts, each in its own line.

A subsequent call to an external solver with one of the abducts in the
scope of the proof results in a goal that is likely to be provable by
the solver. To bring an abduct into scope, the user can then either
locally assert and prove it, or pass a theorem representing the abduct
as a lemma to the external solver.

The theories that are currently supported by this tactic are `QF_UF`
(theory of equality), `QF_LIA` (linear integer arithmetic), `QF_IDL`
(integer difference logic), `QF_BV` (theory of fixed-size bit vectors),
`QF_A` (theory of arrays), and their combinations. However, the abduce tactic
can be used more generally on any quantifier-free theory (on a goal that has
the shape specified above). Any symbols that are not supported (specified
in one of the supported theories) will be treated as uninterpreted by
the SMT solver.


## Conversion tactics

SMTCoq provides conversion tactics, to inject various integer types into
the type Z supported by SMTCoq. They can be called before the other
SMTCoq tactics. These tactics are named `nat_convert`, `N_convert` and
`pos_convert`. They can be combined.
