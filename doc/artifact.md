# SMTCoq artifact

SMTCoq is a Coq tool that checks proof witnesses coming from external SAT and SMT solvers.
It currenly supports the quantifier free fragments of the theories of fixed-sized bit-vectors (`QF_BV`),
functional arrays (`QF_A`), linear integer arithmetic (`QF_LIA`), equality over uninterpreted functions
(`QF_EUF`), propositional reasoning and their combinations.

This document describes the organization of the SMTCoq artifact.

## How to download the artifact

To get the articaft, please browse [here](https://drive.google.com/file/d/0BzDtBR99eKp9RVd2aDVidktPNm8/view)
and download the `SMTCoq.ova` which is an image of an 
Ubuntu 16.04 LTS running virtual machine with approximately 3.6GB size 
(using 8GB memory, single processor and approximately 63GB virtual disk space once imported).
Then, please run [VirtualBox](https://www.virtualbox.org/wiki/VirtualBox);
from the `File` top-down menu click on `Import Appliance...` and locate the `SMTCoq.ova`
image. This will create you a virtual machine named `SMTCoq`. To run it, simply click on `Start`.
The login (and super user) password is two underscores in a row: `__`.


## How to install the artifact

Once logged into the virtual machine, you will find SMTCoq installed. 
If you want to install it on a seperate machine, please check the 
[installation guide] (https://github.com/lfsc/smtcoq/blob/master/INSTALL.md).


## How to run the artifact

There are two use-cases of SMTCoq:
 - `within a Coq tactic`: we can give a Coq goal to an external solver and get a
proof certificate for it. If the checker can validate the certificate, 
the soundness of the checker allow us to establish a proof of the initial goal
(aka `computational reflection`).
In this use case, the trusted base consists only of Coq: if something else goes wrong
(e.g., the checker cannot validate the certificate), the tactic will fail, but
nothing unsound will be added to the system.
 - `correct-by-construction checker`: the idea is to check the
validity of a proof witness, or proof certificate, coming from an external solver
against some input problem. In this use case, the
trusted base is both Coq and the parser of the input problem.
The parse is part of the trusted based because we need to make sure 
we are effectively verifying a proof of the problem we sent to the external solver.
However, this parser is fairly straightforward.

### within a Coq tactic

Once logged into the virtual machine, open a terminal and go to `unit-tests` directory
by typing `cd Desktop/smtcoq/unit-tests` from home. There, to open the test file run
`coqide Tests_lfsc.v` in the terminal. This will browse you in `CoqIDE` (the Coq interactive development environment)
the file where we use SMTCoq within a Coq tactic called `smt`.
Within the CoqIDE, please use `Forward one command` button (downarrow on the top-left corner) to navigate through the source since `Go to end` button
uses a parallelization strategy which has not yet been supported by SMTCoq.
Note also that if the background becomes green after going one command forward, this means that Coq has accepted the statement,
and at the end of the session the whole file should be green. If Coq fails to accept any statement,
you will see a brief reason of the failure in the bottom-right rectangle within the `Errors` tab.

```coq
Require Import SMTCoq.
```

loads the SMTCoq module whose implementation is explained
[here](https://github.com/lfsc/smtcoq/blob/master/doc/sources.md) in details.

Similarly,

```coq
Require Import Bool PArray Int63 List ZArith Logic.
```

loads above-mentioned modules from the Coq standard library.

```coq
Infix "-->" := implb (at level 60, right associativity) : bool_scope.
```

introduces a new notation `-->` for the boolean implication.

Using 

```coq
Section BV.
```
we open a new section to prove theorems from the theory of fixed-size bitvectors. 

```coq
Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.
```

are to load our own [bitvector library](https://github.com/lfsc/smtcoq/blob/master/src/bva/BVList.v)
(called BITVECTOR_LIST in BVList.v file)
to be able to use theorems proven and notations introduced there. Note that to end a section `XX` you need to
type

```coq
End XX.
```

Now, we can state goals and prove them automatically. For instance, the goal

```coq
  Goal forall (a b c: bitvector 4),
                                 (c = (bv_and a b)) ->
                                 ((bv_and (bv_and c a) b) = c).
```

is proven by the `smt` tactic which subsumes the powers of the reification tactics `cvc4` and `verit`:
```coq
  Proof.
    smt.
  Qed.
```

Here are some more detailed explanation of the tactics: 

 - `verit` -> can function on the goals in Coq's `Prop`: 
 first calls `prop2bool` on the goal, getting the goal in `bool`, 
 then calls the reificiation tactic `verit_bool` (can only function on Boolean goals),
 and finally puts the goal back in Coq's `Prop`, by calling `bool2prop`, if not solved.
 
 - `cvc4` -> can function on the goals in Coq's `Prop`: 
 first calls `prop2bool` on the goal, getting the goal in `bool`, 
 then calls the reificiation tactic `cvc4_bool` (can only function on Boolean goals),
 and finally puts the goal(s) back in Coq's `Prop`, by calling `bool2prop`, in case it is not solved or additional goals returned.
 
 - `smt` -> subsumes the powers of `cvc4` and `verit` tactics: 
 first calls `prop2bool` on the goal, getting the goal in `bool`, 
 then calls either of the reificiation tactics `cvc4_bool`, `verit_bool` (can only function on Boolean goals),
 and finally puts the goal(s) back in Coq's `Prop`, by calling `bool2prop`, in case it is not solved or additional goals returned.

Notice that the tactics `cvc4_bool` and `verit_bool` are (implemented in OCaml) doing the main job: 
calling the external solvers (`CVC4` and `veriT` respectively), getting a
proof certificate and if the checker can validate the certificate, establishing the proof of the initial goal.
The tactics `prop2bool` and `bool2prop` are implemented in Coq using the Ltac language and are giving the Boolean counterpart
of a propositional goal and vice versa.

Another example of a goal in the theory of bit-vectors is the following:

```coq
  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
  Proof. 
     smt.
  Qed.
```

Above goal uses three bit-vectors of size four: `bv1`, `bv2` and `bv3` then sets them to `0000`, `1000` and `1100` in the given order
(`#b|1|0|...|` is the notation to annotate the bits of a bit-vector; `0` stands for `false` and `1` is for `true`). Finally,
it states that `bv1` is less than (unsigned less than over bit-vectors) `bv2` and (propositional) `bv2` is less than `bv3`.
The tactic `smt` suffices to solve the goal. 


The following sections `Arrays`, `LIA`, `EUF`, `PR`and `A_BV_EUF_LIA_PR`
include goals that could be proven by the `smt` tactic from the
theories of functional arrays; linear integer arithmetic;
uninterpreted functions; propositional reasoning and
the combination of functional arrays, fixed-size bit-vectors, uninterpreted functions, linear integer arithmetic
and propositional reasoning; respectively.


The example appears in the paper could be found in the section `A_BV_EUF_LIA_PR`:

```coq
Goal forall (a b: farray Z Z) (v w x y: Z)
            (r s: bitvector 4)
            (f: Z -> Z)
            (g: farray Z Z -> Z)
            (h: bitvector 4 -> Z),
            a[x <- v] = b /\ a[y <- w] = b ->
            r = s /\ h r = v /\ h s = y ->
            v < x + 1 /\ v > x - 1 ->
            f (h r) = f (h s) \/ g a = g b.
  Proof.
    smt. (** "cvc4. verit." also solves the goal *)
  Qed.
```

It introduces two arrays `a` and `b` of type `farray Z Z` (the type of integer arrays with integer indices);
four integers `v`, `w`, `x` and `y`; three uninterpreted fuctions `f`, `g` and `h`. Then it does some assignments
and states that either `f (h r) = f (h s)` or (propositional) `g a = g b`.
Notice that `a[i]` is to select the value stored in the `i^th^` index of the array `a` while `a[x <- v]` is to store the value `v`
in `a[x]`, `x^th^` index of array `a`. 

You can also run Coq in batch mode on our test file by running (once you are in the correct directory) by simply typing
`coqc Tests_lfsc.v`.


### correct-by-construction checker

Using SMTCoq as a `correct-by-construction checker` means that it is possible to start with a problem in SMT-LIB standard,
call an external solver (CVC4 or veriT) on it, get the unsatisfiability proof and certify it using the certified Coq checkers.

To test that, in a terminal go to `tests` directory (from home) by typing `cd Desktop/smtcoq/src/lfsc/tests`. Run the shell script `cvc4tocoq` providing
an input file (i.e., `inp_file.smt2` extended) by typing `./cvc4tocoq inp_file.smt2`. This will call `CVC4`, get the proof in `LFSC` format,
type check and convert it (using a converter written in OCaml) into SMTCoq format (which is very close to the proof format of `veriT`)
and call the Coq checker. If the checker returns `true` that means that Coq indeed agreed that the proof of the input problem is correct. If it
returns `false`, that means either that the proof is incorrect or that the OCaml converter is mistaken/incomplete.

To get a working example, you can run `./cvc4tocoq X.smt2` where `X.smt2` being any input file under `tests` directory (`/home/Desktop/smtcoq/src/lfsc/tests`).
Feel free to generate your own problem files but please recall that the input problems should be from the
supported theories: `QF_A`, `QF_BV`, `QF_LIA`, `QF_EUF`, propositional reasoning and their combinations.





