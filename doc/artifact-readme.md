# SMTCoq artifact

SMTCoq is a Coq tool that can be used to dispatch goals to external SAT and SMT solvers
or simply to check proof witnesses produced by them.
It currenly supports the quantifier free fragments of the SMT-LIB theories of fixed-sized bit-vectors (`QF_BV`),
functional arrays (`QF_A`), linear integer arithmetic (`QF_LIA`), equality over uninterpreted functions
(`QF_EUF`), and their combinations.

This document describes the organization of the SMTCoq artifact submission for CAV 2017.

## How to download the artifact

To get the artifact, please browse [here](https://drive.google.com/file/d/0BzDtBR99eKp9YWM3bHV0S0RqMGM/view)
and download the `SMTCoq.ova` which is an image of an 
Ubuntu 16.04 LTS running virtual machine with approximately 3.6GB size 
(using 8GB memory, single processor which runs at the same frequency with the host processor,
and approximately 63GB virtual disk space once imported).
Then, please run [VirtualBox](https://www.virtualbox.org/wiki/VirtualBox);
from the `File` top-down menu click on `Import Appliance...` and locate the `SMTCoq.ova`
image. This will create you a virtual machine named `SMTCoq`. To run it, simply click on `Start`.
The login (and super user) password is `123`.


## How to install the artifact

Once logged into the virtual machine, you will find SMTCoq installed. 
If you want to install it on a separate machine, please check the SMTCoq
[installation guide](https://github.com/lfsc/smtcoq/blob/master/INSTALL.md).


## How to run the artifact

There are two use-cases of SMTCoq:
 - `within a Coq tactic`: we can give a Coq goal to an external solver and get a
proof certificate for it. If the checker can validate the certificate, 
the soundness of the checker allow us to establish a proof of the initial goal
(by `computational reflection`).
In this use case, the trusted base consists only of Coq: if something else goes wrong
(e.g., the checker cannot validate the certificate), the tactic will fail, but
nothing unsound will be added to the system.
 - `correct-by-construction checker`: the idea is to check the
validity of a proof witness, or proof certificate, produced by an external SMT solver
for some input problem. In this use case, the
trusted base is both Coq and the parser of the input problem.

### Within a Coq tactic

Once logged into the virtual machine, open a terminal and go to `unit-tests` directory
by typing `cd Desktop/smtcoq/unit-tests` from home. It contains a test file (`Tests_lfsc.v`) which makes
use of the new SMTCoq tactics inside Coq, to discharge goals with the aid of various SMT
solvers.

#### Running everything with a single command

You can run Coq in batch mode on our test file by running (once you are in the correct
directory) by simply running the following command:

```
coqc Tests_lfsc.v
```

The return code should be 0 to indicate that Coq typed-checked everything correctly. The batch
compiler `coqc` tries to compile `Tests_lfsc.v` file into `Test_lfsc.vo`. Please refer to
[Coq reference manual](https://coq.inria.fr/refman/Reference-Manual008.html#compiled) for details.

#### Interactive session through CoqIDE

In the `unit-test` directory, open the test file by running

```
coqide Tests_lfsc.v
```

in the terminal. This will load in `CoqIDE` (the Coq interactive development environment)
the file where we use SMTCoq within a Coq tactic called `smt`.
Within the CoqIDE, use `Forward one command` button (downarrow on the top-left corner) to
navigate through the source since `Go to end` button uses a parallelization strategy
which is not yet supported by SMTCoq.

If the background becomes green after going one command forward, this means
that Coq has accepted the statement. At the end of the session the whole file should be green.
If Coq fails to accept any statement, you will see a brief reason of the failure in the
bottom-right rectangle within the `Errors` tab.



#### Understanding the test file

```coq
Require Import SMTCoq.
```

loads the SMTCoq module. It might be interesting to check out the implementation
details (with pointers to source codes) of the SMTCoq module
[here](https://github.com/lfsc/smtcoq/blob/master/doc/sources.md). 

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
to be able to use theorems proven and notations introduced there. Note that to end a
section `XX` you need to type

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

 - `verit` -> applies to Coq goals of type `Prop`: 
 it first calls `prop2bool` on the goal, converting the goal to a term of type `bool`, 
 it then calls the reification tactic `verit_bool` (which applies only to Boolean goals),
 and it finally converts the goals back to `Prop`, by calling `bool2prop`, if it is not
 solved.
 
- `cvc4` -> applies to Coq goals of type `Prop`: 
 it first calls `prop2bool` on the goal, converting the goal to a term of type `bool`, 
 it then calls the reification tactic `cvc4_bool` (which applies only to Boolean goals),
 and it finally converts any unsolved subgoals returned by CVC4 back to `Prop`, 
 by calling `bool2prop`.
 
- `smt` -> has the combined effect of the `cvc4` and `verit` tactics: 
 it first calls `prop2bool` on the goal, it then calls either of the `cvc4_bool` and 
 `verit_bool` tactics, and it finally converts any unsolved subgoals back to `Prop`, 
 by calling `bool2prop`.

The tactics `cvc4_bool` and `verit_bool`, implemented in OCaml, do most of the work:
calling the external solvers (`CVC4` and `veriT` respectively), getting a
proof certificate, and if SMTCoq's checker can validate the certificate, establishing the proof
of the initial goal. The translation tactics `prop2bool` and `bool2prop` are implemented in Coq using
the Ltac language. 

NB: all of the above tactics perform better on a "standard" machine compared to the VM.

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

This goal uses three bit-vectors of size four: `bv1`, `bv2` and `bv3` then sets them to
`0000`, `1000` and `1100` in the given order (`#b|1|0|...|` is the notation for bit-vector
constants, where `0` stands for `false` and `1` is for `true`). Finally, it states
that `bv1` is less than (unsigned less than over bit-vectors) `bv2` and (propositional)
`bv2` is less than `bv3`. The tactic `smt` suffices to solve the goal. 


The following sections `Arrays`, `LIA`, `EUF`, `PR`and `A_BV_EUF_LIA_PR` in the Coq file include goals that
can be proven by the `smt` tactic from the theories of functional arrays; linear integer
arithmetic; uninterpreted functions; propositional reasoning and the combination of functional
arrays, fixed-size bit-vectors, uninterpreted functions, linear integer arithmetic and
propositional reasoning; respectively.


The example that appears in the paper can be found in the section `A_BV_EUF_LIA_PR`:

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

It introduces two arrays `a` and `b` of type `farray Z Z` (the type of integer arrays
with integer indices); four integers `v`, `w`, `x` and `y`; three uninterpreted fuctions
`f`, `g` and `h`. 
Notice that `a[i]` is used to select the value stored in the `i^th^` index of the array `a`
while `a[x <- v]` is used to store the value `v` in `a[x]`, `x^th^` index of array `a`. 



### Correct-by-construction checker

Using SMTCoq as a `correct-by-construction checker` means that it is possible to start with
a problem in SMT-LIB standard, call an external solver (CVC4 or veriT) on it, get the
unsatisfiability proof and certify it using the certified "small checkers" of SMTCoq.

To test that, in a terminal go to `tests` directory (from home) by typing 
`cd Desktop/smtcoq/src/lfsc/tests`. Run the shell script `cvc4tocoq` providing
an input file (i.e., `uf1.smt2`) by typing `./cvc4tocoq uf1.smt2`. 
This will call `CVC4`, get the proof in `LFSC` format, type check and convert it (using a converter
written in OCaml) into SMTCoq format (which is very close to the proof format of `veriT`) and call
the SMTCoq checker. If the checker returns `true` that means that SMTCoq indeed agreed that the proof of
the input problem is correct. If it returns `false`, that means either that the proof is incorrect
or that the OCaml converter is mistaken/incomplete. Note that you can replace `uf1.smt2`
with any `.smt2` extended file under
`tests` directory (`/home/Desktop/smtcoq/src/lfsc/tests`).

Feel free to generate your own problem files but please recall that the input problems should be from the
supported theories: `QF_A`, `QF_BV`, `QF_LIA`, `QF_EUF`, and their combinations.
