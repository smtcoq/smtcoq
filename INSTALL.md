# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64).

You have various ways to install it:
- the simplest one is via opam;
- you can also install it from the sources, using two different versions
  of Coq (depending on the efficiency you want).
In either case, you will also need to install the provers you want to
use (see below).

## Requirements

You need to have OCaml version > 4.03.0 and Coq version 8.5pl2. The easiest
way to install these two pieces of software is through opam.

## Installation via opam (*only for base branch of main fork*)

Simply add the coq-extra-dev repo to opam:
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
and install smtcoq:
```
opam install coq-smtcoq
```


## Installation from the sources

You can also build SMTCoq from the sources, using either Coq 8.5 or the
[version of Coq with native data-structures](https://github.com/smtcoq/native-coq).
We recommend Coq 8.5 for standard use, and native-coq for uses that
require very efficient computation (such as checking big certificates).


### Installation with Coq 8.5

1. Download the last stable version of Coq 8.5:
```
wget https://coq.inria.fr/distrib/V8.5pl2/files/coq-8.5pl2.tar.gz
```
   and compile it by following the instructions available in the
   repository (make sure you use OCaml 4.03.0 for that). We recommand
   that you do not install it, but only compile it in local:
```
./configure -local
make
```

2. Set an environment variable COQBIN to the directory where Coq's
   binaries are; for instance:
```
export COQBIN=/home/jdoe/coq-8.5pl2/bin/
```
   (the final slash is mandatory).

3. Compile and install SMTCoq by using the commands:
```
./configure.sh
make
make install
```
   in the src directory.


### Installation with native-coq

1. Download the git version of Coq with native compilation:
```
git clone https://github.com/smtcoq/native-coq.git
```
   and compile it by following the instructions available in the
   repository. We recommand that you do not install it, but only compile
   it in local:
```
./configure -local
make
```

2. Set an environment variable COQBIN to the directory where Coq's
   binaries are; for instance:
```
export COQBIN=/home/jdoe/native-coq/bin/
```
   (the final slash is mandatory).

3. Compile and install SMTCoq by using the commands:
```
./configure.sh -native
make
make install
```
   in the src directory.


## Installation of the provers

To use SMTCoq, you need one or more solvers supported by SMTCoq.
Currently, these solvers are:

- [veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/verit2c2b43b.tar.gz)

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

- [CVC4](http://cvc4.cs.nyu.edu)

Please download the solvers you would like to use via the above links
(since SMTCoq might not support later versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**, as detailed below.


### veriT

The
[above link](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/verit2c2b43b.tar.gz)
points to a snapshot of veriT which is known to be compatible with
SMTCoq, and is already in proof production mode. If you encounter
problems to compile it, please report an issue.


### zChaff

zChaff is not actively maintained, so you might encounter problems to
compile it on modern platforms.
[This patch](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/zchaff64.patch)
might solve your problems (thanks to Sylvain Boulmé for it); if not,
please report an issue.

To turn proof production on, you need to uncomment the line
`// #define VERIFY_ON ` in `zchaff_solver.cpp`.


### CVC4

Use the version of CVC4 that is available in the master branch of its
[git repository](https://github.com/CVC4/CVC4) or one of the **development**
versions available at [http://cvc4.cs.nyu.edu/downloads/] (we recommend using
the latest version available). CVC4's binary must be present in your PATH to use
it through SMTCoq.
