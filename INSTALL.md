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


## Installation via opam (uses Coq-8.5)

Simply add the coq-extra-dev repo to opam:
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
and install smtcoq:
```
opam install coq-smtcoq
```


## Installation from the sources (uses Coq-8.6 or native-coq)

You can also build SMTCoq from the sources, using either Coq 8.6 or the
[version of Coq with native data-structures](https://github.com/smtcoq/native-coq).
We recommend Coq 8.6 for standard use, and native-coq for uses that
require very efficient computation (such as checking big certificates).


### Installation with Coq 8.6

1. Download the last stable version of Coq 8.6:
```
wget https://coq.inria.fr/distrib/8.6.1/files/coq-8.6.1.tar.gz
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
export COQBIN=/home/jdoe/coq-8.6.1/bin/
```
   (the final slash is mandatory).

3. Compile and install SMTCoq by using the following commands in the src directory.
```
./configure.sh
make
make install
```


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

3. Compile and install SMTCoq by using the following commands in the src directory.
```
./configure.sh -native
make
make install
```


## Installation of the provers

To use SMTCoq, you need one or more solvers supported by SMTCoq.
Currently, these solvers are:

- [veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

Please download the solvers you would like to use via the above links
(since SMTCoq might not support other versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**, as detailed below.


### veriT

The
[above link](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)
points to a snapshot of veriT which is known to be compatible with
SMTCoq, and is already in proof production mode. To compile it, unpack
the archive and use the following commands:
```
autoconf
./configure
make
```
This will produce an executable called `veriT` that you should add to
your path. If you encounter problems to compile it, please report an
issue.


### zChaff

zChaff is not actively maintained, so you might encounter problems to
compile it on modern platforms.
[This patch](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/zchaff64.patch)
might solve your problems (thanks to Sylvain Boulmé for it); if not,
please report an issue.

To turn proof production on, you need to uncomment the line
`// #define VERIFY_ON ` in `zchaff_solver.cpp`.
