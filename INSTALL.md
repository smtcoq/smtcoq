# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64).


## Quick installation

The simplest way to install SMTCoq is to use the OPAM package, available
in the
[Coq unstable repository](https://github.com/coq/repo-unstable.git).
Once you have OPAM installed on your system:
```
opam repo add coq-stable https://github.com/coq/repo-stable.git
opam repo add coq-unstable https://github.com/coq/repo-unstable.git
opam update
opam install coq coq:smtcoq
```
For more information of opam packages for Coq, see
[Use OPAM for Coq](http://coq-blog.clarus.me/use-opam-for-coq.html).

This version is sufficient to check small certificates and to solve
small goals. However, if you want to check larger certificates, we
recommend using SMTCoq with the
[version of Coq with native data-structures](https://github.com/maximedenes/native-coq),
following the instructions in Section "Installation from the sources".


## Installation of the provers

To use SMTCoq, you also need one or more solvers supported by SMTCoq.
Currently, these solvers are:

- [veriT](http://prosecco.gforge.inria.fr/personal/ckeller/Documents-recherche/Smtcoq/verit2c2b43b.tar.gz)

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

Please download the solvers you would like to use via the above links
(since SMTCoq might not support later versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**.


## Installation from the sources

From the sources, SMTCoq can be built either with the standard version
of Coq or with the
[version of Coq with native data-structures](https://github.com/maximedenes/native-coq).
We recommend this latter for efficiency.


### With the version of Coq with native data-structures

1. Download the git version of Coq with native compilation:
```
git clone git://github.com/maximedenes/native-coq.git
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
./configure.sh
make
make install
```
   in the src directory.


### With the standard version of Coq

1. Install the standard version of Coq (>= 8.4) by any means that give
   access to the sources (e.g. via OPAM or from the sources).

2. Set an environment variable COQBIN to the directory where Coq's
   binaries are; for instance:
```
export COQBIN=/home/jdoe/coq-8.4pl5/bin/
```
   (the final slash is mandatory).

3. Compile and install SMTCoq by using the commands:
```
./configure.sh -standard
make
make install
```
   in the src directory.
