# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64).


## Installation from the sources

Currently, SMTCoq can be built only from the sources, using the
[version of Coq with native data-structures](https://github.com/maximedenes/native-coq). The design of an opam package is under progress.

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


## Installation of the provers

To use SMTCoq, you need one or more solvers supported by SMTCoq.
Currently, these solvers are:

- [veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/verit2c2b43b.tar.gz)

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

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
