# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64).

It relies on the
[git version of Coq with native compilation](https://github.com/maximedenes/native-coq),
and its dependencies (OCaml, camlp5, GNU/Make). We explain below how to
compile it (but not the dependencies).

To use SMTCoq, you also need one or more solvers supported by SMTCoq.
Currently, these solvers are:

- [veriT](http://prosecco.gforge.inria.fr/personal/ckeller/Documents-recherche/Smtcoq/verit2c2b43b.tar.gz)

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

Please download the solvers you would like to use via the above links
(since SMTCoq might not support later versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**.


## Installation of native-coq and SMTCoq

1. Download the git version of Coq with native compilation:
     `git clone git://github.com/maximedenes/native-coq.git`
   and compile it by following the instructions available in the
   repository. We recommand that you do not install it, but only compile
   it in local:
```
./configure -local
make
```

2. Set an environment variable COQBIN to the directory where Coq's
   binaries are; for instance:
     `export COQBIN=/home/jdoe/native-coq/bin/`
   (the final slash is mandatory).

3. Compile and install SMTCoq by using the commands:
```
make
make install
```
   in the src directory.
