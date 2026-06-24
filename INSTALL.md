# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux.

Two simple ways to install SMTCoq are using opam or Nix. You can also install it
from the sources.

If you are using opam or from the sources, you will also need to [install the
provers](#installation-of-the-provers) you want to use.


## Installation of the latest version via opam (recommended)

### In an existing switch

You need to have OCaml version >= 4.14 and Rocq >= 9.0.

Simply add the rocq-released repo to opam:
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
```
and install SMTCoq:
```bash
opam install rocq-smtcoq
```

### In a new switch

Create a switch:
```bash
opam switch create ocaml-base-compiler.4.14.2
eval $(opam env)
```
add the Rocq repos to opam:
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
```
and install SMTCoq:
```bash
opam install rocq-smtcoq
```

### If you are new to opam

We recommended to install the required packages from
[opam](https://opam.ocaml.org). Once you have installed opam on your system you
should issue the following command:

```bash
opam init
```

which will initialize the opam installation and prompt for modifying the shell
init file.

Once opam is installed you should still issue

```bash
eval `opam config env`
```

(this is not necessary if you start another session in your shell).

Then follow the instructions of the previous section.


## Installation of the development version via opam

### In an existing switch

You need to have OCaml version >= 4.14 and Rocq >= 9.0.

Simply add the rocq-extra-dev repo to opam:
```bash
opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
```
and install SMTCoq:
```bash
opam install rocq-smtcoq
```

### In a new switch

Create a switch:
```bash
opam switch create ocaml-base-compiler.4.14.0
eval $(opam env)
```
add the Rocq repos to opam:
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
```
and install SMTCoq:
```bash
opam install rocq-smtcoq
```


## Installation from Nix

TODO: [VL]


## Installation from the sources, using opam (not recommended)

### Requirements

You need to have OCaml version >= 4.14.2 and Rocq >= 9.0.

> **Warning**: The version of Rocq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.14.2.

### Install opam

We recommended to install the required packages from
[opam](https://opam.ocaml.org). Once you have installed opam on your system you
should issue the following command:

```bash
opam init
```

which will initialize the opam installation and prompt for modifying the shell
init file.

Once opam is installed you should still issue

```bash
eval `opam config env`
```

(this is not necessary if you start another session in your shell).

### Install OCaml

Now you can install an OCaml compiler (we recommend 4.14.2):

```bash
opam switch create ocaml-base-compiler.4.14.2
```

### Install Coq

After OCaml is installed, you can install Rocq through opam.

```bash
opam install rocq
```

If you also want to install RocqIDE at the same time you can do

```bash
opam install rocq rocqide
```

but you might need to install some extra packages and libraries for your system.


### Install SMTCoq

Compile and install SMTCoq by using the following commands in the src directory.

```bash
dune build -p rocq-smtcoq
dune install rocq-smtcoq
```

## Installation of the provers

To use SMTCoq, we recommend installing the following two SMT solvers:
- CVC4
- [veriT](https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)

SMTCoq also supports the following SAT solver for propositional reasoning:
- [ZChaff](https://www.princeton.edu/~chaff/zchaff.html)

SMTCoq finally provides an abduction tactic using the
[cvc5](https://cvc5.github.io) SMT solver.

Please download the solvers you would like to use via the links below
(since SMTCoq might not support other versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**, as detailed below.


### CVC4

Use the stable version 1.6 of CVC4 that is available either:
- as a [Linux binary](http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt)
- as a [Windows binary](http://cvc4.cs.stanford.edu/downloads/builds/win64-opt/cvc4-1.6-win64-opt.exe)
- as a [MacOs binary](https://github.com/cvc5/cvc5/releases/download/1.6/cvc4-1.6-macos-opt)
- from [the sources](https://github.com/cvc5/cvc5/releases/tag/1.6), using the following commands:
```
./autogen.sh
./configure
make
```
Whatever solution you choose, a binary called `cvc4` must be present in
your PATH to use it through SMTCoq.

In your `.bashrc` (or `.bash_profile`, or any other initialization file read by
your shell), export the following environment variable to make it point at the
`signatures` directory distributed with SMTCoq.

> Don't use `~` in the path but rather `$HOME`.

```bash
export LFSCSIGS="$HOME/path/to/smtcoq/src/lfsc/tests/signatures/"
```

If you installed SMTCoq via opam (recommended), the path to SMTCoq
(to replace `path/to/smtcoq`) is
`.opam/NAMEOFTHESWITCH/.opam-switch/sources/coq-smtcoq.dev+ROCQVERSION`
where `NAMEOFTHESWITCH` must be replaced by the name of the opam switch
(`ocaml-base-compiler.4.14.2` if you created a new switch following the
instructions above) and `ROCQVERSION` must be replaced by the first two
parts of the version of Rocq (e.g `9.0`, `9.1`...).


### veriT

Download this [snapshot of
veriT](https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)
which is known compatible with SMTCoq, and is already in proof
production mode. To compile it, unpack the archive and use the following
commands:
```
./configure
make
```
This will produce an executable called `veriT` that you should add to
your path. If you encounter problems to compile it, please report an
issue.


### cvc5

Use version 1.0.7 that is available
[here](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.7) either as a
Linux, Windows, or MacOS binary, or from the sources.

Whatever solution you choose, a binary called `cvc5` must be present in
your PATH to use it through SMTCoq.


### ZChaff

ZChaff can be downloaded
[here](https://www.princeton.edu/~chaff/zchaff.html). It is not actively
maintained, so you might encounter problems to compile it on modern
platforms. [This
patch](https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/zchaff64.patch)
might solve your problems (thanks to Sylvain Boulmé for it); if not,
please report an issue.

To turn proof production on, you need to uncomment the line
`// #define VERIFY_ON ` in `zchaff_solver.cpp`.

The `zchaff` binary must be present in your PATH to use it through SMTCoq.
