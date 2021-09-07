# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64) and Mac OS X.

The simplest way is to install it using opam. You can also install it
from the sources.

You will also need to [install the provers](#installation-of-the-provers)
you want to use.


## Installation via opam (recommended)

### In an existing switch

You need to have OCaml version >= 4.09 and Coq >= 8.11.

Simply add the coq-extra-dev repo to opam:
```bash
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
and install SMTCoq:
```bash
opam install coq-smtcoq
```

### In a new switch

Create a switch:
```bash
opam switch create ocaml-base-compiler.4.09.0
eval $(opam env)
```
add the Coq repos to opam:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
and install SMTCoq:
```bash
opam install coq-smtcoq
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


## Installation from the sources, using opam (not recommended)

### Requirements

You need to have OCaml version >= 4.09.0 and Coq version 8.11.*.

> **Warning**: The version of Coq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.08.

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

Now you can install an OCaml compiler (we recommend 4.10.0):

```bash
opam switch create ocaml-base-compiler.4.10.0
```

### Install Coq

After OCaml is installed, you can install Coq-8.11.2 through opam.

```bash
opam install coq.8.11.2
```

If you also want to install CoqIDE at the same time you can do

```bash
opam install coq.8.11.2 coqide.8.11.2
```

but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).


### Install SMTCoq

Compile and install SMTCoq by using the following commands in the src directory.

```bash
./configure.sh
make
make install
```

## Installation of the provers

To use SMTCoq, we recommend installing the following two SMT solvers:

- CVC4

- [veriT](https://verit.loria.fr)

SMTCoq also supports the following SAT solver for propositional reasoning:

- [ZChaff](http://www.princeton.edu/~chaff/zchaff.html)

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
`.opam/NAMEOFTHESWITCH/.opam-switch/sources/coq-smtcoq.dev+COQVERSION`
where `NAMEOFTHESWITCH` must be replaced by the name of the opam switch
(`ocaml-base-compiler.4.09.0` if you created a new switch following the
instructions above) and `COQVERSION` must be replaced by the first two
parts of the version of Coq (`8.11`, `8.12` or `8.13`).

If you don't want SMTCoq to spit the translated proof in your proof environment
window, add the following optional definition (in the same file).

```bash
export DONTSHOWVERIT="yes"
```


### veriT

Download this [snapshot of
veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)
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


### ZChaff

ZChaff can be downloaded
[here](http://www.princeton.edu/~chaff/zchaff.html). It is not actively
maintained, so you might encounter problems to compile it on modern
platforms. [This
patch](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/zchaff64.patch)
might solve your problems (thanks to Sylvain Boulmé for it); if not,
please report an issue.

To turn proof production on, you need to uncomment the line
`// #define VERIFY_ON ` in `zchaff_solver.cpp`.

The `zchaff` binary must be present in your PATH to use it through SMTCoq.


## Setting up environment for SMTCoq
### Using SMTCoq without installing

If you want to use SMTCoq without adding it to your Coq installation, you can
tell Coq where to find SMTCoq by adding the following line in the file
`~/.config/coqrc`:

```coq
Add Rec LoadPath "~/path/to/smtcoq/src" as SMTCoq.
```

See [this
documentation](https://coq.inria.fr/refman/practical-tools/coq-commands.html#by-resource-file)
if it does not work.


### Emacs and ProofGeneral

If you use Emacs and ProofGeneral for Coq development, we recommend to use the
package [exec-path-from-shell](https://github.com/purcell/exec-path-from-shell)
(which can be installed with `M-x package-install exec-path-from-shell`) and to
add the following in your `.emacs`:

```elisp
(exec-path-from-shell-initialize)
```

This will make emacs use the same environment as your shell. This is also
particularly useful if you have installed Coq and OCaml from opam.


### Warning about CoqIDE

The latest versions of CoqIDE can now check Coq scripts in parallel. This
feature is very useful but it seems SMTCoq doesn't work with it. This means
that if you use any of the SMTCoq tactics or vernacular commands, we suggest to
instruct CoqIDE to go through the script step-by-step.
