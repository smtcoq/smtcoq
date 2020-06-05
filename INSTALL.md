# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64) and Mac OS X.

<!-- The simplest way is to install it using opam. You can also install it -->
<!-- from the sources (this is mandatory if you want to use the native -->
<!-- version, see below). -->

You will also need to [install the provers](#installation-of-the-provers)
you want to use.

## Requirements

You need to have OCaml version >= 4.04.0 and Coq version 8.11.*.
The easiest way to install these two pieces of software is through opam.

> **Warning**: The version of Coq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.04.0.

If you want to use SMTCoq with high performance to check large proof
certificates, you need to use the [version of Coq with native
data-structures](https://github.com/smtcoq/native-coq) instead of
Coq-8.11 (warning: this allows one to use the vernacular commands but not
the tactics).


<!-- ### Installation via opam (recommended) -->

<!-- Simply add the coq-extra-dev repo to opam: -->
<!-- ```bash -->
<!-- opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev -->
<!-- ``` -->
<!-- and install SMTCoq: -->
<!-- ```bash -->
<!-- opam install coq-smtcoq -->
<!-- ``` -->


### Installation from the sources, using opam <!-- (not recommended) -->

#### Install opam

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

#### Install OCaml

Now you can install an OCaml compiler (we recommend 4.08.1 or the latest
release):

```bash
opam switch 4.08.1
```

#### Install Coq

After OCaml is installed, you can install Coq-8.11.0 through opam.

```bash
opam install coq.8.11.0
```

If you also want to install CoqIDE at the same time you can do

```bash
opam install coq.8.11.0 coqide.8.11.0
```

but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).


#### Install SMTCoq

Compile and install SMTCoq by using the following commands in the src directory.

```bash
./configure.sh
make
make install
```


<!-- ### Installation from the sources, with official Coq 8.9 release (not recommended) -->

<!-- 1. Download the last stable version of Coq 8.9: -->
<!-- ```bash -->
<!-- wget https://github.com/coq/coq/archive/V8.9.0.tar.gz -->
<!-- ``` -->
<!--    and compile it by following the instructions available in the -->
<!--    repository (make sure you use OCaml 4.04.0 for that). We recommand -->
<!--    that you do not install it, but only compile it in local: -->
<!-- ```bash -->
<!-- ./configure -local -->
<!-- make -->
<!-- ``` -->

<!-- 2. Set an environment variable COQBIN to the directory where Coq's -->
<!--    binaries are; for instance: -->
<!-- ```bash -->
<!-- export COQBIN=/home/jdoe/coq-8.9.0/bin/ -->
<!-- ``` -->
<!--    (the final slash is mandatory). -->

<!-- 3. Compile and install SMTCoq by using the following commands in the src directory. -->
<!-- ``` -->
<!-- ./configure.sh -->
<!-- make -->
<!-- make install -->
<!-- ``` -->


<!-- ### Installation with native-coq (not recommended except for high performances) -->

<!-- > **Warning**: this installation procedure is recommended only to use -->
<!-- > the vernacular commands efficiently (in particular, to check very -->
<!-- > large proof certificates). It does not allow one to use the tactics. -->

<!-- 1. Download the git version of Coq with native compilation: -->
<!-- ```bash -->
<!-- git clone https://github.com/smtcoq/native-coq.git -->
<!-- ``` -->
<!--    and compile it by following the instructions available in the -->
<!--    repository. We recommand that you do not install it, but only compile -->
<!--    it in local: -->
<!-- ```bash -->
<!-- ./configure -local -->
<!-- make -->
<!-- ``` -->

<!-- 2. Set an environment variable COQBIN to the directory where Coq's -->
<!--    binaries are; for instance: -->
<!-- ```bash -->
<!-- export COQBIN=/home/jdoe/native-coq/bin/ -->
<!-- ``` -->
<!--    (the final slash is mandatory). -->

<!-- 3. Compile and install SMTCoq by using the following commands in the src directory. -->
<!-- ``` -->
<!-- ./configure.sh -native -->
<!-- make -->
<!-- make install -->
<!-- ``` -->


## Installation of the provers

To use SMTCoq, we recommend installing the following two SMT solvers:

- [CVC4](http://cvc4.cs.nyu.edu)

- [veriT](https://verit.loria.fr)

SMTCoq also supports the following SAT solver for propositional reasoning:

- [zChaff](http://www.princeton.edu/~chaff/zchaff.html)

Please download the solvers you would like to use via the links below
(since SMTCoq might not support other versions), and follow the
instructions available for each solver in order to compile them **in a
proof production mode**, as detailed below.


### CVC4

Use the stable version 1.6 of CVC4 that is available in the **stable
versions** column at [http://cvc4.cs.stanford.edu/downloads]. You can
either get a binary (recommended) or compile it from the sources using
the following commands:
```
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
autoconf
./configure
make
```
This will produce an executable called `veriT` that you should add to
your path. If you encounter problems to compile it, please report an
issue.


### zChaff

zChaff can be downloaded
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
