# Installation procedures for SMTCoq

## What do you need?

SMTCoq is designed to work on computers equipped with a POSIX (Unix or a
clone) operating system. It is known to work under GNU/Linux (i386 and
amd64) and Mac OS X.

<!--
You have various ways to install it:

- the simplest one is via opam;
- you can also install 
-->
  
For now you have to install it from the sources, using two different versions
of Coq (depending on the efficiency you want). (We plan on releasing an updated
opam package soon with the latest additions.)
  
  
In either case, you will also need to
[install the provers](#installationoftheprovers) you want to use and make
some [small configuration changes](#settingupenvironmentforsmtcoq).

## Requirements

You need to have OCaml version >= 4.03.0 and Coq version 8.5pl2. The easiest
way to install these two pieces of software is through opam.

<!-- This branch is not on opam
## Installation via opam (*only for base branch of main fork*)

Simply add the coq-extra-dev repo to opam:
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
and install smtcoq:
```
opam install coq-smtcoq
```
-->

## Installation from the sources

You can <!-- also --> build SMTCoq from the sources, using either Coq 8.5 or
the
[version of Coq with native data-structures](https://github.com/smtcoq/native-coq).
We recommend Coq 8.5 for standard use, and native-coq for uses that require
very efficient computation (such as checking big certificates).

> **Warning**: The version of Coq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.03.0.


### Installation with Coq and OCaml opam packages

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

Now you can install an OCaml compiler (we recommend 4.03.0 or the latest
release):

```bash
opam switch 4.03.0
```

#### Install Coq

After OCaml is installed, you can install Coq through opam (we recommend 8.5.2
because we haven't tested 8.5.3 with SMTCoq yet).

```bash
opam install coq.8.5.2
```

If you also want to install CoqIDE at the same time you can do

```bash
opam install coq.8.5.2 coqide.8.5.2
```

but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).


#### Install SMTCoq

Compile and install SMTCoq by using the commands:

```bash
./configure.sh
make
make install
```

in the src directory.


### Installation with official Coq 8.5 release

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


## Setting up environment for SMTCoq

To use the latest features of SMTCoq, you need to make these configuration
changes:

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

### Using SMTCoq without installing

If you want to use SMTCoq without installing it your Coq installation, you can
tell Coq where to find SMTCoq by adding the following line in the file
`~/.config/coqrc`:

```Coq
Add Rec LoadPath "~/path/to/smtcoq/src" as SMTCoq.
```


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
