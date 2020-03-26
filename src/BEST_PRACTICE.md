# Proofs
## Axioms

No axiom should be added. No library adding axioms should be imported
(except Int63 and Array).


# Code organization
## Side effects

Tactics and vernacular commands may have a local state, but it should
not be shared between two calls of the tactic/command. See
trace/localState.mli.

When a global state is absolutely required, it should be put in
trace/globalState.mli, and one should follow the instructions given in
[tuto2](https://github.com/coq/coq/tree/master/doc/plugin_tutorial) in
the plugin tutorial.

## Documentation
Every OCaml module comes with a documented interface.

## Theories

Theories are organized in sub-directories whose names are the names of
each theory.

## Compilation

Before pushing or making a pull request to the master branch:
- make sure that the project compiles (`make`) and that the unit tests
  pass (`make test`) with **both** standard and native Coq;
- make sure that the unit tests pass in asynchronous mode with standard
  Coq (`make asynctest`).
