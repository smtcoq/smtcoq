# Proofs
## Axioms

No axiom should be added. No library adding axioms should be imported,
except:
- Int63 and Array, used in core SMTCoq
- ProofIrrelevance, to be used with care (it is currently used only to
  treat equality over bit vectors and functional arrays, which are
  implemented as dependent types).


## Hints

Every hint should be put in a hint database, whose name starts with
"smtcoq_". There should be a different database for each part of SMTCoq
(e.g., one for each theory). The general database that is used across
the project is named `smtcoq_core`.


# Code organization
## Documentation
Every OCaml module comes with a documented interface.


# Build system
This project uses `dune` as a build system. A documentation can be found here:
https://dune.readthedocs.io/en/latest/rocq.html
