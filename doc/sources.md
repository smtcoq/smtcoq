# SMTCoq sources

This document describes the organization of the SMTCoq repository and locations
of source code and modules.

Sources are contained in the directory [src](../src) which can be found at
top-level. The directories [examples](../examples) and
[unit-tests](../unit-tests) contain respectively example files of usage for
SMTCoq and regression tests for the different tactics and vernacular commands
that the plugin provides.

The rest of the document describes the organization of `src`.


## Top-level architecture of SMTCoq

SMTCoq sources are contained in this directory. A few Coq files can be found at
top-level.

### [configure.sh](../src/configure.sh)

This script is meant to be run when compiling SMTCoq for the first time. It
should also be run every time the Makefile is modified. It takes as argument an
optional flag `-native` which, when present, will set up the sources to use the
*native Coq* libraries. Otherwise the standard version 8.5 of Coq is used. See
section [versions](#versions).

### [SMTCoq.v](../src/SMTCoq.v)

This is the main SMTCoq entry point, it is meant to be imported by users that
want to use SMTCoq in their Coq developments. It provides (exports) the other
SMTCoq modules as well as declares the OCaml plugin for adding the new
vernacular commands and tactics.

### [Trace.v](../src/Trace.v)

This file defines the types of certificates and steps (atomic certificate
pieces) as well as the *main checkers*.

The first section `trace` gives a generic definition of a main checker
parameterized by the type of individual steps and a function to check
individual steps `check_step` (small checkers). Correctness of the main checker
is proved under the assumption that the small checker is correct.

These generic definitions are applied to construct main checkers for resolution
(module `Sat_Checker`), CNF conversion (module `Cnf_Checker`) and
satisfiability modulo theories (module `Euf_Checker`). They each define an
inductive type `step` to represent certificate steps. For instance, in the case
of the resolution checker, the only possible step is to apply the resolution
rule so steps are defined as:

```coq
Inductive step :=
   | Res (_:int) (_:resolution).
```

The main theorems for these modules are named `checker_*correct`. For instance
the main result for the SMT checker (`Euf_Checker`) is formulated as follows:

```coq
Lemma checker_correct : forall d used_roots c,
    checker d used_roots c = true ->
    ~ valid t_func t_atom t_form d.
```

which means that if the checker returns true on the formula `d` and the
certificate `c` then `d` is not valid (*i.e.* `c` is a refutation proof
certificate for `d`).



### [State.v](../src/State.v)

This module is used to define representations for the global state of the
checker. 

A state is an array of clauses:

```coq
Module S.
  Definition t := array C.t.
...
End S.
```

on which we define resolution chain operations `set_resolve` that modify the
state.

Variables, literals and clauses are defined respectively in modules `Var`,
`Lit` and `C`. Binary resolution is defined between two clauses in `C.resolve`.



### [SMT_terms.v](../src/SMT_terms.v)

This Coq module defines reification types for formulas (`Form.form`), types
(`Typ.type`) and atoms/terms (`Atom.atom`). Formulas are given an
interpretation in Coq's Booleans, types are interpreted in Coq types (for
instance, type `TZ` is interpreted as Coq's mathematical integers `Z`) and
atoms are interpreted as Coq terms of type the interpretation of their type
(for instance an atom whose type is `TZ` is interpreted as an integer of `Z`).


**Some important lemmas:**

A function `cast` allows to change the encoded type of a term of type
`Typ.type` when we know two types are equal (the inductive `cast_result`
provides the conversion function).

```coq
Fixpoint cast_refl A:
      cast A A = Cast (fun P (H : P A) => H).
```

This is the lemma to use to remove cast constructions during the proofs.



```coq
Lemma i_eqb_spec : forall t x y, i_eqb t x y <-> x = y.
```

This other lemma says that Boolean equality over interpretation of types is the
equivalent to Leibniz equality. This is useful to allow rewriting.


Atom (as well as formulas) are encoded by integers, and mapping is preserved by
an array `t_atom`. Another array maintains interpretations of encodings. The
following lemma states that these two relates:

```coq
Lemma t_interp_wf : forall i,
   t_interp.[i] = interp_aux (PArray.get t_interp) (t_atom.[i]).
```




### [Misc.v](../src/Misc.v)

This module contains miscellaneous general lemmas that are used in several
places throughout the development of SMTCoq.


### [versions](../src/versions)

This directory contains everything that is dependent on the version of Coq that
one wants to use. `standard` contains libraries for the standard version of Coq
and `native` contains everything related to native Coq. Note that some
libraries are already present in the default libraries of native Coq, in this
case they have a counterpart in `standard` that replicates the functionality
(without using native integers or native arrays).

A particular point of interest is the files
[smtcoq_plugin_standard.ml4](../src/versions/standard/smtcoq_plugin_standard.ml4)
and
[smtcoq_plugin_native.ml4](../src/versions/native/smtcoq_plugin_native.ml4). They
provide extension points for Coq by defining new vernacular commands and new
tactics. For instance the tactic `verit` tells Coq to call the OCaml function
`verit.tactic` (which in turns uses the Coq API to manipulate the goals and
call the certified checkers).

```ocaml
TACTIC EXTEND Tactic_verit
| [ "verit" ] -> [ Verit.tactic () ]
END
```



### [spl](../src/spl)

This directory contains everything related to simplifications of input
formulas as well as the Coq machinery to handle step checkers that use
assumptions (and generate sub-goals).

- [Arithmetic.v](../src/spl/Arithmetic.v): Arithmetic simplifications
- [Operators.v](../src/spl/Operators.v): Simplifications of SMT-LIB 2 operators
  (atomic disequalities and distinct operators)
- [Syntactic.v](../src/spl/Syntactic.v): Flattening and normalization of
  propositional structures
- [Assumptions.v](../src/spl/Assumptions.v): Small checker for assumptions



### [extraction](../src/extraction)

This is the extracted version of the SMTCoq checker, that can be run outside
Coq. It still needs to be fixed for the new additions and extensions.



### [classes](../src/classes)


The definitions of interpretations of terms and types of SMTCoq requires some
additional constraints that are encoded as Coq type-classes. This directory
contains definitions and properties of these classes
[SMT_classes.v](../src/classes/SMT_classes.v) as well as predefined useful
instances of these classes
[SMT_classes_instances.v](../src/classes/SMT_classes_instances.v).

These classes are:

- `EqbType`: types with a Boolean equality that reflects in Leibniz equality
- `DecType`: types with a decidable equality
- `OrdType`: class of types with a partial order 
- `Comparable`: augmentation of class of partial order with a compare function
  to obtain a total order
- `Inhabited`: class of inhabited types (used to obtain default values for
  types)
- `CompDec`: a class that merges all previous classes



## Small checkers

Small Coq checkers are organized in sub-directories that reflect the theories
they handle. Small checkers for propositional logic, equality over
uninterpreted functions and linear integer arithmetic all use preexisting
standard Coq libraries (Bool, Arith, Z, BinPos, ...) to formalize the
underlying interpretation of these theories. The theories of fixed-width
bit-vectors and functional unbounded arrays are formalized in new custom Coq
libraries (that are distributed with SMTCoq).


Computational small checkers have the following signature:

```coq
Definition checker (s : S.t) (p1 ... pn : int) (l1 ... lm : lit) : C.t := ...
```

where `s` is the state of the main checker, `p1`, ..., `pn` are positions
(there can be none) of deduced clauses that appear in the state `s` and `l1`,
..., `lm` are literals. The function `checker` returns a clause that is
`deducible` from the already deduced clauses in the state `s`.

Correctness of checkers are specified (and proven) through lemmas of the form:

```coq
Lemma valid_checker : forall s rho p1 ... pm l1 ... lm,
                      C.valid rho (checker s p1 ... pm l1 ... lm).
```

It states that the clause returned by `checker` is valid. In most cases for the
small checkers, when they fail they return a trivially true clause (`C._true`).


### [cnf](../src/cnf)

Small checkers for CNF (conjunctive normal form) are defined in the module
[Cnf.v](../src/cnf/Cnf.v). In essence they implement a Tseitin conversion.

For instance, the checker `check_BuildDef` returns a tautology in clausal form
(the validity of the clause is not dependent on the validity of the state) and
the checker `check_ImmBuildDef` is a generic encoding of conversion rules that
have a premise (which appears in the state).



### [euf](../src/euf)

The checkers for EUF (equality over uninterpreted functions) are defined in the
module [Euf.v](../src/euf/Euf.v).

The first one checks application of the rule of transitivity. `check_trans`
takes as argument the result of the rule application as well as list of
equalities of the form `a = b`, `b = c`, ..., `x = y`, `y = z`.

The other checker takes care of applications of the congruence rule. Functions
in SMT-LIB have a given arity and they are interpreted as Coq functions. The
checker for congruence can check rule applications with a number of equalities
corresponding to the arity of the function.


### [lia](../src/lia)

Checking linear arithmetic lemmas that come from the SMT solver is performed
using the already existing `Micromega` solver of Coq. The corresponding
checker is implemented in module [Lia.v](../src/lia/Lia.v).





### [bva](../src/bva)

The small checkers for bit-vector operations can be found in module
[Bva_checker.v](../src/bva/Bva_checker.v). They implement the rules for
bit-blasting operators of the theory of fixed width bit-vector.

There are small checkers for:

- bit-wise operators (`bvand`, `bvor`, `bvxor`, `bvnot`)
- equality
- variables
- constants
- extraction
- concatenation
- arithmetic operations (addition, negation, multiplication)
- comparison predicates (signed/unsigned)
- extensions (zero/signed)


The theory of fixed width is realized by an implementation provided in
[BVList.v](../src/bva/BVList.v). There, bit-vectors are interpreted by lists of
Booleans. The type of bit-vectors is a dependent type:

```coq
Parameter bitvector : N -> Type.
```

In the implementation, a bit-vector is a record that contains a list of
Booleans `bv`, *i.e.* the lists of its bits, as well as a proof of well
formedness `wf`, *i.e.* a proof that the size of the list `bv` is the parameter
`n` of the type.

```coq
Record bitvector_ (n:N) : Type :=
    MkBitvector
      { bv :> M.bitvector;
        wf : M.size bv = n
      }.
```



### [array](../src/array)

The theory of unbounded functional arrays with extensionality is realized in
Coq by a custom type that can be found in [FArray.v](../src/array/FArray.v).

```coq
Definition farray (key elt : Type) _ _  :=
```

The type `farray` is parameterized by the type of keys (or indexes) of the
array and the type of the elements. `key` must be a type equipped with a
partial order and `elt` must be inhabited. 


```coq
Record slist :=
  {this :> Raw.farray key elt;
   sorted : sort (Raw.ltk key_ord) this;
   nodefault : NoDefault this
   }.
   
Definition farray := slist.
```

An array is represented internally by an association list for its mappings with
additional constraints that encode the fact that the list is sorted and that
there are no mapping to the default value.

Computable equality and comparison functions require additional constraints on
the types `key` and `elt` (for instance they need to have a total order,
*etc.*).

This library also provides useful properties on these arrays. Notably
extensionality which is required by the theory of arrays in SMT solvers:

```coq
Lemma extensionnality : forall a b, (forall i, select a i = select b i) -> a = b.
```

The extensionality rule that is used by the checker is a bit different and
requires classical axioms to be proven. This is done in section
```Classical_extensionnality``` which provides an alternative version without
contaminating uses of the library.

There are three small checkers for arrays. They check application of the axioms
(in the theory sense) of the theory of arrays, two for *read over write* and
one for *extensionality*



## OCaml implementation of the plugin

Part of SMTCoq is implemented in OCaml. These concern functionality which are
not certified such as the reification mechanism, the parsers, pre-processors
and the definitions of tactics.

This part communicates directly with Coq by using the OCaml Coq API.


### [trace](../src/trace)

This directory contain the implementation of certificates and the
representation of SMT-LIB formulas in SMTCoq.

[coqTerms.ml](../src/trace/coqTerms.ml) contains imports from Coq of terms to
be used directly in OCaml. These include usual Coq terms but also ones specific
to SMTCoq.

[smtAtom.mli](../src/trace/smtAtom.mli) contains the definitions for the types
of atoms in SMTCoq but also provides smart constructors for them. The modules
defined in this file have functions to reify Coq terms in OCaml and to
translate back OCaml atoms and types to their Coq counterpart interpretation.

[smtForm.mli](../src/trace/smtForm.mli) plays the same role as `smtAtom` but on
the level of formulas.

[smtCertif.ml](../src/trace/smtCertif.ml) contains definitions for an OCaml
version of the steps of the certificate. These are the objects that are
constructed when importing a certificate from an SMT solver for instance.

[smtTrace.ml](../src/trace/smtTrace.ml) contains functions to build the Coq
version of the certificate from the OCaml one.

[smtCommands.ml](../src/trace/smtCommands.ml) constitute the bulk of the
implementation of the plugin. It contains the OCaml functions that are used to
build the Coq vernacular commands (`Verit_checker`, `Lfsc_checker`, ...) and
the tactics. It also contains functions to reconstruct Coq counter-examples
from models returned by the SMT solver.

[smtCnf.ml](../src/trace/smtCnf.ml) implements a CNF conversion on the type of
SMTCoq formulas.

[smtMisc.ml](../src/trace/smtMisc.ml) contains miscellaneous functions used in
the previous modules.



### [smtlib2](../src/smtlib2)

This directory contains utilities to communicate directly with SMT
solvers. This includes a lexer/parser for the SMT-LIB 2 format
([smtlib2_parse.mly](../src/smtlib2/smtlib2_parse.mly)) a conversion module
from SMT-LIB 2 to formulas and atoms of SMTCoq
([smtlib2_genConstr.ml](../src/smtlib2/smtlib2_genConstr.ml)) and a way to call
and communicate with SMT solvers through pipes
([smtlib2_solver.mli](../src/smtlib2/smtlib2_solver.mli)).



### [zchaff](../src/zchaff)

Files in this directory allow to call the SAT solver ZChaff. It contains a
parser for the sat solver input files and ZChaff certificates. The
implementation for the Coq tactic `zchaff` can be found in
[zchaff.ml](../src/zchaff/zchaff.ml).



### [verit](../src/verit)

This directory contains the necessary modules to support the SMT solver veriT.
In particular it contains a parser for the format of certificates of veriT
([veritParser.mly](../src/verit/veritParser.mly)) and an intermediate
representation of those certificates
([veritSyntax.mli](../src/verit/veritSyntax.mli)). This module also implements
a conversion function from veriT certificates to SMTCoq format of
certificates. This pre-processor is a simple one-to-one conversion.

The file ([verit.ml](../src/verit/verit.ml)) contains the functions to invoke
veritT and create SMT-LIB 2 scripts. This is used by the definition of the
tactic `verit` of the same file.



### [lfsc](../src/lfsc)

This directory contains the pre-processor for LFSC proofs to SMTCoq
certificates (as well as veriT certificates). The files
[ast.ml](../src/lfsc/ast.ml) and [builtin.ml](../src/lfsc/builtin.ml) contain
an OCaml implementation of a type checker for LFSC proofs. This directory also
contains a parser and lexer for LFSC (*c.f.*,
[lfscParser.mly](../src/lfsc/lfscParser.mly)).

The pre-processor is implemented in the module
[converter.ml](../src/lfsc/converter.ml)) as a *functor*. Depending on the
module (for terms and clauses conversions) that is passed in the functor
application, we obtain either a pre-processor from LFSC proofs to SMTCoq
certificates directly or a converter from LFSC proofs to veriT certificates.

> **Note:** You can obtain a standalone version of the converter by issuing
> `make` in this directory. This produces a binary `lfsctosmtcoq.native` that
> can be run with an LFSC proof as argument and produces a veriT certificate
> on the standard output.

Finally, the tactic `cvc4` is implemented in the file
[lfsc.ml](../src/lfsc/lfsc.ml)). It contains functions to call the SMT solver
CVC4, convert its proof and call the base tactic of `smtCommands`.
