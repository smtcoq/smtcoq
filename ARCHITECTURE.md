# SMTCoq sources

This document describes the organization of the SMTCoq repository and locations
of source code and modules.

Sources are contained in the directories [src](src) and [theories](theories).
The directories [examples](examples) and [unit-tests](unit-tests) contain
respectively example files of usage for SMTCoq and regression tests for the
different tactics and vernacular commands that the plugin provides.

The rest of the document describes the organization of `src` and `theories`.


## Entry point of SMTCoq
### [SMTCoq.v](theories/SMTCoq.v)

This is the main Rocq entry point, it is meant to be imported by users that
want to use SMTCoq in their Rocq developments. It provides (by exporting) the other
SMTCoq modules as well as declares the OCaml plugin for adding the new
vernacular commands and tactics.


### [extraction](extraction)

This is the extracted version of the SMTCoq checker, that can be run outside
Rocq. It still needs to be fixed for the new additions and extensions.


### Working with user-defined types
#### Decidable equalities, and beyond

The definitions of interpretations of terms and types of SMTCoq requires some
additional constraints that are encoded as Rocq type-classes. A file
contains definitions and properties of these classes
[CompDec.v](theories/utils/CompDec.v) and another one contains predefined useful
instances of these classes
[CompDecInstances.v](theories/structures/CompDecInstances.v).

These classes are:

- `EqbType`: types with a Boolean equality that reflects Leibniz equality
- `OrdType`: class of types with a partial order 
- `Comparable`: augmentation of class of partial order with a compare function
  to obtain a total order
- `Inhabited`: class of inhabited types (used to obtain default values for
  types)
- `CompDec`: a class that merges all previous classes

To use SMTCoq on a user-defined type or a type variable `A`, one needs
to establish or assume an instance of `CompDec A`.


#### Working with various representations of similar mathematical objects

SMTCoq makes use of the builtin theories of SMT solvers. To be able to
do so, it has to recognize some of the types as interpreted, such as
integers for integer arithmetic.

This process is based on the [Trakt
library](https://rocq-trakt.github.io/trakt) and is extensible. For
instance, if one is using a representation of integers that has not been
considered yet in SMTCoq, they can make it interpreted by SMTCoq by
embedding it into the Rocq type `Z`. Examples of the way to build such
an embedding are given [here](theories/tactics/preproc/DatabaseTrakt.v).


## The Rocq checker
### Top-lever checker
#### [MainChecker.v](theories/checker/MainChecker.v)

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


#### [State.v](theories/checker/fol/State.v)

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


#### [Terms.v](theories/checker/fol/Terms.v)

This Rocq module defines reification types for formulas (`Form.form`), types
(`Typ.type`) and atoms/terms (`Atom.atom`). Formulas are given an
interpretation in Rocq's Booleans, types are interpreted in Rocq types (for
instance, type `TZ` is interpreted as Rocq's mathematical integers `Z`) and
atoms are interpreted as Rocq terms of type the interpretation of their type
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


### Theory dedicated checkers (aka small checkers)

The main checker relies on independent checkers which are dedicated to
one SMT theories, and that we call *small cherckers*.

They are organized in sub-directories that reflect the theories
they handle. Small checkers for propositional logic, equality over
uninterpreted functions and linear integer arithmetic all use preexisting
standard Rocq libraries (Bool, Arith, Z, BinPos, ...) to formalize the
underlying interpretation of these theories. The theories of fixed-width
bit-vectors and functional unbounded arrays are formalized in new custom Rocq
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


#### [Conversion into Conjunctive Normal Form](theories/checker/small-checkers/cnf)

Small checkers for CNF (conjunctive normal form) are defined in the module
[CNF.v](theories/checker/small-checkers/cnf/CNF.v). In essence they implement a Tseitin conversion.

For instance, the checker `check_BuildDef` returns a tautology in clausal form
(the validity of the clause is not dependent on the validity of the state) and
the checker `check_ImmBuildDef` is a generic encoding of conversion rules that
have a premise (which appears in the state).


#### [Equality of Uninterpreted Functions](theories/checker/small-checkers/euf)

The checkers for EUF (equality over uninterpreted functions) are defined in the
module [EUF.v](theories/checker/small-checkers/euf/EUF.v).

The first one checks application of the rule of transitivity. `check_trans`
takes as argument the result of the rule application as well as list of
equalities of the form `a = b`, `b = c`, ..., `x = y`, `y = z`.

The other checker takes care of applications of the congruence rule. Functions
in SMT-LIB have a given arity and they are interpreted as Rocq functions. The
checker for congruence can check rule applications with a number of equalities
corresponding to the arity of the function.


#### [Linear Integer Arithmetic](theories/checker/small-checkers/lia)

Checking linear arithmetic lemmas that come from the SMT solver is performed
using the already existing `Micromega` solver of Rocq. The corresponding
checker is implemented in module [LIA.v](theories/checker/small-checkers/lia/LIA.v).


#### [Bitvectors Arithmetic](theories/checker/small-checkers/bva)

The small checkers for bit-vector operations can be found in module
[Bva_checker.v](theories/checker/small-checkers/BVA.v). They implement the rules
for bit-blasting operators of the theory of fixed width bit-vector.

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
[BVList.v](theories/structures/BVList.v). There, bit-vectors are interpreted by
lists of Booleans. The type of bit-vectors is a dependent type:

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


#### [Functional arrays](theories/checker/small-checkers/array)

The theory of unbounded functional arrays with extensionality is realized in
Rocq by a custom type that can be found in
[FArray.v](theories/structures/FArray.v).

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


#### [Silent simplifications](theories/checker/small-checkers/spl)

This directory contains everything related to silent simplifications of input
formulas as well as the Rocq machinery to handle step checkers that use
assumptions (and generate sub-goals).

- [Arithmetic.v](theories/checker/small-checkers/spl/Arithmetic.v): Arithmetic simplifications
- [Operators.v](theories/checker/small-checkers/spl/Operators.v): Simplifications of SMT-LIB 2 operators
  (atomic disequalities and distinct operators)
- [Syntactic.v](theories/checker/small-checkers/spl/Syntactic.v): Flattening and normalization of
  propositional structures
- [Assumptions.v](theories/checker/small-checkers/spl/Assumptions.v): Small checker for assumptions


## Automatic tactics

On top of the checker, we provide tactics in first-order logic to call the
automatic provers on Rocq goals and check their proof witnesses to actually
solve the goals. Thanks to a bit of preprocessing, these tactics can work with
the sort `Prop` as well as the type `bool`, and can deal with similar
representations of mathematical objects, as explained
[here](ARCHITECTURE.md#working-with-various-representations-of-similar-mathematical-objects).


### [Tactics](theories/tactics/Tactics.v)

This file includes a variety of tactics written using the `Ltac` and
`Ltac2` languages, applied to the three solvers supported by SMTCoq:
ZChaff, veriT and CVC4. A fourth tactic combines CVC4 with veriT.

- Tactics starting with `zchaff` solve purely propositional logic goals
  using the ZChaff prover.
- Tactics starting with `verit` solve a combination of equality and
  linear integer arithmetic goals using the veriT prover.
- Tactics starting with `cvc4` solve a combination of equality, linear
  integer arithmetic, bitvectors and arrays goals using the CVC4 prover.
- Tactics starting with `smt` subsumes the `cvc4` and `verit` tactics by
  combining the two.


### [Preprocessing](theories/tactics/preproc)

As explained right above, the SMTCoq tactics perform a bit of
preprocessing to match with usual Rocq objects. This preprocessing
highly relies on the Rocq [Trakt
library](https://rocq-trakt.github.io/trakt).

The [Conversion](theories/tactics/preproc/Conversion.v) file contains
the tactics to preprocess Rocq goals using Trakt.

The [DatabaseTrakt](theories/tactics/preproc/DatabaseTrakt.v) file
contains conversions between various representations of integers and
`Z`, and is meant to be extensible with other representations as well as
with other theories.

Note that Trakt is currently not well suited to deal with some
dependently-typed theories, such as bitvectors whose type is
parameterized by a natural numbers `N` (Trakt will try to convert `N`
into `Z` and the resulting type will be ill-formed).


## OCaml implementation of the plugin

Part of SMTCoq is implemented in OCaml. These concern functionalities
which do not need to be certified such as the reification mechanism, the
parsers, pre-processors
and the definitions of tactics.

This part communicates directly with Rocq by using the OCaml Rocq API.


### [Common parts of the pugin](src/common)

This directory contain the implementation of certificates and the
representation of SMT-LIB formulas in SMTCoq.

[coqTerms.ml](src/common/coqTerms.ml) contains imports from Rocq of terms to
be used directly in OCaml. These include usual Rocq terms but also ones specific
to SMTCoq.

[smtAtom.mli](src/common/smtAtom.mli) contains the definitions for the types
of atoms in SMTCoq but also provides smart constructors for them. The modules
defined in this file have functions to reify Rocq terms in OCaml and to
translate back OCaml atoms and types to their Rocq counterpart interpretation.

[smtForm.mli](src/common/smtForm.mli) plays the same role as `smtAtom` but on
the level of formulas.

[smtCertif.ml](src/common/smtCertif.ml) contains definitions for an OCaml
version of the steps of the certificate. These are the objects that are
constructed when importing a certificate from an SMT solver for instance.

[smtTrace.ml](src/common/smtTrace.ml) contains functions to build the Rocq
version of the certificate from the OCaml one.

[smtCommands.ml](src/common/smtCommands.ml) constitute the bulk of the
implementation of the plugin. It contains the OCaml functions that are used to
build the Rocq vernacular commands (`Verit_checker`, `Lfsc_checker`, ...) and
the tactics. It also contains functions to reconstruct Rocq counter-examples
from models returned by the SMT solver.

[smtCnf.ml](src/common/smtCnf.ml) implements a CNF conversion on the type of
SMTCoq formulas.

[smtMisc.ml](src/common/smtMisc.ml) contains miscellaneous functions used in
the previous modules.



### [Communicating with the solvers through the SMT-LIB2 format (from Alt-Ergo)](3rdparty/alt-ergo)

This directory contains utilities to communicate directly with SMT
solvers. This includes a lexer/parser for the SMT-LIB 2 format
([smtlib2_parse.mly](3rdparty/alt-ergo/smtlib2_parse.mly)) a conversion module
from SMT-LIB 2 to formulas and atoms of SMTCoq
([smtlib2_genConstr.ml](3rdparty/alt-ergo/smtlib2_genConstr.ml)) and a way to call
and communicate with SMT solvers through pipes
([smtlib2_solver.mli](3rdparty/alt-ergo/smtlib2_solver.mli)).

The parser and the lexer are coming from the SMT solver Alt-Ergo.


### [ZChaff](src/zchaff)

Files in this directory allow to call the SAT solver ZChaff. It contains a
parser for the sat solver input files and ZChaff certificates. The
implementation for the Rocq tactic `zchaff_bool` can be found in
[zchaff.ml](src/zchaff/zchaff.ml).


### [veriT](src/verit)

This directory contains the necessary modules to support the SMT solver veriT.
In particular it contains a parser for the format of certificates of veriT
([parser.mly](src/verit/parser.mly)) and an intermediate representation of those
certificates ([syntax.mli](src/verit/syntax.mli)). This module also implements a
conversion function from veriT certificates to SMTCoq format of certificates.
This pre-processor is a simple one-to-one conversion.

The file ([verit.ml](src/verit/verit.ml)) contains the functions to invoke
veritT and create SMT-LIB 2 scripts. This is used by the definition of the
tactic `verit_bool` of the same file.


### [LFSC](src/lfsc)

This directory contains the pre-processor for LFSC proofs to SMTCoq certificates
(as well as veriT certificates). The files [ast.ml](src/lfsc/ast.ml) and
[builtin.ml](src/lfsc/builtin.ml) contain an OCaml implementation of a type
checker for LFSC proofs. This directory also contains a parser and lexer for
LFSC (*c.f.*, [parser.mly](src/lfsc/parser.mly)).

The pre-processor is implemented in the module
[converter.ml](src/lfsc/converter.ml)) as a *functor*. Depending on the
module (for terms and clauses conversions) that is passed in the functor
application, we obtain either a pre-processor from LFSC proofs to SMTCoq
certificates directly or a converter from LFSC proofs to veriT certificates.

<!-- TODO -->
<!-- > **Note:** You can obtain a standalone version of the converter by -->
<!-- > issuing `make` in this directory, after having issued `make` in the -->
<!-- > `src` directory. This produces a binary `lfsctosmtcoq.native` that can -->
<!-- > be run with an LFSC proof as argument and produces a veriT certificate -->
<!-- > on the standard output. Such a proof can be built using the script -->
<!-- > `tests/runcvc4.sh`. -->

Finally, the tactic `cvc4_bool` is implemented in the file
[lfsc.ml](src/lfsc/lfsc.ml)). It contains functions to call the SMT solver CVC4,
convert its proof and call the base tactic of `smtCommands`.
