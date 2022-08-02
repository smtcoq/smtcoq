# List of user's files and name of the final program (edit this part)

USERFILES=smtcoq.ml
# USERFILES=test.ml
PROGRAM=smtcoq


# Compilation

LIB=smtcoq_extr.cmx

COQLIBPATH=$(shell ocamlfind query coq-core)/

FLAGS=-rectypes
COMPILEFLAGS=-for-pack Smtcoq_extr
PROGRAMFLAGS=-cclib -lunix -linkall
LIBFLAGS=-cclib -lunix -pack

SMTLIB=-I ..

COQCMX=unix.cmxa threads.cmxa nums.cmxa str.cmxa zarith.cmxa dynlink.cmxa findlib.cmxa findlib_dynload.cmxa clib.cmxa config.cmxa boot.cmxa lib.cmxa coqworkmgrapi.cmxa gramlib.cmxa kernel.cmxa library.cmxa engine.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa printing.cmxa tactics.cmxa vernac.cmxa sysinit.cmxa stm.cmxa toplevel.cmxa ltac_plugin.cmxa micromega_plugin.cmxa coqrun.cmxa
SMTCOQCMX=smtcoq_plugin.cmx

MLIFILES=sat_checker.mli zchaff_checker.mli smt_checker.mli verit_checker.mli
MLFILES=sat_checker.ml zchaff_checker.ml smt_checker.ml verit_checker.ml
CMI=$(MLIFILES:%.mli=%.cmi)
CMX=$(MLFILES:%.ml=%.cmx)

USERMLI=$(filter %.mli,$(USERFILES))
USERML=$(filter %.ml,$(USERFILES))
USERCMI=$(USERMLI:%.mli=%.cmi)
USERCMX=$(USERML:%.ml=%.cmx)

COQUNITS=kernel lib library parsing pretyping interp proofs tactics toplevel \
         clib gramlib engine config printing vernac stm coqworkmgrapi sysinit \
         boot vm plugins.ltac plugins.micromega

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLFIND=ocamlfind
OCAMLFINDLIB=-thread -package zarith,num,findlib $(foreach x,$(COQUNITS),-package coq-core.$(x))


all: $(LIB) $(PROGRAM)

%.cmi: %.mli
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFINDLIB) -c $(FLAGS) $(SMTLIB) $<

%.cmx: %.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLFINDLIB) -c $(FLAGS) $(COMPILEFLAGS) $(SMTLIB) $<

$(LIB): $(CMI) $(CMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) -o $@ $(LIBFLAGS) $(CMX)

$(PROGRAM): $(LIB) $(USERCMI) $(USERCMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) -o $@ $(PROGRAMFLAGS) $(COQCMX) $(SMTCOQCMX) $(LIB) $(USERCMX)


.PHONY: clean mrproper


clean:
	rm -f *.cmi *.cmx *.o

mrproper: clean
	rm -rf $(PROGRAM)
