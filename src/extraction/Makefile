# List of user's files and name of the final program (edit this part)

USERFILES=smtcoq.ml
# USERFILES=test.ml
PROGRAM=smtcoq


# Compilation

LIB=smtcoq_extr.cmx

COQLIBPATH=$(shell coqtop -where)/

FLAGS=-rectypes
COMPILEFLAGS=-for-pack Smtcoq_extr
PROGRAMFLAGS=-cclib -lunix -linkall
LIBFLAGS=-cclib -lunix -pack

SMTLIB=-I ..
COQLIB=-I ${COQLIBPATH}kernel -I ${COQLIBPATH}lib -I ${COQLIBPATH}library -I ${COQLIBPATH}parsing -I ${COQLIBPATH}pretyping -I ${COQLIBPATH}interp -I ${COQLIBPATH}proofs -I ${COQLIBPATH}tactics -I ${COQLIBPATH}toplevel -I ${COQLIBPATH}plugins/btauto -I ${COQLIBPATH}plugins/cc -I ${COQLIBPATH}plugins/decl_mode -I ${COQLIBPATH}plugins/extraction -I ${COQLIBPATH}plugins/field -I ${COQLIBPATH}plugins/firstorder -I ${COQLIBPATH}plugins/fourier -I ${COQLIBPATH}plugins/funind -I ${COQLIBPATH}plugins/micromega -I ${COQLIBPATH}plugins/nsatz -I ${COQLIBPATH}plugins/omega -I ${COQLIBPATH}plugins/quote -I ${COQLIBPATH}plugins/ring -I ${COQLIBPATH}plugins/romega -I ${COQLIBPATH}plugins/rtauto -I ${COQLIBPATH}plugins/setoid_ring -I ${COQLIBPATH}plugins/syntax -I ${COQLIBPATH}plugins/xml -I ${COQLIBPATH}clib -I ${COQLIBPATH}gramlib/.pack -I ${COQLIBPATH}engine -I ${COQLIBPATH}config -I ${COQLIBPATH}printing -I ${COQLIBPATH}vernac -I ${COQLIBPATH}plugins/ltac -I ${COQLIBPATH}stm -I ${COQLIBPATH}kernel/byterun

COQCMX=unix.cmxa threads.cmxa nums.cmxa str.cmxa zarith.cmxa dynlink.cmxa clib.cmxa config.cmxa lib.cmxa gramlib.cmxa kernel.cmxa library.cmxa engine.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa printing.cmxa tactics.cmxa vernac.cmxa stm.cmxa toplevel.cmxa ltac_plugin.cmx micromega_plugin.cmx
SMTCOQCMX=smtcoq_plugin.cmx

MLIFILES=sat_checker.mli zchaff_checker.mli smt_checker.mli verit_checker.mli
MLFILES=sat_checker.ml zchaff_checker.ml smt_checker.ml verit_checker.ml
CMI=$(MLIFILES:%.mli=%.cmi)
CMX=$(MLFILES:%.ml=%.cmx)

USERMLI=$(filter %.mli,$(USERFILES))
USERML=$(filter %.ml,$(USERFILES))
USERCMI=$(USERMLI:%.mli=%.cmi)
USERCMX=$(USERML:%.ml=%.cmx)

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLFIND=ocamlfind
OCAMLFINDLIB=-I +threads -package zarith


all: $(LIB) $(PROGRAM)

%.cmi: %.mli
	$(OCAMLC) -c $(FLAGS) $(SMTLIB) $(COQLIB) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(FLAGS) $(COMPILEFLAGS) $(SMTLIB) $(COQLIB) $<

$(LIB): $(CMI) $(CMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(COQLIB) -o $@ $(LIBFLAGS) $(CMX)

$(PROGRAM): $(LIB) $(USERCMI) $(USERCMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(COQLIB) -o $@ $(PROGRAMFLAGS) $(COQCMX) $(SMTCOQCMX) $(LIB) $(USERCMX)


.PHONY: clean mrproper


clean:
	rm -f *.cmi *.cmx *.o

mrproper: clean
	rm -rf $(PROGRAM)
