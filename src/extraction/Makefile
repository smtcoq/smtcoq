# List of user's files and name of the final program (edit this part)

USERFILES=smtcoq.ml smtcoq.mli
PROGRAM=smtcoq
# USERFILES=test.ml
# PROGRAM=test
# USERFILES=../../../../examples/example.ml
# PROGRAM=../../../../examples/example


# Compilation

COQLIBPATH=$(shell coqtop -where)/

FLAGS=-rectypes
COMPILEFLAGS=-cclib -lunix

SMTLIB=-I .. -I ../zchaff -I ../verit -I ../trace -I ../smtlib2 -I ../lia -I ../euf -I ../cnf -I ../../3rdparty/alt-ergo
COQLIB=-I ${COQLIBPATH}kernel -I ${COQLIBPATH}lib -I ${COQLIBPATH}library -I ${COQLIBPATH}parsing -I ${COQLIBPATH}pretyping -I ${COQLIBPATH}interp -I ${COQLIBPATH}proofs -I ${COQLIBPATH}tactics -I ${COQLIBPATH}toplevel -I ${COQLIBPATH}plugins/btauto -I ${COQLIBPATH}plugins/cc -I ${COQLIBPATH}plugins/decl_mode -I ${COQLIBPATH}plugins/extraction -I ${COQLIBPATH}plugins/field -I ${COQLIBPATH}plugins/firstorder -I ${COQLIBPATH}plugins/fourier -I ${COQLIBPATH}plugins/funind -I ${COQLIBPATH}plugins/micromega -I ${COQLIBPATH}plugins/nsatz -I ${COQLIBPATH}plugins/omega -I ${COQLIBPATH}plugins/quote -I ${COQLIBPATH}plugins/ring -I ${COQLIBPATH}plugins/romega -I ${COQLIBPATH}plugins/rtauto -I ${COQLIBPATH}plugins/setoid_ring -I ${COQLIBPATH}plugins/syntax -I ${COQLIBPATH}plugins/xml -I /usr/lib/ocaml/camlp5

CMXA=nums.cmxa str.cmxa unix.cmxa gramlib.cmxa dynlink.cmxa ${COQLIBPATH}kernel/byterun/coq_fix_code.o ${COQLIBPATH}kernel/byterun/coq_interp.o ${COQLIBPATH}kernel/byterun/coq_memory.o ${COQLIBPATH}kernel/byterun/coq_values.o clib.cmxa lib.cmxa kernel.cmxa library.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa tactics.cmxa toplevel.cmxa micromega_plugin.cmxa smtcoq.cmxa
CMI=sat_checker.cmi zchaff_checker.cmi smt_checker.cmi # verit_checker.cmi
CMX=sat_checker.cmx zchaff_checker.cmx smt_checker.cmx verit_checker.cmx
USERML=$(filter %.ml,$(USERFILES))
USERCMX=$(USERML:%.ml=%.cmx)
USERMLI=$(filter %.mli,$(USERFILES))
USERCMI=$(USERMLI:%.mli=%.cmi)

OCAMLC=ocamlc
OCAMLOPT=ocamlopt


all: $(PROGRAM)

%.cmi: %.mli
	$(OCAMLC) -c $(FLAGS) $(SMTLIB) $(COQLIB) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(FLAGS) $(SMTLIB) $(COQLIB) $<

$(PROGRAM): $(CMI) $(CMX) $(USERCMI) $(USERCMX)
	$(OCAMLOPT) $(FLAGS) $(SMTLIB) $(COQLIB) -o $@ $(COMPILEFLAGS) $(CMXA) $(CMX) $(USERCMX)


.PHONY: clean mrproper


clean:
	rm -f *.cmi *.cmx *.o

mrproper: clean
	rm -rf $(PROGRAM)
