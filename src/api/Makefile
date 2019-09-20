# This is to be used with coq-8.9.O only for the moment

PROGRAM=example

COQTOP=$(COQBIN)../

FLAGS=-rectypes
COMPILEFLAGS=-cclib -lunix

SMTLIB=-I .. -I ../zchaff -I ../verit -I ../trace -I ../smtlib2 -I ../lia -I ../euf -I ../cnf -I ../versions/standard -I ../../3rdparty/alt-ergo
COQLIB=-I ${COQTOP}kernel -I ${COQTOP}lib -I ${COQTOP}library -I ${COQTOP}parsing -I ${COQTOP}pretyping -I ${COQTOP}interp -I ${COQTOP}proofs -I ${COQTOP}tactics -I ${COQTOP}toplevel -I ${COQTOP}plugins/btauto -I ${COQTOP}plugins/cc -I ${COQTOP}plugins/decl_mode -I ${COQTOP}plugins/extraction -I ${COQTOP}plugins/field -I ${COQTOP}plugins/firstorder -I ${COQTOP}plugins/fourier -I ${COQTOP}plugins/funind -I ${COQTOP}plugins/micromega -I ${COQTOP}plugins/nsatz -I ${COQTOP}plugins/omega -I ${COQTOP}plugins/quote -I ${COQTOP}plugins/ring -I ${COQTOP}plugins/romega -I ${COQTOP}plugins/rtauto -I ${COQTOP}plugins/setoid_ring -I ${COQTOP}plugins/syntax -I ${COQTOP}plugins/xml -I /usr/lib/ocaml/camlp5

CMXA=nums.cmxa str.cmxa unix.cmxa gramlib.cmxa dynlink.cmxa ${COQTOP}kernel/byterun/coq_fix_code.o ${COQTOP}kernel/byterun/coq_interp.o ${COQTOP}kernel/byterun/coq_memory.o ${COQTOP}kernel/byterun/coq_values.o lib.cmxa kernel.cmxa library.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa tactics.cmxa toplevel.cmxa
# CMI=example.cmi
CMX=../smtlib2/smtlib2_genConstr.cmx ../trace/smtBtype.cmx example.cmx

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
