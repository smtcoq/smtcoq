# List of user's files and name of the final program (edit this part)

USERFILES=smtcoq.ml smtcoq.mli
PROGRAM=smtcoq
# USERFILES=test.ml
# PROGRAM=test
# USERFILES=../../../../examples/example.ml
# PROGRAM=../../../../examples/example


# Compilation

COQTOP=$(COQBIN)../

FLAGS=-rectypes
COMPILEFLAGS=-cclib -lunix

SMTLIB=-I . -I .. -I ../array -I ../bva -I ../classes -I ../cnf -I ../euf -I ../lfsc -I ../lia -I ../smtlib2 -I ../spl -I ../trace -I ../verit -I ../zchaff -I ../../3rdparty/alt-ergo -I ../versions/native
COQLIB=-I ${COQTOP}kernel -I ${COQTOP}lib -I ${COQTOP}library -I ${COQTOP}parsing -I ${COQTOP}pretyping -I ${COQTOP}interp -I ${COQTOP}proofs -I ${COQTOP}tactics -I ${COQTOP}toplevel -I ${COQTOP}plugins/btauto -I ${COQTOP}plugins/cc -I ${COQTOP}plugins/decl_mode -I ${COQTOP}plugins/extraction -I ${COQTOP}plugins/field -I ${COQTOP}plugins/firstorder -I ${COQTOP}plugins/fourier -I ${COQTOP}plugins/funind -I ${COQTOP}plugins/micromega -I ${COQTOP}plugins/nsatz -I ${COQTOP}plugins/omega -I ${COQTOP}plugins/quote -I ${COQTOP}plugins/ring -I ${COQTOP}plugins/romega -I ${COQTOP}plugins/rtauto -I ${COQTOP}plugins/setoid_ring -I ${COQTOP}plugins/syntax -I ${COQTOP}plugins/xml -I /usr/lib/ocaml/camlp5

CMXA=nums.cmxa str.cmxa unix.cmxa gramlib.cmxa dynlink.cmxa ${COQTOP}kernel/byterun/coq_fix_code.o ${COQTOP}kernel/byterun/coq_interp.o ${COQTOP}kernel/byterun/coq_memory.o ${COQTOP}kernel/byterun/coq_values.o clib.cmxa lib.cmxa kernel.cmxa library.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa tactics.cmxa toplevel.cmxa micromega_plugin.cmxa smtcoq.cmxa
CMI=extrNative.cmi sat_checker.cmi zchaff_checker.cmi smt_checker.cmi verit_checker.cmi
CMX=extrNative.cmx sat_checker.cmx zchaff_checker.cmx smt_checker.cmx verit_checker.cmx
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
