# List of user's files and name of the final program (edit this part)

# USERFILES=smtcoq.ml
# USERFILES=test.ml
USERFILES=testapi.ml
PROGRAM=smtcoq


# Compilation

LIB=ocaml/smtcoq_extr.cmx

COQLIBPATH=$(shell ocamlfind query coq-core)/

FLAGS=-rectypes
COMPILEFLAGS=-for-pack Smtcoq_extr
PROGRAMFLAGS=-linkall
LIBFLAGS=-pack

SMTLIB=-I ..
CURLIB=-I ocaml

COQCMX=unix.cmxa threads.cmxa nums.cmxa str.cmxa zarith.cmxa dynlink.cmxa findlib.cmxa findlib_dynload.cmxa clib.cmxa config.cmxa boot.cmxa coqperf.cmxa lib.cmxa coqworkmgrlib.cmxa gramlib.cmxa kernel.cmxa library.cmxa engine.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa printing.cmxa tactics.cmxa vernac.cmxa sysinit.cmxa stm.cmxa toplevel.cmxa ltac_plugin.cmxa micromega_plugin.cmxa coqrun.cmxa
SMTCOQCMX=smtcoq_plugin.cmx

MLIFILES=ocaml/utils.mli ocaml/sat_checker.mli ocaml/zchaff_checker.mli ocaml/smt_checker.mli ocaml/smt_utils.mli ocaml/verit_checker.mli ocaml/api.mli ocaml/debug_checker.mli
MLFILES=ocaml/utils.ml ocaml/sat_checker.ml ocaml/zchaff_checker.ml ocaml/smt_checker.ml ocaml/smt_utils.ml ocaml/verit_checker.ml ocaml/api.ml ocaml/debug_checker.ml
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


CLIB=c/libsmtcoqapi.a
CH=c/types.h c/checker.h
CPROG=cprog

all: $(LIB) $(PROGRAM) $(CLIB) $(CPROG)

%.cmi: %.mli
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFINDLIB) -c $(FLAGS) $(SMTLIB) $(CURLIB) $<

%.cmx: %.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLFINDLIB) -c $(FLAGS) $(COMPILEFLAGS) $(SMTLIB) $(CURLIB) $<

$(LIB): $(CMI) $(CMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(CURLIB) -o $@ $(LIBFLAGS) $(CMX)

$(PROGRAM): $(LIB) $(USERCMI) $(USERCMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(CURLIB) -o $@ $(PROGRAMFLAGS) $(COQCMX) $(SMTCOQCMX) $(LIB) $(USERCMX)


# C API
CFILES=c/checker.c
OFILES=$(CFILES:%.c=%.o)
MLOFILE=c/capicaml.o
CMAIN=main.c

%.o : %.c
	$(OCAMLOPT) -c $<
	mv $(notdir $@) $@

$(CLIB): $(LIB) ocaml/api.cmx $(OFILES)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(CURLIB) -output-obj -o $(MLOFILE) $(PROGRAMFLAGS) $(COQCMX) $(SMTCOQCMX) $(LIB)
	cp `ocamlc -where`/libasmrun.a $(CLIB) && chmod +w $(CLIB)
	ar r $(CLIB) $(MLOFILE) $(OFILES)

$(CPROG): $(CLIB)
	cc -o $(CPROG) -I `ocamlc -where` -L `ocamlc -where` -L `ocamlc -where`/../zarith -L `ocamlc -where`/../coq-core/perf -L `ocamlc -where`/../coq-core/vm $(CMAIN) $(CLIB) -lm -lunix -lthreads -lnums -lcamlstr -lzarith -lgmp -lcoqperf_stubs -lcoqrun_stubs


.PHONY: clean mrproper install smtcoq


smtcoq:
	cd ..
	make
	cd extraction


install: $(CLIB)
	mkdir -p `ocamlc -where`/../smtcoq
	cp $(CH) $(CLIB) `ocamlc -where`/../smtcoq

# To compile after make install:
# cc -o cprog -I `ocamlc -where` -L `ocamlc -where` -L `ocamlc -where`/../zarith -L `ocamlc -where`/../coq-core/perf -L `ocamlc -where`/../coq-core/vm -L `ocamlc -where`/../smtcoq main.c -lsmtcoqapi -lm -lunix -lthreads -lnums -lcamlstr -lzarith -lgmp -lcoqperf_stubs -lcoqrun_stubs


clean:
	rm -f *.cmi *.cmx *.o c/*.o c/*.a ocaml/*.cmi ocaml/*.cmx ocaml/*.o

mrproper: clean
	rm -rf $(PROGRAM) $(CPROG)
