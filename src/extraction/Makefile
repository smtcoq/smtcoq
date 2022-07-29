# List of user's files and name of the final program (edit this part)

USERFILES=smtcoq.ml
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
COQLIB=-I ${COQLIBPATH}kernel -I ${COQLIBPATH}lib -I ${COQLIBPATH}library -I ${COQLIBPATH}parsing -I ${COQLIBPATH}pretyping -I ${COQLIBPATH}interp -I ${COQLIBPATH}proofs -I ${COQLIBPATH}tactics -I ${COQLIBPATH}toplevel -I ${COQLIBPATH}plugins/btauto -I ${COQLIBPATH}plugins/cc -I ${COQLIBPATH}plugins/decl_mode -I ${COQLIBPATH}plugins/extraction -I ${COQLIBPATH}plugins/field -I ${COQLIBPATH}plugins/firstorder -I ${COQLIBPATH}plugins/fourier -I ${COQLIBPATH}plugins/funind -I ${COQLIBPATH}plugins/micromega -I ${COQLIBPATH}plugins/nsatz -I ${COQLIBPATH}plugins/omega -I ${COQLIBPATH}plugins/quote -I ${COQLIBPATH}plugins/ring -I ${COQLIBPATH}plugins/romega -I ${COQLIBPATH}plugins/rtauto -I ${COQLIBPATH}plugins/setoid_ring -I ${COQLIBPATH}plugins/syntax -I ${COQLIBPATH}plugins/xml -I ${COQLIBPATH}clib -I ${COQLIBPATH}gramlib/.pack -I ${COQLIBPATH}engine -I ${COQLIBPATH}config -I ${COQLIBPATH}printing -I ${COQLIBPATH}vernac -I ${COQLIBPATH}plugins/ltac -I ${COQLIBPATH}stm -I ${COQLIBPATH}kernel/byterun

CMXA=unix.cmxa threads.cmxa nums.cmxa str.cmxa zarith.cmxa dynlink.cmxa clib.cmxa config.cmxa lib.cmxa gramlib.cmxa kernel.cmxa library.cmxa engine.cmxa pretyping.cmxa interp.cmxa proofs.cmxa parsing.cmxa printing.cmxa tactics.cmxa toplevel.cmxa vernac.cmxa stm.cmxa ltac_plugin.cmx micromega_plugin.cmx
SMTCOQCMX=smtlib2_util.cmx smtlib2_ast.cmx smtlib2_parse.cmx smtlib2_lex.cmx smtMaps.cmx coqInterface.cmx smtMisc.cmx coqTerms.cmx smtCertif.cmx smtTrace.cmx smtBtype.cmx smtForm.cmx smtAtom.cmx smtCnf.cmx satAtom.cmx smtlib2_genConstr.cmx smtCommands.cmx satParser.cmx cnfParser.cmx zchaffParser.cmx zchaff.cmx lia.cmx veritSyntax.cmx veritParser.cmx veritLexer.cmx verit.cmx
CMI=sat_checker.cmi zchaff_checker.cmi smt_checker.cmi verit_checker.cmi
CMX=sat_checker.cmx zchaff_checker.cmx smt_checker.cmx verit_checker.cmx
USERML=$(filter %.ml,$(USERFILES))
USERCMX=$(USERML:%.ml=%.cmx)
USERMLI=$(filter %.mli,$(USERFILES))
USERCMI=$(USERMLI:%.mli=%.cmi)

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLFIND=ocamlfind
OCAMLFINDLIB=-I +threads -package zarith


all: $(PROGRAM)

%.cmi: %.mli
	$(OCAMLC) -c $(FLAGS) $(SMTLIB) $(COQLIB) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(FLAGS) $(SMTLIB) $(COQLIB) $<

$(PROGRAM): $(CMI) $(CMX) $(USERCMI) $(USERCMX)
	$(OCAMLFIND) $(OCAMLOPT) $(FLAGS) $(OCAMLFINDLIB) $(SMTLIB) $(COQLIB) -o $@ $(COMPILEFLAGS) $(CMXA) $(SMTCOQCMX) $(CMX) $(USERCMX)


.PHONY: clean mrproper


clean:
	rm -f *.cmi *.cmx *.o

mrproper: clean
	rm -rf $(PROGRAM)
