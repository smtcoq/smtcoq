ZCHAFFSRC=$(wildcard sat*.cnf) hole4.cnf cmu-bmc-barrel6.cnf velev-sss-1.0-05.cnf
VERITSRC=$(wildcard sat*.smt2) hole4.smt2 $(wildcard uf*.smt2) $(wildcard lia*.smt2) $(wildcard let*.smt2)
ZCHAFFLOG=$(ZCHAFFSRC:.cnf=.zlog)
VERITLOG=$(VERITSRC:.smt2=.vtlog)
OBJ=$(ZCHAFFLOG) $(VERITLOG)

COQLIBS?= -R ../src SMTCoq
OPT?=
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC?=$(COQBIN)coqc


all: $(OBJ) Tests_zchaff.vo Tests_verit.vo
zchaff: $(ZCHAFFLOG) Tests_zchaff.vo
verit: $(VERITLOG) Tests_verit.vo
lfsc: Tests_lfsc.vo
logs: $(OBJ)


%.zlog: %.cnf
	./runzchaff.sh $<


%.vtlog: %.smt2
	./runverit.sh $<


%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*


clean:
	rm -rf *~ $(ZCHAFFLOG) $(VERITLOG)
