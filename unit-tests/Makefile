ZCHAFFSRC=$(wildcard sat*.cnf) hole4.cnf cmu-bmc-barrel6.cnf velev-sss-1.0-05.cnf
VERITSRC=$(wildcard sat*.smt2) hole4.smt2 $(wildcard uf*.smt2) $(wildcard lia*.smt2) $(wildcard let*.smt2)
ZCHAFFLOG=$(ZCHAFFSRC:.cnf=.zlog)
VERITLOG=$(VERITSRC:.smt2=.vtlog)
OBJ=$(ZCHAFFLOG) $(VERITLOG)

COQLIBS?= -R ../src SMTCoq
OPT?=
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
VIOFLAG?=-quick
COQC?=$(COQBIN)coqc


all: zchaff verit lfsc
vernac: zchaffv veritv
tactics: zchafft veritt lfsc

zchaff: zchaffv zchafft
zchaffv: $(ZCHAFFLOG) Tests_zchaff_vernac.vo
zchafft: Tests_zchaff_tactics.vo

verit: veritv veritt
veritv: $(VERITLOG) Tests_verit_vernac.vo
veritt: Tests_verit_tactics.vo

lfsc: Tests_lfsc_tactics.vo

logs: $(OBJ)


%.zlog: %.cnf
	./runzchaff.sh $<


%.vtlog: %.smt2
	./runverit.sh $<


%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*


%.vio: %.v logs
	$(COQC) $(VIOFLAG) $(COQDEBUG) $(COQFLAGS) $*


parallel: Tests_zchaff_tactics.vio Tests_verit_tactics.vio Tests_lfsc_tactics.vio
	coqtop -schedule-vio-checking 3 Tests_zchaff_tactics Tests_verit_tactics Tests_lfsc_tactics


clean: cleanvo
	rm -rf *~ $(ZCHAFFLOG) $(VERITLOG)


cleanvo:
	rm -rf *~ *.vo *.glob *.vio
