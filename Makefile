all:
	dune build theories/SMTCoq.vo

install:
	dune build -p rocq-smtcoq
	dune install rocq-smtcoq

test:
	cd unit-tests && dune build

example:
	cd examples && dune build

clean:
	dune clean
	rm -f rocq-smtcoq.install
	find . -name _RocqProject -delete

.PHONY: all install test example clean
.NOTPARALLEL:
