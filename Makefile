all:
	dune build -p rocq-smtcoq

install:
	dune install rocq-smtcoq

test:
	cd unit-tests && dune build

example:
	cd examples && dune build

clean:
	dune clean
	rm -f rocq-smtcoq.install {theories,example,test}/_RocqProject

.PHONY: all install test example clean
.NOTPARALLEL:
