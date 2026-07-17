all:
	dune build theories

install:
	dune build -p rocq-smtcoq
	dune install rocq-smtcoq

test:
	dune build unit-tests

example:
	dune build examples

benchmark:
	dune build benchmarks

clean:
	dune clean
	find . -name "_RocqProject" -delete
	rm -f rocq-smtcoq.install

.PHONY: all install test example benchmark clean
.NOTPARALLEL:
