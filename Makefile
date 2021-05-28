all:
	cd src && coq_makefile -f _CoqProject -o Makefile && $(MAKE)

install: all
	cd src && $(MAKE) install
