all:
	cd src && ./configure.sh && $(MAKE)

install: all
	cd src && $(MAKE) install
