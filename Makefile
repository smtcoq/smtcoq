all:
	cd src && $(MAKE)

install: all
	cd src && $(MAKE) install
