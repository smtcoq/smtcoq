all:
	cd src && $(MAKE)

install: all
	cd src && $(MAKE) install

extrapi: all
	cd src/extraction && $(MAKE) c/libsmtcoqapi.a

extrapi-install: extrapi
	cd src/extraction && $(MAKE) install
