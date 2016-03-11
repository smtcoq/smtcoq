native:
	ocamlbuild -libs nums lfsctosmtcoq.native

byte:
	ocamlbuild -libs nums lfsctosmtcoq.byte

clean:
	ocamlbuild -clean
