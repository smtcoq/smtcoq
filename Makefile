native:
	ocamlbuild -libs nums lfsctosmtcoq.native

byte:
	ocamlbuild -libs nums lfsctosmtcoq.d.byte

clean:
	ocamlbuild -clean
