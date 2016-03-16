native:
	ocamlbuild -r -libs nums lfsctosmtcoq.native

byte:
	ocamlbuild -r -libs nums lfsctosmtcoq.d.byte

clean:
	ocamlbuild -clean
