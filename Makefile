native:
	ocamlbuild -r -tags annot,bin_annot -libs nums lfsctosmtcoq.native

byte:
	ocamlbuild -r -tags annot,bin_annot -libs nums lfsctosmtcoq.d.byte

clean:
	ocamlbuild -clean
