native:
	ocamlbuild -r -tags annot,bin_annot -libs nums lfsctosmtcoq.native

byte:
	ocamlbuild -r -tags annot,bin_annot -libs nums lfsctosmtcoq.d.byte

prof:
	ocamlbuild -r -tags annot,bin_annot,profile -tag profile -libs nums lfsctosmtcoq.native

clean:
	ocamlbuild -clean
