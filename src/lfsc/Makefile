native:
	ocamlbuild -r -tags annot,bin_annot -libs nums,unix lfsctosmtcoq.native

byte:
	ocamlbuild -r -tags annot,bin_annot -libs nums,unix lfsctosmtcoq.d.byte

prof:
	ocamlbuild -r -tags annot,bin_annot,profile -tag profile -libs nums,unix lfsctosmtcoq.native

clean:
	ocamlbuild -clean
