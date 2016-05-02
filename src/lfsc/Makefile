native:
	ocamlbuild -r -tags annot,bin_annot,rectypes -libs nums,unix -no-hygiene lfsctosmtcoq.native

byte:
	ocamlbuild -r -tags annot,bin_annot,rectypes -libs nums,unix -no-hygiene lfsctosmtcoq.d.byte

prof:
	ocamlbuild -r -tags annot,bin_annot,profile,rectypes -tag profile -libs nums,unix -no-hygiene lfsctosmtcoq.native

clean:
	ocamlbuild -clean
	rm *.cm*
