
all :
	ocamllex veritLexer.mll       
	menhir --explain veritParser.mly 
	ocamlc -c -rectypes veritParser.mli
	ocamlc -c -rectypes veritLexer.ml

clean :
	rm -f veritLexer.cmo
	rm -f veritParser.mli

.PHONY: all clean
