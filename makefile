out/Encode.native: Proto3.fst Encode.fst
	fstar.exe --codegen OCaml --extract Encode --extract Proto3 --odir out Proto3.fst Encode.fst
	cd out; ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Encode.native

run: out/Encode.native
	./out/Encode.native | protoscope

clean: 
	rm out/Encode.native

.PHONY: run clean
