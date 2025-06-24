pollux/_build/default/bin/main.exe: pollux/lib/Proto3.ml pollux/lib/Encode.ml pollux/bin/main.ml
	cd pollux; dune build

pollux/lib/%.ml: %.fst
	fstar.exe --codegen OCaml --extract $(basename $?) --odir pollux/lib $? 

run: pollux/_build/default/bin/main.exe
	./pollux/_build/default/bin/main.exe 
	@protoscope msg.bin 
	@rm msg.bin

capture: pollux/_build/default/bin/main.exe
	./pollux/_build/default/bin/main.exe

dump: pollux/_build/default/bin/main.exe
	./pollux/_build/default/bin/main.exe 
	protoscope msg.bin
	@xxd -b msg.bin
	@rm msg.bin

clean: 
	rm msg.bin

.PHONY: run capture dump clean
