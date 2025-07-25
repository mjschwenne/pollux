all: verify compile

FSTAR_OPTIONS = --cache_checked_modules --ext optimize_let_vc \
		    --cmi \
	        --odir ocaml/extracted \
			--warn_error -321

FSTAR_EXE ?= fstar.exe

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

NOT_INCLUDED=$(wildcard Pollux.Old.*)

ALL_SOURCE_FILES = $(filter-out $(NOT_INCLUDED), $(wildcard *.fst *.fsti))

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full --extract '* -Prims -FStar' $(ALL_SOURCE_FILES) --output_deps_to $@

depend: .depend

-include .depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

extract: $(ALL_ML_FILES)

ocaml/extracted/%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<)))

compile: extract
	$(MAKE) -C ocaml


install: PREFIX ?= .
install: compile 
	mkdir -p $(PREFIX)/bin
	cp ocaml/_build/default/bin/main.exe $(PREFIX)/bin/pollux.exe

test: compile 
	./ocaml/_build/default/test/test_pollux.exe

clean:
	-rm -rf *.checked .depend bin/*.exe 
	$(MAKE) -C ocaml clean

.PHONY: all verify clean depend compile install
