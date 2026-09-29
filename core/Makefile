# telic-core: build with an OxCaml switch (`opam switch 5.2.0+ox`).
OCAMLOPT ?= ocamlopt
W := $(shell $(OCAMLOPT) -where)
SRC := json.ml term.ml ir.ml vc.ml smt.ml main.ml

telic-core: $(SRC)
	$(OCAMLOPT) -O3 -unboxed-types -I $(W)/unix $(W)/unix/unix.cmxa $(SRC) -o $@ 2>/dev/null || \
	$(OCAMLOPT) -O3 -I $(W)/unix $(W)/unix/unix.cmxa $(SRC) -o $@

clean:
	rm -f *.cm* *.o telic-core
