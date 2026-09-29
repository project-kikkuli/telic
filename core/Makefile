# telic-core: any OCaml >= 5.1 builds it; an OxCaml switch (`opam switch
# 5.2.0+ox`, flambda2) is what makes -O3 count. OCAMLFLAGS passes extra
# flags, e.g. linker options for a local toolchain.
OCAMLOPT ?= ocamlopt
OCAMLFLAGS ?=
W := $(shell $(OCAMLOPT) -where)
SRC := json.ml term.ml ir.ml vc.ml smt.ml main.ml

telic-core: $(SRC)
	$(OCAMLOPT) -O3 $(OCAMLFLAGS) -I $(W)/unix $(W)/unix/unix.cmxa $(SRC) -o $@

clean:
	rm -f *.cm* *.o telic-core
