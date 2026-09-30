# telic-core: any OCaml >= 5.1 builds it; an OxCaml switch (`opam switch
# 5.2.0+ox`, flambda2) is what makes -O3 count. OCAMLFLAGS passes extra
# flags, e.g. linker options for a local toolchain.
OCAMLOPT ?= ocamlopt
OCAMLFLAGS ?=
# Homebrew's OCaml may be built against a newer macOS than the installed SDK
# declares, which leaves dup3 and pipe2 unresolved at link time; the running
# system provides them.
ifeq ($(shell uname -s),Darwin)
PLATFORM_FLAGS := -ccopt -Wl,-U,_dup3 -ccopt -Wl,-U,_pipe2
endif
W := $(shell $(OCAMLOPT) -where)
SRC := json.ml term.ml ir.ml vc.ml smt.ml main.ml

telic-core: $(SRC)
	$(OCAMLOPT) -O3 $(PLATFORM_FLAGS) $(OCAMLFLAGS) -I $(W)/unix $(W)/unix/unix.cmxa $(SRC) -o $@

clean:
	rm -f *.cm* *.o telic-core
