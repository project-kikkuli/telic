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

# telic refuses a binary whose source_hash.ml does not match the sources
telic-core: $(SRC)
	printf 'let value = "%s"\n' "$$(cat $(SRC) | { sha256sum 2>/dev/null || shasum -a 256; } | cut -c1-16)" > source_hash.ml
	$(OCAMLOPT) -O3 $(PLATFORM_FLAGS) $(OCAMLFLAGS) -I $(W)/unix $(W)/unix/unix.cmxa source_hash.ml $(SRC) -o $@

clean:
	rm -f *.cm* *.o telic-core source_hash.ml
