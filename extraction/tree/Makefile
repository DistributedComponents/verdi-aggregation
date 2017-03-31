OCAMLBUILD = ocamlbuild -package uuidm -package verdi-runtime -I ocaml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

MLEXTRACTED = ocaml/Tree.ml ocaml/Tree.mli

MLFILES = ocaml/TreeArrangement.ml ocaml/TreeMain.ml ocaml/Serialization.ml

MLFILES_TEST = test/SerializationTest.ml test/TreeTest.ml

default: TreeMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/tree/$@

TreeMain.native: $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) TreeMain.native

TreeTest.native: $(MLEXTRACTED) $(MLFILES) $(MLFILES_TEST)
	$(OCAMLBUILD_TEST) TreeTest.native

test: TreeTest.native
	./TreeTest.native

clean:
	ocamlbuild -clean

.PHONY: default clean test $(MLEXTRACTED)

.NOTPARALLEL: TreeMain.native TreeTest.native
.NOTPARALLEL: $(MLEXTRACTED)
