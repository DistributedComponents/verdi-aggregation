OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ocaml -cflag -g
OCAMLBUILD_TEST = ocamlbuild -package oUnit -lib str -I ocaml -I test -cflag -g

TREE = ocaml/Tree.ml ocaml/Tree.mli ocaml/TreeArrangement.ml ocaml/TreeMain.ml ocaml/Serialization.ml
TREE_TEST = test/SerializationTest.ml test/TreeTest.ml
LIB = lib/OrderedMain.ml lib/OrderedShim.ml

default: TreeMain.native

TreeMain.native: $(TREE) $(LIB)
	$(OCAMLBUILD) TreeMain.native

TreeTest.native: $(TREE) $(TREE_TEST)
	$(OCAMLBUILD_TEST) TreeTest.native

test: TreeTest.native
	./TreeTest.native

clean:
	$(OCAMLBUILD) TreeMain.native -clean
	$(OCAMLBUILD_TEST) TreeTest.native -clean

.PHONY: default clean test
