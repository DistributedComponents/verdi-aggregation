OCAMLBUILD = ocamlbuild -package uuidm -lib str -lib unix -I lib -I ocaml -cflag -g
OCAMLBUILD_TEST = ocamlbuild -package uuidm -package oUnit -lib str -I ocaml -I test -I lib -cflag -g

LIB = lib/OrderedShim.ml lib/Util.ml lib/Opts.ml

TREE = ocaml/Tree.ml ocaml/Tree.mli ocaml/TreeArrangement.ml \
 ocaml/TreeMain.ml ocaml/Serialization.ml

TREE_TEST = test/SerializationTest.ml test/TreeTest.ml

default: TreeMain.native

TreeMain.native: $(LIB) $(TREE)
	$(OCAMLBUILD) TreeMain.native

TreeTest.native: $(LIB) $(TREE) $(TREE_TEST)
	$(OCAMLBUILD_TEST) TreeTest.native

test: TreeTest.native
	./TreeTest.native

clean:
	$(OCAMLBUILD) TreeMain.native -clean
	$(OCAMLBUILD_TEST) TreeTest.native -clean

.PHONY: default clean test

.NOTPARALLEL: TreeMain.native TreeTest.native
