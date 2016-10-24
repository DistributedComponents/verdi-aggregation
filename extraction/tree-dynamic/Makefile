OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ocaml -cflag -g
TREE = ocaml/Tree.ml ocaml/Tree.mli ocaml/TreeArrangement.ml ocaml/TreeMain.ml
LIB = lib/OrderedMain.ml lib/OrderedShim.ml

default: TreeMain.native

TreeMain.native: $(TREE) $(LIB)
	$(OCAMLBUILD) TreeMain.native

clean:
	$(OCAMLBUILD) TreeMain.native -clean

.PHONY: default clean
