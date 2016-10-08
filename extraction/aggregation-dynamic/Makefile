OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq -cflag -g

default: Tree.native TreeAggregation.native

TreeAggregation.native : coq/TreeAggregation.ml coq/TreeAggregation.mli
	$(OCAMLBUILD) TreeAggregation.native

Tree.native : coq/Tree.ml coq/Tree.mli
	$(OCAMLBUILD) Tree.native

clean:
	$(OCAMLBUILD) Tree.native -clean
	$(OCAMLBUILD) TreeAggregation.native -clean

.PHONY: default clean
