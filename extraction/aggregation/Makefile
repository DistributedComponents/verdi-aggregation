OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ocaml -cflag -g
TREE_AGGREGATION = ocaml/TreeAggregation.ml ocaml/TreeAggregation.mli \
 ocaml/TreeAggregationArrangement.ml ocaml/TreeAggregationMain.ml
TREE = ocaml/Tree.ml ocaml/Tree.mli ocaml/TreeArrangement.ml ocaml/TreeMain.ml
LIB = lib/OrderedMain.ml lib/OrderedShim.ml

default: TreeMain.native TreeAggregationMain.native

TreeAggregationMain.native: $(TREE_AGGREGATION) $(LIB)
	$(OCAMLBUILD) TreeAggregationMain.native

TreeMain.native: $(TREE) $(LIB)
	$(OCAMLBUILD) TreeMain.native

clean:
	$(OCAMLBUILD) Tree.native -clean
	$(OCAMLBUILD) TreeAggregation.native -clean

.PHONY: default clean
