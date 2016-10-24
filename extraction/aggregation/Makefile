OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ocaml -cflag -g
TREE_AGGREGATION = ocaml/TreeAggregation.ml ocaml/TreeAggregation.mli \
 ocaml/TreeAggregationArrangement.ml ocaml/TreeAggregationMain.ml
LIB = lib/OrderedMain.ml lib/OrderedShim.ml

default: TreeAggregationMain.native

TreeAggregationMain.native: $(TREE_AGGREGATION) $(LIB)
	$(OCAMLBUILD) TreeAggregationMain.native

clean:
	$(OCAMLBUILD) TreeAggregation.native -clean

.PHONY: default clean
