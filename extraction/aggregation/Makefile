OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ocaml -cflag -g
OCAMLBUILD_TEST = ocamlbuild -package oUnit -lib str -I ocaml -I test -cflag -g

AGGREGATION = ocaml/TreeAggregation.ml ocaml/TreeAggregation.mli \
 ocaml/TreeAggregationArrangement.ml ocaml/TreeAggregationMain.ml ocaml/Serialization.ml
AGGREGATION_TEST = test/SerializationTest.ml test/TreeAggregationTest.ml
LIB = lib/OrderedMain.ml lib/OrderedShim.ml

default: TreeAggregationMain.native

TreeAggregationMain.native: $(AGGREGATION) $(LIB)
	$(OCAMLBUILD) TreeAggregationMain.native

TreeAggregationTest.native: $(AGGREGATION) $(AGGREGATION_TEST)
	$(OCAMLBUILD_TEST) TreeAggregationTest.native

test: TreeAggregationTest.native
	./TreeAggregationTest.native

clean:
	$(OCAMLBUILD) TreeAggregationMain.native -clean
	$(OCAMLBUILD_TEST) TreeAggregationTest.native -clean

.PHONY: default clean test
