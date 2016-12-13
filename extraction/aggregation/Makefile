PYTHON=python2.7

OCAMLBUILD = ocamlbuild -package uuidm -lib str -lib unix -I ocaml -I lib -cflag -g
OCAMLBUILD_TEST = ocamlbuild -package uuidm -package oUnit -lib str -I ocaml -I test -I lib -cflag -g

LIB = lib/OrderedShim.ml lib/Util.ml lib/Opts.ml lib/Daemon.ml

MLEXTRACTED = ocaml/TreeAggregation.ml ocaml/TreeAggregation.mli

MLFILES = ocaml/TreeAggregationArrangement.ml ocaml/TreeAggregationMain.ml \
 ocaml/Serialization.ml

MLFILES_TEST = test/SerializationTest.ml test/OptsTest.ml \
 test/TreeAggregationTest.ml test/TestCommon.ml

default: TreeAggregationMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/aggregation/$@

TreeAggregationMain.native: $(LIB) $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) TreeAggregationMain.native

TreeAggregationTest.native: $(LIB) $(MLEXTRACTED) $(MLFILES) $(MLFILES_TEST)
	$(OCAMLBUILD_TEST) TreeAggregationTest.native

test-units: TreeAggregationTest.native
	./TreeAggregationTest.native

test-integration: TreeAggregationMain.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units test-integration

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean test test-units test-integration $(MLEXTRACTED)

.NOTPARALLEL: TreeAggregationMain.native TreeAggregationTest.native
.NOTPARALLEL: $(MLEXTRACTED)
