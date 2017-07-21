PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -pkgs 'uuidm verdi-runtime' -I ocaml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -pkg oUnit -I test

MLEXTRACTED = ocaml/TreeAggregation.ml ocaml/TreeAggregation.mli
MLFILES = ocaml/TreeAggregationArrangement.ml ocaml/TreeAggregationMain.ml ocaml/Serialization.ml
MLFILES_TEST = test/SerializationTest.ml test/OptsTest.ml test/TreeAggregationTest.ml test/UtilTest.ml

default: TreeAggregationMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/aggregation/$@

TreeAggregationMain.native: $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) TreeAggregationMain.native

TreeAggregationTest.native: $(MLEXTRACTED) $(MLFILES) $(MLFILES_TEST)
	$(OCAMLBUILD_TEST) TreeAggregationTest.native

test-units: TreeAggregationTest.native
	./TreeAggregationTest.native

test-integration: TreeAggregationMain.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units

clean:
	ocamlbuild -clean

.PHONY: default clean test test-units test-integration $(MLEXTRACTED)

.NOTPARALLEL: TreeAggregationMain.native TreeAggregationTest.native
.NOTPARALLEL: $(MLEXTRACTED)
