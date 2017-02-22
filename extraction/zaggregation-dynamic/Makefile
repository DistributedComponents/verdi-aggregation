PYTHON=python2.7

OCAMLBUILD = ocamlbuild -use-ocamlfind -tag thread -package 'uuidm verdi-runtime' -I ocaml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

MLEXTRACTED = ocaml/ZTreeAggregation.ml ocaml/ZTreeAggregation.mli

MLFILES = ocaml/ZTreeAggregationArrangement.ml ocaml/ZTreeAggregationMain.ml ocaml/Serialization.ml

MLFILES_TEST = test/SerializationTest.ml test/ZTreeAggregationTest.ml test/TestCommon.ml

default: ZTreeAggregationMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/zaggregation-dynamic/$@

ZTreeAggregationMain.native: $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) ZTreeAggregationMain.native

ZTreeAggregationTest.native: $(MLEXTRACTED) $(MLFILES) $(MLFILES_TEST)
	$(OCAMLBUILD_TEST) ZTreeAggregationTest.native

test-units: ZTreeAggregationTest.native
	./ZTreeAggregationTest.native

test-integration: ZTreeAggregationMain.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean test test-units test-integration $(MLEXTRACTED)

.NOTPARALLEL: ZTreeAggregationMain.native ZTreeAggregationTest.native
.NOTPARALLEL: $(MLEXTRACTED)
