PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi Aggregation is only compatible with Coq version 8.5")
endif

COQPROJECT_EXISTS=$(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

CHECKPATH := $(shell ./script/checkpaths.sh)

ifneq ("$(CHECKPATH)","")
$(info $(CHECKPATH))
$(warning checkpath reported an error)
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

proofalytics:
	$(MAKE) -C proofalytics clean
	$(MAKE) -C proofalytics
	$(MAKE) -C proofalytics publish

STDBUF=$(shell [ -x "$$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")

proofalytics-aux: Makefile.coq
	sed "s|^TIMECMD=$$|TIMECMD=$(PWD)/proofalytics/build-timer.sh $(STDBUF) -i0 -o0|" \
	  Makefile.coq > Makefile.coq_tmp
	mv Makefile.coq_tmp Makefile.coq
	$(MAKE) -f Makefile.coq

TREE_MLFILES = extraction/tree/ocaml/Tree.ml extraction/tree/ocaml/Tree.mli

TREE_DYN_MLFILES = extraction/tree-dynamic/ocaml/Tree.ml extraction/tree-dynamic/ocaml/Tree.mli

AGGREGATION_MLFILES = extraction/aggregation/ocaml/TreeAggregation.ml extraction/aggregation/ocaml/TreeAggregation.mli

AGGREGATION_DYN_MLFILES = extraction/aggregation-dynamic/ocaml/TreeAggregation.ml extraction/aggregation-dynamic/ocaml/TreeAggregation.mli

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -no-install \
          -extra '$(TREE_MLFILES)' \
	    'extraction/tree/coq/ExtractTree.v systems/TreeStatic.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/tree/coq/ExtractTree.v' \
          -extra '$(TREE_DYN_MLFILES)' \
            'extraction/tree-dynamic/coq/ExtractTree.v systems/TreeDynamic.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/tree-dynamic/coq/ExtractTree.v' \
          -extra '$(AGGREGATION_MLFILES)' \
	    'extraction/aggregation/coq/ExtractTreeAggregation.v systems/TreeAggregationStatic.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/aggregation/coq/ExtractTreeAggregation.v' \
	  -extra '$(AGGREGATION_DYN_MLFILES)' \
	    'extraction/aggregation-dynamic/coq/ExtractTreeAggregation.v extraction/aggregation-dynamic/coq/ExtractionDeps.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/aggregation-dynamic/coq/ExtractTreeAggregation.v' \
          -extra-phony 'distclean' 'clean' \
	    'rm -f $$(join $$(dir $$(VFILES)),$$(addprefix .,$$(notdir $$(patsubst %.v,%.aux,$$(VFILES)))))'

$(TREE_MLFILES) $(TREE_DYN_MLFILES) $(AGGREGATION_MLFILES) $(AGGREGATION_DYN_MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

tree:
	+$(MAKE) -C extraction/tree

tree-test:
	+$(MAKE) -C extraction/tree test

tree-dynamic:
	+$(MAKE) -C extraction/tree-dynamic

tree-dynamic-test:
	+$(MAKE) -C extraction/tree-dynamic test

aggregation:
	+$(MAKE) -C extraction/aggregation

aggregation-test:
	+$(MAKE) -C extraction/aggregation test

aggregation-dynamic:
	+$(MAKE) -C extraction/aggregation-dynamic

aggregation-dynamic-test:
	+$(MAKE) -C extraction/aggregation-dynamic test

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq distclean; fi
	rm -f Makefile.coq
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean
	$(MAKE) -C extraction/aggregation clean
	$(MAKE) -C extraction/aggregation-dynamic clean
	$(MAKE) -C extraction/tree clean
	$(MAKE) -C extraction/tree-dynamic clean

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick clean lint proofalytics proofalytics-aux distclean \
	$(TREE_MLFILES) $(TREE_DYN_MLFILES) $(AGGREGATION_MLFILES) $(AGGREGATION_DYN_MLFILES) \
	aggregation aggregation-dynamic tree tree-dynamic \
	aggregation-test aggregation-dynamic-test tree-test tree-dynamic-test
