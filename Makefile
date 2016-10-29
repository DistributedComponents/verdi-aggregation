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

TREE_DEPS='extraction/tree/coq/ExtractTree.v systems/TreeStatic.vo'
TREE_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/tree/coq/ExtractTree.v'
TREE_DYN_DEPS='extraction/tree-dynamic/coq/ExtractTree.v systems/TreeDynamic.vo'
TREE_DYN_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/tree-dynamic/coq/ExtractTree.v'

AGGREGATION_DEPS='extraction/aggregation/coq/ExtractTreeAggregation.v systems/TreeAggregationStatic.vo'
AGGREGATION_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/aggregation/coq/ExtractTreeAggregation.v'
AGGREGATION_DYN_DEPS='extraction/aggregation-dynamic/coq/ExtractTreeAggregation.v systems/TreeAggregationDynamic.vo'
AGGREGATION_DYN_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/aggregation-dynamic/coq/ExtractTreeAggregation.v'

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
          -extra 'extraction/tree/ocaml/Tree.ml' $(TREE_DEPS) $(TREE_COMMAND) \
          -extra 'extraction/tree/ocaml/Tree.mli' $(TREE_DEPS) $(TREE_COMMAND) \
          -extra 'extraction/tree-dynamic/ocaml/Tree.ml' $(TREE_DYN_DEPS) $(TREE_DYN_COMMAND) \
          -extra 'extraction/tree-dynamic/ocaml/Tree.mli' $(TREE_DYN_DEPS) $(TREE_DYN_COMMAND) \
          -extra 'extraction/aggregation/ocaml/TreeAggregation.ml' $(AGGREGATION_DEPS) $(AGGREGATION_COMMAND) \
          -extra 'extraction/aggregation/ocaml/TreeAggregation.mli' $(AGGREGATION_DEPS) $(AGGREGATION_COMMAND) \
          -extra 'extraction/aggregation-dynamic/ocaml/TreeAggregation.ml' $(AGGREGATION_DYN_DEPS) $(AGGREGATION_DYN_COMMAND) \
          -extra 'extraction/aggregation-dynamic/ocaml/TreeAggregation.mli' $(AGGREGATION_DYN_DEPS) $(AGGREGATION_DYN_COMMAND)

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject \
	 extraction/aggregation/lib \
	 extraction/aggregation-dynamic/lib \
	 extraction/tree/lib \
	 extraction/tree-dynamic/lib

.PHONY: default quick clean lint proofalytics distclean
