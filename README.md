Verdi Aggregation
=================

[![Build Status](https://api.travis-ci.org/palmskog/verdi.svg?branch=aggregation)](https://travis-ci.org/palmskog/verdi)

An implementation of a distributed aggregation protocol, verified in Coq using the Verdi framework.

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Verdi`](https://github.com/uwplse/verdi)
 - [`mathcomp`](https://math-comp.github.io/math-comp/) (`ssreflect`, `fingroup`, `algebra`)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/palmskog/InfSeqExt)
 - [`AAC_tactics`](https://github.com/coq-contribs/aac-tactics) (branch `v8.5`)

Building
--------

First run `./configure` in the root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. 

By default, the script checks for `verdi`, `StructTact`,
`InfSeqExt` and `AAC_tactics` in the current parent directory, but this can be
overridden by setting the `Verdi_PATH`, `StructTact_PATH`, `InfSeqExt_PATH`,
and `AAC_tactics_PATH` environment variables.

Then run `make` in the root directory.
