Verdi Aggregation
=================

An implementation of a distributed aggregation protocol, verified in Coq using the Verdi framework.

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Verdi`](https://github.com/uwplse/verdi)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/palmskog/InfSeqExt)

Building
--------

First run `./configure` in the root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. By default, it checks for `verdi`, `StructTact`,
and `InfSeqExt` in the current parent directory, but this can be
overridden by setting the `Verdi_PATH`, `StructTact_PATH`, and 
`InfSeqExt_PATH` environment variables.

Then run `make` in the root directory.
