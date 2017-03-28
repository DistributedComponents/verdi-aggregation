Verdi Aggregation
=================

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-aggregation.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-aggregation)

An implementation of a distributed aggregation protocol, verified in Coq using the Verdi framework.

Requirements
------------

Definitions and proofs:

- [`Coq 8.5`](https://coq.inria.fr/coq-85)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`math-comp`](https://math-comp.github.io/math-comp/) (`ssreflect`, `fingroup`, `algebra`)
- [`StructTact`](https://github.com/uwplse/StructTact)
- [`InfSeqExt`](https://github.com/DistributedComponents/InfSeqExt)
- [`AAC_tactics`](https://github.com/coq-contribs/aac-tactics)
- [`verdi-cheerios`](https://github.com/DistributedComponents/verdi-cheerios)

Executable code:

- [`OCaml 4.02.3`](https://ocaml.org)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](http://projects.camlcity.org/projects/findlib.html)
- [`verdi-runtime`](https://github.com/DistributedComponents/verdi-runtime)
- [`Uuidm`](http://erratique.ch/software/uuidm)
- [`PortAudio`](http://www.portaudio.com)
- [`ocaml-portaudio`](https://github.com/savonet/ocaml-portaudio)

Building
--------

First, make sure the PortAudio library is installed on the system; on Ubuntu and Debian systems, the package is called `portaudio19-dev`.

The recommended way to install the OCaml and Coq dependencies of Verdi Aggregation is via [OPAM](https://coq.inria.fr/opam/www/using.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install coq-mathcomp-ssreflect coq-mathcomp-fingroup coq-mathcomp-algebra coq-aac-tactics
opam install verdi StructTact InfSeqExt verdi-cheerios verdi-runtime uuidm portaudio
```

Then, run `./configure` in the root directory.  This will check for the appropriate version of Coq and ensure all necessary dependencies can be located.

By default, the script assumes that `Verdi`, `StructTact`, `InfSeqExt`, and `VerdiCheerios` are installed in Coq's `user-contrib` directory, but this can be overridden by setting the `Verdi_PATH`, `StructTact_PATH`, `InfSeqExt_PATH`, and `VerdiCheerios_PATH` environment variables.

Finally, run `make` in the root directory.
