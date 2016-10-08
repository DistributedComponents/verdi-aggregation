Verdi Raft
==========

[![Build Status](https://api.travis-ci.org/uwplse/verdi-raft.svg?branch=master)](https://travis-ci.org/uwplse/verdi-raft)

An implementation of the Raft distributed consensus protocol, verified in Coq using the Verdi framework.

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Verdi`](https://github.com/uwplse/verdi)
 - [`StructTact`](https://github.com/uwplse/StructTact)

Building
--------

First run `./configure` in the root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. By default, it checks for `verdi` 
and `StructTact` in the current parent directory, but this can be
overridden by setting the `Verdi_PATH` and `StructTact_PATH` environment
variables.

Then run `make` in the root directory. This will compile the Raft 
implementation and proof interfaces, and check all the proofs.

Files
-----

The `raft` and `raft-proofs` subdirectories contain the implementation and
verification of Raft. For each proof interface file in `raft`, there is a 
corresponding proof file in `raft-proofs`. The files in the `raft` 
subdirectory include:

- `Raft.v`: an implementation of Raft in Verdi
- `RaftRefinementInterface.v`: an application of the ghost-variable transformer
  to Raft which tracks several ghost variables used in the
  verification of Raft
- `CommonTheorems.v`: several useful theorems about functions used by
  the Raft implementation
- `OneLeaderPerTermInterface`: a statement of Raft's **Election
  safety** property. See also the corresponding proof file in `raft-proofs`.
  - `CandidatesVoteForSelvesInterface.v`, `VotesCorrectInterface.v`, and
    `CroniesCorrectInterface.v`: statements of properties used by the proof
    `OneLeaderPerTermProof.v`
- `LogMatchingInterface.v`: a statement of Raft's *Log Matching*
    property. See also `raft-proofs/LogMatchingProof.v`
  - `LeaderSublogInterface.v`, `SortedInterface.v`, and `UniqueIndicesInterface.v`: statements
   of properties used by `LogMatchingProof.v`

The vard Key-Value Store
------------------------

Requirements:

- `Coq 8.5`
- `ocaml`, `ocamlbuild`

vard is a simple key-value store implemented using
Verdi. vard is specified and verified against Verdi's state-machine
semantics in `VarD.v`. When the Raft transformer is applied, `vard`
can be run as a strongly-consistent, fault-tolerant key-value store
along the lines of etcd. The Coq and Ocaml files necessary to run vard
on real hardware are in `extraction/vard`. Running `make` in that
directory will extract the vard and Raft code, link it against the
Verdi shim and some vard-specific serialization/debugging code, and
compile it all into a `vard.native` binary. Running `make bench-vard`
will produce some benchmark numbers, which are largely meaningless on
localhost (multiple processes writing and fsync-ing to the same disk
and communicating over loopback doesn't accurately model real-world
use cases). Running `make debug` will get you a `tmux` session where
you can play around with a vard cluster in debug mode; look in
`bench/vard.py` for a simple python `vard` client.

As the name suggests, vard is designed to be comparable to the etcd
key-value store (although it currently supports many fewer
features). To that end, we include a very simple etcd "client" which
can be used for benchmarking. Running `make bench-etcd` will run the
vard benchmarks against etcd (although see above for why these results
are not particularly meaningful). See below for instructions to run
both stores on a cluster in order to get a more useful performance
comparison.

Running vard on a cluster
-------------------------

vard doesn't support run-time configuration, so in order to run vard
in another configuration (i.e. on multiple hosts) you'll have to edit
the `extraction/vard/ml/vard.ml` file, specifically the 4 lines starting
with `let nodes = ...`. For instance, to run it on a cluster with ip
addresses `192.168.0.1, 192.168.0.2, 192.168.0.3` you'd edit those
lines to read

    let nodes = [ (1, ("192.168.0.1", 9001))
                ; (2, ("192.168.0.2", 9001))
                ; (3, ("192.168.0.3", 9001))
                ]

The port is the port used for internal communication; the client port
is hard-coded to be `internal-port - 1000` (8001 in this
example). After recompiling with this config, you could run the
benchmarks on a cluster as follows:

    # on 192.168.0.1
    $ ./vard.native 1

    # on 192.168.0.2
    $ ./vard.native 2
    
    # on 192.168.0.3
    $ ./vard.native 3

    # on the client machine
    $ python2 bench/setup.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001"
    $ python2 bench/bench.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001" \
                             --threads 8 --requests 100


Running etcd on a cluster
-------------------------

We can compare vard's numbers to etcd running on the same cluster as
follows:

    # on 192.168.0.1
    $ etcd --name=one \
     --listen-client-urls http://192.168.0.1:8001 \
     --advertise-client-urls http://192.168.0.1:8001 \
     --initial-advertise-peer-urls http://192.168.0.1:9001 \
     --listen-peer-urls http://192.168.0.1:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on 192.168.0.2
    $ etcd --name=two \
     --listen-client-urls http://192.168.0.2:8001 \
     --advertise-client-urls http://192.168.0.2:8001 \
     --initial-advertise-peer-urls http://192.168.0.2:9001 \
     --listen-peer-urls http://192.168.0.2:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on 192.168.0.3
    $ etcd --name=three \
     --listen-client-urls http://192.168.0.3:8001 \
     --advertise-client-urls http://192.168.0.3:8001 \
     --initial-advertise-peer-urls http://192.168.0.3:9001 \
     --listen-peer-urls http://192.168.0.3:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on the client machine
    $ python2 bench/setup.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001"
    $ python2 bench/bench.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001" \
                             --threads 8 --requests 100
