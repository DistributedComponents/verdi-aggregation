set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose
opam pin add coq-mathcomp-ssreflect $SSREFLECT_VERSION --yes --verbose
opam pin add coq-aac-tactics $AAC_TACTICS_VERSION --yes --verbose

opam install coq-mathcomp-fingroup coq-mathcomp-algebra StructTact InfSeqExt verdi --yes --verbose

case $MODE in
  analytics)
    ./build.sh proofalytics
    ;;
  tree-test)
    opam install verdi-runtime ounit.2.0.0 uuidm.0.9.6 --yes --verbose
    ./build.sh tree-test
    ;;
  tree-dynamic-test)
    opam install verdi-runtime ounit.2.0.0 uuidm.0.9.6 --yes --verbose
    ./build.sh tree-dynamic-test
    ;;
  aggregation-test)
    opam install verdi-runtime ounit.2.0.0 uuidm.0.9.6 --yes --verbose
    ./build.sh aggregation-test
    ;;
  aggregation-dynamic-test)
    opam install verdi-runtime ounit.2.0.0 uuidm.0.9.6 portaudio.0.2.1 --yes --verbose
    ./build.sh aggregation-dynamic-test
    ;;
  *)
    ./build.sh
    ;;
esac
