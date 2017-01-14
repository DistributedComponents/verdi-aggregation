opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents http://opam.distributedcomponents.net
opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$MATHCOMP_VERSION \
  coq-mathcomp-fingroup.$MATHCOMP_VERSION coq-mathcomp-algebra.$MATHCOMP_VERSION \
  coq-aac-tactics.$AAC_TACTICS_VERSION StructTact InfSeqExt verdi \
  verdi-runtime ounit.2.0.0 uuidm.0.9.6 --yes --verbose

case $MODE in
  analytics)
    ./build.sh proofalytics
    ;;
  tree-test)
    ./build.sh tree-test
    ;;
  tree-dynamic-test)
    ./build.sh tree-dynamic-test
    ;;
  aggregation-test)
    ./build.sh aggregation-test
    ;;
  aggregation-dynamic-test)
    ./build.sh aggregation-dynamic-test
    ;;
  *)
    ./build.sh
    ;;
esac
