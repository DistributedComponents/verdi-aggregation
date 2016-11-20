opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$MATHCOMP_VERSION coq-mathcomp-fingroup.$MATHCOMP_VERSION coq-mathcomp-algebra.$MATHCOMP_VERSION ounit.2.0.0 uuidm.0.9.6 --yes --verbose

pushd ..
  git clone 'https://github.com/uwplse/StructTact.git'
  pushd StructTact
    ./build.sh
  popd

  git clone 'https://github.com/DistributedComponents/InfSeqExt.git'
  pushd InfSeqExt
    ./build.sh
  popd

  git clone 'https://github.com/uwplse/verdi.git'
  pushd verdi
    ./build.sh
  popd

  git clone -b v8.5 https://github.com/coq-contribs/aac-tactics.git AAC_tactics
  pushd AAC_tactics
    make
  popd
popd

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
