pushd ..
  wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
  tar xf coq-8.5-build-local.tgz
  export PATH=$PWD/coq-8.5/bin:$PATH

  opam init --yes --no-setup
  eval $(opam config env)
  opam install ounit --yes

  git clone 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd

  git clone 'http://github.com/palmskog/InfSeqExt'
  pushd InfSeqExt
    ./build.sh
  popd

  git clone 'http://github.com/uwplse/verdi' verdi-framework
  pushd verdi-framework
    ./build.sh
  popd

  git clone -b v8.5 https://github.com/coq-contribs/aac-tactics.git AAC_tactics
  pushd AAC_tactics
    make
  popd
popd

export Verdi_PATH=../verdi-framework

case $MODE in
  analytics)
    ./script/analytics.sh
    ;;
  tree-test)
    ./script/tree-test.sh
    ;;
  tree-dynamic-test)
    ./script/tree-dynamic-test.sh
    ;;
  aggregation-test)
    ./script/aggregation-test.sh
    ;;
  aggregation-dynamic-test)
    ./script/aggregation-dynamic-test.sh
    ;;
  *)
    ./build.sh
    ;;
esac
