set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

case $MODE in
  proofalytics)
    opam pin add verdi-aggregation . --yes --verbose --no-action
    opam install verdi-aggregation --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every 9 minutes to prevent a travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 540
    done
    ;;
  aggregation-dynamic)
    opam pin add aggregation-dynamic . --yes --verbose
    ;;
  *)
    opam pin add verdi-aggregation . --yes --verbose
    ;;
esac
