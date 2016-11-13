open Printf
open Opts

module TreeAggregationShim = OrderedShim.Shim(TreeAggregationArrangement.TreeAggregationArrangement)

let _ =
  let  _ = parse Sys.argv in

  let _ =
    try
      validate ()
    with Arg.Bad msg ->
      eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in

  let open TreeAggregationShim in
  main { cluster = !cluster
       ; me = !me
       ; port = !port
       }
