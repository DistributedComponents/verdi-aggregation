open Printf
open Opts

module TreeAggregationShimDebug = OrderedShim.Shim(TreeAggregationArrangement.TreeAggregationArrangement(TreeAggregationArrangement.DebugParams))

module TreeAggregationShimProduction = OrderedShim.Shim(TreeAggregationArrangement.TreeAggregationArrangement(TreeAggregationArrangement.ProductionParams))


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

  if !debug then
    let open TreeAggregationShimDebug in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         }
  else
    let open TreeAggregationShimProduction in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         }
