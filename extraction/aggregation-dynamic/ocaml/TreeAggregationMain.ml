open Printf
open Opts

let () =
  let () =
    try
      parse Sys.argv
    with
    | Arg.Help msg ->
      printf "%s: %s" Sys.argv.(0) msg;
      exit 2
    | Arg.Bad msg ->
      eprintf "%s" msg;
      exit 2
  in
  let () =
    try
      validate ()
    with Arg.Bad msg ->
      eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in
  let module Arr = TreeAggregationArrangement.TreeAggregationArrangement in
  if !debug then
    let module Pms = TreeAggregationArrangement.DebugParams in
    let module Shim = OrderedShim.Shim(Arr(Pms)) in
    let open Shim in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         }
  else
    let module Pms = TreeAggregationArrangement.ProductionParams in
    let module Shim = OrderedShim.Shim(Arr(Pms)) in
    let open Shim in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         }
