open Opts
open TreeAggregationArrangement

module Shim = OrderedShim.Shim(TreeAggregationArrangement(SerializationIntPair))

let () =
  let () =
    try
      parse Sys.argv
    with
    | Arg.Help msg ->
      Printf.printf "%s: %s" Sys.argv.(0) msg;
      exit 2
    | Arg.Bad msg ->
      Printf.eprintf "%s" msg;
      exit 2
  in
  let () =
    try
      validate ()
    with Arg.Bad msg ->
      Printf.eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in
  let open Shim in
  main { cluster = !cluster
       ; me = !me
       ; port = !port
       }
