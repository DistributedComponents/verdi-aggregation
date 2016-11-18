open Printf
open Opts

module TreeShim = OrderedShim.Shim(TreeArrangement.TreeArrangement)

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

  let open TreeShim in
  main { cluster = !cluster
       ; me = !me
       ; port = !port
       }
