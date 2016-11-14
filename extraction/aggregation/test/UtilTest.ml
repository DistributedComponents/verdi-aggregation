open OUnit2
open ListLabels

let tear_down () text_ctxt = ()

let test_raw_bytes_of_int test_ctxt =
  assert_equal 10 (Util.int_of_raw_bytes (Util.raw_bytes_of_int 10))

let test_list =
  [
    "raw bytes of int", test_raw_bytes_of_int;
  ]

let tests =
  "Util" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
