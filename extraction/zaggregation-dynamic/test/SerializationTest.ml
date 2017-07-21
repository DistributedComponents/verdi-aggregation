open OUnit2
open ListLabels

let tear_down () text_ctxt = ()

let test_deserialize_name text_ctxt =
  assert_equal (Some 5) (Serialization.deserializeName "5")

let test_list =
  [
    "deserialize name", test_deserialize_name;
  ]

let tests =
  "Serialization" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
