open OUnit2

let () =
  run_test_tt_main 
    ~exit
    ("Z Tree Aggregation" >:::
	[
          SerializationTest.tests;
	  OptsTest.tests
	])
