open OUnit2

let () =
  run_test_tt_main 
    ~exit
    ("Tree Aggregation" >:::
	[
          SerializationTest.tests;
	  OptsTest.tests;
	  UtilTest.tests;
	])
