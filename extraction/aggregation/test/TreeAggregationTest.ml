open OUnit2

let () =
  run_test_tt_main 
    ~exit
    ("VarD" >:::
	[
          SerializationTest.tests;
	  OptsTest.tests;
	])
