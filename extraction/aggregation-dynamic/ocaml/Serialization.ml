open TreeAggregation
open TreeAggregationNames

let serializeName : Names.name -> string = string_of_int

let deserializeName : string -> Names.name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

let deserializeMsg : string -> coq_Msg = fun s ->
  Marshal.from_string s 0

let serializeMsg : coq_Msg -> string = fun msg ->
  Marshal.to_string msg []

let serializeLevelOption (olv : int option) : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""
