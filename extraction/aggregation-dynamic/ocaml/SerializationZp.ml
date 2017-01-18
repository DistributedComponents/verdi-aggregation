open TreeAggregation
open TreeAggregationNames
open Util

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""

let deserializeInput (s : string) (c : string) : coq_Input option =
  match s with
  | "SendAggregate" -> Some SendAggregate
  | "Broadcast" -> Some Broadcast
  | "AggregateRequest" -> Some (AggregateRequest (char_list_of_string c))
  | "LevelRequest" -> Some (LevelRequest (char_list_of_string c))
  | _ -> 
    try Scanf.sscanf s "Local %d" (fun x -> Some (Local (Obj.magic x)))
    with _ -> None

let two_compl x = if x >= 8388608 then -16777216 + x else x

let serializeOutput : coq_Output -> string * string = function
  | AggregateResponse (c, x) -> (string_of_char_list c, Printf.sprintf "AggregateResponse %d" (two_compl (Obj.magic x)))
  | LevelResponse (c, olv) -> (string_of_char_list c, Printf.sprintf "LevelResponse %s" (serializeLevelOption olv))

let debugSerializeInput : coq_Input -> string = function
  | SendAggregate -> "SendAggregate"
  | Broadcast -> "Broadcast"
  | AggregateRequest x -> Printf.sprintf "AggregateRequest %s" (string_of_char_list x)
  | Local x -> Printf.sprintf "Local %d" (two_compl (Obj.magic x))
  | LevelRequest x -> Printf.sprintf "LevelRequest %s" (string_of_char_list x)

let debugSerializeMsg : coq_Msg -> string = function
  | New -> "New"
  | Aggregate x -> Printf.sprintf "Aggregate %d" (two_compl (Obj.magic x))
  | Fail -> "Fail"
  | Level olv -> Printf.sprintf "Level %s" (serializeLevelOption olv)
