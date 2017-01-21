open TreeAggregation
open TreeAggregationNames
open Util

let deserializeInput (s : string) (c : string) : coq_Input option =
  match s with
  | "SendAggregate" -> Some SendAggregate
  | "Broadcast" -> Some Broadcast
  | "AggregateRequest" -> Some (AggregateRequest (char_list_of_string c))
  | "LevelRequest" -> Some (LevelRequest (char_list_of_string c))
  | _ -> 
    (* should be converted into 0...p-1 range *)
    try Scanf.sscanf s "Local %d %d" (fun x y -> Some (Local (Obj.magic (Obj.magic x, Obj.magic y))))
    with _ -> None

let two_compl x = if x >= 8388608 then -16777216 + x else x

let serializeOutput : coq_Output -> string * string = function
  | AggregateResponse (c, x) -> (string_of_char_list c, Printf.sprintf "AggregateResponse %d %d" (two_compl (fst (Obj.magic x))) (two_compl (snd (Obj.magic x))))
  | LevelResponse (c, olv) -> (string_of_char_list c, Printf.sprintf "LevelResponse %s" (Serialization.serializeLevelOption olv))

let debugSerializeInput : coq_Input -> string = function
  | SendAggregate -> "SendAggregate"
  | Broadcast -> "Broadcast"
  | AggregateRequest x -> Printf.sprintf "AggregateRequest %s" (string_of_char_list x)
  | Local x -> Printf.sprintf "Local %d %d" (two_compl (fst (Obj.magic x))) (two_compl (snd (Obj.magic x)))
  | LevelRequest x -> Printf.sprintf "LevelRequest %s" (string_of_char_list x)

let debugSerializeMsg : coq_Msg -> string = function
  | New -> "New"
  | Aggregate x -> Printf.sprintf "Aggregate %d %d" (two_compl (fst (Obj.magic x))) (two_compl (snd (Obj.magic x)))
  | Fail -> "Fail"
  | Level olv -> Printf.sprintf "Level %s" (Serialization.serializeLevelOption olv)
