open Str
open Printf
open Scanf
open TreeAggregation
open TreeAggregationNames
open Util

let serializeName : Names.name -> string = string_of_int

let deserializeName : string -> Names.name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

let deserializeMsg : string -> coq_Msg = fun s ->
  Marshal.from_string s 0

let serializeMsg : coq_Msg -> string = fun msg ->
  Marshal.to_string msg []

let deserializeInput (s : string) (c : string) : coq_Input option =
  match s with
  | "SendAggregate" -> Some SendAggregate
  | "Broadcast" -> Some Broadcast
  | "AggregateRequest" -> Some (AggregateRequest (char_list_of_string c))
  | "LevelRequest" -> Some (LevelRequest (char_list_of_string c))
  | _ -> 
    try Scanf.sscanf s "Local %d" (fun x -> Some (Local (Obj.magic x)))
    with _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""

let serializeOutput : coq_Output -> string * string = function
  | AggregateResponse (c, x) -> (string_of_char_list c, sprintf "AggregateResponse %d" (Obj.magic x))
  | LevelResponse (c, olv) -> (string_of_char_list c, sprintf "LevelResponse %s" (serializeLevelOption olv))

let debugSerializeInput : coq_Input -> string = function
  | SendAggregate -> "SendAggregate"
  | Broadcast -> "Broadcast"
  | AggregateRequest x -> sprintf "AggregateRequest %s" (string_of_char_list x)
  | Local x -> sprintf "Local %d" (Obj.magic x)
  | LevelRequest x -> sprintf "LevelRequest %s" (string_of_char_list x)

let debugSerializeMsg : coq_Msg -> string = function
  | New -> "New"
  | Aggregate x -> sprintf "Aggregate %d" (Obj.magic x)
  | Fail -> "Fail"
  | Level olv -> sprintf "Level %s" (serializeLevelOption olv)
