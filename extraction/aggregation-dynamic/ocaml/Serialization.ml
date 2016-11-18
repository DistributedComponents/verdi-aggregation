open Str
open Printf
open Scanf
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

let deserializeInput (s : string) (client_id : int) : coq_Input option =
  match String.trim s with
  | "SendAggregate" -> Some SendAggregate
  | "Broadcast" -> Some Broadcast
  | "AggregateRequest" -> Some (AggregateRequest client_id)
  | "LevelRequest" -> Some (LevelRequest client_id)
  | _ -> 
    try sscanf s "Local %d" (fun x -> Some (Local (Obj.magic x))) 
    with _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""

let serializeOutput : coq_Output -> int * string = function
  | AggregateResponse (client_id, x) -> (client_id, sprintf "AggregateResponse %d" (Obj.magic x))
  | LevelResponse (client_id, olv) -> (client_id, sprintf "LevelResponse %s" (serializeLevelOption olv))

let debugSerializeInput : coq_Input -> string = function
  | SendAggregate -> "SendAggregate"
  | Broadcast -> "Broadcast"
  | AggregateRequest x -> sprintf "AggregateRequest %d" (Obj.magic x)
  | Local x -> sprintf "Local %d" (Obj.magic x)
  | LevelRequest x -> sprintf "LevelRequest %d" (Obj.magic x)

let debugSerializeMsg : coq_Msg -> string = function
  | New -> "New"
  | Aggregate x -> sprintf "Aggregate %d" (Obj.magic x)
  | Fail -> "Fail"
  | Level olv -> sprintf "Level %s" (serializeLevelOption olv)
