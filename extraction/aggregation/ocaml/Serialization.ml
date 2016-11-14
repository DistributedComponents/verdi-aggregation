open Str
open Printf
open Scanf
open TreeAggregation
open TreeAggregationNames

let serializeName : Names.name -> string = fun nm -> sprintf "%d" nm

let deserializeName : string -> Names.name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

let serializeInput : coq_Input -> string = function
  | SendAggregate -> "SendAggregate"
  | Broadcast -> "Broadcast"
  | AggregateRequest x -> Printf.sprintf "AggregateRequest %d" (Obj.magic x)
  | Local x -> Printf.sprintf "Local %d" (Obj.magic x)
  | LevelRequest x -> Printf.sprintf "LevelRequest %d" (Obj.magic x)

let deserializeInput (s : string) (client_id : int) : coq_Input option =
  match s with
  | "SendAggregate" -> Some SendAggregate
  | "Broadcast" -> Some Broadcast
  | "AggregateRequest" -> Some (AggregateRequest client_id)
  | "LevelRequest" -> Some (LevelRequest client_id)
  | _ -> 
    try Scanf.sscanf s "Local %d" (fun x -> Some (Local (Obj.magic x)))
    with _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> "-"

let serializeOutput : coq_Output -> int * string = function
  | AggregateResponse (client_id, x) -> (client_id, Printf.sprintf "AggregateResponse %d" (Obj.magic x))
  | LevelResponse (client_id, olv) -> (client_id, Printf.sprintf "LevelResponse %s" (serializeLevelOption olv))

let serializeMsg : coq_Msg -> string = function
  | Aggregate x -> Printf.sprintf "Aggregate %d" (Obj.magic x)
  | Fail -> "Fail"
  | Level olv -> Printf.sprintf "Level %s" (serializeLevelOption olv)
