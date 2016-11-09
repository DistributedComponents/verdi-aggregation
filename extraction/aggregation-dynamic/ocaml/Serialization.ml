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
  | Local x -> sprintf "Local(%d)" (Obj.magic x)
  | SendAggregate -> "SendAggregate"
  | AggregateRequest -> "AggregateRequest"
  | LevelRequest -> "LevelRequest"
  | Broadcast -> "Broadcast"

let deserializeInput (s : string) : coq_Input option =
  match String.trim s with
  | "SendAggregate" -> Some SendAggregate
  | "AggregateRequest" -> Some AggregateRequest
  | "LevelRequest" -> Some LevelRequest
  | "Broadcast" -> Some Broadcast
  | _ -> try sscanf s "Local(%d)" (fun x -> Some (Local (Obj.magic x))) with _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""

let serializeOutput : coq_Output -> string = function
  | AggregateResponse x -> sprintf "AggregateResponse(%d)" (Obj.magic x)
  | LevelResponse olv -> sprintf "LevelResponse(%s)" (serializeLevelOption olv)

let serializeMsg : coq_Msg -> string = function
  | New -> "New"
  | Aggregate x -> sprintf "Aggregate(%d)" (Obj.magic x)
  | Fail -> "Fail"
  | Level olv -> sprintf "Level(%s)" (serializeLevelOption olv)
