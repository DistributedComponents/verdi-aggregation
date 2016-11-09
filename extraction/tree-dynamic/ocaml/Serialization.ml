open Str
open Printf
open Tree
open TreeNames

let serializeName : Names.name -> string = fun nm -> sprintf "%d" nm

let deserializeName : string -> Names.name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

let serializeInput : coq_Input -> string = function
  | LevelRequest -> "LevelRequest"
  | Broadcast -> "Broadcast"

let deserializeInput (s : string) : coq_Input option =
  match String.trim s with
  | "LevelRequest" -> Some LevelRequest
  | "Broadcast" -> Some Broadcast
  | _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> ""

let serializeOutput (o : coq_Output) : string =
  sprintf "LevelResponse (%s)" (serializeLevelOption o)

let serializeMsg : coq_Msg -> string = function
  | Fail -> "Fail"
  | Level x -> sprintf "Level (%s)" (serializeLevelOption x)
  | New -> "New"
