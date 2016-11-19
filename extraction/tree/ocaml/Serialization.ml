open Str
open Printf
open Scanf
open Tree
open TreeNames
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
  | "Broadcast" -> Some Broadcast
  | "LevelRequest" -> Some (LevelRequest (char_list_of_string c))
  | _ -> None

let serializeLevelOption olv : string =
  match olv with
  | Some lv -> string_of_int lv
  | _ -> "-"

let serializeOutput : coq_Output -> string * string = function
  | LevelResponse (c, olv) -> (string_of_char_list c, sprintf "LevelResponse %s" (serializeLevelOption olv))

let debugSerializeInput : coq_Input -> string = function
  | Broadcast -> "Broadcast"
  | LevelRequest x -> sprintf "LevelRequest %d" (Obj.magic x)

let debugSerializeMsg : coq_Msg -> string = function
  | Fail -> "Fail"
  | Level olv -> sprintf "Level %s" (serializeLevelOption olv)
