module TreeArrangement = struct
  open Tree
  open T

  type name = FN_N5.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type res = (output list * state) * ((name * msg) list)
  type request_id = int
  let systemName : string = "Static Tree Building Protocol"
  let serializeName : name -> string = fun nm -> Printf.sprintf "%d" nm
  let deserializeName : string -> name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

  let init : name -> state = fun n ->
    Obj.magic (coq_Tree_MultiParams.init_handlers (Obj.magic n))
  let handleIO : name -> input -> state -> res =
    fun n i s ->
    Obj.magic (coq_Tree_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))
  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
    Obj.magic (coq_Tree_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let handleTimeout : name -> state -> res = fun _ s -> (([], s), [])
  let setTimeout : name -> state -> float = fun _ _ -> 1.0

  let serializeInput : input -> string = function
    | LevelRequest -> "LevelRequest"
    | Broadcast -> "Broadcast"

  let deserializeInput (s : string) : input option =
    match String.trim s with
    | "LevelRequest" -> Some LevelRequest
    | "Broadcast" -> Some Broadcast
    | _ -> None

  let serializeLevelOption olv : string =
    match olv with
    | Some lv -> string_of_int lv
    | _ -> ""

  let serializeOutput (o : output) : string =
    Printf.sprintf "LevelResponse (%s)" (serializeLevelOption o)

  let serializeMsg : msg -> string = function
    | Fail -> "Fail"
    | Level x -> Printf.sprintf "Level (%s)" (serializeLevelOption x)
    | New -> "New"

  let failMsg = Some Fail

  let newMsg = Some New

  let debug : bool = true

  let debugInput : state -> input -> unit = fun _ inp ->
    Printf.printf "got input %s" (serializeInput inp);
    print_newline ()

  let debugRecv : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "receiving message %s from %s" (serializeMsg msg) (serializeName nm);
    print_newline ()

  let debugSend : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "sending message %s to %s" (serializeMsg msg) (serializeName nm);
    print_newline ()

  let debugTimeout : state -> unit = fun _ -> ()
end
