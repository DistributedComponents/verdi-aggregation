module TreeAggregationArrangement = struct
  open TreeAggregation
  open TA

  type name = FN_N5.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type res = (output list * state) * ((name * msg) list)
  type request_id = int
  let systemName : string = "Static Tree Aggregation Protocol"

  let serializeName : name -> string = fun nm -> Printf.sprintf "%d" nm
  let deserializeName : string -> name option = fun s ->
    try Some (int_of_string s)
    with Failure _ -> None

  let init : name -> state = fun n ->
    Obj.magic (coq_TreeAggregation_MultiParams.init_handlers (Obj.magic n))
  let handleIO : name -> input -> state -> res =
    fun n i s ->
    Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))
  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
    Obj.magic (coq_TreeAggregation_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let handleTimeout : name -> state -> res = fun _ s -> (([], s), [])
  let setTimeout : name -> state -> float = fun _ _ -> 1.0

  let serializeInput : input -> string = function
    | Local x -> Printf.sprintf "Local(%d)" (Obj.magic x)
    | SendAggregate -> "SendAggregate"
    | AggregateRequest -> "AggregateRequest"
    | LevelRequest -> "LevelRequest"
    | Broadcast -> "Broadcast"

  let deserializeInput (s : string) : input option =
    match String.trim s with
    | "SendAggregate" -> Some SendAggregate
    | "AggregateRequest" -> Some AggregateRequest
    | "LevelRequest" -> Some LevelRequest
    | "Broadcast" -> Some Broadcast
    | _ -> try Scanf.sscanf s "Local(%d)" (fun x -> Some (Local (Obj.magic x)))
           with _ -> None

  let serializeLevelOption olv : string =
    match olv with
    | Some lv -> string_of_int lv
    | _ -> ""

  let serializeOutput : output -> string = function
    | AggregateResponse x -> Printf.sprintf "AggregateResponse(%d)" (Obj.magic x)
    | LevelResponse olv -> Printf.sprintf "LevelResponse(%s)" (serializeLevelOption olv)

  let serializeMsg : msg -> string = function
    | New -> "New"
    | Aggregate x -> Printf.sprintf "Aggregate(%d)" (Obj.magic x)
    | Fail -> "Fail"
    | Level olv -> Printf.sprintf "Level(%s)" (serializeLevelOption olv)

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

(*
  type name = FN_N5.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type res = (output list * state) * ((name * msg) list)
  type request_id = int
  let init : name -> state = fun n ->
    Obj.magic (coq_TreeAggregation_MultiParams.init_handlers (Obj.magic n))
  let handleIO : name -> input -> state -> res =
    fun n i s ->
    Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))
  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
    Obj.magic (coq_TreeAggregation_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let handleTimeout : name -> state -> res = fun _ s -> (([], s), [])
  let setTimeout : name -> state -> float = fun _ _ -> 1.0

  let deserialize (s : string) : input option =
    match String.trim s with
    | "LevelRequest" -> Some LevelRequest
    | "Broadcast" -> Some Broadcast
    | _ -> None

  let serialize (o : output) : string =
    "LevelResponse (" ^
      (match o with
       | Some n -> string_of_int n
       | _ -> "") ^ ")"

  let debug : bool = true
  let debugRecv : state -> (name * msg) -> unit = fun _ _ -> ()
  let debugSend : state -> (name * msg) -> unit = fun _ _ -> ()
  let debugTimeout : state -> unit = fun _ -> ()
end
 *)
