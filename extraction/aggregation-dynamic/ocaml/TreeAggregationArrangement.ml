open TreeAggregation
open TreeAggregationNames

module type Serializer = sig
  val deserializeInput : string -> string -> coq_Input option
  val serializeOutput : coq_Output -> string * string
  val debugSerializeInput : coq_Input -> string
  val debugSerializeMsg : coq_Msg -> string
end

module TreeAggregationArrangement (P : Serializer) = struct
  type name = Names.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type client_id = string
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float

  let systemName : string = "Dynamic Tree Aggregation Protocol"

  let serializeName : name -> string = Serialization.serializeName

  let deserializeName : string -> name option = Serialization.deserializeName

  let init : name -> state =
    fun n ->
      Obj.magic (coq_TreeAggregation_MultiParams.init_handlers (Obj.magic n))

  let handleIO : name -> input -> state -> res =
    fun n i s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
      Obj.magic (coq_TreeAggregation_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let deserializeMsg : string -> msg = Serialization.deserializeMsg

  let serializeMsg : msg -> string = Serialization.serializeMsg

  let deserializeInput : string -> client_id -> input option = P.deserializeInput

  let serializeOutput : output -> client_id * string = P.serializeOutput

  let failMsg : msg option = Some Fail

  let newMsg : msg option = Some New

  let debug : bool = true

  let debugInput : state -> input -> unit =
    fun _ inp ->
      Printf.printf "[%s] got input %s" (Util.timestamp ()) (P.debugSerializeInput inp);
      print_newline ()

  let debugRecv : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] receiving message %s from %s" (Util.timestamp ()) (P.debugSerializeMsg msg) (serializeName nm);
      print_newline ()

  let debugSend : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] sending message %s to %s" (Util.timestamp ()) (P.debugSerializeMsg msg) (serializeName nm);
      print_newline ()

  let createClientId () : client_id = Uuidm.to_string (Uuidm.create `V4)

  let serializeClientId (c : client_id) : string = c

  let deliverSendAggregateHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic SendAggregate) (Obj.magic s))

  let setSendAggregateTimeout : timeout_setter = fun n s -> 2.0

  let deliverBroadcastHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic Broadcast) (Obj.magic s))

  let setBroadcastTimeout : timeout_setter = fun n s -> 3.0

  let deliverSumSquaresHandler : task_handler =
    fun n s ->
      let sum_squares = Record.read () in
      let local = Obj.magic (Local (Obj.magic (1, sum_squares))) in
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) local (Obj.magic s))

  let setSumSquaresTimeout : timeout_setter = fun n s -> 1.0

  let timeoutTasks : (task_handler * timeout_setter) list = 
    [
      (deliverSendAggregateHandler, setSendAggregateTimeout);
      (deliverBroadcastHandler, setBroadcastTimeout);
      (deliverSumSquaresHandler, setSumSquaresTimeout);
    ]
end
