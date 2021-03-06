open ZTreeAggregation
open ZTreeAggregationNames

module type Params = sig
  val debug : bool
  val aggregate_timeout : float
  val broadcast_timeout : float
end

module ZTreeAggregationArrangement (P : Params) = struct
  type name = Names.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type client_id = string
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option

  let systemName : string = "Dynamic Z Tree Aggregation Protocol"

  let serializeName : name -> string = Serialization.serializeName

  let deserializeName : string -> name option = Serialization.deserializeName

  let init : name -> state =
    fun n ->
      Obj.magic (coq_ZTreeAggregation_MultiParams.init_handlers (Obj.magic n))

  let handleIO : name -> input -> state -> res =
    fun n i s ->
      Obj.magic (coq_ZTreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
      Obj.magic (coq_ZTreeAggregation_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let deserializeMsg : string -> msg = Serialization.deserializeMsg

  let serializeMsg : msg -> string = Serialization.serializeMsg

  let deserializeInput : string -> client_id -> input option = Serialization.deserializeInput

  let serializeOutput : output -> client_id * string = Serialization.serializeOutput

  let failMsg : msg option = None

  let newMsg : msg option = Some New

  let debug : bool = P.debug

  let debugInput : state -> input -> unit =
    fun _ inp ->
      Printf.printf "[%s] got input %s" (Util.timestamp ()) (Serialization.debugSerializeInput inp);
      print_newline ()

  let debugRecv : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] receiving message %s from %s" (Util.timestamp ()) (Serialization.debugSerializeMsg msg) (serializeName nm);
      print_newline ()

  let debugSend : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] sending message %s to %s" (Util.timestamp ()) (Serialization.debugSerializeMsg msg) (serializeName nm);
      print_newline ()

  let createClientId () : client_id = Uuidm.to_string (Uuidm.create `V4)

  let serializeClientId (c : client_id) : string = c

  let deliverSendAggregateHandler : task_handler =
    fun n s ->
      Obj.magic (coq_ZTreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic SendAggregate) (Obj.magic s))

  let setSendAggregateTimeout : timeout_setter = fun n s -> Some P.aggregate_timeout

  let deliverBroadcastHandler : task_handler =
    fun n s ->
      Obj.magic (coq_ZTreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic Broadcast) (Obj.magic s))

  let setBroadcastTimeout : timeout_setter = fun n s -> Some P.broadcast_timeout

  let timeoutTasks : (task_handler * timeout_setter) list = 
    [
      (deliverSendAggregateHandler, setSendAggregateTimeout);
      (deliverBroadcastHandler, setBroadcastTimeout)
    ]
end
