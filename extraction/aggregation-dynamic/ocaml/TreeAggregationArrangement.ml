open TreeAggregation
open TreeAggregationNames

module type TreeAggregationParams = sig
  val debug : bool
  val send_aggregate_timeout : float
  val broadcast_timeout : float
end

module DebugParams = struct
  let debug = true
  let send_aggregate_timeout = 3.0
  let broadcast_timeout = 5.0
end

module ProductionParams = struct
  let debug = false
  let send_aggregate_timeout = 2.0
  let broadcast_timeout = 3.0
end

module TreeAggregationArrangement (P : TreeAggregationParams) = struct
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

  let deserializeInput : string -> client_id -> input option = Serialization.deserializeInput

  let serializeOutput : output -> client_id * string = Serialization.serializeOutput

  let failMsg : msg option = Some Fail

  let newMsg : msg option = Some New

  let debug : bool = P.debug

  let debugInput : state -> input -> unit =
    fun _ inp ->
      Printf.printf "[%s] got input %s\n" (Util.timestamp ()) (Serialization.debugSerializeInput inp)

  let debugRecv : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] receiving message %s from %s\n" (Util.timestamp ()) (Serialization.debugSerializeMsg msg) (serializeName nm)

  let debugSend : state -> (name * msg) -> unit =
    fun _ (nm, msg) ->
      Printf.printf "[%s] sending message %s to %s\n" (Util.timestamp ()) (Serialization.debugSerializeMsg msg) (serializeName nm)

  let createClientId () : client_id = Uuidm.to_string (Uuidm.create `V4)

  let serializeClientId (c : client_id) : string = c

  let deliverSendAggregateHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic SendAggregate) (Obj.magic s))

  let setSendAggregateTimeout : timeout_setter = fun n s -> P.send_aggregate_timeout

  let deliverBroadcastHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic Broadcast) (Obj.magic s))

  let setBroadcastTimeout : timeout_setter = fun n s -> P.broadcast_timeout

  let timeoutTasks : (task_handler * timeout_setter) list = 
    [(deliverSendAggregateHandler, setSendAggregateTimeout); (deliverBroadcastHandler, setBroadcastTimeout)]
end
