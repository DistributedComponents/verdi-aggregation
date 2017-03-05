open TreeAggregation
open TreeAggregationNames

module TreeAggregationArrangement = struct
  type name = Names.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type client_id = string
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option

  let systemName : string = "Static Tree Aggregation Protocol"

  let serializeName : name -> string = Serialization.serializeName

  let deserializeName : string -> name option = Serialization.deserializeName

  let init : name -> state = fun n ->
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

  let newMsg : msg option = None

  let debug : bool = true

  let debugInput : state -> input -> unit = fun _ inp ->
    Printf.printf "got input %s" (Serialization.debugSerializeInput inp);
    print_newline ()

  let debugRecv : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "receiving message %s from %s" (Serialization.debugSerializeMsg msg) (serializeName nm);
    print_newline ()

  let debugSend : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "sending message %s to %s" (Serialization.debugSerializeMsg msg) (serializeName nm);
    print_newline ()

  let createClientId () = Uuidm.to_string (Uuidm.create `V4)

  let serializeClientId (c : client_id) = c

  let deliverSendAggregateHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic SendAggregate) (Obj.magic s))

  let setSendAggregateTimeout : timeout_setter =
    fun n s ->
      Some 3.0

  let deliverBroadcastHandler : task_handler =
    fun n s ->
      Obj.magic (coq_TreeAggregation_MultiParams.input_handlers (Obj.magic n) (Obj.magic Broadcast) (Obj.magic s))

  let setBroadcastTimeout : timeout_setter =
    fun n s ->
      Some 5.0

  let timeoutTasks = [(deliverSendAggregateHandler, setSendAggregateTimeout); (deliverBroadcastHandler, setBroadcastTimeout)]
end
