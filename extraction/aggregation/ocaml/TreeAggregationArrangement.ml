open TreeAggregation
open TreeAggregationNames

module TreeAggregationArrangement = struct
  type name = Names.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type res = (output list * state) * ((name * msg) list)
  type request_id = int
  let systemName : string = "Static Tree Aggregation Protocol"

  let serializeName = Serialization.serializeName
  let deserializeName = Serialization.deserializeName

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

  let serializeInput = Serialization.serializeInput

  let deserializeInput = Serialization.deserializeInput

  let serializeOutput = Serialization.serializeOutput

  let failMsg = Some Fail

  let newMsg = None

  let debug : bool = true

  let debugInput : state -> input -> unit = fun _ inp ->
    Printf.printf "got input %s" (serializeInput inp);
    print_newline ()

  let debugRecv : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "receiving message %s from %s" (Serialization.serializeMsg msg) (serializeName nm);
    print_newline ()

  let debugSend : state -> (name * msg) -> unit = fun _ (nm, msg) ->
    Printf.printf "sending message %s to %s" (Serialization.serializeMsg msg) (serializeName nm);
    print_newline ()

  let debugTimeout : state -> unit = fun _ -> ()
end
