open Tree
open TreeNames

module TreeArrangement = struct
  type name = Names.name
  type state = coq_Data
  type input = coq_Input
  type output = coq_Output
  type msg = coq_Msg
  type res = (output list * state) * ((name * msg) list)

  let systemName : string = "Static Tree Building Protocol"

  let serializeName : name -> string = Serialization.serializeName

  let deserializeName : string -> name option = Serialization.deserializeName

  let init : name -> state = fun n ->
    Obj.magic (coq_Tree_MultiParams.init_handlers (Obj.magic n))

  let handleIO : name -> input -> state -> res =
    fun n i s ->
    Obj.magic (coq_Tree_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handleNet : name -> name -> msg -> state -> res =
    fun dst src m s ->
    Obj.magic (coq_Tree_MultiParams.net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let setTimeout : name -> state -> float = fun _ _ -> 1.0
    
  let deserializeMsg : string -> msg = Serialization.deserializeMsg

  let serializeMsg : msg -> string = Serialization.serializeMsg

  let deserializeInput = Serialization.deserializeInput

  let serializeOutput = Serialization.serializeOutput

  let failMsg = Some Fail

  let newMsg = None

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

  let debugTimeout : state -> unit = fun _ -> ()
end
