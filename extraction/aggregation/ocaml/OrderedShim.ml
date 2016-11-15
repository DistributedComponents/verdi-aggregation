open Printf
open Unix
open Util

module M = Marshal

module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type res = (output list * state) * ((name * msg) list)
  val systemName : string
  val serializeName : name -> string
  val deserializeName : string -> name option
  val init : name -> state
  val handleIO : name -> input -> state -> res
  val handleNet : name -> name -> msg -> state -> res
  val setTimeout : name -> state -> float
  val deserializeMsg : string -> msg
  val serializeMsg : msg -> string
  val deserializeInput : string -> int -> input option
  val serializeOutput : output -> int * string
  val failMsg : msg option
  val newMsg : msg option
  val debug : bool
  val debugInput : state -> input -> unit
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> unit
end

module Shim (A: ARRANGEMENT) = struct
  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      }

  type env =
      { cfg : cfg
      ; listen_fd : file_descr
      ; input_fd : file_descr
      ; node_read_fds : (file_descr, A.name) Hashtbl.t
      ; node_write_fds : (A.name, file_descr) Hashtbl.t
      ; failed_nodes : (A.name, unit) Hashtbl.t
      ; mutable fail_msg_queue : A.name list
      ; client_read_fds : (file_descr, int) Hashtbl.t
      ; client_write_fds : (int, file_descr) Hashtbl.t
      }

  type severity =
    | S_info
    | S_error

  exception NodeDisconnect of (severity * string)
  exception ClientDisconnect of (severity * string)

  let get_node_from_name cfg nm : string * int =
    try List.assoc nm cfg.cluster
    with Not_found -> failwith (sprintf "Unknown node name %s" (A.serializeName nm))

  (* Translate node name to TCP socket address *)
  let denote_node (env : env) (name : A.name) : file_descr =
    Hashtbl.find env.node_write_fds name

  (* Translate TCP socket address to node name *)
  let undenote_node (env : env) (fd : file_descr) : A.name =
    Hashtbl.find env.node_read_fds fd

  (* Translate client id to TCP socket address *)
  let denote_client (env : env) (id : int) : file_descr =
    Hashtbl.find env.client_write_fds id

  (* Translate TCP socket address to client id *)
  let undenote_client (env : env) (fd : file_descr) : int =
    Hashtbl.find env.client_read_fds fd

  (* Gets state from the most recent snapshot, or the initial state from the arrangement. *)
  let get_initial_state (cfg : cfg) : A.state =
    A.init (cfg.me)

  (* Initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let port = snd (get_node_from_name cfg cfg.me) in
    let initial_state = get_initial_state cfg in
    let env =
      { cfg = cfg
      ; listen_fd = socket PF_INET SOCK_STREAM 0
      ; input_fd = socket PF_INET SOCK_STREAM 0
      ; node_read_fds = Hashtbl.create 17
      ; node_write_fds = Hashtbl.create 17
      ; failed_nodes = Hashtbl.create 17
      ; fail_msg_queue = []
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      }
    in
    setsockopt env.listen_fd SO_REUSEADDR true;
    setsockopt env.input_fd SO_REUSEADDR true;
    bind env.listen_fd (ADDR_INET (inet_addr_any, port));
    bind env.input_fd (ADDR_INET (inet_addr_any, cfg.port));
    listen env.listen_fd 8;
    listen env.input_fd 8;
    (env, initial_state)

  let string_of_sockaddr (saddr : sockaddr) : string =
    match saddr with
    | ADDR_UNIX path -> (sprintf "unix://%s" path)
    | ADDR_INET (addr, port) -> (sprintf "%s:%d" (string_of_inet_addr addr) port)

  let close_node_conn env fd =
    let node_name = undenote_node env fd in
    Hashtbl.remove env.node_read_fds fd;
    Hashtbl.remove env.node_write_fds node_name;
    Hashtbl.add env.failed_nodes node_name ();
    env.fail_msg_queue <- node_name :: env.fail_msg_queue;
    Unix.close fd

  let close_client_conn env fd =
    let client_id : int = undenote_client env fd in
    Hashtbl.remove env.client_read_fds fd;
    Hashtbl.remove env.client_write_fds client_id;
    Unix.close fd

  let close_and_fail_node env fd reason =
    begin
      try close_node_conn env fd
      with e -> raise (NodeDisconnect (S_error, sprintf "close_node_conn threw: %s" (Printexc.to_string e)))
    end;
    raise (NodeDisconnect (S_info, sprintf "disconnected with reason: %s" reason))

  let close_and_fail_client env fd reason =
    begin
      try close_client_conn env fd
      with e -> raise (ClientDisconnect (S_error, sprintf "close_client_conn threw: %s" (Printexc.to_string e)))
    end;
    raise (ClientDisconnect (S_info, sprintf "disconnected with reason: %s" reason))

  let send_chunk (fd : file_descr) (buf : string) fail_handler : unit =
    let len = String.length buf in
    let n = Unix.send fd (raw_bytes_of_int len) 0 4 [] in
    if n < 4 then
      fail_handler "send_chunk: message header failed to send all at once.";
    let n = Unix.send fd buf 0 len [] in
    if n < len then
      fail_handler (sprintf "send_chunk: message of length %d failed to send all at once." len);
    ()

  let recv_or_close fd buf offs len flags fail_handler =
    let n = recv fd buf offs len flags in
    if n = 0 then
      fail_handler "recv_or_close: other side closed connection.";
    n

  let receive_chunk env (fd : file_descr) fail_handler : bytes =
    let buf4 = Bytes.make 4 '\x00' in
    let n = recv_or_close fd buf4 0 4 [] fail_handler in
    if n < 4 then
      fail_handler "receive_chunk: message header did not arrive all at once.";
    let len = int_of_raw_bytes buf4 in
    let buf = Bytes.make len '\x00' in
    let n = recv_or_close fd buf 0 len [] fail_handler in
    if n < len then
      fail_handler (sprintf "receive_chunk: message of length %d did not arrive all at once." len);
    buf

  let send_on_fd (fd : file_descr) (msg : A.msg) fail_handler : unit =
    send_chunk fd (A.serializeMsg msg) fail_handler

  let add_write_fd env node_name node_addr =
    printf "connecting to %s for the first time..." (A.serializeName node_name);
    print_newline ();
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    connect write_fd node_addr;
    send_chunk write_fd (A.serializeName env.cfg.me) (close_and_fail_node env write_fd);
    begin match A.newMsg with
          | Some m -> send_on_fd write_fd m (close_and_fail_node env write_fd)
          | None -> ()
    end;
    print_endline "...connected!";
    Hashtbl.add env.node_write_fds node_name write_fd;
    write_fd

  let get_node_write_fd env node_name =
    try denote_node env node_name
    with Not_found ->
      if not (Hashtbl.mem env.failed_nodes node_name)
      then
        let (ip, port) = get_node_from_name env.cfg node_name in
        let entry = gethostbyname ip in
        let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
        add_write_fd env node_name node_addr
      else
        failwith "get_node_write_fd: cannot find name"

  let send env ((nm : A.name), (msg : A.msg)) : unit =
    let fd = get_node_write_fd env nm in
    send_on_fd fd msg (close_and_fail_node env fd)

  let output env o =
    let (client_id, out) = A.serializeOutput o in
    let fd =
      try denote_client env client_id
      with Not_found -> failwith "output: failed to find destination" in
    send_chunk fd out (close_and_fail_client env fd)

  let respond env ((os, s), ps) =
    let go p =
      try
        if A.debug then A.debugSend s p;
        send env p
      with e -> printf "respond moving on after exception: %s" (Printexc.to_string e);
                print_newline () in
    List.iter (output env) os;
    List.iter go ps;
    s

  let deliver_msg env state src msg : A.state =
    let state' = respond env (A.handleNet env.cfg.me src msg state) in
    if A.debug then begin
      A.debugRecv state' (src, msg)
    end;
    state'

  let recv_step (env : env) (fd : file_descr) (state : A.state) : A.state =
    let buf = receive_chunk env fd (close_and_fail_node env fd) in
    let src = try undenote_node env fd
              with Not_found ->
                failwith ("recv_step: failed to find source for message (it has probably been marked failed)") in
    let msg = A.deserializeMsg buf in
    deliver_msg env state src msg

  let new_node_conn env =
    printf "new node connection";
    print_newline ();
    let (node_fd, node_addr) = accept env.listen_fd in
    let buf = receive_chunk env node_fd (close_and_fail_node env node_fd) in
    match A.deserializeName buf with
    | Some node_name ->
      Hashtbl.add env.node_read_fds node_fd node_name;
      ignore (get_node_write_fd env node_name);
      printf "done processing new connection from node %s" buf;
      print_newline ()
    | None ->
      printf "failed to deserialize name %s, closing connection" buf;
      Unix.close node_fd

  let new_client_conn env =
    let (client_fd, client_addr) = accept env.input_fd in
    let client_uuid = Uuidm.to_string (Uuidm.create `V4) in
    let client_id = int_of_string ("0x" ^ String.sub client_uuid 0 8) in
    Hashtbl.add env.client_read_fds client_fd client_id;
    Hashtbl.add env.client_write_fds client_id client_fd;
    printf "client %d connected on %s" client_id (string_of_sockaddr client_addr);
    print_newline ()

  let connect_to_nodes env =
    let go (nm, _) =
      try ignore (get_node_write_fd env nm)
      with e -> printf "respond moving on after exception: %s" (Printexc.to_string e);
                print_newline () in
    List.iter go (List.filter (fun (nm,_) -> not (Hashtbl.mem env.failed_nodes nm)) env.cfg.cluster)

  let input_step (fd : file_descr) (env : env) (name : A.name) (state : A.state) =
    let buf = receive_chunk env fd (close_and_fail_client env fd) in
    let client_id : int = undenote_client env fd in
    match A.deserializeInput buf client_id with
    | Some inp ->
      let state' = respond env (A.handleIO name inp state) in
      if A.debug then begin
        A.debugInput state' inp
      end;
      state'
    | None -> 
      failwith (sprintf "input_step could not deserialize: %s" buf)

  let rec eloop (env : env) (state : A.state) : unit =
    let client_read_fds = Hashtbl.fold (fun fd _ acc -> fd :: acc) env.client_read_fds [] in
    let node_read_fds = Hashtbl.fold (fun fd _ acc -> fd :: acc) env.node_read_fds [] in
    let all_fds = env.input_fd :: env.listen_fd :: List.append client_read_fds node_read_fds in
    let (ready_fds, _, _) = select all_fds [] [] (A.setTimeout env.cfg.me state) in
    let state = ref state in
    begin
      try
	match (List.mem env.listen_fd ready_fds,
	       List.mem env.input_fd ready_fds,
	       ready_fds) with
	| (true, _, _) ->
	  new_node_conn env
	| (_, true, _) ->
	  new_client_conn env
	| (_, _, fd :: _) ->
	  if Hashtbl.mem env.client_read_fds fd then
	    state := input_step fd env env.cfg.me !state
	  else
	    state := recv_step env fd !state
	| _ -> 
	  connect_to_nodes env   
      with
      | ClientDisconnect (S_info, reason) -> 
	printf "client info: %s" reason;
	print_newline ()
      | ClientDisconnect (S_error, reason) ->
	printf "client error: %s" reason;
	print_newline ()
      | NodeDisconnect (S_info, reason) -> 
	printf "node info: %s" reason;
	print_newline ()
      | NodeDisconnect (S_error, reason) ->
	printf "node error: %s" reason;
	print_newline ()
    end;
    begin
      match A.failMsg with
      | Some m ->
	begin
	  try List.iter (fun nm -> state := deliver_msg env !state nm m) env.fail_msg_queue
	  with
	  | NodeDisconnect (S_info, reason) ->
	    printf "node info: %s" reason;
	    print_newline ()
	  | NodeDisconnect (S_error, reason) ->
	    printf "node error: %s" reason;
	    print_newline ()
	end
      | None -> ()
    end;
    env.fail_msg_queue <- [];
    eloop env !state

  let main (cfg : cfg) : unit =
    print_endline "ordered shim running setup";
    let (env, initial_state) = setup cfg in
    print_endline "ordered shim ready for action";
    eloop env initial_state

end
