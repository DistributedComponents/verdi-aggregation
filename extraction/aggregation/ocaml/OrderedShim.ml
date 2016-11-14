open Printf
open Unix

type bytes = string

module M = Marshal

module Utils = struct
  let raw_bytes_of_int (x : int) : bytes =
    let buf = Bytes.make 4 '\x00' in
    Bytes.set buf 0 (char_of_int (x land 0xff));
    Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
    Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
    Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
    buf

  let int_of_raw_bytes (buf : bytes) : int =
     (int_of_char (Bytes.get buf 0)) lor
    ((int_of_char (Bytes.get buf 1)) lsl 8) lor
    ((int_of_char (Bytes.get buf 2)) lsl 16) lor
    ((int_of_char (Bytes.get buf 3)) lsl 24)
end

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
  val handleTimeout : name -> state -> res
  val setTimeout : name -> state -> float
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
  type client =
      { id   : int
      ; sock : file_descr
      ; addr : sockaddr
      }

  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      }

  type env =
      { cfg : cfg
      ; listen_fd : file_descr
      ; input_fd : file_descr
      ; read_fds : (file_descr, A.name) Hashtbl.t
      ; write_fds : (A.name, file_descr) Hashtbl.t
      ; failed_nodes : (A.name, unit) Hashtbl.t
      ; mutable fail_msg_queue : A.name list
      ; mutable clients : client list
      }

  type severity =
    | S_info
    | S_error

  let get_node_from_name cfg nm : string * int =
    try List.assoc nm cfg.cluster
    with Not_found -> failwith (sprintf "Unknown node name %s" (A.serializeName nm))

  (* Translate node name to TCP socket address *)
  let denote (env : env) (name : A.name) : file_descr =
    Hashtbl.find env.write_fds name

  (* Translate TCP socket address to node name *)
  let undenote (env : env) (fd : file_descr) : A.name =
    Hashtbl.find env.read_fds fd

  (* Gets state from the most recent snapshot, or the initial state from the arrangement. *)
  let get_initial_state (cfg : cfg) : A.state =
    A.init (cfg.me)

  (* Initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let port = snd (get_node_from_name cfg cfg.me) in
    (*
    let addressify (name, (host, port)) =
      let entry = gethostbyname host in
      (name, ADDR_INET (Array.get entry.h_addr_list 0, port))
    in *)
    let initial_state = get_initial_state cfg in
    let env =
      { cfg = cfg
      ; listen_fd = socket PF_INET SOCK_STREAM 0
      ; input_fd = socket PF_INET SOCK_STREAM 0
      ; read_fds = Hashtbl.create 17
      ; write_fds = Hashtbl.create 17
      ; failed_nodes = Hashtbl.create 17
      ; fail_msg_queue = []
      ; clients = []
      }
    in
    setsockopt env.listen_fd SO_REUSEADDR true;
    bind env.listen_fd (ADDR_INET (inet_addr_any, port));
    bind env.input_fd (ADDR_INET (inet_addr_any, cfg.port));
    listen env.listen_fd 8;
    listen env.input_fd 8;
    (env, initial_state)

  let close_neighbor_conn env fd =
    let node_name = undenote env fd in
    Hashtbl.remove env.read_fds fd;
    Hashtbl.remove env.write_fds node_name;
    Hashtbl.add env.failed_nodes node_name ();
    env.fail_msg_queue <- node_name :: env.fail_msg_queue;
    Unix.close fd

  let close_and_fail env fd msg =
    begin
      try close_neighbor_conn env fd
      with e -> printf "close_neighbor_conn threw: %s" (Printexc.to_string e)
    end;
    failwith msg

  let string_of_sockaddr (saddr : sockaddr) : string =
    match saddr with
    | ADDR_UNIX path -> (sprintf "unix://%s" path)
    | ADDR_INET (addr, port) -> (sprintf "%s:%d" (string_of_inet_addr addr) port)

  let disconnect_client env client reason =
    close client.sock;
    env.clients <- List.filter (fun c -> c <> client) env.clients;
    printf "Client %d (%s) disconnected with reason: %s" client.id (string_of_sockaddr client.addr) reason;
    print_newline ()

  let send_chunk env (fd : file_descr) (buf : string) : unit =
    let len = String.length buf in
    let n = Unix.send fd (Utils.raw_bytes_of_int len) 0 4 [] in
    if n < 4 then
      close_and_fail env fd "send_chunk: message header failed to send all at once.";
    let n = Unix.send fd buf 0 len [] in
    if n < len then
      close_and_fail env fd
          (sprintf "send_chunk: message of length %d failed to send all at once." len);
    ()

  let recv_or_close env fd buf offs len flags =
    let n = recv fd buf offs len flags in
    if n = 0 then
      close_and_fail env fd "recv_or_close: other side closed connection.";
    n

  let receive_chunk env (fd : file_descr) : bytes =
    let buf4 = Bytes.make 4 '\x00' in
    let n = recv_or_close env fd buf4 0 4 [] in
    if n < 4 then
      close_and_fail env fd "receive_chunk: message header did not arrive all at once.";
    let len = Utils.int_of_raw_bytes buf4 in
    let buf = Bytes.make len '\x00' in
    let n = recv_or_close env fd buf 0 len [] in
    if n < len then
      close_and_fail env fd
          (sprintf "receive_chunk: message of length %d did not arrive all at once." len);
    buf

  let send_on_fd env (fd : file_descr) (msg : A.msg) : unit =
    send_chunk env fd (M.to_string msg [])

  let add_write_fd env node_name node_addr =
    Printf.printf "Connecting to %s for the first time..." (A.serializeName node_name);
    print_newline ();
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    connect write_fd node_addr;
    send_chunk env write_fd (A.serializeName env.cfg.me);
    begin match A.newMsg with
          | Some m -> send_on_fd env write_fd m
          | None -> ()
    end;
    print_endline "...connected!";
    Hashtbl.add env.write_fds node_name write_fd;
    write_fd

  let get_write_fd env node_name =
    try denote env node_name
    with Not_found ->
      if not (Hashtbl.mem env.failed_nodes node_name)
      then
        let (ip, port) = get_node_from_name env.cfg node_name in
        let entry = gethostbyname ip in
        let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
        add_write_fd env node_name node_addr
      else
        failwith "get_write_fd: cannot find name "

  let send env ((nm : A.name), (msg : A.msg)) : unit =
    send_on_fd env (get_write_fd env nm) msg

  let respond_to_client env client msg =
    try
      ignore (Unix.send client.sock (msg ^ "\n") 0 (String.length msg) [])
    with Unix_error (err, fn, arg) ->
      disconnect_client env client ("Error from send: " ^ (error_message err))

  let output env o =
    let (client_id, out) = A.serializeOutput o in
    let client = 
      try List.find (fun c -> client_id = c.id) env.clients
      with Not_found -> failwith ("output: failed to find destination") in
    respond_to_client env client out

  let unpack_msg buf : A.msg =
    M.from_string buf 0

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
    let chunk = receive_chunk env fd in
    let src = try undenote env fd
              with Not_found ->
                failwith ("recv_step: failed to find source for message! " ^
                          "(probably it has been marked failed)") in
    let msg = unpack_msg chunk in
    deliver_msg env state src msg

  let get_all_read_fds env =
    Hashtbl.fold (fun fd _ acc -> fd :: acc) env.read_fds []

  let new_neighbor_conn env =
    print_endline "new neighbor connection!";
    let (node_fd, node_addr) = accept env.listen_fd in
    let chunk = receive_chunk env node_fd in
    let node_name = match A.deserializeName chunk with
      | Some nm -> nm
      | None -> close_and_fail env node_fd
                    (Printf.sprintf "Failed to deserialize name %s" chunk) in
    Hashtbl.add env.read_fds node_fd node_name;
    ignore (get_write_fd env node_name);
    Printf.printf "done processing new connection from node %s" chunk;
    print_newline ()

  let new_client_conn env =
    let (client_sock, client_addr) = accept env.input_fd in
    let client_uuid = Uuidm.to_string (Uuidm.create `V4) in
    let client_id = int_of_string ("0x" ^ String.sub client_uuid 0 8) in
    let client =
      { id = client_id
      ; sock = client_sock
      ; addr = client_addr
      } in
    env.clients <- client :: env.clients;
    printf "Client %d connected on %s" client_id (string_of_sockaddr client_addr);
    print_newline ()

  let connect_to_neighbors env =
    let go (nm, _) =
      try ignore (get_write_fd env nm)
      with e -> printf "respond moving on after exception: %s" (Printexc.to_string e);
                print_newline () in
    List.iter go env.cfg.cluster

  exception Disconnect_client of (severity * string)

  let input_step (client : client) (env : env) (name : A.name) (state : A.state) =
    let len = 1024 in
    let buf = Bytes.make len '\x00' in
    let n = recv client.sock buf 0 len [MSG_PEEK] in
    if n = 0 then begin
      raise (Disconnect_client (S_info, "client closed socket"))
    end;
    let buf2 = Bytes.make n '\x00' in
    let () = Bytes.blit buf 0 buf2 0 n in
    let msg_len = (Bytes.index buf '\n') + 1 in
    let _ = recv client.sock (Bytes.make msg_len '\x00') 0 msg_len [] in
    match A.deserializeInput buf2 client.id with
    | Some inp ->
       let state' = respond env (A.handleIO name inp state) in
       if A.debug then begin
           A.debugInput state' inp
         end;
       state'
    | None -> failwith (sprintf "input_step could not deserialize: %s" buf2)

  let rec eloop (env : env) (state : A.state) : unit =
    let client_fds = List.map (fun c -> c.sock) env.clients in
    let fds = List.append (env.input_fd :: env.listen_fd :: get_all_read_fds env) client_fds in
    let (ready_fds, _, _) = select fds [] [] (A.setTimeout env.cfg.me state) in
    let state = ref state in
    begin match (List.mem env.listen_fd ready_fds, List.mem env.input_fd ready_fds, List.filter (fun c -> List.mem c.sock ready_fds) env.clients, ready_fds) with
    | (true, _, _, _) ->
      new_neighbor_conn env
    | (_, true, _, _) ->
      new_client_conn env
    | (_, _, client_socket :: _, _) -> begin
      try 
	state := input_step client_socket env env.cfg.me !state
      with
        Unix_error (err, fn, arg) ->
          disconnect_client env client_socket (sprintf "%s failed: %s" fn (error_message err))
      | Disconnect_client (sev, msg) ->
          disconnect_client env client_socket msg
    end
    | (_, _, _, fd :: _) ->
      state := recv_step env fd !state
    | _ -> 
      connect_to_neighbors env
    end;
    begin
      match A.failMsg with
      | Some m ->
         List.iter (fun nm -> state := deliver_msg env !state nm m) env.fail_msg_queue
      | None -> ()
    end;
    env.fail_msg_queue <- [];
    eloop env !state

  let main (cfg : cfg) : unit =
    print_endline "Ordered shim running setup";
    let (env, initial_state) = setup cfg in
    print_endline "Ordered shim ready for action";
    eloop env initial_state
end
