open Portaudio
open Bigarray

let initial_tap_threshold = 0.010

let format = format_int16

let short_normalize = 1.0 /. 32768.0

let channels = 2

let rate = 44100.0

let input_block_time = 0.05

let input_frames_per_block = int_of_float (rate *. input_block_time)

let output_frames_per_block = 256

(* if we get this many noisy blocks in a row, increase the threshold *)
let oversensitive = 15.0 /. input_block_time

(* if we get this many quiet blocks in a row, decrease the threshold *)
let undersensitive = 120.0 /. input_block_time

(* if the noise was longer than this many blocks, it's not a 'tap' *)
let max_tap_blocks = 0.15 /. input_block_time

let device = 5

let open_mic_stream () =
  let interleaved = true in
  let inparam =
    Some { channels = channels 
	 ; device = device 
	 ; sample_format = format 
	 ; latency = 1.0 } in
  open_stream ~interleaved inparam None rate input_frames_per_block []

let open_speaker_stream () =
  let interleaved = true in
  let outparam = 
    Some { channels = channels
	 ; device = device
	 ; sample_format = format
	 ; latency = 1.0 } 
  in
  open_stream ~interleaved None outparam rate input_frames_per_block []

let rec string_of_flat_ba_aux ba i ls =
  if i = 0 then ((string_of_int (Genarray.get ba [|0|])) :: ls)
  else string_of_flat_ba_aux ba (i-1) ((string_of_int (Genarray.get ba [|i|])) :: ls)

let string_of_flat_ba ba =
  let len = Genarray.nth_dim ba 0 in
  let strl = string_of_flat_ba_aux ba (len-1) [] in
  String.concat " " strl

let get_rms ba =
  let sum_squares = ref 0.0 in
  for i = 0 to (Genarray.nth_dim ba 0 - 1) do
    let n = float_of_int (Genarray.get ba [|i|]) *. short_normalize in
    sum_squares := !sum_squares +. (n *. n)
  done;
  sqrt (!sum_squares /. float_of_int (Genarray.nth_dim ba 0))

let () =
  let tap_threshold = ref initial_tap_threshold in
  let noisycount = ref (max_tap_blocks +. 1.0) in
  let quietcount = ref 0.0 in
  Portaudio.init ();
  let in_stream = open_mic_stream () in
  Portaudio.start_stream in_stream;
  let buf = Genarray.create int16_signed c_layout [|channels*input_frames_per_block|] in
  for i = 0 to 1000 do
    Portaudio.read_stream_ba in_stream buf 0 input_frames_per_block;
    let amplitude = get_rms buf in
    (*
    Printf.printf "%.15f" amplitude;
    print_newline (); 
    *)
    if amplitude > !tap_threshold then begin
      (* noisy block *)
      quietcount := 0.0;
      noisycount := !noisycount +. 1.0;
      if !noisycount > oversensitive then 
	tap_threshold := !tap_threshold *. 1.1
    end
    else begin
      (* quiet block *)
      if 1.0 <= !noisycount && !noisycount <= max_tap_blocks then begin
	Printf.printf "Tap!"; print_newline ()
      end;
      noisycount := 0.0;
      quietcount := !quietcount +. 1.0;
      if !quietcount > undersensitive then
	tap_threshold := !tap_threshold *. 0.9      
    end      
  done;
  Portaudio.close_stream in_stream
