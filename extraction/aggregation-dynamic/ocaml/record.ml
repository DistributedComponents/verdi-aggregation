open Portaudio
open Bigarray

let format = format_int16

let channels = 1

let rate = 44100.0

let input_block_time = 0.05

let input_frames_per_block = int_of_float (rate *. input_block_time)

let output_frames_per_block = 256

let device = 2

let normalize_int16 n =
  n / 32

let open_mic_stream () =
  let interleaved = true in
  let inparam =
    Some { channels = channels 
	 ; device = device 
	 ; sample_format = format 
	 ; latency = 1.0 } in
  open_stream ~interleaved inparam None rate input_frames_per_block []

let sum_squares ba =
  let sum = ref 0 in
  for i = 0 to (Genarray.nth_dim ba 0 - 1) do
    let n = normalize_int16 (Genarray.get ba [|i|]) in
    sum := !sum + (n * n)
  done;
  !sum

let () =
  Portaudio.init ()

let read () =
  let in_stream = open_mic_stream () in
  Portaudio.start_stream in_stream;
  let buf = Genarray.create int16_signed c_layout [|channels*input_frames_per_block|] in
  Portaudio.read_stream_ba in_stream buf 0 input_frames_per_block;
  Portaudio.close_stream in_stream;
  sum_squares buf
