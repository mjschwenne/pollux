open Stdio
open Pollux

let test_val : Z.t Proto3.proto_dec = Proto3.IMPLICIT (Some (Z.of_int 128))
let test_field : Proto3.proto_ty = Proto3.INT (Z.of_int 32, test_val)

let test_msg : Proto3.msg =
  {
    Proto3.name = "test";
    Proto3.reserved = FStar_Set.empty ();
    Proto3.fields = [ ("field1", Z.of_int 1, test_field) ];
  }

let fstar_u8_to_char u8 = Char.chr (Z.to_int (FStar_UInt8.v u8))

let () =
  print_endline "==== Pollux Encoding Test Program ====";
  let enc = Encode.encode_msg test_msg in
  let enc_byt : bytes =
    Bytes.init (List.length enc) (fun i -> fstar_u8_to_char (List.nth enc i))
  in
  let output_file = open_out_bin "msg.bin" in
  Printf.fprintf output_file "%s" (Bytes.to_string enc_byt);
  close_out output_file;
  print_endline "================ end ================="
