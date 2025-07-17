open S64
open Stdio
open Ocaml_protoc_plugin

let () =
  let s64 = S64.make ~field:Int64.min_int () in
  let enc = Writer.contents (S64.to_proto s64) in
  let out = open_out_bin "msg.bin" in
  Printf.fprintf out "%s" enc;
  close_out out;
  match S64.from_proto (Reader.create enc) with
  | Error e ->
      printf "Error parsing struct: %s\n" (Runtime'.Result.show_error e)
  | Ok z ->
      printf "Parsed: %s should be %s\n" (Int64.to_string z)
        (Int64.to_string Int64.min_int)
