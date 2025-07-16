open Stdio
open Proto.Everything
open Ocaml_protoc_plugin
open Pollux
module D = Pollux_Proto_Descriptors
module Prelude = Pollux_Proto_Prelude
open Stdint

let z = Z.of_int

let test_proto : Everything.t =
  Everything.make ~i32i:3 ~i64o:(-1) ~u32r:[ 1; 2; 3 ] ~u64i:0 ?s32o:None
    ~s64r:[ -1 ] ~f32i:1024l ~f64o:3668L ~sf32r:[ -19l ] ~sf64i:26L ?bo:None
    ~sr:[ "Hello"; "World" ]
    ~bi:(String.to_bytes "DEADBEEF")
    ()

let pollux_md : D.md =
  let open D in
  {
    reserved = FStar_Set.empty ();
    fields =
      [
        ("i32i", z 1, P_INT (z 32, P_IMPLICIT));
        ("i64o", z 2, P_INT (z 64, P_OPTIONAL));
        ("u32r", z 4, P_UINT (z 32, P_REPEATED));
        ("u64i", z 5, P_UINT (z 64, P_IMPLICIT));
        ("s32o", z 6, P_SINT (z 32, P_OPTIONAL));
        ("s64r", z 7, P_SINT (z 64, P_REPEATED));
        ("f32i", z 8, P_FIXED (z 32, P_IMPLICIT));
        ("f64o", z 9, P_FIXED (z 64, P_OPTIONAL));
        ("sf32r", z 10, P_SFIXED (z 32, P_REPEATED));
        ("sf64i", z 11, P_SFIXED (z 64, P_IMPLICIT));
        ("bo", z 12, P_BOOL P_OPTIONAL);
        ("sr", z 13, P_STRING P_REPEATED);
        ("bi", z 14, P_BYTES P_IMPLICIT);
      ];
  }

let test_pollux : Pollux_Proto_Descriptors.msg =
  let open D in
  [
    ("i32i", VINT (VIMPLICIT (z 3)));
    ("i64o", VINT (VOPTIONAL (Some (z (-1)))));
    ("u32r", VINT (VREPEATED [ z 1; z 2; z 3 ]));
    ("u64i", VINT (VIMPLICIT (z 0)));
    ("s32o", VINT (VOPTIONAL None));
    ("s64r", VINT (VREPEATED [ z (-1) ]));
    ("f32i", VINT (VIMPLICIT (z 1024)));
    ("f64o", VINT (VOPTIONAL (Some (z 3668))));
    ("sf32r", VINT (VREPEATED [ z (-19) ]));
    ("sf64i", VINT (VIMPLICIT (z 26)));
    ("bo", VBOOL (VOPTIONAL None));
    ("sr", VSTRING (VREPEATED [ "Hello"; "World" ]));
    ("bi", VBYTES (VIMPLICIT [ 68; 69; 65; 68; 66; 69; 69; 70 ]));
  ]

(* Crazy that this isn't built in... *)
let id x = x
let str_int x = string_of_int (Z.to_int x)

let str_bytes (x : int list) : string =
  String.of_seq (List.to_seq (List.map Char.chr x))

let str_pollux_option v str : string =
  match v with None -> "None" | Some v' -> "Some " ^ str v'

let str_pollux_list l str : string =
  match l with
  | [] -> "[]"
  | h :: t -> "[" ^ List.fold_left (fun a b -> a ^ "; " ^ str b) (str h) t ^ "]"

let str_pollux_pdec (d : D.pdec) : string =
  match d with
  | D.P_IMPLICIT -> "IMPLICIT"
  | D.P_OPTIONAL -> "OPTIONAL"
  | D.P_REPEATED -> "REPEATED"

let str_pollux_pty (p : D.pty) : string =
  match p with
  | D.P_DOUBLE p' -> str_pollux_pdec p' ^ " DOUBLE"
  | D.P_FLOAT p' -> str_pollux_pdec p' ^ " FLOAT"
  | D.P_INT (w, p') -> str_pollux_pdec p' ^ " INT " ^ str_int w
  | D.P_UINT (w, p') -> str_pollux_pdec p' ^ " UINT " ^ str_int w
  | D.P_SINT (w, p') -> str_pollux_pdec p' ^ " SINT " ^ str_int w
  | D.P_FIXED (w, p') -> str_pollux_pdec p' ^ " FIXED " ^ str_int w
  | D.P_SFIXED (w, p') -> str_pollux_pdec p' ^ " SFIXED " ^ str_int w
  | D.P_BOOL p' -> str_pollux_pdec p' ^ " BOOL"
  | D.P_STRING p' -> str_pollux_pdec p' ^ " STRING"
  | D.P_BYTES p' -> str_pollux_pdec p' ^ " BYTES"
  | D.P_MSG p' -> str_pollux_pdec p' ^ " MSG"
  | D.P_ENUM p' -> str_pollux_pdec p' ^ " ENUM"

let str_pollux_dvty (v : 'a D.dvty) (str : 'a -> string) : string =
  match v with
  | D.VIMPLICIT v' -> str v'
  | D.VOPTIONAL v' -> str_pollux_option v' str
  | D.VREPEATED v' -> str_pollux_list v' str

let str_pollux_vty (v : D.vty) : string =
  match v with
  | D.VDOUBLE _ -> "DOUBLE"
  | D.VFLOAT _ -> "FLOAT"
  | D.VINT v' -> str_pollux_dvty v' str_int
  | D.VBOOL v' -> str_pollux_dvty v' string_of_bool
  | D.VSTRING v' -> str_pollux_dvty v' id
  | D.VBYTES v' -> str_pollux_dvty v' str_bytes
  | D.VMSG v' -> "MSG"
  | D.VENUM v' -> "ENUM"

let str_pollux_field (f : D.vf) : string =
  let n, v = f in
  n ^ ": " ^ str_pollux_vty v

let str_pollux_msg (m : D.msg) : string =
  List.fold_left (fun a f -> a ^ "\n  " ^ str_pollux_field f) "  " m

let fstar_u8_to_char u8 = Char.chr (Z.to_int (FStar_UInt8.v u8))
let print_fstar_u8 u8 = printf "%X " (Z.to_int (FStar_UInt8.v u8))

let bytes_of_pollux_bytes (enc : Prelude.bytes) : bytes =
  Bytes.init (List.length enc) (fun i -> fstar_u8_to_char (List.nth enc i))

let string_of_pollux_bytes (enc : Prelude.bytes) : string =
  Bytes.to_string (bytes_of_pollux_bytes enc)

let pollux_bytes_of_string (enc : string) : Prelude.bytes =
  String.fold_left (fun b x -> FStar_List.append b [ Char.code x ]) [] enc

let () =
  print_endline "==== Pollux Encoding Test Program ====";
  printf "Original Proto Struct: %s\n" (Everything.show test_proto);
  let proto_enc = Writer.contents (Everything.to_proto test_proto) in
  let proto_reconstructed = Everything.from_proto (Reader.create proto_enc) in
  (match proto_reconstructed with
  | Ok p -> printf "Reconstructed Proto Struct: %s\n" (Everything.show p)
  | Error e ->
      printf "Error parsing proto struct: %s\n" (Runtime'.Result.show_error e));
  printf "Original Pollux Struct:%s\n" (str_pollux_msg test_pollux);
  let pollux_enc = Pollux_Proto_Parse.encode_message pollux_md test_pollux in
  let pollux_str = string_of_pollux_bytes pollux_enc in
  let output_file = open_out_bin "msg.bin" in
  Printf.fprintf output_file "%s" pollux_str;
  close_out output_file;
  let pollux_from_pollux = Pollux_Proto_Parse.parse pollux_md pollux_enc in
  (match pollux_from_pollux with
  | None -> printf "Failed to decode Pollux struct\n"
  | Some p -> printf "Reconstructed Pollux struct:%s\n" (str_pollux_msg p));
  let chunks, rest = Pollux_Proto_Parse.decode_fields pollux_enc in
  printf "Decoded %d fields, %d leftover bytes\n" (List.length chunks)
    (List.length rest);
  List.iter
    (fun e ->
      printf "(%d, " (Z.to_int (fst e));
      List.iter print_fstar_u8 (snd e);
      printf ")\n")
    chunks;
  List.iter print_fstar_u8 rest;
  print_newline ();
  printf "Default Struct:%s\n" (str_pollux_msg (D.init_msg pollux_md));
  List.iter
    (fun e ->
      let ty = Pollux_Proto_Parse.find_field pollux_md (fst e) in
      match ty with
      | None -> printf "Failed to find ty for %d\n" (Z.to_int (fst e))
      | Some (n, f, pty) -> (
          printf "Found field \"%s\" : %s for %d" n (str_pollux_pty pty)
            (Z.to_int f);
          match Pollux_Proto_Parse.parse_field pty (snd e) with
          | None -> printf " -> Failed to parse\n"
          | Some v -> printf " -> parsed to %s\n" (str_pollux_vty v)))
    chunks;
  let proto_from_pollux = Everything.from_proto (Reader.create pollux_str) in
  (match proto_from_pollux with
  | Ok p -> printf "Proto from Pollux Struct: %s\n" (Everything.show p)
  | Error e ->
      printf "Error parsing pollux struct with proto: %s\n"
        (Runtime'.Result.show_error e));
  let pollux_from_proto =
    Pollux_Proto_Parse.parse pollux_md (pollux_bytes_of_string proto_enc)
  in
  (match pollux_from_proto with
  | None -> printf "Failed to decode Pollux from Proto struct\n"
  | Some p -> printf "Pollux from Proto struct:%s\n" (str_pollux_msg p));
  print_endline "================ end ================="
