open Stdio
open Proto.Everything
open Ocaml_protoc_plugin
open Pollux
module D = Pollux_Proto_Descriptors
open Stdint

let z = Z.of_int
let u32 = Uint32.of_int
let u64 = Uint64.of_int

let test_proto : Everything.t =
  Everything.make ~i32i:3 ~i64o:(-1) ~u32r:[ 1; 2; 3 ] ~u64i:0 ?s32o:None
    ~s64r:[ -1 ] ~f32i:1024l ~f64o:3668L ~sf32r:[ -19l ] ~sf64i:26L ~bo:true
    ~sr:[ "Hello"; "World" ]
    ~bi:(String.to_bytes "DEADBEEF")
    ()

let pollux_md : D.md =
  let open D in
  {
    name = "Test";
    reserved = FStar_Set.empty ();
    fields =
      [
        (* TODO: make F* md type enforce unique field numbers *)
        ("i32i", z 1, P_INT (z 32, P_IMPLICIT));
        ("i640", z 2, P_INT (z 64, P_OPTIONAL));
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
    ("i32i", VINT32 (VIMPLICIT 3l));
    ("i64o", VINT64 (VOPTIONAL (Some (-1L))));
    ("u32r", VUINT32 (VREPEATED [ u32 1; u32 2; u32 3 ]));
    ("u64i", VUINT64 (VIMPLICIT (u64 0)));
    ("s32o", VSINT32 (VOPTIONAL None));
    ("s64r", VSINT64 (VREPEATED [ -1L ]));
    ("f32i", VFIXED32 (VIMPLICIT (u32 1024)));
    ("f64o", VFIXED64 (VOPTIONAL (Some (u64 3668))));
    ("sf32r", VSFIXED32 (VREPEATED [ -19l ]));
    ("sf64i", VSFIXED64 (VIMPLICIT 26L));
    ("bo", VBOOL (VOPTIONAL None));
    ("sr", VSTRING (VREPEATED [ "Hello"; "World" ]));
    ("bi", VBYTES (VIMPLICIT [ 68; 69; 65; 68; 66; 69; 69; 70 ]));
  ]

(* Crazy that this isn't built in... *)
let id x = x
let str_i32 x = string_of_int (Int32.to_int x)
let str_i64 x = string_of_int (Int64.to_int x)
let str_u32 x = string_of_int (Uint32.to_int x)
let str_u64 x = string_of_int (Uint64.to_int x)

let str_bytes (x : int list) : string =
  String.of_seq (List.to_seq (List.map Char.chr x))

let str_pollux_option v str : string =
  match v with None -> "None" | Some v' -> "Some " ^ str v'

let str_pollux_list l str : string =
  match l with
  | [] -> "[]"
  | h :: t -> "[" ^ List.fold_left (fun a b -> a ^ "; " ^ str b) (str h) t ^ "]"

let str_pollux_dvty (v : 'a D.dvty) (str : 'a -> string) : string =
  match v with
  | D.VIMPLICIT v' -> str v'
  | D.VOPTIONAL v' -> str_pollux_option v' str
  | D.VREPEATED v' -> str_pollux_list v' str

let str_pollux_field (f : D.vf) : string =
  let n, v = f in
  let str_v =
    match v with
    | D.VDOUBLE _ -> "DOUBLE"
    | D.VFLOAT _ -> "FLOAT"
    | D.VINT32 v' | D.VSINT32 v' | D.VSFIXED32 v' -> str_pollux_dvty v' str_i32
    | D.VINT64 v' | D.VSINT64 v' | D.VSFIXED64 v' -> str_pollux_dvty v' str_i64
    | D.VUINT32 v' | D.VFIXED32 v' -> str_pollux_dvty v' str_u32
    | D.VUINT64 v' | D.VFIXED64 v' -> str_pollux_dvty v' str_u64
    | D.VBOOL v' -> str_pollux_dvty v' string_of_bool
    | D.VSTRING v' -> str_pollux_dvty v' id
    | D.VBYTES v' -> str_pollux_dvty v' str_bytes
    | D.VMSG v' -> "MSG"
    | D.VENUM v' -> "ENUM"
  in
  n ^ ": " ^ str_v

let str_pollux_msg (m : D.msg) : string =
  List.fold_left (fun a f -> a ^ "\n  " ^ str_pollux_field f) "  " m

let fstar_u8_to_char u8 = Char.chr (Z.to_int (FStar_UInt8.v u8))
let print_fstar_u8 u8 = printf "%X " (Z.to_int (FStar_UInt8.v u8))

let bytes_of_pollux_bytes (enc : Pollux_Proto_Parse.bytes) : bytes =
  Bytes.init (List.length enc) (fun i -> fstar_u8_to_char (List.nth enc i))

let string_of_pollux_bytes (enc : Pollux_Proto_Parse.bytes) : string =
  Bytes.to_string (bytes_of_pollux_bytes enc)

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
  let pollux_enc =
    string_of_pollux_bytes
      (Pollux_Proto_Parse.encode_message pollux_md test_pollux)
  in
  let problem_value =
    Pollux_Proto_Parse.encode_value pollux_md (List.nth test_pollux 11)
  in
  (match problem_value with
  | None -> printf "Failed to encode sr value: None\n"
  | Some h ->
      printf "Encoded sr value:";
      List.iter print_fstar_u8 h;
      printf "\n");
  let output_file = open_out_bin "msg.bin" in
  Printf.fprintf output_file "%s" pollux_enc;
  close_out output_file;
  let proto_from_pollux = Everything.from_proto (Reader.create pollux_enc) in
  (match proto_from_pollux with
  | Ok p -> printf "Proto from Pollux Struct: %s\n" (Everything.show p)
  | Error e ->
      printf "Error parsing pollux struct with proto: %s\n"
        (Runtime'.Result.show_error e));
  print_endline "================ end ================="
