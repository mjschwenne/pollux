open Ocaml_protoc_plugin
open Proto.Varint
open Stdint
module Pollux = Pollux.Pollux_Proto_Parse

let id z = z
let u32_to_z z = Z.of_int32_unsigned (Int32.of_int z)
let i32_to_z z = Z.of_int32 (Int32.of_int z)

let serialize to_proto make from_Z (z : Z.t) : string =
  Writer.contents (to_proto (make ?field:(Some (from_Z z)) ()))

let parse from_proto to_Z (s : string) : Z.t option =
  match from_proto (Reader.create s) with
  | Ok z -> Some (to_Z z)
  | Error e -> None

let serialize_u32 = serialize U32.to_proto U32.make Z.to_int
let parse_u32 = parse U32.from_proto u32_to_z
let serialize_u64 = serialize U64.to_proto U64.make Z.to_int64_unsigned
let parse_u64 = parse U64.from_proto Z.of_int64_unsigned
let serialize_i32 = serialize I32.to_proto I32.make Z.to_int
let parse_i32 = parse I32.from_proto i32_to_z
let serialize_i64 = serialize I64.to_proto I64.make Z.to_int64
let parse_i64 = parse I64.from_proto Z.of_int64
let serialize_s32 = serialize S32.to_proto S32.make Z.to_int
let parse_s32 = parse S32.from_proto i32_to_z
let serialize_s64 = serialize S64.to_proto S64.make Z.to_int64
let parse_s64 = parse S64.from_proto Z.of_int64
let pollux_wrap_32 (f : Z.t -> Z.t -> Z.t) (z : Z.t) : Z.t = f (Z.of_int 32) z
let pollux_wrap_64 (f : Z.t -> Z.t -> Z.t) (z : Z.t) : Z.t = f (Z.of_int 64) z
let pollux_uint_to_uint32 = pollux_wrap_32 Pollux.uint_change_w
let pollux_uint_to_uint64 = pollux_wrap_64 Pollux.uint_change_w
let pollux_uint32_int32 = pollux_wrap_32 Pollux.uint_int
let pollux_uint64_int64 = pollux_wrap_64 Pollux.uint_int
let pollux_uint32_sint32 = pollux_wrap_32 Pollux.uint_sint
let pollux_uint64_sint64 = pollux_wrap_64 Pollux.uint_sint
let pollux_int_to_int32 = pollux_wrap_32 Pollux.int_change_w
let pollux_int_to_int64 = pollux_wrap_64 Pollux.int_change_w
let pollux_int32_uint32 = pollux_wrap_32 Pollux.int_uint
let pollux_int64_uint64 = pollux_wrap_64 Pollux.int_uint
let pollux_int32_sint32 = pollux_wrap_32 Pollux.int_sint
let pollux_int64_sint64 = pollux_wrap_64 Pollux.int_sint
let pollux_sint_to_sint32 = pollux_wrap_32 Pollux.sint_change_w
let pollux_sint_to_sint64 = pollux_wrap_64 Pollux.sint_change_w
let pollux_sint32_uint32 = pollux_wrap_32 Pollux.sint_uint
let pollux_sint64_uint64 = pollux_wrap_64 Pollux.sint_uint
let pollux_sint32_int32 = pollux_wrap_32 Pollux.sint_int
let pollux_sint64_int64 = pollux_wrap_64 Pollux.sint_int

let test parse serialize convert (z : Z.t) : bool =
  match parse (serialize z) with
  | Some z' ->
      if not (Z.equal z' (convert z)) then
        QCheck.Test.fail_reportf "%s -> %s != %s ( %s)\n" (Z.to_string z)
          (Z.to_string (convert z))
          (Z.to_string z')
          (String.fold_left
             (fun a c -> a ^ Printf.sprintf "%02X " (Char.code c))
             "" (serialize z))
      else true
  | None -> QCheck.Test.fail_report "Failed to parse int"

let test_32 parse serialize convert to_Z (z : int32) : bool =
  test parse serialize convert (to_Z z)

let test_64 parse serialize convert to_Z (z : int64) : bool =
  test parse serialize convert (to_Z z)

(*
  INFO: Some tests require only positive i32 values. 

  Since I'm abusing zarith to try and operate at the arbitrary width integers 
  for as long as possible, I can treat a negative i32 value as a large u32 value. 
*)
let gen_pos_u32 =
  QCheck.make
    (QCheck.Gen.map Int32.of_int
       (QCheck.Gen.int_bound (Int32.to_int Int32.max_int)))

let count = 10000

let u32_id =
  QCheck.Test.make ~count ~name:"uint32 -> uint32"
    QCheck.(int32)
    (test_32 parse_u32 serialize_u32 pollux_uint_to_uint32 Z.of_int32_unsigned)

let u64_id =
  QCheck.Test.make ~count ~name:"uint64 -> uint64"
    QCheck.(int64)
    (test_64 parse_u64 serialize_u64 pollux_uint_to_uint64 Z.of_int64_unsigned)

let uint_demote =
  QCheck.Test.make ~count ~name:"uint64 -> uint32"
    QCheck.(int64)
    (test_64 parse_u32 serialize_u64 pollux_uint_to_uint32 Z.of_int64_unsigned)

let uint_premote =
  QCheck.Test.make ~count ~name:"uint32 -> uint64" gen_pos_u32
    (test_32 parse_u64 serialize_u32 pollux_uint_to_uint64 Z.of_int32)

let uint32_int32 =
  QCheck.Test.make ~count ~name:"uint32 -> int32"
    QCheck.(int32)
    (test_32 parse_i32 serialize_u32 pollux_uint32_int32 Z.of_int32_unsigned)

let uint64_int64 =
  QCheck.Test.make ~count ~name:"uint64 -> int64"
    QCheck.(int64)
    (test_64 parse_i64 serialize_u64 pollux_uint64_int64 Z.of_int64_unsigned)

let uint32_sint32 =
  QCheck.Test.make ~count ~name:"uint32 -> sint32"
    QCheck.(int32)
    (test_32 parse_s32 serialize_u32 pollux_uint32_sint32 Z.of_int32_unsigned)

let uint64_sint64 =
  QCheck.Test.make ~count ~name:"uint64 -> sint64"
    QCheck.(int64)
    (test_64 parse_s64 serialize_u64 pollux_uint64_sint64 Z.of_int64_unsigned)

let i32_id =
  QCheck.Test.make ~count ~name:"int32 -> int32"
    QCheck.(int32)
    (test_32 parse_i32 serialize_i32 pollux_int_to_int32 Z.of_int32)

let i64_id =
  QCheck.Test.make ~count ~name:"int64 -> int64"
    QCheck.(int64)
    (test_64 parse_i64 serialize_i64 pollux_int_to_int64 Z.of_int64)

let int_demote =
  QCheck.Test.make ~count ~name:"int64 -> int32"
    QCheck.(int64)
    (test_64 parse_i32 serialize_i64 pollux_int_to_int32 Z.of_int64)

let int_premote =
  QCheck.Test.make ~count ~name:"int32 -> int64"
    QCheck.(int32)
    (test_32 parse_i64 serialize_i32 pollux_int_to_int64 Z.of_int32)

let int32_uint32 =
  QCheck.Test.make ~count ~name:"int32 -> uint32"
    QCheck.(int32)
    (test_32 parse_u32 serialize_i32 pollux_int32_uint32 Z.of_int32)

let int64_uint64 =
  QCheck.Test.make ~count ~name:"int64 -> uint64"
    QCheck.(int64)
    (test_64 parse_u64 serialize_i64 pollux_int64_uint64 Z.of_int64)

let int32_sint32 =
  QCheck.Test.make ~count ~name:"int32 -> sint32" gen_pos_u32
    (test_32 parse_s32 serialize_i32 pollux_int32_sint32 Z.of_int32)

let int64_sint64 =
  QCheck.Test.make ~count ~name:"int64 -> sint64"
    QCheck.(int64)
    (test_64 parse_s64 serialize_i64 pollux_int64_sint64 Z.of_int64)

let s32_id =
  QCheck.Test.make ~count ~name:"sint32 -> sint32"
    QCheck.(int32)
    (test_32 parse_s32 serialize_s32 pollux_sint_to_sint32 Z.of_int32)

let s64_id =
  QCheck.Test.make ~count ~name:"sint64 -> sint64"
    QCheck.(int64)
    (test_64 parse_s64 serialize_s64 id Z.of_int64)

let sint_demote =
  QCheck.Test.make ~count ~name:"sint64 -> sint32"
    QCheck.(int64)
    (test_64 parse_s32 serialize_s64 pollux_sint_to_sint32 Z.of_int64)

let sint_premote =
  QCheck.Test.make ~count ~name:"sint32 -> sint64"
    QCheck.(int32)
    (test_32 parse_s64 serialize_s32 pollux_sint_to_sint64 Z.of_int32)

let sint32_uint32 =
  QCheck.Test.make ~count ~name:"sint32 -> uint32"
    QCheck.(int32)
    (test_32 parse_u32 serialize_s32 pollux_sint32_uint32 Z.of_int32)

let sint64_uint64 =
  QCheck.Test.make ~count ~name:"sint64 -> uint64"
    QCheck.(int64)
    (test_64 parse_u64 serialize_s64 pollux_sint64_uint64 Z.of_int64)

let sint32_int32 =
  QCheck.Test.make ~count ~name:"sint32 -> int32"
    QCheck.(int32)
    (test_32 parse_i32 serialize_s32 pollux_sint32_int32 Z.of_int32)

let sint64_int64 =
  QCheck.Test.make ~count ~name:"sint64 -> int64"
    QCheck.(int64)
    (test_64 parse_i64 serialize_s64 pollux_sint64_int64 Z.of_int64)

let () =
  let out = open_out_bin "msg.bin" in
  let enc = serialize_s64 (Z.of_int64 2147483648L) in
  (match S32.from_proto (Reader.create enc) with
  | Error e -> Stdio.printf "Failed to parse!"
  | Ok x ->
      Stdio.printf "Parsed: %s (%s)\n" (Int.to_string x)
        (Int32.to_string (Int32.of_int x)));
  Printf.fprintf out "%s" enc;
  close_out out;
  exit
    (QCheck_base_runner.run_tests ~verbose:true
       [
         u32_id;
         u64_id;
         uint_demote;
         uint_premote;
         uint32_int32;
         uint64_int64;
         uint32_sint32;
         uint64_sint64;
         i32_id;
         i64_id;
         int_demote;
         int_premote;
         int32_uint32;
         int64_uint64;
         int32_sint32;
         int64_sint64;
         s32_id;
         s64_id;
         sint_demote;
         sint_premote;
         sint32_uint32;
         sint64_uint64;
         sint32_int32;
         sint64_int64;
       ])
