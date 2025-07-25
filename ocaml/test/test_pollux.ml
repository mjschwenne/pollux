open Unix
module Pollux = Pollux.Pollux_Proto_Parse

type format = U32 | U64 | I32 | I64 | S32 | S64 [@@deriving show]

type transform = { mutable fst : format; mutable snd : format }
[@@deriving show]

let string_of_format fmt =
  match fmt with
  | U32 -> "u32"
  | U64 -> "u64"
  | I32 -> "i32"
  | I64 -> "i64"
  | S32 -> "s32"
  | S64 -> "s64"

let string_of_transform t =
  string_of_format t.fst ^ string_of_format t.snd ^ "\n"

let pollux_wrap_32 (f : Z.t -> Z.t -> Z.t) (z : Z.t) : Z.t = f (Z.of_int 32) z
let pollux_wrap_64 (f : Z.t -> Z.t -> Z.t) (z : Z.t) : Z.t = f (Z.of_int 64) z

let get_conversion_func fst_fmt snd_fmt =
  match (fst_fmt, snd_fmt) with
  | U32, U32 -> pollux_wrap_32 Pollux.uint_change_w
  | U64, U32 -> pollux_wrap_32 Pollux.uint_change_w
  | U32, U64 -> pollux_wrap_64 Pollux.uint_change_w
  | U64, U64 -> pollux_wrap_64 Pollux.uint_change_w
  | U32, I32 -> pollux_wrap_32 Pollux.uint_int
  | U64, I64 -> pollux_wrap_64 Pollux.uint_int
  | U32, S32 -> pollux_wrap_32 Pollux.uint_sint
  | U64, S64 -> pollux_wrap_64 Pollux.uint_sint
  | I32, I32 -> pollux_wrap_32 Pollux.int_change_w
  | I64, I32 -> pollux_wrap_32 Pollux.int_change_w
  | I32, I64 -> pollux_wrap_64 Pollux.int_change_w
  | I64, I64 -> pollux_wrap_64 Pollux.int_change_w
  | I32, U32 -> pollux_wrap_32 Pollux.int_uint
  | I64, U64 -> pollux_wrap_64 Pollux.int_uint
  | I32, S32 -> pollux_wrap_32 Pollux.int_sint
  | I64, S64 -> pollux_wrap_64 Pollux.int_sint
  | S32, S32 -> pollux_wrap_32 Pollux.sint_change_w
  | S64, S32 -> pollux_wrap_32 Pollux.sint_change_w
  | S32, S64 -> pollux_wrap_64 Pollux.sint_change_w
  | S64, S64 -> pollux_wrap_64 Pollux.sint_change_w
  | S32, U32 -> pollux_wrap_32 Pollux.sint_uint
  | S64, U64 -> pollux_wrap_64 Pollux.sint_uint
  | S32, I32 -> pollux_wrap_32 Pollux.sint_int
  | S64, I64 -> pollux_wrap_64 Pollux.sint_int

let _ =
  let count = 10000 in
  (* INFO: The default value here can be anything EXCEPT the first transformation *)
  let trans = { fst = U32; snd = U64 } in
  let in_ch, out_ch = open_process "pollux_varint_conversion" in
  let update_trans (fst : format) (snd : format) : unit =
    if trans.fst != fst || trans.snd != snd then (
      trans.fst <- fst;
      trans.snd <- snd;
      Out_channel.output_string out_ch (string_of_transform trans))
  in
  let mk_pollux_test to_z fst_fmt snd_fmt x : bool =
    let z = to_z x in
    update_trans fst_fmt snd_fmt;
    Out_channel.output_string out_ch (Z.to_string z);
    Out_channel.output_string out_ch "\n";
    (* 
       I recognize that having to flush here isn't super efficient... 
       But it is nice to be able to reuse the input generation and checking 
       from qcheck by not totally abandoning the property-based testing framework 
    *)
    Out_channel.flush out_ch;
    match In_channel.input_line in_ch with
    | None -> false
    | Some s ->
        let expected = Z.of_string s in
        let actual = (get_conversion_func fst_fmt snd_fmt) z in
        Z.equal expected actual
  in
  exit
    (QCheck_base_runner.run_tests ~verbose:true
       [
         (* Uint tests *)
         QCheck.Test.make ~count ~name:"uint32 -> uint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32_unsigned U32 U32);
         QCheck.Test.make ~count ~name:"uint64 -> uint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64_unsigned U64 U64);
         QCheck.Test.make ~count ~name:"uint64 -> uint32"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64_unsigned U64 U32);
         QCheck.Test.make ~count ~name:"uint32 -> uint64"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32_unsigned U32 U64);
         QCheck.Test.make ~count ~name:"uint32 -> int32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32_unsigned U32 I32);
         QCheck.Test.make ~count ~name:"uint64 -> int64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64_unsigned U64 I64);
         QCheck.Test.make ~count ~name:"uint32 -> sint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32_unsigned U32 S32);
         QCheck.Test.make ~count ~name:"uint64 -> sint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64_unsigned U64 S64);
         (* Int tests *)
         QCheck.Test.make ~count ~name:"int32 -> int32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 I32 I32);
         QCheck.Test.make ~count ~name:"int64 -> int64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 I64 I64);
         QCheck.Test.make ~count ~name:"int64 -> int32"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 I64 I32);
         QCheck.Test.make ~count ~name:"int32 -> int64"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 I32 I64);
         QCheck.Test.make ~count ~name:"int32 -> uint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 I32 U32);
         QCheck.Test.make ~count ~name:"int64 -> uint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 I64 U64);
         QCheck.Test.make ~count ~name:"int32 -> sint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 I32 S32);
         QCheck.Test.make ~count ~name:"int64 -> sint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 I64 S64);
         (* Sint tests *)
         QCheck.Test.make ~count ~name:"sint32 -> sint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 S32 S32);
         QCheck.Test.make ~count ~name:"sint64 -> sint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 S64 S64);
         QCheck.Test.make ~count ~name:"sint64 -> sint32"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 S64 S32);
         QCheck.Test.make ~count ~name:"sint32 -> sint64"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 S32 S64);
         QCheck.Test.make ~count ~name:"sint32 -> uint32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 S32 U32);
         QCheck.Test.make ~count ~name:"sint64 -> uint64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 S64 U64);
         QCheck.Test.make ~count ~name:"sint32 -> int32"
           QCheck.(int32)
           (mk_pollux_test Z.of_int32 S32 I32);
         QCheck.Test.make ~count ~name:"sint64 -> int64"
           QCheck.(int64)
           (mk_pollux_test Z.of_int64 S64 I64);
       ])
