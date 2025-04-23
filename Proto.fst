module Proto
open FStar.UInt
open FStar.UInt64
open FStar.UInt32
open FStar.UInt16
open FStar.UInt8
open FStar.Seq
open FStar.Bytes
open FStar.List.Tot
open FStar.Int.Cast.Full

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = FStar.Bytes
module Seq = FStar.Seq 
module List = FStar.List.Tot

(* Placeholder, until I have something actually finished for variable width integer encoding *)
let vint64 = n:nat{n < pow2 64}
let vint32 = n:nat{n < pow2 32}
(* 
   Simple inductive type for the tags/value combinations in an encoded proto 
   Tag-Length-Value field. 

   Not modeling SGROUP or EGROUP this these types are deprecated.
*)
type proto_enc_lv : Type = 
| VARINT : vint64 -> proto_enc_lv
| I64 : U64.t -> proto_enc_lv 
| LEN : B.bytes -> proto_enc_lv
| I32 : U32.t -> proto_enc_lv

type proto_enc_field : Type = vint32 & proto_enc_lv

type proto_enc_msg : Type = list proto_enc_field

let proto_compat_field (f1 f2 : proto_enc_field) : bool = 
  f1._1 = f2._1 && (match f1._2, f2._2 with 
  | VARINT v1, VARINT v2 -> v1 = v2
  | I64 v1, I64 v2 -> v1 = v2
  | LEN v1, LEN v2 -> B.length v1 = B.length v2 
  | I32 v1, I32 v2 -> v1 = v2 
  | _, _ -> false)

let msg1 : proto_enc_msg = [(2, VARINT 3)]

type proto_enum_descriptor = {
  name : string;
  fields : list proto_enum_field;
}
and proto_enum_field = string * nat

type proto_msg_descriptor : Type = {
  name: string;
  fields: list proto_field_descriptor
}
and proto_field_descriptor : Type = 
| FIELD : proto_decorator -> proto_terminal -> string -> nat -> proto_field_descriptor
| MAP : proto_decorator -> proto_terminal -> proto_terminal -> string -> nat -> proto_field_descriptor
| ONEOF : proto_decorator -> list proto_terminal -> string -> nat -> proto_field_descriptor

and proto_decorator : Type = 
| PLAIN 
| OPTION
| REPEATED

and proto_terminal : Type = 
| DOUBLE
| FLOAT
| INT32
| INT64
| UINT32
| UINT64
| SINT32
| SINT64
| FIXED32
| FIXED64
| SFIXED32
| SFIXED64
| BOOL
| STRING
| BYTES
(* The natural number marks the index in the descriptor set *)
| MSG : nat -> proto_terminal
| ENUM : nat -> proto_terminal

type descriptor_set = {
  enums : list proto_enum_descriptor;
  msgs : list proto_msg_descriptor;
}

(* 
   While this design should allow for mutual recursion between messages, 
   It doesn't track the scoping rules for enums, i.e. an enum defined in
   a message.

   I'm also suspicious about the use of records for top level objects like
   messages. I should probably be tracking the name, and while it does mirror
   the structure of the descriptor.proto, it doesn't feel very proof assistant.
*)

let descriptor_set1 : descriptor_set = {
  enums = [];
  msgs = [
    { 
      name = "test"; 
      fields = [
        FIELD PLAIN STRING "test_field" 2;
        FIELD REPEATED INT32 "test_int" 3;
      ];
    }
  ];
}

let f : proto_field_descriptor = match (List.nth descriptor_set1.msgs 0) with 
| Some m -> match (List.nth m.fields 1) with 
  | Some f -> f


type proto_enc_tv : eqtype = 
| VARINT' : t:proto_terminal{
          match t with
          | INT32 -> true
          | INT64 -> true
          | UINT32 -> true
          | UINT64 -> true
          | SINT32 -> true
          | SINT64 -> true
          | ENUM _ -> true
          | BOOL -> true
          | _ -> false
          } -> proto_enc_tv
| I64' : t:proto_terminal{
          match t with
          | FIXED64 -> true 
          | SFIXED64 -> true
          | _ -> false
          } -> proto_enc_tv
| LEN' : t:proto_terminal{
          match t with 
          | STRING -> true 
          | BYTES -> true 
          | MSG _ -> true 
          | _ -> false
          } -> proto_enc_tv
| I32' : t:proto_terminal{
          match t with
          | FIXED32 -> true 
          | SFIXED32 -> true
          | _ -> false
          } -> proto_enc_tv

type proto_enc_field' : Type = vint32 & proto_enc_tv

let proto_compat_field' (f1 f2 : proto_enc_field') : bool = 
  f1._1 = f2._1 && (match f1._2, f2._2 with 
  | VARINT' v1, VARINT' v2 -> v1 = v2
  | I64' v1, I64' v2 -> v1 = v2
  | LEN' v1, LEN' v2 -> v1 = v2 
  | I32' v1, I32' v2 -> v1 = v2 
  | _, _ -> false)
