module Proto
open FStar.UInt
open FStar.UInt64
open FStar.UInt32
open FStar.UInt8
open FStar.Seq
open FStar.Bytes
open FStar.List.Tot

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = FStar.Bytes
module Seq = FStar.Seq 
module List = FStar.List.Tot

(* Placeholder, until I have something actually finished for variable width integer encoding *)
let vint = nat

(* 
   Simple inductive type for the tags/value combinations in an encoded proto 
   Tag-Length-Value field. 

   Not modeling SGROUP or EGROUP this these types are deprecated.
*)
type proto_enc_lv : Type = 
| VARINT : vint -> proto_enc_lv
| I64 : U64.t -> proto_enc_lv 
| LEN : B.bytes -> proto_enc_lv
| I32 : U32.t -> proto_enc_lv

type proto_enc_field : Type = vint * proto_enc_lv

type proto_enc_msg : Type = list proto_enc_field


