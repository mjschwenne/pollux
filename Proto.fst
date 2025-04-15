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
   Simple inductive type for the tags in an encoded proto Tag-Length-Value field. 

   Not modeling SGROUP or EGROUP this this types are deprecated.
*)
type proto_enc_tag : Type = 
| VARINT
| I64
| LEN
| I32
