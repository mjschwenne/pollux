module Varint
open FStar.Ghost
open FStar.UInt
open FStar.UInt8
open FStar.UInt16
open FStar.UInt32
open FStar.UInt64
open FStar.Int.Cast.Full
open FStar.Seq
open FStar.List.Tot

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast.Full
module Seq = FStar.Seq
module List = FStar.List.Tot

let rec valid (v:list UInt8.t) : bool = 
  match v with 
  | [] -> false
    (* A one-byte varint is valid if the continuation bit is zero *)
  | msb :: [] -> U8.(msb &^ 128uy) = 0uy
    (* Otherwise the continuation bit should be one *)
  | msb :: rest -> (U8.(msb &^ 0x80uy) = 128uy) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ length v <= 10 /\ valid v}


let encode (x: UInt64.t) : varint = 
  assert UInt.logand_le (U64.v x) 0x7F;
  let nextByte = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
  let rest = U64.(x >>^ 7ul) in
  [nextByte] 

let rec decode (bs:varint) (x:erased UInt64.t) : y:UInt64.t{(requires bs == encode(x)) (ensures y == x)}
  = 0

(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
