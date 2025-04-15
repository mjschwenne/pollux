module Varint
open FStar.Ghost
open FStar.UInt
open FStar.UInt64
open FStar.UInt8
open FStar.List.Tot

let rec valid (v:list UInt8.t) : bool = 
  match v with 
  | [] -> false
    (* A one-byte varint is valid if the continuation bit is zero *)
  | msb :: [] -> (msb &^ 0b10000000uy) = 0uy
    (* Otherwise the continuation bit should be one *)
  | msb :: rest -> ((msb &^ 0x80uy) = 128uy) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ length v <= 10 /\ valid v}

let encode (x: UInt64.t) : varint = 
  let nextByte = UInt8.uint_to_t (UInt64.v (UInt64.logand x 0x7FuL)) in 
  let rest = FStar.UInt64.(x >>^ 7ul) in
  [nextByte] 

let rec decode (bs:varint) (x:erased UInt64.t) : y:UInt64.t{(requires bs == encode(x)) (ensures y == x)}
  = 0

(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
