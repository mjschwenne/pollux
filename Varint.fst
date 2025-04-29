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
open FStar.Mul

module U = FStar.UInt
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
    (* A one-byte varint is valid if the continuation bit is zero,
       which is equivalent to the number fitting into 7 bits *)
  | msb :: [] -> UInt.fits (U8.v msb) 7
    (* Otherwise the continuation bit should be one *)
    (* Note that U.msb is "most significant bit" while the msb is the patter match is "most significant byte" *)
  | msb :: rest -> U.msb (U8.v msb) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ valid v}


let rec encode (x: U64.t) : Tot varint (decreases (U64.v x)) = 
  let nextByte = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
  let rest = U64.(x >>^ 7ul) in
  UInt.logand_le (U64.v x) 0x7F;
  assert UInt.fits U8.(v nextByte) 7;
  if U64.(lte rest 0uL) then 
    [nextByte]
  else 
    let nextByte = U8.(nextByte +^ 128uy) in
    UInt.shift_right_value_lemma (U64.v x) 7;
    assert op_Division (U64.v x) 128 = (U64.v rest);
    let restEnc = encode rest in
    assert (U8.v nextByte) >= 128;
    UInt.lemma_msb_pow2 (U8.v nextByte);
    List.append [nextByte] restEnc

let rec decode (bs:varint) (x:erased U64.t{bs == encode(x)}) : y:U64.t{y == reveal x} =
  let nextByte = hd bs in
  match U.msb (U8.v nextByte) with 
  | true -> Cast.uint8_to_uint64 nextByte
  | false -> 0uL
  

(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
