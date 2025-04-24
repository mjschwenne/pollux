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
  | msb :: rest -> (U8.(msb &^ 0x80uy) = 128uy) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ valid v}


// let rec encode (l:pos{l % 8 = 0}) (x: U.uint_t l) : Tot varint (decreases l) = 
//   assert l > 7; 
//   let nextByte = U.logand x (U.to_uint_t l 0x7F) in 
//   let rest = U.(shift_right x 7) in
//   UInt.logand_le x (U.to_uint_t l 0x7F);
//   assert nextByte < 128;
//   assert U.fits nextByte 8;
//   if rest = U.zero l then
//     [U8.uint_to_t nextByte]
//   else 
//     let nextByte = U8.(uint_to_t nextByte |^ 128uy) in 
//     [nextByte]

let rec encode (x: U64.t) : Tot varint (decreases (U64.v x)) = 
  let nextByte = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
  let rest = U64.(x >>^ 7ul) in
  UInt.logand_le (U64.v x) 0x7F;
  assert UInt.fits U8.(v nextByte) 7;
  if rest = 0uL then 
    [nextByte]
  else 
    let nextByte = U8.(nextByte |^ 128uy) in
    assume U64.v rest < U64.v x;
    let restEnc = encode rest in
    assert valid restEnc;
    assume U8.(nextByte &^ 0x80uy) = 128uy;
    List.append [nextByte] restEnc
  

let rec decode (bs:varint) (x:erased UInt64.t) : y:UInt64.t{(requires bs == encode(x)) (ensures y == x)}
  = 0

(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
