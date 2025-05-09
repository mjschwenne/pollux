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
    (* Note that U.msb is "most significant bit" while the msb in the pattern is "most significant byte" *)
  | msb :: rest -> U.msb (U8.v msb) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ valid v}

#push-options "--split_queries always"

let rec encode (x: U64.t) : Tot varint (decreases (U64.v x)) = 
  let nextByte = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
  let rest = U64.(x >>^ 7ul) in
  UInt.logand_le (U64.v x) 0x7F;
  if U64.(lte rest 0uL) then 
    (
        assert op_Division (U64.v x) 128 = 0;
        assert (U64.v x) < 128;
        UInt.logand_mask (U64.v x) 7;
        FStar.Math.Lemmas.modulo_lemma (U64.v x) 128;
        FStar.Math.Lemmas.modulo_lemma (U64.v x) 256;
        assert U8.v nextByte = U64.v x;
        [nextByte]
    )
  else 
    let nextByte = U8.(nextByte +^ 128uy) in
    UInt.shift_right_value_lemma (U64.v x) 7;
    assert op_Division (U64.v x) 128 = (U64.v rest);
    let restEnc = encode rest in
    assert (U8.v nextByte) >= 128;
    UInt.lemma_msb_pow2 (U8.v nextByte);
    let enc = List.append [nextByte] restEnc in 
    enc


val lemma_varint_max (bs:varint) (x: U64.t) : 
  Lemma (requires bs = encode x) (ensures UInt.fits (U64.v x) (7 * length bs))
let rec lemma_varint_max bs x = 
  match bs with 
  | msb :: [] -> let nextByte = U64.logand x 0x7FuL in
               let nextByte' = Cast.uint64_to_uint8 nextByte in
               UInt.logand_le (U64.v x) 0x7F;
               assert UInt.fits (U64.v nextByte) 7;
               assert [msb] = [nextByte'];
               assert op_Division (U64.v x) 128 = 0; 
               ()
  | msb :: rest -> assume False; ()

val lemma_varint_max' (bs:varint) : 
  Lemma (exists x. bs = encode x /\ UInt.fits (U64.v x) (7 * length bs))
let lemma_varint_max' bs = assume False

let rec decode (bs:varint) (x:erased U64.t{bs = encode(reveal x)}) : y:U64.t{y = reveal x} =
  match bs with 
  | msb :: [] -> 
            assert UInt.fits (U8.v msb) 7;
            UInt.logand_le (U64.v x) 0x7F;
            lemma_varint_max bs x;
            assert U64.v (reveal x) < 128;
            UInt.logand_mask (U64.v x) 7;
            FStar.Math.Lemmas.modulo_lemma (U64.v x) 128;
            FStar.Math.Lemmas.modulo_lemma (U64.v x) 256;
            Cast.uint8_to_uint64 msb
  | msb :: rest -> let msx = U64.(Cast.uint8_to_uint64 msb |^ 128uL) in
                 assume rest = encode U64.(x |^ msx);
                 let rx = decode rest U64.(x |^ msx) in 
                 assume False;
                 U64.(msx +^ rx <<^ 7ul)

let rec decode' (bs:varint) (x:erased U64.t{bs = encode(reveal x)}) : y:U64.t{y = reveal x} =
  let nextByte = hd bs in
  match U.msb (U8.v nextByte) with 
  | false -> assert length bs = 1; 
            assert UInt.fits (U8.v nextByte) 7;
            UInt.logand_le (U64.v x) 0x7F;
            lemma_varint_max bs x;
            assert U64.v (reveal x) < 128;
            UInt.logand_mask (U64.v x) 7;
            FStar.Math.Lemmas.modulo_lemma (U64.v x) 128;
            FStar.Math.Lemmas.modulo_lemma (U64.v x) 256;
            Cast.uint8_to_uint64 nextByte
  | true ->  assert length bs > 1; 
            let rest : varint = tl bs in
            let nextByte' = U8.(nextByte -^ 128uy) in
            assume False; 0uL 
  
#pop-options
(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
