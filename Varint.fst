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
open FStar.Tactics.V2

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
        [nextByte]
  else 
    let nextByte = U8.(nextByte +^ 128uy) in
    UInt.shift_right_value_lemma (U64.v x) 7;
    assert op_Division (U64.v x) 128 = (U64.v rest);
    let restEnc = encode rest in
    assert (U8.v nextByte) >= 128;
    UInt.lemma_msb_pow2 (U8.v nextByte);
    List.append [nextByte] restEnc


val lemma_varint_max (bs:varint) (x: U64.t) : 
  Lemma (requires bs = encode x) (ensures UInt.fits (U64.v x) (7 * length bs))
let rec lemma_varint_max bs x = 
  match bs with 
  | msb :: [] -> let nextByte = U64.logand x 0x7FuL in
               let nextByte' = Cast.uint64_to_uint8 nextByte in
               UInt.logand_le (U64.v x) 0x7F;
               assert UInt.fits (U64.v nextByte) 7;
               assert [msb] = [nextByte'];
               assert U64.(lte (x >>^ 7ul) 0uL); 
               assert op_Division (U64.v x) 128 = 0; 
               ()
  | msb :: rest -> assume False; ()

val lemma_varint_trunc (bs:varint) (x:U64.t) :
  Lemma (requires bs = encode x /\ length bs >= 2) (ensures tl bs = encode U64.(x >>^ 7ul))
let lemma_varint_trunc bs x = 
  match bs with 
  | msb :: rest -> let nextX = U64.(x >>^ 7ul) in 
                 let nextByteEnc = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
                 let restEnc = encode nextX in
                 UInt.logand_le (U64.v x) 0x7F;
                 assert not U64.(lte nextX 0uL);
                 assert bs = List.append [U8.(nextByteEnc +^ 128uy)] restEnc;
                 assert rest = encode nextX;
                 ()

let n_lower_ones (n:pos{n < 64}) : U64.t = 
  let shift = pow2 n in
  FStar.Math.Lemmas.pow2_lt_compat 64 n;
  U64.(uint_to_t shift -^ 1uL)

let n_upper_ones (n:pos{n < 64}) : U64.t = 
  let shift = pow2 n in 
  FStar.Math.Lemmas.pow2_lt_compat 64 n;
  let ones = U64.(uint_to_t shift -^ 1uL) in 
  U64.lognot ones

val lemma_and_comp (x y z:U64.t) (p:pos{n < 64}) : 
  Lemma (requires U64.v y = U64.v U64.(x &^ (n_upper_ones p)) /\ U64.v z = U64.v U64.(x &^ (n_lower_ones p)))
        (ensures U64.v U64.(z &^ y) = U64.v x)
let lemma_and_comp x y z p = 
  assume False;
  ()
  
let rec decode (bs:varint) (x:erased U64.t{bs = encode(reveal x)}) : y:U64.t{y = reveal x} =
  match bs with 
  | msb :: [] -> assert length bs = 1;
            assert UInt.fits (U8.v msb) 7;
            UInt.logand_le (U64.v x) 0x7F;
            lemma_varint_max bs x;
            assert U64.v x < 128;
            UInt.logand_mask (U64.v x) 7;
            FStar.Math.Lemmas.modulo_lemma (U64.v x) 128;
            assert msb = Cast.uint64_to_uint8 U64.(logand x 0x7FuL);
            assert msb = Cast.uint64_to_uint8 x;
            assert U8.v msb = U64.v x;
            assume False; 
            Cast.uint8_to_uint64 msb
  | msb :: rest -> let msbx = U8.logand msb 0x7Fuy in
                 let msx = Cast.uint8_to_uint64 msbx in
                 lemma_varint_trunc bs x;
                 let restx : erased U64.t = U64.(x >>^ 7ul) in
                 let rx = decode rest restx in 
                 UInt.shift_left_value_lemma (U64.v rx) 7;
                 assert U64.(v (restx <<^ 7ul)) <= pow2 U64.n;
                 FStar.Math.Lemmas.modulo_lemma (U64.v restx) (pow2 U64.n);
                 assume U64.v msx = U64.v U64.(x &^ n_lower_ones 7);
                 assume U64.v rx = U64.v U64.(x &^ n_upper_ones 7);
                 lemma_and_comp x rx msx 7;
                 let y = U64.(msx &^ (rx <<^ 7ul)) in
                 assert y = reveal x;
                 assume False;
                 y

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
