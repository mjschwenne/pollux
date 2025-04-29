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
    (* Note that U.msb is "most significant bit" while the msb in the pattern match is "most significant byte" *)
  | msb :: rest -> U.msb (U8.v msb) && valid rest

let varint = v:list UInt8.t{length v >= 1 /\ valid v}

let zero_extend_m_vec (#n:pos) (a:BitVector.bv_t n) (m:pos): Tot (BitVector.bv_t (n+m)) = 
  Seq.append (create m false) a

let zero_extend_m (#n:pos) (a:uint_t n) (m:pos): Tot (uint_t (n+m)) = 
  from_vec (zero_extend_m_vec (to_vec a) m)

val logand_append: #n:pos -> #m:pos -> a:BitVector.bv_t n -> b:BitVector.bv_t n -> 
                    c:BitVector.bv_t m -> d:BitVector.bv_t m ->
                    Lemma (ensures Seq.append (BitVector.logand_vec a b) (BitVector.logand_vec c d) =
                                   BitVector.logand_vec #(n+m) (Seq.append a c) (Seq.append b d))

val logand_trunc_lemma: #n:pos -> a:uint_t n -> m:pos ->
  Lemma (requires U.size a m /\ m <= n) (ensures (U.logand a (U.to_uint_t n (U.max_int m))) = a)

let logand_trunc_lemma #n a m = 
  let b = U.max_int m in
  let b' = U.to_uint_t m b in
  let b'' = U.to_uint_t n b in
  let a' = U.to_uint_t m a in
  FStar.Math.Lemmas.pow2_le_compat n m;
  FStar.Math.Lemmas.modulo_lemma b (pow2 n);
  FStar.Math.Lemmas.modulo_lemma b (pow2 m);
  assert b' = b'';
  FStar.Math.Lemmas.modulo_lemma a (pow2 m);
  assert a = a';
  UInt.logand_lemma_2 a';
  assert U.logand a b'' = a;
  assert True
  
  
let rec encode (x: U64.t) : Tot varint (decreases (U64.v x)) = 
  let nextByte = Cast.uint64_to_uint8 (U64.logand x 0x7FuL) in 
  let rest = U64.(x >>^ 7ul) in
  UInt.logand_le (U64.v x) 0x7F;
  if U64.(lte rest 0uL) then 
    (
        assert UInt.fits U8.(v nextByte) 7;
        UInt.shift_right_value_lemma (U64.v x) 7;
        assert op_Division (U64.v x) 128 = 0;
        assert (U64.v x) < 128;
        assert (U8.v nextByte) < 128;
        assert (UInt.to_uint_t 7 (U64.v x)) = U64.v x;
        // UInt.logand_lemma_2 (UInt.to_uint_t)
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
    List.append [nextByte] restEnc


let rec decode (bs:varint) (x:erased U64.t{bs = encode(reveal x)}) : y:U64.t{y = reveal x} =
  let nextByte = hd bs in
  match U.msb (U8.v nextByte) with 
  | false -> assert length bs = 1; 
            // UInt.logand_le (U64.v x) 0x7F;
            // assert nextByte = Cast.uint64_to_uint8 (U64.logand (reveal x) 0x7FuL);
            // UInt.logand_mask (U64.v x) 8;
            // assert U64.v (reveal x) < 128;
            assert U8.v nextByte = U64.v (reveal x);
            Cast.uint8_to_uint64 nextByte
  | true -> 0uL
  
(* Relevant F* code in ASN1*: ANS1.Spec.IdentifierU32.fst *)
