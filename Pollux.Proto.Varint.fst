module Pollux.Proto.Varint

open FStar.Ghost
open FStar.Mul
open FStar.Tactics.V2

module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = FStar.Bytes
module Cast = FStar.Int.Cast.Full
module Seq = FStar.Seq
module List = FStar.List.Tot

let rec valid (v:list U8.t) : bool = 
  match v with 
  | [] -> false
    (* A one-byte varint is valid if the continuation bit is zero,
       which is equivalent to the number fitting into 7 bits *)
  | msb :: [] -> UInt.fits (U8.v msb) 7
    (* Otherwise the continuation bit should be one *)
    (* Note that U.msb is "most significant bit" while the msb in the pattern is "most significant byte" *)
  | msb :: rest -> U.msb (U8.v msb) && valid rest

let varint = v:list U8.t{List.length v >= 1 /\ valid v}

let set_msb_u8 (b:U8.t{U8.v b < 128}) : r:U8.t{UInt.msb (U8.v r) /\ (U8.v r) = (U8.v b + 128)} = 
  let r = U8.(b +^ 128uy) in 
  assert U8.v r >= pow2 7;
  UInt.lemma_msb_pow2 (U8.v r);
  r

let unset_msb_u8 (b:U8.t{UInt.msb (U8.v b)}) : r:U8.t{~ (UInt.msb (U8.v r)) /\ (U8.v r) = (U8.v b - 128)} = 
  UInt.lemma_msb_pow2 (U8.v b);
  let r = U8.(b -^ 128uy) in 
  UInt.lemma_msb_pow2 (U8.v r);
  r

let rec decode (bs:varint) : U64.t =
  match bs with 
  | msb :: [] -> Cast.uint8_to_uint64 msb
  | msb :: rest -> let msbx = unset_msb_u8 msb in
                 let msx = Cast.uint8_to_uint64 msbx in
                 let rx = decode rest in 
                 let y = U64.((rx <<^ 7ul) |^ msx) in
                 y

let split (#b:pos) (x: UInt.uint_t b) (n:pos{n < b}) : 
  s:(UInt.uint_t b & UInt.uint_t b){x = s._1 * (pow2 n) + s._2} = 
    FStar.Math.Lemmas.pow2_lt_compat b n; 
    let lo = U.(logand x ((pow2 n) - 1)) in 
    let hi = U.(shift_right x n) in 
    UInt.shift_right_value_lemma x n;
    UInt.logand_mask x n;
    FStar.Math.Lemmas.euclidean_division_definition x (pow2 n);
    hi, lo

let split64 (x: U64.t) (n:pos{n < 64}) : 
  s:(UInt.uint_t U64.n & UInt.uint_t U64.n){U64.v x = s._1 * (pow2 n) + s._2} = 
  split (U64.v x) n

val pollux_split_lo_val (#b:pos) (x: UInt.uint_t b) (n: pos{n < b}) :
  Lemma (let _, lo = split x n in 
         lo = x % pow2 n)
let pollux_split_lo_val #b x n = let _, lo = split x n in 
  FStar.Math.Lemmas.pow2_lt_compat b n; 
  UInt.logand_mask x n

val pollux_split_lo_bound (#b:pos) (x: UInt.uint_t b) (n: pos{n < b}) :
  Lemma (let hi, lo = split x n in 
         hi = 0 ==> x <= (pow2 n) - 1 /\ lo = x)
let pollux_split_lo_bound x n = let hi, lo = split x n in 
  pollux_split_lo_val x n;
  // Turns out the post conditions have some type of dependency between them 
  // So we need to know lo = x before we get that x <= (pow2 n) - 1
  assert hi = 0 ==> lo = x;
  assert hi = 0 ==> x <= (pow2 n) - 1

val pollux_split_hi_val (#b:pos) (x: UInt.uint_t b) (n: pos{n < b}) :
  Lemma (let hi, _ = split x n in 
         hi = x / pow2 n)
let pollux_split_hi_val x n = UInt.shift_right_value_lemma x n

// Also getting a warning about assertions only succeeding after splitting 
// them, but I don't see any assertions which can be split...
#push-options "--split_queries always"
val pollux_split_hi_bound (#b:pos) (x: UInt.uint_t b) (n: pos{n < b}) :
  Lemma (let hi, _ = split x n in
         hi > 0 ==> x >= pow2 n)
let pollux_split_hi_bound x n = let hi, _ = split x n in 
  pollux_split_hi_val x n;
  assert (forall (n d:pos). n / d > 0 ==> n >= d);
  assert hi > 0 ==> x >= pow2 n
#pop-options 

let split_lo_to_u8 (x: erased (UInt.uint_t U64.n)) 
                   (lo: UInt.uint_t U64.n{let _, slo = split x 7 in lo = slo}) : b:U8.t{U8.v b = lo} = 
    pollux_split_lo_val x 7;
    FStar.Math.Lemmas.modulo_lemma lo (pow2 8);
    Cast.uint64_to_uint8 (U64.uint_to_t lo)

val decode_prepend (x:UInt.uint_t U64.n) (v:varint{let shi, _ = split x 7 in U64.v (decode v) = shi}) : 
  Lemma (let hi, lo = split x 7 in 
           pollux_split_lo_val x 7;
             U64.v (decode ((set_msb_u8 (split_lo_to_u8 x lo)) :: v)) = hi * (pow2 7) + lo)
let decode_prepend x v = let hi, lo = split #U64.n x 7 in 
  pollux_split_hi_val x 7;
  pollux_split_lo_val x 7;
  let lo8 = split_lo_to_u8 x lo in
  let slo8 = set_msb_u8 lo8 in
  let hi64 = U64.uint_to_t hi in 
  let lo64 = U64.uint_to_t lo in
  assert U64.v (decode (slo8 :: v)) = U64.v U64.(logor (shift_left hi64 7ul) lo64);
  assert U64.v (decode (slo8 :: v)) = U.(logor (shift_left hi 7) lo);
  FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat hi (pow2 7);
  FStar.Math.Lemmas.modulo_lemma (hi * pow2 7) (pow2 U64.n);
  UInt.shift_left_value_lemma hi 7;
  FStar.Math.Lemmas.multiple_modulo_lemma hi (pow2 7);
  assert (U.shift_left hi 7) = hi * (pow2 7);
  UInt.logor_disjoint U.(shift_left hi 7) lo 7

#push-options "--z3rlimit 8 --split_queries always"

let rec encode (x: U64.t) : Tot (v:varint{U64.v (decode v) = U64.v x}) (decreases (U64.v x)) = 
  let xn : erased (UInt.uint_t U64.n) = U64.v x in
  let hi, lo = split64 x 7 in
  let hi64 = (U64.uint_to_t hi) in 
  pollux_split_lo_bound xn 7; 
  if U64.(lte hi64 0uL) then 
    [split_lo_to_u8 xn lo]
  else 
    let lo8 = split_lo_to_u8 xn lo in
    pollux_split_hi_bound xn 7;
    pollux_split_lo_val xn 7;
    let rx = encode hi64 in 
    decode_prepend xn rx;
    (set_msb_u8 lo8) :: rx

#pop-options
