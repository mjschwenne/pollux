module Encode

open FStar.Ghost
open FStar.Mul

module U = FStar.UInt
module I = FStar.Int
module U8 = FStar.UInt8
module I8 = FStar.Int8
module U16 = FStar.UInt16
module I16 = FStar.Int16
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast.Full
module Seq = FStar.Seq
module List = FStar.List.Tot
module Char = FStar.Char 
module String = FStar.String 

module P = Pollux.Proto.Descriptors

let nat_to_u8 (n:nat) : U8.t = U8.uint_to_t (UInt.to_uint_t U8.n n)
let nat_to_u32 (n:nat) : U32.t = U32.uint_to_t (UInt.to_uint_t U32.n n)
let nat_to_u64 (n:nat) : U64.t = U64.uint_to_t (UInt.to_uint_t U64.n n)
let int_to_i64 (z:int) : I64.t = I64.int_to_t (Int.to_int_t I64.n z)

let rec valid (v:list UInt8.t) : bool = 
  match v with 
  | [] -> false
    (* A one-byte varint is valid if the continuation bit is zero,
       which is equivalent to the number fitting into 7 bits *)
  | msb :: [] -> UInt.fits (U8.v msb) 7
    (* Otherwise the continuation bit should be one *)
    (* Note that U.msb is "most significant bit" while the msb in the pattern is "most significant byte" *)
  | msb :: rest -> U.msb (U8.v msb) && valid rest

let varint = v:list U8.t{List.length v >= 1 /\ valid v}


(* Code taken from Varint.fst *)
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

(* Strip out the verification stuff *)
let rec decode (bs:varint) : U64.t =
  match bs with 
  | msb :: [] -> Cast.uint8_to_uint64 msb
  | msb :: rest -> let msbx = U8.logand msb 0x7Fuy in
                 let msx = Cast.uint8_to_uint64 msbx in
                 let rx = decode rest in 
                 let y = U64.((rx <<^ 7ul) |^ msx) in
                 y

#pop-options

type tag : Type =
| VARINT
| I64
| LEN
| I32

let tag_func (p:P.pty) : tag =
  match p with 
  | P.P_INT _ _ 
  | P.P_UINT _ _ 
  | P.P_SINT _ _ 
  | P.P_BOOL _ 
  | P.P_ENUM _ -> VARINT 
  | P.P_FIXED 32 _
  | P.P_SFIXED 32 _
  | P.P_FLOAT _ -> I32
  | P.P_FIXED 64 _ 
  | P.P_SFIXED 64 _
  | P.P_DOUBLE _ -> I64
  | _ -> LEN


let tag_num (t:tag) : U64.t = 
  match t with 
  | VARINT -> nat_to_u64 0  
  | I64 -> nat_to_u64 1
  | LEN -> nat_to_u64 2
  | I32 -> nat_to_u64 5

let byte_list_of_string (s:string) : list U8.t = 
List.map (fun c -> (U8.uint_to_t 
                  (UInt.to_uint_t U8.n 
                    (Char.int_of_char c)))) 
  (String.list_of_string s)

let encode_field (f:P.fd) : list U8.t = 
  let tagn = tag_num (tag_func f._3) in 
  // TODO: check maximum field number
  let id_u64 = nat_to_u64 f._2 in
  let header_u64 = U64.(logor (shift_left id_u64 (nat_to_u32 3)) tagn) in
  let header_enc = encode header_u64 in
  let body_enc = match f._3 with 
                 | P.P_UINT _ (P.P_IMPLICIT (Some v)) -> encode (nat_to_u64 v)
                 | P.P_UINT _ (P.P_OPTIONAL (Some v)) -> encode (nat_to_u64 v)
                 | P.P_INT _  (P.P_IMPLICIT (Some v)) -> encode  (Cast.int64_to_uint64 (int_to_i64 v))
                 | P.P_INT _  (P.P_OPTIONAL (Some v)) -> encode  (Cast.int64_to_uint64 (int_to_i64 v))
                 | P.P_SINT _ (P.P_IMPLICIT (Some v)) -> encode (Cast.int64_to_uint64 (int_to_i64 v))
                 | P.P_SINT _ (P.P_OPTIONAL (Some v)) -> encode (Cast.int64_to_uint64 (int_to_i64 v))
                 | P.P_STRING (P.P_IMPLICIT (Some v)) -> List.Tot.Base.append 
                                                     (encode (nat_to_u64 (String.length v))) 
                                                     (byte_list_of_string v)
                 | P.P_STRING (P.P_OPTIONAL (Some v)) -> List.Tot.Base.append 
                                                     (encode (nat_to_u64 (String.length v))) 
                                                     (byte_list_of_string v)
                 | _ -> [] 
  in 
  if body_enc = [] then 
    []
  else
    List.Tot.Base.append header_enc body_enc

let encode_msg (m:P.msg) : list U8.t = // 
  List.fold_left List.Tot.Base.append [] (List.map encode_field m.fields) 
  
