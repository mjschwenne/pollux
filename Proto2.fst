module Proto2
open FStar.UInt
open FStar.Int.Cast.Full
open FStar.Mul

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = FStar.Bytes 
module Seq = FStar.Seq
module Set = FStar.Set 
module List = FStar.List.Tot 

let vint64 = n:nat{n < pow2 64}
let vint32 = n:nat{n < pow2 32}

unopteq 
type proto_msg_descriptor : Type = {
  name: string;
  reserved: Set.set nat;
}

type proto_decorator : Type = 
| IMPLICIT
| OPTIONAL 
| REPEATED

type proto_terminal : Type = 
| DOUBLE
| FLOAT
| INT32
| INT64
| UINT32
| UINT64
| SINT32
| SINT64
| FIXED32
| FIXED64
| SFIXED32
| SFIXED64
| BOOL
| STRING
| BYTES
| MSG
| ENUM

// type proto_field_descriptor (#t:eqtype) (dec : proto_decorator) (ty : proto_terminal) (name : string) (id : nat) : Type = 
// | FIELD : t -> proto_field_descriptor #t dec ty name id

type field_descriptor (dec : proto_decorator) (ty : proto_terminal) (name : string) (id : nat) : Type = 
| BFIELD : bool -> field_descriptor dec ty name id
| IFIELD : int -> field_descriptor dec ty name id
| SFIELD : string -> field_descriptor dec ty name id

let f1 : field_descriptor IMPLICIT INT32 "field1" 0 = IFIELD (-9)
let f2 : field_descriptor OPTIONAL STRING "field2" 0 = SFIELD "test"
let f3 : field_descriptor IMPLICIT SINT32 "field3" 0 = IFIELD (-2147483644)
let f4 : field_descriptor IMPLICIT INT64 "field4" 0 = IFIELD 0
let f5 : field_descriptor OPTIONAL INT64 "field5" 0 = IFIELD 0
let f6 : field_descriptor IMPLICIT BOOL "field6" 0 = BFIELD false

let val_eq #d1 #ty1 #n1 #id1 #d2 #ty2 #n2 #id2 
  (f1 : field_descriptor d1 ty1 n1 id1) (f2 : field_descriptor d2 ty2 n2 id2) = 
  match f1, f2 with 
  | BFIELD v1, BFIELD v2 -> v1 = v2
  | IFIELD v1, IFIELD v2 -> v1 = v2
  | SFIELD v1, SFIELD v2 -> v1 = v2
  | _, _ -> false
 
(*
   TAKEN FROM PROTO.FST
   
   Compute x^n using exponentiation by squares.

   For now, n must be positive. Since I have a few 
   rules which require taking (-1)^n with a negative n,
   we'll use the fact that (-1)^(-n) = (-1)^n. 

   It seems tricky to get this function to do that since 
   F* has to prove termination, so that trick will be applied 
   in the relevant rule directly.
*)
let rec exp (x:int) (n:nat) : Tot int (decreases n) = 
  if n = 0 then 
    1
  else if n % 2 = 0 then
    exp (x * x) (n / 2)
  else 
    x * (exp (x * x) ((n - 1) / 2))

let idn c = if c then 1 else 0

let base = b:nat{b = 32 \/ b = 64}
let uint_promote (v:int) : int = v
let uint_demote (v:int) : int = v % pow2 32
let int_promote (v:int) : int = v
let int_demote' (v:int) : int = (v % pow2 32 - pow2 32 * (idn (v >= pow2 31))) % pow2 32
let int_demote (v:int) : int = (v % pow2 32 - pow2 32 * (idn (v >= pow2 31))) % pow2 32
let sint_promote (v:int) : int = v 
let sint_demote (v:int) : int = v % pow2 31
let uint_int (v:int) (b:base) : int = v - (pow2 b) * (idn (v >= pow2 (b - 1)))
let int_uint (v:int) (b:base) : int = v + (pow2 b) * (idn (v < 0))
let uint_sint (v:int) (b:base) : int = (exp (-1) (abs v)) * (v / 2) - (v % 2)
let sint_uint (v:int) (b:base) : int = 2 * (abs v) - idn (v < 0)
let int_sint (v:int) (b:base) : int = if v >= 0 then 
    (exp (-1) (abs v)) * (v / 2) - (v % 2)
  else 
    (exp (-1) (abs v)) * (v + (pow2 (b - 1)) - (v / 2)) // - (v % 2) 
let sint_int (v:int) (b:base) : int = if -(pow2 (b-2)) <= v && v < pow2 (b-2) then 
    2 * (abs v) - idn (v < 0) 
  else 
    abs (2 * v - pow2 (b-1)) - pow2 (b-1) - idn (v < pow2 (b-2))

let val_rel #d1 #ty1 #n1 #id1 #d2 #ty2 #n2 #id2 
  (f1 : field_descriptor d1 ty1 n1 id1) (f2 : field_descriptor d2 ty2 n2 id2) = 
  if ty1 = ty2 then 
    val_eq f1 f2 
  else 
  match f1, f2 with 
  | BFIELD b1, IFIELD i2 -> begin match ty1, ty2 with
                            | BOOL, UINT32 
                            | BOOL, UINT64
                            | BOOL, INT32 
                            | BOOL, INT64 -> i2 = idn b1
                            | BOOL, SINT32
                            | BOOL, SINT64 -> i2 = - (idn b1)
                            | _ -> false
                           end
  | IFIELD i1, BFIELD b2 -> begin match ty1, ty2 with 
                            | UINT32, BOOL 
                            | UINT64, BOOL 
                            | INT32, BOOL 
                            | INT64, BOOL 
                            | SINT32, BOOL 
                            | SINT64, BOOL -> b2 <> (i1 = 0)
                            | _ -> false 
                           end
  | IFIELD i1, IFIELD i2 -> begin match ty1, ty2 with 
                            | UINT32, UINT64 -> i2 = uint_promote i1
                            | UINT64, UINT64 -> i2 = uint_demote i1
                            | INT32, INT64 -> i2 = int_promote i1 
                            | INT64, INT32 -> i2 = int_demote i1
                            | SINT32, SINT64 -> i2 = sint_promote i1
                            | SINT64, SINT32 -> i2 = sint_demote i1
                            | UINT32, INT32 -> i2 = uint_int i1 32
                            | UINT64, INT64 -> i2 = uint_int i1 64
                            | INT32, UINT32 -> i2 = int_uint i1 32
                            | INT64, UINT64 -> i2 = int_uint i1 64 
                            | UINT32, SINT32 -> i2 = uint_sint i1 32 
                            | UINT64, SINT64 -> i2 = uint_sint i1 64
                            | SINT32, UINT32 -> i2 = sint_uint i1 32 
                            | SINT64, UINT64 -> i2 = sint_uint i1 64
                            | INT32, SINT32 -> i2 = int_sint i1 32 
                            | INT64, SINT64 -> i2 = int_sint i1 64
                            | SINT32, INT32 -> i2 = sint_int i1 32 
                            | SINT64, INT64 -> i2 = sint_int i1 64
                            | _ -> false
                           end 
  | SFIELD s1, SFIELD s2 -> begin match ty1, ty2 with 
                            | STRING, BYTES 
                            | BYTES, STRING -> s1 = s2
                            | _ -> false
                           end
  | _ -> false

let field_rel #d1 #ty1 #n1 #id1 #d2 #ty2 #n2 #id2 
  (f1 : field_descriptor d1 ty1 n1 id1) (f2 : field_descriptor d2 ty2 n2 id2) = 
  if (d1, ty1, id1) = (d2, ty2, id2) && val_eq f1 f2 then 
    true // Refl rule 
  else if (ty1, id1) = (ty2, id2) && val_eq f1 f2 && d1 = IMPLICIT && d2 = OPTIONAL then
    true // Add-Opt rule
  else if (ty1, id1) = (ty2, id2) && val_eq f1 f2 && d1 = OPTIONAL && d2 = IMPLICIT then 
    true // Rm-Opt rule
  else if (ty1, id1) = (ty2, id2) && val_eq f1 f2 && d1 = IMPLICIT && d2 = REPEATED then
    true // Add-Rep rule
  else if (d1, id1) = (d2, id2) && val_rel f1 f2 then 
    true // Type-Chg rule
  else
    false

let test_rel12 = field_rel f1 f2 // false
let test_rel13 = field_rel f1 f3 // true
let test_rel14 = field_rel f1 f4 // false
let test_rel15 = field_rel f1 f5 // false
let test_rel16 = field_rel f1 f6 // true
let test_rel23 = field_rel f2 f3 // false 
let test_rel24 = field_rel f2 f4 // false
let test_rel25 = field_rel f2 f5 // false
let test_rel26 = field_rel f2 f6 // false
let test_rel34 = field_rel f3 f4 // false
let test_rel35 = field_rel f3 f5 // false
let test_rel36 = field_rel f3 f6 // true
let test_rel45 = field_rel f4 f5 // true
let test_rel46 = field_rel f4 f6 // true
let test_rel54 = field_rel f5 f4 // true
let test_rel56 = field_rel f5 f6 // false, but would be true if considering multiple steps

(* 
   I realize now that this 'field_rel' only applies one rule, but I need it to be capable of 
   applying multiple rules to check for compatibility. 

   Time to take a closer look at the STLC tutorial example, I guess. See Proto3.fst
*)
