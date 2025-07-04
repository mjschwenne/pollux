module Proto
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

(* Placeholder, until I have something actually finished for variable width integer encoding *)
let vint64 = n:nat{n < pow2 64}
let vint32 = n:nat{n < pow2 32}
  (* 
     Simple inductive type for the tags/value combinations in an encoded proto 
     Tag-Length-Value field. 

     Not modeling SGROUP or EGROUP this these types are deprecated.
   *)
type proto_enc_lv : Type = 
| VARINT : vint64 -> proto_enc_lv
| I64 : U64.t -> proto_enc_lv 
| LEN : B.bytes -> proto_enc_lv
| I32 : U32.t -> proto_enc_lv

type proto_enc_field : Type = vint32 & proto_enc_lv

type proto_enc_msg : Type = list proto_enc_field

let proto_compat_field (f1 f2 : proto_enc_field) : bool = 
  f1._1 = f2._1 && (match f1._2, f2._2 with 
  | VARINT v1, VARINT v2 -> v1 = v2
  | I64 v1, I64 v2 -> v1 = v2
  | LEN v1, LEN v2 -> B.length v1 = B.length v2 
  | I32 v1, I32 v2 -> v1 = v2 
  | _, _ -> false)

let msg1 : proto_enc_msg = [(2, VARINT 3)]

type proto_enum_descriptor = {
  name : string;
  fields : list proto_enum_field;
}
and proto_enum_field = string & nat

unopteq
type proto_msg_descriptor : Type = {
  name: string;
  reserved: Set.set nat;
  fields: list proto_field_descriptor
}
and proto_field_descriptor : Type = 
| FIELD : proto_decorator -> proto_terminal -> string -> nat -> proto_field_descriptor
| MAP : proto_decorator -> proto_terminal -> proto_terminal -> string -> nat -> proto_field_descriptor
| ONEOF : proto_decorator -> list proto_terminal -> string -> nat -> proto_field_descriptor

and proto_decorator : Type = 
| IMPLICIT 
| OPTION
| REPEATED

and proto_terminal : Type = 
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
| MSG : proto_msg_descriptor -> proto_terminal
| ENUM : proto_enum_descriptor -> proto_terminal

let msg_descriptor1 : proto_msg_descriptor = {
      name = "test"; 
      reserved = Set.empty;
      fields = [
        FIELD IMPLICIT STRING "test_field" 2;
        FIELD REPEATED INT32 "test_int" 3;
      ];
    }

let f : proto_field_descriptor = match (List.nth msg_descriptor1.fields 1) with 
  | Some f -> f


type proto_enc_tv : eqtype = 
| VARINT' : t:proto_terminal{
          match t with
          | INT32 -> true
          | INT64 -> true
          | UINT32 -> true
          | UINT64 -> true
          | SINT32 -> true
          | SINT64 -> true
          | ENUM _ -> true
          | BOOL -> true
          | _ -> false
          } -> proto_enc_tv
| I64' : t:proto_terminal{
          match t with
          | FIXED64 -> true 
          | SFIXED64 -> true
          | _ -> false
          } -> proto_enc_tv
| LEN' : t:proto_terminal{
          match t with 
          | STRING -> true 
          | BYTES -> true 
          | MSG _ -> true 
          | _ -> false
          } -> proto_enc_tv
| I32' : t:proto_terminal{
          match t with
          | FIXED32 -> true 
          | SFIXED32 -> true
          | _ -> false
          } -> proto_enc_tv

type proto_enc_field' : Type = vint32 & proto_enc_tv

let proto_compat_field' (f1 f2 : proto_enc_field') : bool = 
  f1._1 = f2._1 && (match f1._2, f2._2 with 
  | VARINT' v1, VARINT' v2 -> v1 = v2
  | I64' v1, I64' v2 -> v1 = v2
  | LEN' v1, LEN' v2 -> v1 = v2 
  | I32' v1, I32' v2 -> v1 = v2 
  | _, _ -> false)

(* Beginning of comp and val relation *)

(*
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

type proto_spec_type : Type = 
  | SP_INT : int -> proto_spec_type
  | SP_BOOL : bool -> proto_spec_type
  | SP_STR : string -> proto_spec_type
  | SP_ENUM : nat -> proto_spec_type

let val_rel (v1 : proto_spec_type) (t1 : proto_terminal) (v2 : proto_spec_type) (t2 : proto_terminal) = 
  if t1 = t2 then 
     v1 = v2 
  else 
  match v1, v2 with 
  | SP_INT i1, SP_INT i2 -> begin match t1, t2 with 
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
  | SP_STR s1, SP_STR s2 -> begin match t1, t2 with 
                            | STRING, BYTES 
                            | BYTES, STRING -> s1 = s2
                            | _ -> false
                           end
  | SP_BOOL b1, SP_INT i2 -> begin match t1, t2 with 
                            | BOOL, UINT32 
                            | BOOL, UINT64
                            | BOOL, INT32 
                            | BOOL, INT64 -> i2 = idn b1
                            | BOOL, SINT32
                            | BOOL, SINT64 -> i2 = - (idn b1)
                            | _ -> false
                           end 
  | SP_INT i1, SP_BOOL b1 -> begin match t1, t2 with 
                            | UINT32, BOOL 
                            | UINT64, BOOL 
                            | INT32, BOOL 
                            | INT64, BOOL 
                            | SINT32, BOOL 
                            | SINT64, BOOL -> b1 = (i1 = 0)
                            | _ -> false 
                           end
  | _ -> false
  
(* 
  From protobuf tests:

  i32 encoded value: -9 (dec)
  i32 encoded value: 0000000000000000000000000000000011111111111111111111111111110111 (bin)
  s32 decoded value: 0000000000000000000000000000000011111111111111111111111111110111 (bin)
  s32 decoded value: -2147483644 (dec)
*)
let test_val_rel = val_rel (SP_INT (-9)) INT32 (SP_INT (-2147483644)) SINT32

let comp_rel_field (f1 f2:proto_field_descriptor) : bool = 
  match f1, f2 with 
  | FIELD pd1 pt1 n1 id1, FIELD pd2 pt2 n2 id2 -> if (pd1, pt1, n1, id1) = (pd2, pt2, n2, id2) then 
                                                    true // Refl rule
                                                 else if (pt1, id1) = (pt2, id2) && pd1 = IMPLICIT 
                                                          && pd2 = OPTION then 
                                                    true // Add-Opt rule
                                                 else if (pt1, id1) = (pt2, id2) && pd1 = OPTION 
                                                          && pd2 = IMPLICIT then 
                                                    true // Rm-Opt rule
                                                 else if (pt1, id1) = (pt2, id2) && pd1 = IMPLICIT
                                                          && pd2 = REPEATED then 
                                                    true // Add-Rep rule
                                                 (* 
                                                   TODO How to represent Type-Chg rule? 
                                                   I don't have a value here... 
                                                 *)
                                                 else 
                                                    false // No other field rule applies
  | _ -> false
