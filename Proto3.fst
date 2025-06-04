module Proto3
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

type byte = String.char
type bytes = list byte
 
type proto_dec (a:Type) = 
| IMPLICIT : a -> proto_dec a
| OPTIONAL : option a -> proto_dec a
| REPEATED : list a -> proto_dec a

type proto_ty = 
| DOUBLE // I would add a double here, but F* literally doesn't support any kind of floating point number...
| FLOAT // See above.
| INT32 : proto_dec int -> proto_ty
| INT64 : proto_dec int -> proto_ty
| UINT32 : proto_dec int -> proto_ty // Should this be nat?
| UINT64 : proto_dec int -> proto_ty // Should this be nat?
| SINT32 : proto_dec int -> proto_ty
| SINT64 : proto_dec int -> proto_ty
| FIXED32 : proto_dec int -> proto_ty
| FIXED64 : proto_dec int -> proto_ty
| SFIXED32 : proto_dec int -> proto_ty
| SFIXED64 : proto_dec int -> proto_ty
| BOOL : proto_dec bool -> proto_ty
| STRING : proto_dec string -> proto_ty
| BYTES : proto_dec bytes -> proto_ty
| MSG
| ENUM

let test : proto_ty = INT32 (REPEATED [3; 4])

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

unopteq
type val_rel : proto_ty -> proto_ty -> Type = 
  | ValTrans :
    #f1:proto_ty ->
    #f2:proto_ty ->
    #f3:proto_ty ->
    vr1:val_rel f1 f2 ->
    vr2:val_rel f2 f3 ->
    val_rel f1 f3
  | ValRefl :
    f:proto_ty ->
    val_rel f f
  // Rules from the original value relation
  | ValStrByt : 
    f1:string -> 
    f2:bytes{f2 = String.list_of_string f1} -> 
    val_rel (STRING (IMPLICIT f1)) (BYTES (IMPLICIT f2))
  | ValBytStr : 
    f1:bytes ->
    f2:string{f2 = String.string_of_list f1} ->
    val_rel (BYTES (IMPLICIT f1)) (STRING (IMPLICIT f2))
  | ValUintPro : 
    f1:int ->
    f2:int{f2 = uint_promote f1} ->
    val_rel (UINT32 (IMPLICIT f1)) (UINT64 (IMPLICIT f2))
  | ValUintDem :
    f1:int ->
    f2:int{f2 = uint_demote f1} ->
    val_rel (UINT64 (IMPLICIT f1)) (UINT32 (IMPLICIT f2))
  | ValIntPro : 
    f1:int ->
    f2:int{f2 = int_promote f1} ->
    val_rel (INT32 (IMPLICIT f1)) (INT64 (IMPLICIT f2))
  | ValIntDem : 
    f1:int ->
    f2:int{f2 = int_demote f1} ->
    val_rel (INT64 (IMPLICIT f1)) (INT32 (IMPLICIT f2))
  | ValSintPro :
    f1:int ->
    f2:int{f2 = sint_promote f1} ->
    val_rel (SINT32 (IMPLICIT f1)) (SINT64 (IMPLICIT f2))
  | ValSintDem : 
    f1:int ->
    f2:int{f2 = sint_demote f1} ->
    val_rel (SINT64 (IMPLICIT f1)) (SINT32 (IMPLICIT f2))
  | ValUintInt32 : 
    f1:int ->
    f2:int{f2 = uint_int f1 32} -> 
    val_rel (UINT32 (IMPLICIT f1)) (INT32 (IMPLICIT f2))
  | ValUintInt64 : 
    f1:int ->
    f2:int{f2 = uint_int f1 64} -> 
    val_rel (UINT64 (IMPLICIT f1)) (INT64 (IMPLICIT f2))
  | ValIntUint32 : 
    f1:int ->
    f2:int{f2 = int_uint f1 32} -> 
    val_rel (INT32 (IMPLICIT f1)) (UINT32 (IMPLICIT f2))
  | ValIntUint64 : 
    f1:int ->
    f2:int{f2 = int_uint f1 64} -> 
    val_rel (INT64 (IMPLICIT f1)) (UINT64 (IMPLICIT f2))
  | ValUintSint32 : 
    f1:int ->
    f2:int{f2 = uint_sint f1 32} -> 
    val_rel (UINT32 (IMPLICIT f1)) (SINT32 (IMPLICIT f2))
  | ValUintSint64 : 
    f1:int ->
    f2:int{f2 = uint_sint f1 64} -> 
    val_rel (UINT64 (IMPLICIT f1)) (SINT64 (IMPLICIT f2))
  | ValIntSint32 : 
    f1:int ->
    f2:int{f2 = int_sint f1 32} ->
    val_rel (INT32 (IMPLICIT f1)) (SINT32 (IMPLICIT f2))
  | ValIntSint64 : 
    f1:int ->
    f2:int{f2 = int_sint f1 64} ->
    val_rel (INT64 (IMPLICIT f1)) (SINT64 (IMPLICIT f2))
  | ValSintInt32 : 
    f1:int ->
    f2:int{f2 = sint_int f1 32} ->
    val_rel (SINT32 (IMPLICIT f1)) (INT32 (IMPLICIT f2))
  | ValSintInt64 : 
    f1:int ->
    f2:int{f2 = sint_int f1 64} ->
    val_rel (SINT64 (IMPLICIT f1)) (INT64 (IMPLICIT f2))
  | ValUint32Bool :
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (UINT32 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValUint64Bool :
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (UINT64 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValBoolUint32 :
    f1:bool ->
    f2:int{f2 = idn f1} ->
    val_rel (BOOL (IMPLICIT f1)) (UINT32 (IMPLICIT f2))
  | ValBoolUint64 :
    f1:bool ->
    f2:int{f2 = idn f1} ->
    val_rel (BOOL (IMPLICIT f1)) (UINT64 (IMPLICIT f2))
  | ValInt32Bool : 
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (INT32 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValInt64Bool :
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (INT64 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValBoolInt32 :
    f1:bool ->
    f2:int{f2 = idn f1} ->
    val_rel (BOOL (IMPLICIT f1)) (INT32 (IMPLICIT f2))
  | ValBoolInt64 :
    f1:bool ->
    f2:int{f2 = idn f1} ->
    val_rel (BOOL (IMPLICIT f1)) (INT64 (IMPLICIT f2))
  | ValSint32Bool : 
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (SINT32 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValSint64Bool :
    f1:int ->
    f2:bool{f2 = (f1 <> 0)} ->
    val_rel (SINT64 (IMPLICIT f1)) (BOOL (IMPLICIT f2))
  | ValBoolSint32 :
    f1:bool ->
    f2:int{f2 = - (idn f1)} ->
    val_rel (BOOL (IMPLICIT f1)) (SINT32 (IMPLICIT f2))
  | ValBoolSint64 :
    f1:bool ->
    f2:int{f2 = - (idn f1)} ->
    val_rel (BOOL (IMPLICIT f1)) (SINT64 (IMPLICIT f2))
  // Rules for dealing with modifiers 
  | ValAddOpt :
    #t:Type ->
    pty:(proto_dec t -> proto_ty) ->
    v:t ->
    val_rel (pty (IMPLICIT v)) (pty (OPTIONAL (Some v)))

let test_str = "test"
let test_bytes = String.list_of_string test_str

val test_str_byt : val_rel (STRING (IMPLICIT test_str)) (BYTES (IMPLICIT test_bytes))
let test_str_byt = ValStrByt test_str test_bytes

val test_uint_demotion : val_rel (UINT64 (IMPLICIT 34359738370)) (UINT32 (IMPLICIT 2))
let test_uint_demotion = ValUintDem 34359738370 2

val test_uint_int : val_rel (UINT32 (IMPLICIT 2147483656)) (INT32 (IMPLICIT (-2147483640)))
let test_uint_int = ValUintInt32 2147483656 (-2147483640)

val test_uint_big_int : val_rel (UINT32 (IMPLICIT 2147483656)) (INT64 (IMPLICIT (-2147483640)))
let test_uint_big_int = ValTrans test_uint_int (ValIntPro (-2147483640) (-2147483640))

val test_refl : val_rel (UINT32 (IMPLICIT 0)) (UINT32 (IMPLICIT 0))
let test_refl = ValRefl (UINT32 (IMPLICIT 0))

// FIXME: For some reason, declaring the type ahead of time causes an error, 
// despite the fact that the reported type is the same as the one below...
// val test_add_opt : val_rel (INT32 (IMPLICIT (-9))) (INT32 (OPTIONAL (Some (-9))))
let test_add_opt = ValAddOpt INT32 (-9)
