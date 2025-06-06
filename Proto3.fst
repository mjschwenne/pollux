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

type width = z:int{z = 32 \/ z = 64}
type zw (w:width) = z:int{- pow2 (w-1) <= z /\ z < pow2 (w-1) } 
type uw (w:width) = n:nat{n < pow2 w}
 
type proto_dec (a:Type) = 
| IMPLICIT : a -> proto_dec a
| OPTIONAL : option a -> proto_dec a
| REPEATED : list a -> proto_dec a

let is_IMPLICIT_v (#t:eqtype) (d:proto_dec t) (v:t) : bool = 
  match d with 
  | IMPLICIT e -> e = v
  | _ -> false

let is_OPTIONAL_v (#t:eqtype) (d:proto_dec t) (v:t) : bool = 
  match d with 
  | OPTIONAL (Some e) -> e = v 
  | _ -> false

let is_REPEATED_v (#t:eqtype) (d:proto_dec t) (v:list t) : bool = 
  match d with 
  | REPEATED e -> e = v
  | _ -> false

type proto_ty = 
| DOUBLE // I would add a double here, but F* literally doesn't support any kind of floating point number...
| FLOAT // See above.
| INT :    w:width -> proto_dec (zw w) -> proto_ty
| UINT :   w:width -> proto_dec (uw w) -> proto_ty
| SINT :   w:width -> proto_dec (zw w) -> proto_ty
| FIXED :  w:width -> proto_dec (uw w) -> proto_ty
| SFIXED : w:width -> proto_dec (zw w) -> proto_ty
| BOOL :               proto_dec bool -> proto_ty
| STRING :           proto_dec string -> proto_ty
| BYTES :             proto_dec bytes -> proto_ty
| MSG
| ENUM

let test_pty : proto_ty = INT 32 (REPEATED [3; 4])

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

let parity (v:int) : int = 
  if v % 2 = 0 then 
    1
  else 
    (-1)

let idn c = if c then 1 else 0
let idnuw (w:width) c : (uw w) = if c then 1 else 0
let idnzw (w:width) c : (zw w) = if c then 1 else 0

let uint_change_w (w:width) (v:int) : uw w = v % pow2 w
let int_change_w (w:width) (v:int) : zw w = (v % pow2 (w-1) - (pow2 (w-1)) * idn ((v / pow2 (w-1)) % 2 = 1))
let sint_change_w (w:width) (v:int) : zw w = (v % pow2 (w-1) - (pow2 (w-1)) * idn (v < 0))
let uint_int (w:width) (v:uw w) : zw w = v - (pow2 w) * (idn (v >= pow2 (w - 1)))
let int_uint (w:width) (v:zw w) : uw w = v + (pow2 w) * (idn (v < 0))
let uint_sint (w:width) (v:uw w) : zw w = parity v * (v / 2) - (v % 2)
let sint_uint (w:width) (v:zw w) : uw w = 2 * (abs v) - idn (v < 0)
let int_sint (w:width) (v:zw w) : zw w = if v >= 0 then 
    parity v * (v / 2) - (v % 2)
  else 
    parity v * (v + (pow2 (w - 1)) - (v / 2))
let sint_int (w:width) (v:zw w) : zw w = if -(pow2 (w-2)) <= v && v < pow2 (w-2) then 
      2 * (abs v) - idn (v < 0) 
  else 
      2 * (abs v) - pow2 w - idn (v < 0)

let pty_wrap (#t1:Type) (#t2:Type) (f:t1 -> t2) (a:proto_dec t1) = 
  match a with 
  | IMPLICIT a' -> IMPLICIT (f a')
  | OPTIONAL (Some a') -> OPTIONAL (Some (f a'))
  | OPTIONAL None -> OPTIONAL None 
  | REPEATED l -> REPEATED (List.map f l)

let proto_ty_int_sint32 = pty_wrap (int_sint 32)
let proto_ty_int_sint_test_i = proto_ty_int_sint32 (IMPLICIT (-9))
let proto_ty_int_sint_test_o = proto_ty_int_sint32 (OPTIONAL None)
let proto_ty_int_sint_test_o' = proto_ty_int_sint32 (OPTIONAL (Some 9))
let proto_ty_int_sint_test_r = proto_ty_int_sint32 (REPEATED [(-9); 9])

unopteq
type val_rel : proto_ty -> proto_ty -> Type = 
  | ValTrans :
    #v1:proto_ty ->
    #v2:proto_ty ->
    #v3:proto_ty ->
    vr1:val_rel v1 v2 ->
    vr2:val_rel v2 v3 ->
    val_rel v1 v3
  | ValRefl :
    v:proto_ty ->
    val_rel v v
  // Rules from the original value relation
  | ValStrByt : 
    v1:(proto_dec string) -> 
    v2:(proto_dec bytes){v2 = pty_wrap String.list_of_string v1} -> 
    val_rel (STRING v1) (BYTES v2)
  | ValBytStr : 
    v1:(proto_dec bytes) ->
    v2:(proto_dec string){v2 = pty_wrap String.string_of_list v1} ->
    val_rel (BYTES v1) (STRING v2)
  | ValUintChgW : 
    #w1:width ->
    #w2:width ->
    v1:(proto_dec (uw w1)) ->
    v2:(proto_dec (uw w2)){v2 = pty_wrap (uint_change_w w2) v1} ->
    val_rel (UINT w1 v1) (UINT w2 v2)
  | ValIntChgW : 
    #w1:width ->
    #w2:width ->
    v1:(proto_dec (zw w1)) ->
    v2:(proto_dec (zw w2)){v2 = pty_wrap (int_change_w w2) v1} ->
    val_rel (INT w1 v1) (INT w2 v2)
  | ValSintChgW :
    #w1:width ->
    #w2:width ->
    v1:(proto_dec (zw w1)) ->
    v2:(proto_dec (zw w2)){v2 = pty_wrap (int_change_w w2) v1} ->
    val_rel (SINT w1 v1) (SINT w2 v2)
  | ValUintInt : 
    #w:width ->
    v1:(proto_dec (uw w)) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (uint_int w) v1} -> 
    val_rel (UINT w v1) (INT w v2)
  | ValIntUint : 
    #w:width ->
    v1:(proto_dec (zw w)) ->
    v2:(proto_dec (uw w)){v2 = pty_wrap (int_uint w) v1} -> 
    val_rel (INT w v1) (UINT w v2)
  | ValUintSint : 
    #w:width ->
    v1:(proto_dec (uw w)) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (uint_sint w) v1} -> 
    val_rel (UINT w v1) (INT w v2)
  | ValIntSint : 
    #w:width ->
    v1:(proto_dec (zw w)) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (int_sint w) v1} -> 
    val_rel (INT w v1) (SINT w v2)
  | ValSintInt : 
    #w:width ->
    v1:(proto_dec (zw w)) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (int_sint w) v1} -> 
    val_rel (SINT w v1) (INT w v2)
  | ValUintBool :
    #w:width ->
    v1:(proto_dec (uw w)) ->
    v2:(proto_dec bool){v2 = pty_wrap (fun (u:uw w) -> u <> 0) v1} ->
    val_rel (UINT w v1) (BOOL v2)
  | ValBoolUint :
    #w:width ->
    v1:(proto_dec bool) ->
    v2:(proto_dec (uw w)){v2 = pty_wrap (idnuw w) v1} ->
    val_rel (BOOL v1) (UINT w v2)
  | ValIntBool : 
    #w:width ->
    v1:(proto_dec (zw w)) ->
    v2:(proto_dec bool){v2 = pty_wrap (fun (u:zw w) -> u <> 0) v1} ->
    val_rel (INT w v1) (BOOL v2)
  | ValBoolInt :
    #w:width ->
    v1:(proto_dec bool) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (idnzw w) v1} ->
    val_rel (BOOL v1) (INT w v2)
  | ValSintBool : 
    #w:width ->
    v1:(proto_dec (zw w)) ->
    v2:(proto_dec bool){v2 = pty_wrap (fun (u:zw w) -> u <> 0) v1} ->
    val_rel (SINT w v1) (BOOL v2)
  | ValBoolSint :
    #w:width ->
    v1:(proto_dec bool) ->
    v2:(proto_dec (zw w)){v2 = pty_wrap (idnzw w) v1} ->
    val_rel (BOOL v1) (SINT w v2)
  // Rules for dealing with modifiers 
  | ValAddOpt :
    #t:eqtype ->
    #pty:(proto_dec t -> proto_ty) ->
    #v:t ->
    pty1:(proto_dec t){is_IMPLICIT_v pty1 v} ->
    val_rel (pty (IMPLICIT v)) (pty (OPTIONAL (Some v)))
  | ValRmOpt :
    #t:eqtype ->
    #pty:(proto_dec t -> proto_ty) ->
    #v:t ->
    pty1:(proto_dec t){is_OPTIONAL_v pty1 v} ->
    val_rel (pty (OPTIONAL (Some v))) (pty (IMPLICIT v))
  | ValAddRep :
    #t:eqtype ->
    #pty:(proto_dec t -> proto_ty) ->
    #v:t ->
    pty1:(proto_dec t){is_IMPLICIT_v pty1 v \/ is_OPTIONAL_v pty1 v} ->
    val_rel (pty pty1) (pty (REPEATED [v]))
    

let test_str = "test"
let test_bytes = String.list_of_string test_str

val test_str_byt : val_rel (STRING (IMPLICIT test_str)) (BYTES (IMPLICIT test_bytes))
let test_str_byt = ValStrByt (IMPLICIT test_str) (IMPLICIT test_bytes)

val test_uint_demotion : val_rel (UINT 64 (OPTIONAL (Some 34359738370))) (UINT 32 (OPTIONAL (Some 2)))
let test_uint_demotion = ValUintChgW (OPTIONAL (Some 34359738370)) (OPTIONAL (Some 2))

val test_uint_int : val_rel (UINT 32 (IMPLICIT 2147483656)) (INT 32 (IMPLICIT (-2147483640)))
let test_uint_int = ValUintInt (IMPLICIT 2147483656) (IMPLICIT (-2147483640))

val test_uint_big_int : val_rel (UINT 32 (IMPLICIT 2147483656)) (INT 64 (IMPLICIT (-2147483640)))
let test_uint_big_int = ValTrans test_uint_int (ValIntChgW (IMPLICIT (-2147483640)) (IMPLICIT (-2147483640)))

val test_refl : val_rel (UINT 32 (IMPLICIT 0)) (UINT 32 (IMPLICIT 0))
let test_refl = ValRefl (UINT 32 (IMPLICIT 0))

val test_add_opt : val_rel (UINT 32 (IMPLICIT 0)) (UINT 32 (OPTIONAL (Some 0)))
let test_add_opt = ValAddOpt (IMPLICIT 0)

val test_rm_opt : val_rel (SINT 64 (OPTIONAL (Some 123456))) (SINT 64 (IMPLICIT 123456))
let test_rm_opt = ValRmOpt (OPTIONAL (Some 123456))

val test_add_rep : val_rel (UINT 32 (IMPLICIT 12)) (UINT 32 (REPEATED [12]))
let test_add_rep = ValAddRep (IMPLICIT 12)

val test_add_rep' : val_rel (INT 32 (OPTIONAL (Some (-23)))) (INT 32 (REPEATED [-23]))
let test_add_rep' = ValAddRep (OPTIONAL (Some (-23)))
