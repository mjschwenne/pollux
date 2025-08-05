module Pollux.Old.Valrel

open FStar.Mul
open FStar.List.Tot.Base
open Pollux.Proto.Prelude

module U = FStar.UInt
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast.Full
module Seq = FStar.Seq
module Set = FStar.Set 
module Str = FStar.String
module Map = FStar.Map

module Desc = Pollux.Proto.Descriptors
module Vint = Pollux.Proto.Varint
module Parse = Pollux.Proto.Parse

let is_IMPLICIT_v (#t:eqtype) (d:Desc.dvty t) (v:t) : bool = 
  Desc.(match d with 
  | VIMPLICIT e -> e = v
  | _ -> false)

let is_OPTIONAL_v (#t:eqtype) (d:Desc.dvty t) (v:t) : bool = 
  Desc.(match d with 
  | VOPTIONAL (Some e) -> e = v 
  | _ -> false)

let is_REPEATED_v (#t:eqtype) (d:Desc.dvty t) (v:list t) : bool = 
  Desc.(match d with 
  | VREPEATED e -> e = v
  | _ -> false)

let is_IMPLICIT_p (p:Desc.pty) : bool = 
  Desc.(match p with 
  | P_DOUBLE P_IMPLICIT
  | P_FLOAT P_IMPLICIT
  | P_INT _ P_IMPLICIT
  | P_UINT _ P_IMPLICIT
  | P_SINT _ P_IMPLICIT
  | P_FIXED _ P_IMPLICIT
  | P_SFIXED _ P_IMPLICIT
  | P_BOOL P_IMPLICIT
  | P_STRING P_IMPLICIT
  | P_BYTES P_IMPLICIT
  | P_MSG _ P_IMPLICIT
  | P_ENUM P_IMPLICIT -> true
  | _ -> false)

let is_OPTIONAL_p (p:Desc.pty) : bool = 
  Desc.(match p with 
  | P_DOUBLE P_OPTIONAL
  | P_FLOAT P_OPTIONAL
  | P_INT _ P_OPTIONAL
  | P_UINT _ P_OPTIONAL
  | P_SINT _ P_OPTIONAL
  | P_FIXED _ P_OPTIONAL
  | P_SFIXED _ P_OPTIONAL
  | P_BOOL P_OPTIONAL
  | P_STRING P_OPTIONAL
  | P_BYTES P_OPTIONAL
  | P_MSG _ P_OPTIONAL
  | P_ENUM P_OPTIONAL -> true
  | _ -> false)

let is_REPEATED_p (p:Desc.pty) : bool = 
  Desc.(match p with 
  | P_DOUBLE P_REPEATED
  | P_FLOAT P_REPEATED
  | P_INT _ P_REPEATED
  | P_UINT _ P_REPEATED
  | P_SINT _ P_REPEATED
  | P_FIXED _ P_REPEATED
  | P_SFIXED _ P_REPEATED
  | P_BOOL P_REPEATED
  | P_STRING P_REPEATED
  | P_BYTES P_REPEATED
  | P_MSG _ P_REPEATED
  | P_ENUM P_REPEATED -> true
  | _ -> false)

let dvty_wrap (#t1:Type) (#t2:Type) (f:t1 -> t2) (d:t2) (a:Desc.dvty t1) = 
  Desc.(match a with 
  | VIMPLICIT a' -> VIMPLICIT (f a')
  | VOPTIONAL (Some a') -> VOPTIONAL (Some (f a'))
  | VOPTIONAL None -> VOPTIONAL None 
  | VREPEATED l -> VREPEATED (map f l))

let dvty_int_sint32 = dvty_wrap (Parse.int_sint 32) (Desc.zwz 32)
let dvty_int_sint_test_i = dvty_int_sint32 (Desc.VIMPLICIT (-9))
let dvty_int_sint_test_o = dvty_int_sint32 (Desc.VOPTIONAL None)
let dvty_int_sint_test_o' = dvty_int_sint32 (Desc.VOPTIONAL (Some 9))
let dvty_int_sint_test_r = dvty_int_sint32 (Desc.VREPEATED [(-9); 9])

let string_to_bytes (s:string) : bytes = [] // FIXME: Use Bytes.bytes_of_string once bytes uses bytes
let bytes_to_string (b:bytes) : string = "" // FIXME: Use Bytes.bytes_of_string once bytes uses bytes

let valid_dv (#t:Type) (dv:Desc.dvty t) (dp:Desc.pdec) : bool = 
  Desc.(match dv, dp with
  | VIMPLICIT _, P_IMPLICIT
  | VOPTIONAL _, P_OPTIONAL
  | VREPEATED _, P_REPEATED -> true
  | _ -> false)

(* Checks that the v could actually be an instance of the p *)
let valid_vty (v:Desc.vty) (p:Desc.pty) : bool = 
  Desc.(match v, p with 
  | VDOUBLE v', P_DOUBLE p'
  | VFLOAT v', P_FLOAT p'
  | VINT v', P_INT _ p'
  | VINT v', P_UINT _ p'
  | VINT v', P_SINT _ p'
  | VINT v', P_FIXED _ p'
  | VINT v', P_SFIXED _ p'
  | VBOOL v', P_BOOL p'
  | VSTRING v', P_STRING p'
  | VBYTES v', P_BYTES p' -> valid_dv v' p' 
  | _ -> false)

let same_pty (p1:Desc.pty) (p2:Desc.pty) : bool = 
  Desc.(match p1, p2 with 
  | P_DOUBLE _, P_DOUBLE _
  | P_FLOAT _, P_FLOAT _
  | P_BOOL _, P_BOOL _
  | P_STRING _, P_STRING _
  | P_BYTES _, P_BYTES _
  | P_ENUM _, P_ENUM _ -> true
  | P_INT w1 _, P_INT w2 _
  | P_UINT w1 _, P_UINT w2 _
  | P_SINT w1 _, P_SINT w2 _
  | P_FIXED w1 _, P_FIXED w2 _
  | P_SFIXED w1 _, P_SFIXED w2 _ -> w1 = w2
  | P_MSG m1 _, P_MSG m2 _ -> false // FIXME: Need decidable equality of messages?
  | _ -> false)

let comp_dvty (#t:eqtype) (v1:Desc.dvty t) (v2:Desc.dvty t) (def:t) : bool = 
 Desc.(match v1, v2 with
 | VIMPLICIT v1', VIMPLICIT v2' -> v1' = v2' 
 | VIMPLICIT v1', VOPTIONAL None -> v1' = def 
 | VIMPLICIT v1', VOPTIONAL (Some v2') -> v1' = v2'
 | VIMPLICIT v1', VREPEATED [] -> v1' = def
 | VIMPLICIT v1', VREPEATED v2' -> [v1'] = v2'
 | VOPTIONAL None, VIMPLICIT v2' -> v2' = def
 | VOPTIONAL (Some v1'), VIMPLICIT v2' -> v1' = v2'
 | VOPTIONAL None, VOPTIONAL None -> true 
 | VOPTIONAL (Some v1'), VOPTIONAL (Some v2') -> v1' = v2'
 | VOPTIONAL None, VREPEATED [] -> true
 | VOPTIONAL (Some v1'), VREPEATED v2' -> [v1'] = v2'
 | VREPEATED [], VIMPLICIT v2' -> v2' = def
 | VREPEATED v1', VIMPLICIT v2' -> v1' = [v2']
 | VREPEATED [], VOPTIONAL None -> true 
 | VREPEATED v1', VOPTIONAL (Some v2') -> v1' = [v2']
 | VREPEATED v1', VREPEATED v2' -> v1' = v2'
 | _ -> false)

let comp_vty (v1:Desc.vty) (v2:Desc.vty) : bool = 
  Desc.(match v1, v2 with 
  | VDOUBLE v1', VDOUBLE v2' -> comp_dvty v1' v2' Desc.double_z
  | VFLOAT v1', VFLOAT v2' -> comp_dvty v1' v2' Desc.float_z
  | VINT v1', VINT v2' -> comp_dvty v1' v2' 0
  | VBOOL v1', VBOOL v2' -> comp_dvty v1' v2' false
  | VSTRING v1', VSTRING v2' -> comp_dvty v1' v2' ""
  | VBYTES v1', VBYTES v2' -> comp_dvty v1' v2' []
  | _ -> false)

let width_check (p:Desc.pty) (w:Desc.width) : bool = 
  Desc.(match p with 
  | P_INT w' _ -> w' = w
  | P_UINT w' _ -> w' = w
  | P_SINT w' _ -> w' = w
  | P_FIXED w' _ -> w' = w
  | P_SFIXED w' _ -> w' = w
  | _ -> false)

unopteq
type val_rel : Desc.pty -> Desc.vty -> Desc.pty -> Desc.vty -> Type = 
  | ValTrans :
    #v1:Desc.vty ->
    #v2:Desc.vty ->
    #v3:Desc.vty ->
    #p1:Desc.pty ->
    #p2:Desc.pty ->
    #p3:Desc.pty ->
    vr1:val_rel p1 v1 p2 v2 ->
    vr2:val_rel p2 v2 p3 v3 ->
    val_rel p1 v1 p3 v3
  | ValRefl :
    v:Desc.vty ->
    p:Desc.pty ->
    val_rel p v p v
  // Rules from the original value relation
  | ValStrByt : 
    p1:Desc.pty{Desc.P_STRING? p1} ->
    v1:Desc.vty{valid_vty v1 p1} -> 
    p2:Desc.pty{Desc.P_BYTES? p1} ->
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VBYTES?.v v2 = dvty_wrap string_to_bytes [] (Desc.VSTRING?.v v1)} -> 
    val_rel p1 v1 p2 v2
  | ValBytStr : 
    p1:Desc.pty{Desc.P_BYTES? p1} ->
    v1:Desc.vty{valid_vty v1 p1} -> 
    p2:Desc.pty{Desc.P_STRING? p2} ->
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VSTRING?.v v2 = dvty_wrap bytes_to_string "" (Desc.VBYTES?.v v1)} -> 
    val_rel p1 v1 p2 v2
  | ValUintChgW : 
    p1:Desc.pty{Desc.P_UINT? p1} -> 
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_UINT? p2} -> 
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (Parse.uint_change_w (Desc.P_UINT?.w p2)) 0 (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValIntChgW : 
    p1:Desc.pty{Desc.P_INT? p1} -> 
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_INT? p2} -> 
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (Parse.int_change_w (Desc.P_INT?.w p2)) 0 (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValSintChgW : 
    p1:Desc.pty{Desc.P_SINT? p1} -> 
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_SINT? p2} -> 
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (Parse.sint_change_w (Desc.P_SINT?.w p2)) 0 (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValUintInt : 
    p1:Desc.pty{Desc.P_UINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_INT? p2 /\ Desc.P_INT?.w p2 = Desc.P_UINT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_INT?.w p2 in 
                let v2v = dvty_wrap (Parse.__uint_int w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValIntUint : 
    p1:Desc.pty{Desc.P_INT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_UINT? p2 /\ Desc.P_UINT?.w p2 = Desc.P_INT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_UINT?.w p2 in 
                let v2v = dvty_wrap (Parse.__int_uint w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValUintSint : 
    p1:Desc.pty{Desc.P_UINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_SINT? p2 /\ Desc.P_SINT?.w p2 = Desc.P_UINT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_SINT?.w p2 in 
                let v2v = dvty_wrap (Parse.__uint_sint w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValSintUint : 
    p1:Desc.pty{Desc.P_SINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_UINT? p2 /\ Desc.P_UINT?.w p2 = Desc.P_SINT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_UINT?.w p2 in 
                let v2v = dvty_wrap (Parse.__sint_uint w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValIntSint : 
    p1:Desc.pty{Desc.P_INT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_SINT? p2 /\ Desc.P_SINT?.w p2 = Desc.P_INT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_SINT?.w p2 in 
                let v2v = dvty_wrap (Parse.__int_sint w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValSintInt : 
    p1:Desc.pty{Desc.P_SINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_INT? p2 /\ Desc.P_INT?.w p2 = Desc.P_SINT?.w p1} ->
    v2:Desc.vty{let w = Desc.P_INT?.w p2 in 
                let v2v = dvty_wrap (Parse.__sint_int w) (Desc.zwz w) (Desc.VINT?.v v1) in
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = v2v} ->
    val_rel p1 v1 p2 v2
  | ValUintBool : 
    p1:Desc.pty{Desc.P_UINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_BOOL? p2} ->
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VBOOL?.v v2 = dvty_wrap (fun u -> u <> 0) false (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValBoolUint :
    p1:Desc.pty{Desc.P_BOOL? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_UINT? p2} ->
    v2:Desc.vty{let w = Desc.P_UINT?.w p2 in 
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (Parse.idn) (Desc.uwz w) (Desc.VBOOL?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValIntBool : 
    p1:Desc.pty{Desc.P_INT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_BOOL? p2} ->
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VBOOL?.v v2 = dvty_wrap (fun u -> u <> 0) false (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValBoolInt :
    p1:Desc.pty{Desc.P_BOOL? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_INT? p2} ->
    v2:Desc.vty{let w = Desc.P_INT?.w p2 in 
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (Parse.idn) (Desc.zwz w) (Desc.VBOOL?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValSintBool : 
    p1:Desc.pty{Desc.P_SINT? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_BOOL? p2} ->
    v2:Desc.vty{valid_vty v2 p2 /\ Desc.VBOOL?.v v2 = dvty_wrap (fun u -> u <> 0) false (Desc.VINT?.v v1)} ->
    val_rel p1 v1 p2 v2
  | ValBoolSint :
    p1:Desc.pty{Desc.P_BOOL? p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{Desc.P_SINT? p2} ->
    v2:Desc.vty{let w = Desc.P_SINT?.w p2 in 
                valid_vty v2 p2 /\ Desc.VINT?.v v2 = dvty_wrap (fun b -> if b then (-1) else 0) (Desc.zwz w) (Desc.VBOOL?.v v1)} ->
    val_rel p1 v1 p2 v2
  // Rules for dealing with modifiers
  | ValAddOpt :
    p1:Desc.pty{is_IMPLICIT_p p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{is_OPTIONAL_p p2 /\ same_pty p1 p2 } ->
    v2:Desc.vty{valid_vty v2 p2 /\ comp_vty v1 v2} ->
    val_rel p1 v1 p2 v2
  | ValRmOpt :
    p1:Desc.pty{is_OPTIONAL_p p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{is_IMPLICIT_p p2 /\ same_pty p1 p2 } ->
    v2:Desc.vty{valid_vty v2 p2 /\ comp_vty v1 v2} ->
    val_rel p1 v1 p2 v2
  | ValAddRep :
    p1:Desc.pty{is_IMPLICIT_p p1 \/ is_OPTIONAL_p p1} ->
    v1:Desc.vty{valid_vty v1 p1} ->
    p2:Desc.pty{is_REPEATED_p p2 /\ same_pty p1 p2} ->
    v2:Desc.vty{valid_vty v2 p2 /\ comp_vty v1 v2} ->
    val_rel p1 v1 p2 v2

// let test_str = "test"
// let test_bytes = String.list_of_string test_str

// val test_str_byt : val_rel (STRING (IMPLICIT (Some test_str))) (BYTES (IMPLICIT (Some test_bytes)))
// let test_str_byt = ValStrByt (IMPLICIT (Some test_str)) (IMPLICIT (Some test_bytes))

// val test_uint_demotion : val_rel (UINT 64 (OPTIONAL (Some 34359738370))) (UINT 32 (OPTIONAL (Some 2)))
// let test_uint_demotion = ValUintChgW (OPTIONAL (Some 34359738370)) (OPTIONAL (Some 2))

// val test_uint_int : val_rel (UINT 32 (IMPLICIT (Some 2147483656))) (INT 32 (IMPLICIT (Some (-2147483640))))
// let test_uint_int = ValUintInt (IMPLICIT (Some 2147483656)) (IMPLICIT (Some (-2147483640)))

// val test_uint_big_int : val_rel (UINT 32 (IMPLICIT (Some 2147483656))) (INT 64 (IMPLICIT (Some (-2147483640))))
// let test_uint_big_int = ValTrans test_uint_int (ValIntChgW (IMPLICIT (Some (-2147483640))) (IMPLICIT (Some (-2147483640))))

// val test_refl : val_rel (UINT 32 (IMPLICIT (Some 0))) (UINT 32 (IMPLICIT (Some 0)))
// let test_refl = ValRefl (UINT 32 (IMPLICIT (Some 0)))

// val test_add_opt : val_rel (UINT 32 (IMPLICIT (Some 0))) (UINT 32 (OPTIONAL (Some 0)))
// let test_add_opt = ValAddOpt (IMPLICIT (Some 0))

// val test_rm_opt : val_rel (SINT 64 (OPTIONAL (Some 123456))) (SINT 64 (IMPLICIT (Some 123456)))
// let test_rm_opt = ValRmOpt (OPTIONAL (Some 123456))

// val test_add_rep : val_rel (UINT 32 (IMPLICIT (Some 12))) (UINT 32 (REPEATED [12]))
// let test_add_rep = ValAddRep (IMPLICIT (Some 12))

// val test_add_rep' : val_rel (INT 32 (OPTIONAL (Some (-23)))) (INT 32 (REPEATED [-23]))
// let test_add_rep' = ValAddRep (OPTIONAL (Some (-23)))
