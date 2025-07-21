module Pollux.Proto.Descriptors

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
module Set = FStar.Set 

type float = f:list U8.t{List.length f = 4}
let float_z : float = [0uy; 0uy; 0uy; 0uy]
type double = d:list U8.t{List.length d = 8}
let double_z : double = float_z @ float_z

type width = z:int{z = 32 \/ z = 64}
type zw (w:width) = z:int{- pow2 (w-1) <= z /\ z < pow2 (w-1) } 
let zwz (w:width) : zw w = 0
type uw (w:width) = n:nat{n < pow2 w}
let uwz (w:width) : uw w = 0
 
type pdec = 
| P_IMPLICIT : pdec
| P_OPTIONAL : pdec
| P_REPEATED : pdec

let sort_pair_fst v1 v2 = (bool_of_compare String.compare) (fst v1) (fst v2)
let sort_pair_snd v1 v2 = (bool_of_compare String.compare) (snd v1) (snd v2)
let get_pair_fst l = map fst l
let get_pair_snd l = map snd l
let sort_triple_fst (#a:Type) (#b:Type) (v1:string & a & b) (v2:string & a & b) = (bool_of_compare String.compare) (v1._1) (v2._1)
let get_triple_fst (#a:Type) (#b:Type) (#c:Type) (l:list (a & b & c)) = map (fun (e:a & b & c) -> e._1) l
let get_triple_snd (#a:Type) (#b:Type) (#c:Type) (l:list (a & b & c)) = map (fun (e:a & b & c) -> e._2) l
let get_triple_thd (#a:Type) (#b:Type) (#c:Type) (l:list (a & b & c)) = map (fun (e:a & b & c) -> e._3) l

unopteq
type pty = 
| P_DOUBLE :           pdec -> pty
| P_FLOAT :            pdec -> pty 
| P_INT :    w:width -> pdec -> pty
| P_UINT :   w:width -> pdec -> pty
| P_SINT :   w:width -> pdec -> pty
| P_FIXED :  w:width -> pdec -> pty
| P_SFIXED : w:width -> pdec -> pty
| P_BOOL :             pdec -> pty
| P_STRING :           pdec -> pty
| P_BYTES :            pdec -> pty
| P_MSG :       m:md -> pdec -> pty
| P_ENUM :             pdec -> pty

and md : Type = {
  reserved: Set.set nat;
  fields: l:list (string & nat & pty){List.noRepeats (get_triple_fst l) /\ List.noRepeats (get_triple_snd l) /\ List.sorted sort_triple_fst l}
}

(* 
  F* doesn't like these as part of the recursive type block, something about needing the unopteq 
  tag and these not looking recursive enough? Either way, I want these at least as type aliases
*)
type fd = string & nat & pty 
type fields = l:list (string & nat & pty){List.noRepeats (get_triple_fst l) /\ List.noRepeats (get_triple_snd l) /\ List.sorted sort_triple_fst l}

type dvty (v:Type) =
| VIMPLICIT : v -> dvty v
| VOPTIONAL : option v -> dvty v 
| VREPEATED : list v -> dvty v

type vty = 
| VDOUBLE   : dvty double -> vty
| VFLOAT    : dvty float -> vty
| VINT      : dvty int -> vty 
| VBOOL     : dvty bool -> vty 
| VSTRING   : dvty string -> vty 
| VBYTES    : dvty bytes -> vty 
| VMSG      : dvty msg -> vty
| VENUM     : dvty unit -> vty

and vf = string & vty

and msg = m:list vf{List.sorted sort_pair_fst m /\ List.noRepeats (get_pair_fst m)} 

let empty_msg : msg = []

let init_dec (#a:Type) (dec:pdec) (def:a) = 
  match dec with 
  | P_IMPLICIT -> VIMPLICIT def 
  | P_OPTIONAL -> VOPTIONAL None 
  | P_REPEATED -> VREPEATED []
  
// Refinement needed for proof purposes
let rec init_field (f:fd) : v:vf{f._1 = v._1} = f._1, 
(match f._3 with 
 | P_DOUBLE pd -> VDOUBLE (init_dec pd double_z)
 | P_FLOAT pd -> VFLOAT (init_dec pd float_z)
 | P_INT _ pd 
 | P_UINT _ pd 
 | P_SINT _ pd 
 | P_FIXED _ pd 
 | P_SFIXED _ pd -> VINT (init_dec pd 0)
 | P_BOOL pd -> VBOOL (init_dec pd false)
 | P_STRING pd -> VSTRING (init_dec pd "")
 | P_BYTES pd -> VBYTES (init_dec pd [])
 | P_MSG md pd -> VMSG (init_dec pd (init_msg md))
 | P_ENUM pd -> VENUM (init_dec pd ()))

// Refinement needed for proof purposes
and init_fields (fs:fields) : m:msg{get_triple_fst fs = get_pair_fst m} = 
  match fs with 
  | [] -> []
  | hd :: tl -> let new_field = init_field hd in  
              let rest_fields = init_fields tl in
              let fields = new_field :: rest_fields in 
              List.noRepeats_cons new_field._1 (get_pair_fst rest_fields);
              assert List.noRepeats (get_pair_fst fields);
              fields

and init_msg (m:md) : msg = init_fields m.fields 
