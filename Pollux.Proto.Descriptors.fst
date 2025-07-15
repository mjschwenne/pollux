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
| P_MSG :              pdec -> pty
| P_ENUM :             pdec -> pty

type fd : Type = string & nat & pty

let get_fids (l:list fd) : list nat = map (fun (e : fd) -> e._2) l
let get_names (l:list fd) : list string = map (fun (e : fd) -> e._1) l

let sort_fd (f1:fd) (f2:fd) : bool = (bool_of_compare String.compare) (f1._1) (f2._1) 

type fields = l:list fd{List.noRepeats (get_fids l) /\ List.noRepeats (get_names l) /\ List.sorted sort_fd l}
unopteq
type md : Type = {
  reserved: Set.set nat;
  fields: fields
}

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
| VMSG      : dvty unit -> vty
| VENUM     : dvty unit -> vty

type vf = string & vty

let sort_vf (v1:vf) (v2:vf) : bool = (bool_of_compare String.compare) v1._1 v2._1

let msg_names (m:list vf) : list string = map (fun (f:vf) -> f._1) m
type msg = m:list vf{List.sorted sort_vf m /\ List.noRepeats (msg_names m)} 

let empty_msg : msg = []

let init_dec (#a:Type) (dec:pdec) (def:a) = 
  match dec with 
  | P_IMPLICIT -> VIMPLICIT def 
  | P_OPTIONAL -> VOPTIONAL None 
  | P_REPEATED -> VREPEATED []
  
let init_field (f:fd) : vf = f._1, 
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
 | P_MSG pd -> VMSG (init_dec pd ())
 | P_ENUM pd -> VENUM (init_dec pd ())
)

// Refinement needed for prove purposes
let rec init_fields (fs:fields) : m:msg{get_names fs = msg_names m} = 
  match fs with 
  | [] -> []
  | hd :: tl -> let new_field = init_field hd in  
              let rest_fields = init_fields tl in
              let fields = new_field :: rest_fields in 
              List.noRepeats_cons new_field._1 (msg_names rest_fields);
              assert List.noRepeats (msg_names fields);
              fields

let init_msg (m:md) : msg = init_fields m.fields 
