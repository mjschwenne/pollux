module Pollux.Proto.Descriptors

open FStar.Mul
open FStar.List.Tot.Base

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

unopteq
type md : Type = {
  name: string;
  reserved: Set.set nat;
  fields: list fd
}

type dvty (v:Type) =
| VIMPLICIT : v -> dvty v
| VOPTIONAL : option v -> dvty v 
| VREPEATED : list v -> dvty v

type vty = 
| VDOUBLE   : dvty double -> vty
| VFLOAT    : dvty float -> vty
| VINT32    : dvty I32.t -> vty 
| VINT64    : dvty I64.t -> vty 
| VUINT32   : dvty U32.t -> vty 
| VUINT64   : dvty U64.t -> vty 
| VSINT32   : dvty I32.t -> vty 
| VSINT64   : dvty I64.t -> vty 
| VFIXED32  : dvty U32.t -> vty 
| VFIXED64  : dvty U64.t -> vty 
| VSFIXED32 : dvty I32.t -> vty 
| VSFIXED64 : dvty I64.t -> vty 
| VBOOL     : dvty bool -> vty 
| VSTRING   : dvty string -> vty 
| VBYTES    : dvty (list U8.t) -> vty 
| VMSG      : dvty unit -> vty
| VENUM     : dvty unit -> vty

type vf = string & vty
let sort_vf (v1:vf) (v2:vf) : bool = String.compare v1._1 v2._1 <= 0

type msg = m:list vf{List.sorted sort_vf m} 
let empty_msg : msg = []

let msg_field_names (m:msg) : list string = map (fun (f:vf) -> f._1) m
