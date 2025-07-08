module Pollux.Proto.Parse

open FStar.Mul
open FStar.List.Tot.Base

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
module PartMap = FStar.PartialMap

module Desc = Pollux.Proto.Descriptors
module Vint = Pollux.Proto.Varint

let nat_to_u8 (n:nat) : U8.t = U8.uint_to_t (UInt.to_uint_t U8.n n)
let nat_to_u32 (n:nat) : U32.t = U32.uint_to_t (UInt.to_uint_t U32.n n)
let nat_to_u64 (n:nat) : U64.t = U64.uint_to_t (UInt.to_uint_t U64.n n)
let int_to_i64 (z:int) : I64.t = I64.int_to_t (Int.to_int_t I64.n z)

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

let parity (v:int) : int = 
  if v % 2 = 0 then 
    1
  else 
    (-1)

let idn c = if c then 1 else 0
let idnuw (w:Desc.width) c : (Desc.uw w) = if c then 1 else 0
let idnzw (w:Desc.width) c : (Desc.zw w) = if c then 1 else 0

let uint_change_w (w:Desc.width) (v:int) : Desc.uw w = v % pow2 w
let int_change_w (w:Desc.width) (v:int) : Desc.zw w = (v % pow2 (w-1) - (pow2 (w-1)) * idn ((v / pow2 (w-1)) % 2 = 1))
let sint_change_w (w:Desc.width) (v:int) : Desc.zw w = (v % pow2 (w-1) - (pow2 (w-1)) * idn (v < 0))
let uint_int (w:Desc.width) (v:Desc.uw w) : Desc.zw w = v - (pow2 w) * (idn (v >= pow2 (w - 1)))
let int_uint (w:Desc.width) (v:Desc.zw w) : Desc.uw w = v + (pow2 w) * (idn (v < 0))
let uint_sint (w:Desc.width) (v:Desc.uw w) : Desc.zw w = parity v * (v / 2) - (v % 2)
let sint_uint (w:Desc.width) (v:Desc.zw w) : Desc.uw w = 2 * (abs v) - idn (v < 0)
let int_sint (w:Desc.width) (v:Desc.zw w) : Desc.zw w = if v >= 0 then 
    parity v * (v / 2) - (v % 2)
  else 
    parity v * (v + (pow2 (w - 1)) - (v / 2))
let sint_int (w:Desc.width) (v:Desc.zw w) : Desc.zw w = if -(pow2 (w-2)) <= v && v < pow2 (w-2) then 
      2 * (abs v) - idn (v < 0) 
  else 
      2 * (abs v) - pow2 w - idn (v < 0)

type tag = 
| VARINT 
| I64 
| LEN 
| I32

let tag_num (t:tag) : U64.t = 
  match t with 
  | VARINT -> nat_to_u64 0  
  | I64 -> nat_to_u64 1
  | LEN -> nat_to_u64 2
  | I32 -> nat_to_u64 5

(* The [option] monad *)
// Bind operator
let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

// Sort of applicative
let (and?) (x: option 'a) (y: option 'b): option ('a & 'b)
  = match x, y with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let find_field_string (msg:Desc.md) (id: string) : option (f:Desc.fd{f._1 = id}) = 
  find (fun (f : Desc.fd) -> f._1 = id) msg.fields

let find_tag (p:Desc.pty) : tag = 
  match p with 
  | Desc.P_INT _ _ 
  | Desc.P_UINT _ _ 
  | Desc.P_SINT _ _ 
  | Desc.P_BOOL _
  | Desc.P_ENUM _ -> VARINT
  | Desc.P_FIXED 32 _
  | Desc.P_SFIXED 32 _
  | Desc.P_FLOAT _ -> I32 
  | Desc.P_FIXED 64 _ 
  | Desc.P_SFIXED 64 _ 
  | Desc.P_DOUBLE _ -> I64 
  | _ -> LEN

let encode_header (msg_d:Desc.md) (name:string) : option U64.t = 
  let? f : Desc.fd = find_field_string msg_d name in
  // TODO: Check maximum field number
  let id_n : U64.t = nat_to_u64 f._2 in
  let tag_n : U64.t = tag_num (find_tag f._3) in 
  Some U64.((id_n <<^ (nat_to_u32 3) |^ tag_n))

type bytes = list U8.t

let rec bytes_of_u64 (x:U64.t) : Tot bytes (decreases (U64.v x)) = 
  let hi = U64.(x >>^ 8ul) in
  let lo = Cast.uint64_to_uint8 U64.(logand x 255uL) in 
  if U64.lte hi 0uL then 
    [lo]
  else 
    let rx = bytes_of_u64 hi in 
    lo :: rx
   
let rec bytes_of_u32 (x:U32.t) : Tot bytes (decreases (U32.v x)) = 
  let hi = U32.(x >>^ 8ul) in
  let lo = Cast.uint32_to_uint8 U32.(logand x 255ul) in 
  if U32.lte hi 0ul then 
    [lo]
  else 
    let rx = bytes_of_u32 hi in 
    lo :: rx

let bytes_of_i64 (i:I64.t) : bytes = bytes_of_u64 (Cast.int64_to_uint64 i)
let bytes_of_i32 (i:I32.t) : bytes = bytes_of_u32 (Cast.int32_to_uint32 i)

let u64_of_s32 (s:I32.t) : U64.t = nat_to_u64 (sint_uint 32 (I32.v s))
let u64_of_s64 (s:I64.t) : U64.t = nat_to_u64 (sint_uint 64 (I64.v s))

let bytes_of_bool (b:bool) : bytes = if b then [1uy] else [0uy]

let bytes_of_string (s:string) : bytes = fold_left append [] 
  (map (fun x -> bytes_of_u32 (FStar.Char.u32_of_char x)) (String.list_of_string s))

let encode_value (v:Desc.vty) : option bytes = 
  match v with 
  | Desc.VDOUBLE (Desc.VIMPLICIT (Some v')) 
  | Desc.VDOUBLE (Desc.VOPTIONAL (Some v')) -> Some v'
  // Hopefully this (vh :: vt) pattern will only match non-empty lists
  | Desc.VDOUBLE (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append vh vt)
  | Desc.VFLOAT (Desc.VIMPLICIT (Some v'))
  | Desc.VFLOAT (Desc.VOPTIONAL (Some v')) -> Some v' 
  | Desc.VFLOAT (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append vh vt)
  | Desc.VINT32 (Desc.VIMPLICIT (Some v')) 
  | Desc.VINT32 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode (Cast.int32_to_uint64 v'))
  // FIXME: Add length prefix
  | Desc.VINT32 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_i32 vh) 
                                                   (map (fun x -> Vint.encode (Cast.int32_to_uint64 x)) vt))
  | Desc.VINT64 (Desc.VIMPLICIT (Some v')) 
  | Desc.VINT64 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode (Cast.int64_to_uint64 v'))
  | Desc.VINT64 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (Vint.encode (Cast.int64_to_uint64 vh)) 
                                                   (map (fun x -> Vint.encode (Cast.int64_to_uint64 x)) vt))
  | Desc.VUINT32 (Desc.VIMPLICIT (Some v')) 
  | Desc.VUINT32 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode (Cast.uint32_to_uint64 v'))
  | Desc.VUINT32 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (Vint.encode (Cast.uint32_to_uint64 vh)) 
                                                   (map (fun x -> Vint.encode (Cast.uint32_to_uint64 x)) vt))
  | Desc.VUINT64 (Desc.VIMPLICIT (Some v')) 
  | Desc.VUINT64 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode v')
  | Desc.VUINT64 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (Vint.encode vh) 
                                                   (map Vint.encode vt))
  | Desc.VSINT32 (Desc.VIMPLICIT (Some v')) 
  | Desc.VSINT32 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode (u64_of_s32 v'))
  | Desc.VSINT32 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (Vint.encode (u64_of_s32 vh)) 
                                                   (map (fun x -> Vint.encode (u64_of_s32 x)) vt))
  | Desc.VSINT64 (Desc.VIMPLICIT (Some v')) 
  | Desc.VSINT64 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode (u64_of_s64 v'))
  | Desc.VSINT64 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (Vint.encode (u64_of_s64 vh)) 
                                                   (map (fun x -> Vint.encode (u64_of_s64 x)) vt))
  | Desc.VFIXED32 (Desc.VIMPLICIT (Some v')) 
  | Desc.VFIXED32 (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_u32 v')
  | Desc.VFIXED32 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_u32 vh)
                                                    (map bytes_of_u32 vt))
  | Desc.VFIXED64 (Desc.VIMPLICIT (Some v')) 
  | Desc.VFIXED64 (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_u64 v')
  | Desc.VFIXED64 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_u64 vh)
                                                    (map bytes_of_u64 vt))
  | Desc.VSFIXED32 (Desc.VIMPLICIT (Some v')) 
  | Desc.VSFIXED32 (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_i32 v')
  | Desc.VSFIXED32 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_i32 vh)
                                                    (map bytes_of_i32 vt))
  | Desc.VSFIXED64 (Desc.VIMPLICIT (Some v')) 
  | Desc.VSFIXED64 (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_i64 v')
  | Desc.VSFIXED64 (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_i64 vh)
                                                    (map bytes_of_i64 vt))
  | Desc.VBOOL (Desc.VIMPLICIT (Some v'))
  | Desc.VBOOL (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_bool v')
  | Desc.VBOOL (Desc.VREPEATED (vh :: vt)) -> Some (fold_left append (bytes_of_bool vh)
                                                  (map bytes_of_bool vt))
  | Desc.VSTRING (Desc.VIMPLICIT (Some v'))
  | Desc.VSTRING (Desc.VOPTIONAL (Some v')) -> Some (bytes_of_string v')
  // FIXME: Strings, bytes and messages can be repeated by aren't packed
  | Desc.VSTRING (Desc.VREPEATED (vh :: vt)) -> Some (bytes_of_string vh)
  | Desc.VBYTES (Desc.VIMPLICIT (Some v'))
  | Desc.VBYTES (Desc.VOPTIONAL (Some v')) -> Some v'
  // FIXME: Strings, bytes and messages can be repeated by aren't packed
  | Desc.VBYTES (Desc.VREPEATED (vh :: vt)) -> Some vh
  // TODO: Add message and enum support
  | _ -> None

let encode_field (msg_d:Desc.md) (name:string) (v:Desc.vty) : option bytes = 
  let? header : U64.t = encode_header msg_d name in 
  let header_bytes : bytes = Vint.encode header in 
  let? value : bytes = encode_value v in
  Some (header_bytes @ value)

let test_msg : Desc.md = {
  name = "test";
  reserved = Set.empty;
  fields = [
    ("field1", 1, Desc.P_INT 32 Desc.P_REPEATED)
  ];
}

let test_gh = encode_header test_msg "field2"
