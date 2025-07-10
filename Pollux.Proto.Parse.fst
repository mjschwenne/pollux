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
module Map = FStar.Map

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
  | Desc.P_INT _ Desc.P_REPEATED
  | Desc.P_UINT _ Desc.P_REPEATED
  | Desc.P_SINT _ Desc.P_REPEATED
  | Desc.P_BOOL Desc.P_REPEATED
  | Desc.P_ENUM Desc.P_REPEATED -> LEN
  | Desc.P_INT _ _ 
  | Desc.P_UINT _ _ 
  | Desc.P_SINT _ _ 
  | Desc.P_BOOL _
  | Desc.P_ENUM _ -> VARINT
  | Desc.P_FIXED 32 Desc.P_REPEATED
  | Desc.P_SFIXED 32 Desc.P_REPEATED
  | Desc.P_FLOAT Desc.P_REPEATED -> LEN
  | Desc.P_FIXED 32 _ 
  | Desc.P_FIXED 32 _
  | Desc.P_SFIXED 32 _
  | Desc.P_FLOAT _ -> I32 
  | Desc.P_FIXED 64 Desc.P_REPEATED
  | Desc.P_SFIXED 64 Desc.P_REPEATED
  | Desc.P_DOUBLE Desc.P_REPEATED -> LEN
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

let u64_of_s32 (s:I32.t) : U64.t = nat_to_u64 (sint_uint 32 (I32.v s))
let u64_of_s64 (s:I64.t) : U64.t = nat_to_u64 (sint_uint 64 (I64.v s))

let encode_int32 (i:I32.t) : bytes = Vint.encode (Cast.int32_to_uint64 i)
let encode_int64 (i:I64.t) : bytes = Vint.encode (Cast.int64_to_uint64 i)
let encode_uint32 (u:U32.t) : bytes = Vint.encode (Cast.uint32_to_uint64 u)
let encode_sint32 (s:I32.t) : bytes = Vint.encode (u64_of_s32 s)
let encode_sint64 (s:I64.t) : bytes = Vint.encode (u64_of_s64 s)
let rec __encode_fixed32 (x:U32.t) (b:pos{b <= 4}) : Tot bytes (decreases b) = 
  let hi = U32.(x >>^ 8ul) in
  let lo = Cast.uint32_to_uint8 U32.(logand x 255ul) in 
  if b = 1 then 
    [lo]
  else 
    let rx = __encode_fixed32 hi (b-1) in 
    lo :: rx
let encode_fixed32 (f:U32.t) : bytes = __encode_fixed32 f 4
let rec __encode_fixed64 (x:U64.t) (b:pos{b <= 8}) : Tot bytes (decreases b) = 
  let hi = U64.(x >>^ 8ul) in
  let lo = Cast.uint64_to_uint8 U64.(logand x 255uL) in 
  if b = 1 then 
    [lo]
  else 
    let rx = __encode_fixed64 hi (b-1) in 
    lo :: rx
let encode_fixed64 (f:U64.t) : bytes = __encode_fixed64 f 8
let encode_sfixed32 (i:I32.t) : bytes = encode_fixed32 (Cast.int32_to_uint32 i)
let encode_sfixed64 (i:I64.t) : bytes = encode_fixed64 (Cast.int64_to_uint64 i)
let encode_bool (b:bool) : bytes = if b then [1uy] else [0uy]

let encode_implicit (#a:eqtype) (v:a) (d:a) (enc: a -> bytes) : option bytes = 
  if v = d then None else Some (enc v)
let encode_packed (#a:Type) (l:list a) (enc_one: a -> bytes) : bytes = 
  let bytes = fold_left append [] (map enc_one l) in 
  let length = Vint.encode (nat_to_u64 (length bytes)) in 
  length @ bytes

let rec encode_utf8_char (x:U32.t) : Tot bytes (decreases (U32.v x)) = 
  let hi = U32.(x >>^ 8ul) in
  let lo = Cast.uint32_to_uint8 U32.(logand x 255ul) in 
  UInt.logand_mask (U32.v x) 8;
  if U32.lte hi 0ul then 
    [lo]
  else 
    let rx = encode_utf8_char hi in 
    lo :: rx
let encode_string (s:string) : bytes = encode_packed (map Char.u32_of_char (String.list_of_string s))
                                        encode_utf8_char
// Add the length prefix, separate function for consistency
let encode_bytes (b:bytes) : bytes = encode_packed b (fun x -> [x])

let v_measure (v:Desc.vty) : nat = 
  match v with 
  | Desc.VDOUBLE v'
  | Desc.VFLOAT v'
  | Desc.VINT32 v' 
  | Desc.VINT64 v'
  | Desc.VUINT32 v' 
  | Desc.VUINT64 v' 
  | Desc.VSINT32 v' 
  | Desc.VSINT64 v' 
  | Desc.VFIXED32 v' 
  | Desc.VFIXED64 v' 
  | Desc.VSFIXED32 v' 
  | Desc.VSFIXED64 v' 
  | Desc.VBOOL v' 
  | Desc.VSTRING v' 
  | Desc.VBYTES v' 
  | Desc.VMSG v' 
  | Desc.VENUM v' -> match v' with 
                    | Desc.VIMPLICIT _ -> 0
                    | Desc.VOPTIONAL _ -> 0
                    | Desc.VREPEATED l -> List.length l

let rec encode_field (msg_d:Desc.md) (field:Desc.vf) : Tot (option bytes) (decreases %[v_measure field._2;1]) = 
    let? header : U64.t = encode_header msg_d field._1 in 
    let header_bytes : bytes = Vint.encode header in 
    let? value : bytes = encode_value msg_d field in
    Some (header_bytes @ value)

and encode_value (msg_d:Desc.md) (field:Desc.vf) : Tot (option bytes) (decreases %[v_measure field._2;0]) = 
  match field._2 with 
  | Desc.VDOUBLE (Desc.VIMPLICIT v') -> encode_implicit v' Desc.double_z id
  | Desc.VDOUBLE (Desc.VOPTIONAL (Some v')) -> Some v'
  | Desc.VDOUBLE (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) id)
  | Desc.VFLOAT (Desc.VIMPLICIT v') -> encode_implicit v' Desc.float_z id
  | Desc.VFLOAT (Desc.VOPTIONAL (Some v')) -> Some v' 
  | Desc.VFLOAT (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) id)
  | Desc.VINT32 (Desc.VIMPLICIT v') -> encode_implicit v' 0l encode_int32
  | Desc.VINT32 (Desc.VOPTIONAL (Some v')) -> Some (encode_int32 v')
  | Desc.VINT32 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_int32)
  | Desc.VINT64 (Desc.VIMPLICIT v') -> encode_implicit v' 0L encode_int64 
  | Desc.VINT64 (Desc.VOPTIONAL (Some v')) -> Some (encode_int64 v')
  | Desc.VINT64 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_int64)
  | Desc.VUINT32 (Desc.VIMPLICIT v') -> encode_implicit v' 0ul encode_uint32
  | Desc.VUINT32 (Desc.VOPTIONAL (Some v')) -> Some (encode_uint32 v')
  | Desc.VUINT32 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_uint32)
  | Desc.VUINT64 (Desc.VIMPLICIT v') -> encode_implicit v' 0uL Vint.encode
  | Desc.VUINT64 (Desc.VOPTIONAL (Some v')) -> Some (Vint.encode v')
  | Desc.VUINT64 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) Vint.encode)
  | Desc.VSINT32 (Desc.VIMPLICIT v') -> encode_implicit v' 0l encode_sint32
  | Desc.VSINT32 (Desc.VOPTIONAL (Some v')) -> Some (encode_sint32 v')
  | Desc.VSINT32 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_sint32)
  | Desc.VSINT64 (Desc.VIMPLICIT v') -> encode_implicit v' 0L encode_sint64
  | Desc.VSINT64 (Desc.VOPTIONAL (Some v')) -> Some (encode_sint64 v')
  | Desc.VSINT64 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_sint64)
  | Desc.VFIXED32 (Desc.VIMPLICIT v') -> encode_implicit v' 0ul encode_fixed32 
  | Desc.VFIXED32 (Desc.VOPTIONAL (Some v')) -> Some (encode_fixed32 v')
  | Desc.VFIXED32 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_fixed32)
  | Desc.VFIXED64 (Desc.VIMPLICIT v') -> encode_implicit v' 0uL encode_fixed64 
  | Desc.VFIXED64 (Desc.VOPTIONAL (Some v')) -> Some (encode_fixed64 v')
  | Desc.VFIXED64 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_fixed64)
  | Desc.VSFIXED32 (Desc.VIMPLICIT v') -> encode_implicit v' 0l encode_sfixed32
  | Desc.VSFIXED32 (Desc.VOPTIONAL (Some v')) -> Some (encode_sfixed32 v')
  | Desc.VSFIXED32 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_sfixed32)
  | Desc.VSFIXED64 (Desc.VIMPLICIT v') -> encode_implicit v' 0L encode_sfixed64 
  | Desc.VSFIXED64 (Desc.VOPTIONAL (Some v')) -> Some (encode_sfixed64 v')
  | Desc.VSFIXED64 (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_sfixed64)
  | Desc.VBOOL (Desc.VIMPLICIT v') -> encode_implicit v' false encode_bool
  | Desc.VBOOL (Desc.VOPTIONAL (Some v')) -> Some (encode_bool v')
  | Desc.VBOOL (Desc.VREPEATED (vh :: vt)) -> Some (encode_packed (vh :: vt) encode_bool)
  | Desc.VSTRING (Desc.VIMPLICIT v') -> encode_implicit v' "" encode_string
  | Desc.VSTRING (Desc.VOPTIONAL (Some v')) -> Some (encode_string v')
  | Desc.VSTRING (Desc.VREPEATED (vh :: vt)) -> let rest = (Desc.VSTRING (Desc.VREPEATED vt)) in 
                                              let renc = (encode_field msg_d (field._1, rest)) in 
                                              (match renc with 
                                                | None -> Some (encode_string vh)
                                                | Some r -> Some ((encode_string vh) @ r))
  | Desc.VBYTES (Desc.VIMPLICIT v') -> encode_implicit v' [] encode_bytes
  | Desc.VBYTES (Desc.VOPTIONAL (Some v')) -> Some (encode_bytes v')
  | Desc.VBYTES (Desc.VREPEATED (vh :: vt)) -> let rest = (Desc.VBYTES (Desc.VREPEATED vt)) in 
                                             let renc = (encode_field msg_d (field._1, rest)) in 
                                             (match renc with 
                                               | None -> Some (encode_bytes vh)
                                               | Some r -> Some ((encode_bytes vh) @ r))
  // TODO: Add message and enum support
  | _ -> None

let opt_append (#a:Type) (l1:list a) (l2:option (list a)) : list a =
  match l2 with 
  | None -> l1
  | Some l2' -> l1 @ l2'

let encode_message (md:Desc.md) (msg:Desc.msg) : bytes = 
  let encoder : Desc.vf -> option bytes = encode_field md in 
  fold_left opt_append [] (map encoder msg)

let tag_from_num (n:U64.t) : option tag = 
  match n with 
  | 0uL -> Some VARINT
  | 1uL -> Some I64 
  | 2uL -> Some LEN 
  | 5uL -> Some I32 
  | _ -> None 

let decode_header (enc:bytes) : option (U64.t & tag & b:bytes{length b < length enc}) =
  // FIXME: What if we have an invalid varint encoded here?
  let? header_bytes, bs = Vint.extract_varint enc in
  let header = Vint.decode header_bytes in 
  let fid = U64.( header >>^ 3ul) in 
  let tag_n = U64.( header &^ 7uL) in
  let? tag = tag_from_num tag_n in
  Some (fid, tag, bs)

let find_field (md:Desc.md) (id:nat) : option (f:Desc.fd{f._2 = id}) = 
  find (fun (f: Desc.fd) -> f._2 = id) md.fields

let rec decode_field (md:Desc.md) (enc:bytes) : Tot (option (Desc.vf & b:bytes{length b < length enc})) (decreases (length enc)) =
  // FIXME: Find a way to skip unknown fields
  match decode_header enc with 
  | None -> None 
  | Some (fid, tag, bs) -> (match find_field md (U64.v fid) with 
                          | None -> None 
                          | Some field -> (match decode_value md field._3 bs with 
                                          | None -> None 
                                          | Some (v, bs') -> Some ((field._1, v), bs')))
  // So apparently the monadic let? doesn't like the bytes length decreasing 
  // clause.                                          
  // let? fid, tag, bs = decode_header enc in 
  // let? field = find_field md (U64.v fid) in 
  // let? value, bs' = decode_value md field._3 bs in 
  // let vfv : Desc.vf = (field._1, value) in
  // Some ((field._1, value), bs')

and decode_value (md:Desc.md) (pf:Desc.pty) (enc:bytes) : Tot (option (Desc.vty & b:bytes{length b < length enc})) (decreases (length enc)) = 
  match pf with 
  | Desc.P_INT 32 Desc.P_IMPLICIT -> None 
  | _ -> None
  
