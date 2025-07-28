module Pollux.Proto.Parse

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

let nat_to_u8 (n:nat) : U8.t = U8.uint_to_t (UInt.to_uint_t U8.n n)
let nat_to_u32 (n:nat) : U32.t = U32.uint_to_t (UInt.to_uint_t U32.n n)
let nat_to_u64 (n:nat) : U64.t = U64.uint_to_t (UInt.to_uint_t U64.n n)
let int_to_i32 (z:int) : I32.t = I32.int_to_t (Int.to_int_t I32.n z)
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

let find_field_string (msg:Desc.md) (id: string) : option (f:Desc.fd{f._1 = id}) = 
  find (fun (f : Desc.fd) -> f._1 = id) msg.fields

let find_tag (p:Desc.pty) : tag = 
  Desc.(match p with 
  // Check for packed fields first
  | P_INT _ P_REPEATED
  | P_UINT _ P_REPEATED
  | P_SINT _ P_REPEATED
  | P_BOOL P_REPEATED
  | P_ENUM P_REPEATED
  | P_FIXED _ P_REPEATED
  | P_SFIXED _ P_REPEATED
  | P_FLOAT P_REPEATED
  | P_DOUBLE P_REPEATED -> LEN
  | P_INT _ _ 
  | P_UINT _ _ 
  | P_SINT _ _ 
  | P_BOOL _
  | P_ENUM _ -> VARINT
  | P_FIXED 32 _ 
  | P_FIXED 32 _
  | P_SFIXED 32 _
  | P_FLOAT _ -> I32 
  | P_FIXED 64 _ 
  | P_SFIXED 64 _ 
  | P_DOUBLE _ -> I64 
  | _ -> LEN)

let encode_header (msg_d:Desc.md) (name:string) : option U64.t = 
  let? f : Desc.fd = find_field_string msg_d name in
  // TODO: Check maximum field number
  let id_n : U64.t = nat_to_u64 f._2 in
  let tag_n : U64.t = tag_num (find_tag f._3) in 
  Some U64.((id_n <<^ (nat_to_u32 3) |^ tag_n))

let u64_of_s32 (s:int) : U64.t = nat_to_u64 (sint_uint 32 (I32.v (int_to_i32 s)))
let u64_of_s64 (s:int) : U64.t = nat_to_u64 (sint_uint 64 (I64.v (int_to_i64 s)))

let encode_int32 (i:int) : bytes = Vint.encode (Cast.int64_to_uint64 (int_to_i64 i))
let encode_int64 (i:int) : bytes = Vint.encode (Cast.int64_to_uint64 (int_to_i64 i))
let encode_uint32 (u:int) : bytes = Vint.encode (Cast.int64_to_uint64 (int_to_i64 u))
let encode_uint64 (u:int) : bytes = Vint.encode (Cast.int64_to_uint64 (int_to_i64 u))
let encode_sint32 (s:int) : bytes = Vint.encode (u64_of_s32 s)
let encode_sint64 (s:int) : bytes = Vint.encode (u64_of_s64 s)
let rec __encode_fixed32 (x:U32.t) (b:pos{b <= 4}) : Tot bytes (decreases b) = 
  let hi = U32.(x >>^ 8ul) in
  let lo = Cast.uint32_to_uint8 U32.(logand x 255ul) in 
  if b = 1 then 
    [lo]
  else 
    let rx = __encode_fixed32 hi (b-1) in 
    lo :: rx
let encode_fixed32 (f:int) : bytes = __encode_fixed32 (Cast.int32_to_uint32 (int_to_i32 f)) 4
let rec __encode_fixed64 (x:U64.t) (b:pos{b <= 8}) : Tot bytes (decreases b) = 
  let hi = U64.(x >>^ 8ul) in
  let lo = Cast.uint64_to_uint8 U64.(logand x 255uL) in 
  if b = 1 then 
    [lo]
  else 
    let rx = __encode_fixed64 hi (b-1) in 
    lo :: rx
let encode_fixed64 (f:int) : bytes = __encode_fixed64 (Cast.int64_to_uint64 (int_to_i64 f)) 8
let encode_sfixed32 (i:int) : bytes = encode_fixed32 i
let encode_sfixed64 (i:int) : bytes = encode_fixed64 i
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


let encode_dec_packed (#a:eqtype) (field:Desc.dvty a) (def:a) (encode_one:a -> bytes) : option bytes = 
  Desc.(match field with 
  | VIMPLICIT v' -> encode_implicit v' def encode_one 
  | VOPTIONAL (Some v') -> Some (encode_one v')
  | VREPEATED (vh :: vt) -> Some (encode_packed (vh :: vt) encode_one)
  | _ -> None)

let find_encode_one (msg_d:Desc.md) (name:string) : option (int -> bytes) = 
  let? f : Desc.fd = find_field_string msg_d name in
  Desc.(match f._3 with 
  | P_INT 32 _ -> Some encode_int32
  | P_INT 64 _ -> Some encode_int64
  | P_UINT 32 _ -> Some encode_uint32
  | P_UINT 64 _ -> Some encode_uint64
  | P_SINT 32 _ -> Some encode_sint32
  | P_SINT 64 _ -> Some encode_sint64 
  | P_FIXED 32 _ -> Some encode_fixed32
  | P_FIXED 64 _ -> Some encode_fixed64
  | P_SFIXED 32 _ -> Some encode_sfixed32
  | P_SFIXED 64 _ -> Some encode_sfixed64
  | _ -> None)

let opt_append (#a:Type) (l1:list a) (l2:option (list a)) : list a =
  match l2 with 
  | None -> l1
  | Some l2' -> l1 @ l2'

let rec fields_measure (fs:Desc.fields) : nat = 
  Desc.(match fs with 
  | Nil -> 0 
  | f :: ftl -> (match f._3 with 
                | P_DOUBLE _
                | P_FLOAT _ 
                | P_INT _ _
                | P_UINT _ _ 
                | P_SINT _ _
                | P_FIXED _ _ 
                | P_SFIXED _ _ 
                | P_BOOL _ 
                | P_STRING _ 
                | P_BYTES _
                | P_ENUM _ -> fields_measure ftl
                | P_MSG m _ -> 1 + fields_measure m.fields + fields_measure ftl))

let p_measure (md:Desc.md) : nat = fields_measure md.fields

let rec find_nested_md_f (fs:Desc.fields) (f:Desc.vf) : option (m:Desc.md{p_measure m < fields_measure fs}) = 
  match fs with 
  | Nil -> None 
  | h :: t -> if h._1 = f._1 then (
             match h._3 with 
             | Desc.P_MSG m _ -> Some m
             | _ -> None
            ) else 
              match find_nested_md_f t f with 
              | None -> None
              | Some m -> assert fields_measure t <= fields_measure fs; Some m

let find_nested_md (m:Desc.md) (f:Desc.vf) : option (m':Desc.md{p_measure m' < p_measure m}) = 
  find_nested_md_f m.fields f

let v_measure (v:Desc.vty) : nat = 
  Desc.(match v with 
  | VDOUBLE v'
  | VFLOAT v'
  | VINT v' 
  | VBOOL v' 
  | VSTRING v' 
  | VBYTES v' 
  | VMSG v'
  | VENUM v' -> (match v' with 
               | VIMPLICIT _
               | VOPTIONAL _ -> 1
               | VREPEATED l -> List.length l))

let rec vs_measure (vs:Desc.msg) : nat = 
  match vs with 
  | Nil -> 0 
  | h :: t -> 1 + v_measure h._2 + vs_measure t

let rec encode_field (msg_d:Desc.md) (field:Desc.vf) : Tot (option bytes) 
  (decreases %[p_measure msg_d;vs_measure [field];1]) = 
    let? header : U64.t = encode_header msg_d field._1 in 
    let header_bytes : bytes = Vint.encode header in 
    let? value : bytes = encode_value msg_d field in
    Some (header_bytes @ value)

and encode_value (msg_d:Desc.md) (field:Desc.vf) : Tot (option bytes) 
  (decreases %[p_measure msg_d;vs_measure [field];0]) = 
    Desc.(match field._2 with 
    | VDOUBLE v' -> encode_dec_packed v' double_z id
    | VFLOAT v' -> encode_dec_packed v' float_z id
    | VINT v' -> let? encode_one = find_encode_one msg_d field._1 in encode_dec_packed v' 0 encode_one 
    | VBOOL v' -> encode_dec_packed v' false encode_bool 
    | VSTRING (VIMPLICIT v') -> encode_implicit v' "" encode_string
    | VSTRING (VOPTIONAL (Some v')) -> Some (encode_string v')
    | VSTRING (VREPEATED (vh :: vt)) -> let rest = (VSTRING (VREPEATED vt)) in 
                                                (match encode_field msg_d (field._1, rest) with 
                                                    | None -> Some (encode_string vh)
                                                    | Some r -> Some ((encode_string vh) @ r))
    | VBYTES (VIMPLICIT v') -> encode_implicit v' [] encode_bytes
    | VBYTES (VOPTIONAL (Some v')) -> Some (encode_bytes v')
    | VBYTES (VREPEATED (vh :: vt)) -> let rest = (VBYTES (VREPEATED vt)) in 
                                                (match encode_field msg_d (field._1, rest) with 
                                                | None -> Some (encode_bytes vh)
                                                | Some r -> Some ((encode_bytes vh) @ r))
    | VMSG (VIMPLICIT v')
    | VMSG (VOPTIONAL (Some v')) -> let? md = find_nested_md msg_d field in 
                                   len_prefix_encode_message' md v'
    | VMSG (VREPEATED (vh :: vt)) -> let? md = find_nested_md msg_d field in 
                                   let rest = (VMSG (VREPEATED vt)) in 
                                   (match encode_field msg_d (field._1, rest) with 
                                   | None -> len_prefix_encode_message' md vh
                                   | Some r -> (match len_prefix_encode_message' md vh with 
                                              | None -> Some r 
                                              | Some e -> Some (e @ r)))
    // TODO: Add enum, oneof and map support
    | _ -> None)

and encode_message' (msg_d:Desc.md) (msg:Desc.msg) : Tot (option bytes) 
  (decreases %[p_measure msg_d;vs_measure msg;2]) = 
    match msg with 
    | Nil -> None
    | h :: t -> let h_enc = encode_field msg_d h in 
                match encode_message' msg_d t with 
                | None -> h_enc
                | Some r -> (match h_enc with | None -> Some r | Some e -> Some (e @ r))

and len_prefix_encode_message' (msg_d:Desc.md) (msg:Desc.msg) : Tot (option bytes) 
  (decreases %[p_measure msg_d;vs_measure msg; 3]) = 
    let? msg_bytes = encode_message' msg_d msg in
    Some (Vint.encode (nat_to_u64 (length msg_bytes)) @ msg_bytes)

let encode_message (msg_d:Desc.md) (msg:Desc.msg) : bytes = 
  match encode_message' msg_d msg with 
  | None -> []
  | Some enc -> enc 

let tag_from_num (n:U64.t) : option tag = 
  match n with 
  | 0uL -> Some VARINT
  | 1uL -> Some I64 
  | 2uL -> Some LEN 
  | 5uL -> Some I32 
  | _ -> None 

let decode_header (enc:bytes) : option (nat & tag & b:bytes{length b < length enc}) =
  let? header_bytes, bs = Vint.extract_varint enc in
  let header = Vint.decode header_bytes in 
  let fid : nat = U64.(v (header >>^ 3ul)) in 
  let tag_n = U64.( header &^ 7uL) in
  let? tag = tag_from_num tag_n in
  Some (fid, tag, bs)

let rec find_field' (fs:Desc.fields) (id:nat) : option (f:Desc.fd{f._2 = id /\ fields_measure [f] <= fields_measure fs}) = 
  match fs with 
  | Nil -> None 
  | h :: t -> if h._2 = id then (assert fields_measure [h] <= fields_measure fs; Some h)
            else 
            match find_field' t id with 
            | None -> None 
            | Some m -> assert fields_measure t <= fields_measure fs; Some m
               
let find_field (m:Desc.md) (id:nat) : option (f:Desc.fd{f._2 = id /\ fields_measure [f] <= p_measure m}) =
  find_field' m.fields id 

let rec take (#a:Type) (n:nat) (l:list a) : option (list a & list a) = 
  if n = 0 then Some ([], l) 
  else 
    match l with 
    | [] -> None 
    | hd :: tl -> let? l1, l2 = take (n-1) tl in 
                Some (hd :: l1, l2)

let rec lemma_take_length (#a:Type) (n:nat) (l:list a) : 
  Lemma 
    (ensures (let t = take n l in Some? t ==> n <= length l /\ length (fst (Some?.v t)) = n /\ length (snd (Some?.v t)) = length l - n)) = 
  match n, l with 
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_take_length (n-1) l'

let decode_value (t:tag) (enc:bytes) : Tot (option (debytes enc & dbytes enc)) (decreases (length enc)) = 
  match t with 
  | VARINT -> (match Vint.extract_varint enc with 
             | None -> None 
             | Some (vint, byt) -> Some (vint, byt))
  | I64 -> (match take 8 enc with 
          | None -> None 
          | Some (i64, b) -> lemma_take_length 8 enc; Some (i64, b))
  | LEN -> let? len_byt, enc_byt = Vint.extract_varint enc in 
          let len = Vint.decode len_byt in 
          if U64.(eq len 0uL) then let dbz : debytes enc = [] in Some (dbz, enc_byt) else 
          (match take (U64.v len) enc_byt with 
          | None -> None 
          | Some tak -> lemma_take_length (U64.v len) enc_byt; 
                        let len_byt : debytes enc = fst tak in 
                        let rest_byt : dbytes enc = snd tak in 
                        Some (len_byt, rest_byt))
  | I32 -> (match take 4 enc with 
          | None -> None 
          | Some (i32, b) -> lemma_take_length 4 enc; Some (i32, b))
  | _ -> None

let decode_field (enc:bytes) : Tot (option (nat & dbytes enc & dbytes enc)) (decreases (length enc)) =
  match decode_header enc with 
  | None -> None 
  | Some (fid, t, bs) -> match decode_value t bs with 
                        | None -> None 
                        | Some (v, b) -> Some (fid, v, b)

// While decode_field performs one decode, this one decodes until either 
// - the remaining bytes are empty 
// - something fails to chunk
let rec decode_fields (enc:bytes) : Tot (option (list (nat & dbytes enc) & dbytes enc)) (decreases (length enc)) = 
  match enc with 
  | [] -> None
  | enc -> (match decode_field enc with 
          | None -> None
          | Some (fid, fbs, bs) -> (match decode_fields bs with 
                                  | None -> Some ([(fid, fbs)], bs)
                                  | Some (rfs, rbyt) -> assert length bs < length enc; 
                                                       // Weird type casting bullshit
                                                       let rfs' : list (nat & dbytes enc) = 
                                                         map (fun (b:nat & dbytes bs) -> 
                                                              let b' : dbytes enc = snd b in (fst b), b')
                                                       rfs in 
                                                       Some ((fid, fbs) :: rfs', rbyt)))

type field_parser (a:Type) = b:bytes -> option (a & dbytes b)

// Little-endian
let rec assemble_nat (b:bytes) : n:nat{n < pow2 (8 * length b)} = 
  match b with 
  | [] -> 0 
  | hd :: tl -> let rest = (pow2 8) * assemble_nat tl in 
              FStar.Math.Lemmas.pow2_plus 8 (8 * length tl); 
              U8.v hd + rest

// Splitting and recombining db below is required for type checking
val parse_double : field_parser Desc.double
let parse_double b = 
  match take 8 b with 
  | None -> None 
  | Some db -> lemma_take_length 8 b; Some ((fst db), (snd db))
val parse_float : field_parser Desc.float
let parse_float b = 
  match take 4 b with 
  | None -> None 
  | Some db -> lemma_take_length 4 b; Some ((fst db), (snd db))
val parse_int : w:Desc.width -> field_parser int 
let parse_int w b = 
  match Vint.extract_varint b with 
  | None -> None 
  | Some vint -> let raw_v : int = (U64.v (Vint.decode (fst vint))) in 
                let v = uint_int w (uint_change_w w raw_v) in
                Some (v, (snd vint))
val parse_uint : w:Desc.width -> field_parser int 
let parse_uint w b = 
  match Vint.extract_varint b with 
  | None -> None 
  | Some vint -> let raw_v : int = (U64.v (Vint.decode (fst vint))) in 
                let v = (uint_change_w w raw_v) in 
                Some (v, (snd vint))
val parse_sint : w:Desc.width -> field_parser int 
let parse_sint w b = 
  match Vint.extract_varint b with 
  | None -> None 
  | Some vint -> let raw_v : int = (U64.v (Vint.decode (fst vint))) in 
                let v = uint_sint w (uint_change_w w raw_v) in 
                Some (v, (snd vint))
val parse_fixed : w:Desc.width -> field_parser int 
let parse_fixed w b = 
  let n = w / 8 in
  assert n > 1;
  match take n b with 
  | None -> None 
  | Some db -> lemma_take_length n b; Some (assemble_nat (fst db), (snd db))
val parse_sfixed : w:Desc.width -> field_parser int 
let parse_sfixed w b = 
  let n = w / 8 in
  assert n > 1;
  match take n b with 
  | None -> None 
  | Some db -> lemma_take_length n b; Some (uint_int w (assemble_nat (fst db)), (snd db))
val parse_bool : field_parser bool 
let parse_bool b = 
  match b with 
  | 0uy :: tl -> Some (false, tl)
  | 1uy :: tl -> Some (true, tl)
  | _ -> None
val parse_string : field_parser string 
let parse_string b = 
  if List.isEmpty b then None else
  let s = String.string_of_list (map (fun b -> Char.char_of_int (U8.v b)) b) in 
  Some (s, [])
val parse_bytes : field_parser bytes 
let parse_bytes b = 
  if List.isEmpty b then None else Some (b, [])

let update_field (#a:Type) (name:string) (ori_v:Desc.dvty a) (new_v:Desc.dvty a) : Desc.dvty a =
    Desc.(match ori_v, new_v with 
    | VIMPLICIT _, VIMPLICIT v' -> VIMPLICIT v'
    | VOPTIONAL _, VOPTIONAL v' -> VOPTIONAL v'
    | VREPEATED v', VREPEATED value' -> VREPEATED (v' @ value')
    | _ -> ori_v) 

// Refinement and explicit splitting of hd purely for verification purposes.
let rec update_msg (msg:Desc.msg) (name:string) (value:Desc.vty) : m:Desc.msg{Desc.get_pair_fst msg = Desc.get_pair_fst m} = 
  match msg with 
  | [] -> []
  | hd :: tl -> let n = (fst hd) in 
              let v = (snd hd) in 
              if n = name then (n, 
                Desc.(match v, value with 
                      | VDOUBLE orig, VDOUBLE newv -> VDOUBLE (update_field n orig newv)
                      | VFLOAT orig, VFLOAT newv -> VFLOAT (update_field n orig newv)
                      | VINT orig, VINT newv -> VINT (update_field n orig newv)
                      | VBOOL orig, VBOOL newv -> VBOOL (update_field n orig newv)
                      | VSTRING orig, VSTRING newv -> VSTRING (update_field n orig newv)
                      | VBYTES orig, VBYTES newv -> VBYTES (update_field n orig newv)
                      | VMSG orig, VMSG newv -> VMSG (update_field n orig newv)
                      | VENUM orig, VENUM newv -> VENUM (update_field n orig newv)
                      | _ -> v
                      )) :: tl
              else 
              let r = update_msg tl name value in 
              List.noRepeats_cons n (Desc.get_pair_fst r);
              hd :: r

let rec parse_list (#a:Type) (payload:bytes) (parse_one:field_parser a) :
  Tot (option (list a)) (decreases (length payload)) = 
    match parse_one payload with 
    | None -> None
    | Some (a, bs) -> if List.isEmpty bs then Some ([a]) else  
                       let rest = parse_list bs parse_one in 
                       (match rest with 
                        | None -> None
                        | Some r -> Some (a :: r))

let parse_dec (#a:Type) (dec:Desc.pdec) (payload:bytes) (parse_one:field_parser a) : Tot (option (Desc.dvty a)) (decreases (length payload)) = 
  Desc.(match dec with 
  | P_IMPLICIT -> let? one, _ = parse_one payload in Some (VIMPLICIT one)
  | P_OPTIONAL -> let? one, _ = parse_one payload in Some (VOPTIONAL (Some one))
  | P_REPEATED -> let? many = parse_list payload parse_one in Some (VREPEATED many))

let rec parse_field (ty:Desc.pty) (payload:bytes) : Tot (option Desc.vty) (decreases %[fields_measure ["", 0, ty];0]) = 
  Desc.(match ty with 
  | P_DOUBLE p' -> let? vdec = parse_dec p' payload parse_double in Some (VDOUBLE vdec)
  | P_FLOAT p' -> let? vdec = parse_dec p' payload parse_float in Some (VFLOAT vdec)
  | P_INT w p' -> let? vdec = parse_dec p' payload (parse_int w) in Some (VINT vdec)
  | P_UINT w p' -> let? vdec = parse_dec p' payload (parse_uint w) in Some (VINT vdec) 
  | P_SINT w p' -> let? vdec = parse_dec p' payload (parse_sint w) in Some (VINT vdec)
  | P_FIXED w p' -> let? vdec = parse_dec p' payload (parse_fixed w) in Some (VINT vdec)
  | P_SFIXED w p' -> let? vdec = parse_dec p' payload (parse_sfixed w) in Some (VINT vdec)
  | P_BOOL p' -> let? vdec = parse_dec p' payload parse_bool in Some (VBOOL vdec)
  | P_STRING p' -> let? vdec = parse_dec p' payload parse_string in Some (VSTRING vdec)
  | P_BYTES p' -> let? vdec = parse_dec p' payload parse_bytes in Some (VBYTES vdec)
  | P_MSG m' p' -> let? vdec = parse_dec p' payload (parse_message' m') in Some (VMSG vdec)
  | _ -> None)

and merge_field (m:Desc.md) (msg:option Desc.msg) (f:nat & bytes) : Tot (option Desc.msg) (decreases (%[p_measure m;1])) = 
  let? msg = msg in
  let fid, payload = f in
  let field_desc = find_field m fid in 
  match field_desc with 
  // msg is no longer an option, thanks to the let? on the first line of this function
  | None -> Some msg 
  | Some (n, f, ty) -> let? typed_payload = parse_field ty payload in 
                      let new_msg : Desc.msg = update_msg msg n typed_payload in
                      Some (new_msg)

and parse_fields (m:Desc.md) (msg:option Desc.msg) (fs:list (nat & bytes)) : Tot (option Desc.msg) (decreases %[p_measure m;2;length fs]) = 
  // Basically a custom fold_left to propagate the needed refinements
  match fs with 
  | Nil -> msg 
  | h :: t -> parse_fields m (merge_field m msg h) t

and parse_message' (m:Desc.md) (enc:bytes) : Tot (option (Desc.msg & dbytes enc)) (decreases (%[p_measure m;3])) = 
  let? raw_fields, leftover_byt = decode_fields enc in 
  let msg : Desc.msg = Desc.init_msg m in 
  // INFO: Needed for type checking, but shouldn't be
  let raw_fields : list (nat & bytes) = map 
    (fun (e:nat & dbytes enc) -> let b : bytes = e._2 in e._1, b) 
  raw_fields in
  match parse_fields m (Some msg) raw_fields with 
  | None -> None 
  | Some m -> Some (m, leftover_byt)

let parse_message (m:Desc.md) (enc:bytes) : option Desc.msg =
  match parse_message' m enc with 
  | None -> None 
  | Some (m', _) -> Some m'
