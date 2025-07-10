open Prims
let (nat_to_u8 : Prims.nat -> FStar_UInt8.t) =
  fun n -> FStar_UInt8.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (8)) n)
let (nat_to_u32 : Prims.nat -> FStar_UInt32.t) =
  fun n ->
    FStar_UInt32.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (32)) n)
let (nat_to_u64 : Prims.nat -> FStar_UInt64.t) =
  fun n ->
    FStar_UInt64.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (64)) n)
let (int_to_i64 : Prims.int -> FStar_Int64.t) =
  fun z -> FStar_Int64.int_to_t (FStar_Int.to_int_t (Prims.of_int (64)) z)
let rec (exp : Prims.int -> Prims.nat -> Prims.int) =
  fun x ->
    fun n ->
      if n = Prims.int_zero
      then Prims.int_one
      else
        if (n mod (Prims.of_int (2))) = Prims.int_zero
        then exp (x * x) (n / (Prims.of_int (2)))
        else x * (exp (x * x) ((n - Prims.int_one) / (Prims.of_int (2))))
let (parity : Prims.int -> Prims.int) =
  fun v ->
    if (v mod (Prims.of_int (2))) = Prims.int_zero
    then Prims.int_one
    else (Prims.of_int (-1))
let (idn : Prims.bool -> Prims.int) =
  fun c -> if c then Prims.int_one else Prims.int_zero
let (idnuw :
  Pollux_Proto_Descriptors.width ->
    Prims.bool -> Obj.t Pollux_Proto_Descriptors.uw)
  = fun w -> fun c -> if c then Prims.int_one else Prims.int_zero
let (idnzw :
  Pollux_Proto_Descriptors.width ->
    Prims.bool -> Obj.t Pollux_Proto_Descriptors.zw)
  = fun w -> fun c -> if c then Prims.int_one else Prims.int_zero
let (uint_change_w :
  Pollux_Proto_Descriptors.width ->
    Prims.int -> Obj.t Pollux_Proto_Descriptors.uw)
  = fun w -> fun v -> v mod (Prims.pow2 w)
let (int_change_w :
  Pollux_Proto_Descriptors.width ->
    Prims.int -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      (v mod (Prims.pow2 (w - Prims.int_one))) -
        ((Prims.pow2 (w - Prims.int_one)) *
           (idn
              (((v / (Prims.pow2 (w - Prims.int_one))) mod (Prims.of_int (2)))
                 = Prims.int_one)))
let (sint_change_w :
  Pollux_Proto_Descriptors.width ->
    Prims.int -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      (v mod (Prims.pow2 (w - Prims.int_one))) -
        ((Prims.pow2 (w - Prims.int_one)) * (idn (v < Prims.int_zero)))
let (uint_int :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.uw -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      v - ((Prims.pow2 w) * (idn (v >= (Prims.pow2 (w - Prims.int_one)))))
let (int_uint :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.zw -> Obj.t Pollux_Proto_Descriptors.uw)
  = fun w -> fun v -> v + ((Prims.pow2 w) * (idn (v < Prims.int_zero)))
let (uint_sint :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.uw -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      ((parity v) * (v / (Prims.of_int (2)))) - (v mod (Prims.of_int (2)))
let (sint_uint :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.zw -> Obj.t Pollux_Proto_Descriptors.uw)
  =
  fun w ->
    fun v ->
      ((Prims.of_int (2)) * (Prims.abs v)) - (idn (v < Prims.int_zero))
let (int_sint :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.zw -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      if v >= Prims.int_zero
      then
        ((parity v) * (v / (Prims.of_int (2)))) - (v mod (Prims.of_int (2)))
      else
        (parity v) *
          ((v + (Prims.pow2 (w - Prims.int_one))) - (v / (Prims.of_int (2))))
let (sint_int :
  Pollux_Proto_Descriptors.width ->
    Obj.t Pollux_Proto_Descriptors.zw -> Obj.t Pollux_Proto_Descriptors.zw)
  =
  fun w ->
    fun v ->
      if
        ((- (Prims.pow2 (w - (Prims.of_int (2))))) <= v) &&
          (v < (Prims.pow2 (w - (Prims.of_int (2)))))
      then ((Prims.of_int (2)) * (Prims.abs v)) - (idn (v < Prims.int_zero))
      else
        (((Prims.of_int (2)) * (Prims.abs v)) - (Prims.pow2 w)) -
          (idn (v < Prims.int_zero))
type tag =
  | VARINT 
  | I64 
  | LEN 
  | I32 
let (uu___is_VARINT : tag -> Prims.bool) =
  fun projectee -> match projectee with | VARINT -> true | uu___ -> false
let (uu___is_I64 : tag -> Prims.bool) =
  fun projectee -> match projectee with | I64 -> true | uu___ -> false
let (uu___is_LEN : tag -> Prims.bool) =
  fun projectee -> match projectee with | LEN -> true | uu___ -> false
let (uu___is_I32 : tag -> Prims.bool) =
  fun projectee -> match projectee with | I32 -> true | uu___ -> false
let (tag_num : tag -> FStar_UInt64.t) =
  fun t ->
    match t with
    | VARINT -> nat_to_u64 Prims.int_zero
    | I64 -> nat_to_u64 Prims.int_one
    | LEN -> nat_to_u64 (Prims.of_int (2))
    | I32 -> nat_to_u64 (Prims.of_int (5))
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun x ->
    fun f ->
      match x with
      | FStar_Pervasives_Native.Some x1 -> f x1
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let op_and_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      'b FStar_Pervasives_Native.option ->
        ('a * 'b) FStar_Pervasives_Native.option
  =
  fun x ->
    fun y ->
      match (x, y) with
      | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1) ->
          FStar_Pervasives_Native.Some (x1, y1)
      | uu___ -> FStar_Pervasives_Native.None
let (find_field_string :
  Pollux_Proto_Descriptors.md ->
    Prims.string ->
      Pollux_Proto_Descriptors.fd FStar_Pervasives_Native.option)
  =
  fun msg ->
    fun id ->
      FStar_List_Tot_Base.find
        (fun f -> (FStar_Pervasives_Native.__proj__Mktuple3__item___1 f) = id)
        msg.Pollux_Proto_Descriptors.fields
let (find_tag : Pollux_Proto_Descriptors.pty -> tag) =
  fun p ->
    match p with
    | Pollux_Proto_Descriptors.P_INT
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) -> LEN
    | Pollux_Proto_Descriptors.P_UINT
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) -> LEN
    | Pollux_Proto_Descriptors.P_SINT
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) -> LEN
    | Pollux_Proto_Descriptors.P_BOOL (Pollux_Proto_Descriptors.P_REPEATED)
        -> LEN
    | Pollux_Proto_Descriptors.P_ENUM (Pollux_Proto_Descriptors.P_REPEATED)
        -> LEN
    | Pollux_Proto_Descriptors.P_INT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_UINT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_SINT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_BOOL uu___ -> VARINT
    | Pollux_Proto_Descriptors.P_ENUM uu___ -> VARINT
    | Pollux_Proto_Descriptors.P_FIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) when
        uu___ = (Prims.of_int (32)) -> LEN
    | Pollux_Proto_Descriptors.P_SFIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) when
        uu___ = (Prims.of_int (32)) -> LEN
    | Pollux_Proto_Descriptors.P_FLOAT (Pollux_Proto_Descriptors.P_REPEATED)
        -> LEN
    | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_SFIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_FLOAT uu___ -> I32
    | Pollux_Proto_Descriptors.P_FIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) when
        uu___ = (Prims.of_int (64)) -> I64
    | Pollux_Proto_Descriptors.P_SFIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) when
        uu___ = (Prims.of_int (64)) -> I64
    | Pollux_Proto_Descriptors.P_DOUBLE (Pollux_Proto_Descriptors.P_REPEATED)
        -> I64
    | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (64)) -> I64
    | Pollux_Proto_Descriptors.P_SFIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (64)) -> I64
    | Pollux_Proto_Descriptors.P_DOUBLE uu___ -> I64
    | uu___ -> LEN
let (encode_header :
  Pollux_Proto_Descriptors.md ->
    Prims.string -> FStar_UInt64.t FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun name ->
      op_let_Question (find_field_string msg_d name)
        (fun f ->
           let id_n =
             nat_to_u64
               (FStar_Pervasives_Native.__proj__Mktuple3__item___2 f) in
           let tag_n =
             tag_num
               (find_tag
                  (FStar_Pervasives_Native.__proj__Mktuple3__item___3 f)) in
           FStar_Pervasives_Native.Some
             (FStar_UInt64.logor
                (FStar_UInt64.shift_left id_n (nat_to_u32 (Prims.of_int (3))))
                tag_n))
type bytes = FStar_UInt8.t Prims.list
let (u64_of_s32 : FStar_Int32.t -> FStar_UInt64.t) =
  fun s -> nat_to_u64 (sint_uint (Prims.of_int (32)) (FStar_Int32.v s))
let (u64_of_s64 : FStar_Int64.t -> FStar_UInt64.t) =
  fun s -> nat_to_u64 (sint_uint (Prims.of_int (64)) (FStar_Int64.v s))
let (encode_int32 : FStar_Int32.t -> bytes) =
  fun i -> Pollux_Proto_Varint.encode (FStar_Int_Cast.int32_to_uint64 i)
let (encode_int64 : FStar_Int64.t -> bytes) =
  fun i -> Pollux_Proto_Varint.encode (FStar_Int_Cast.int64_to_uint64 i)
let (encode_uint32 : FStar_UInt32.t -> bytes) =
  fun u -> Pollux_Proto_Varint.encode (FStar_Int_Cast.uint32_to_uint64 u)
let (encode_sint32 : FStar_Int32.t -> bytes) =
  fun s -> Pollux_Proto_Varint.encode (u64_of_s32 s)
let (encode_sint64 : FStar_Int64.t -> bytes) =
  fun s -> Pollux_Proto_Varint.encode (u64_of_s64 s)
let rec (__encode_fixed32 : FStar_UInt32.t -> Prims.pos -> bytes) =
  fun x ->
    fun b ->
      let hi = FStar_UInt32.shift_right x (Stdint.Uint32.of_int (8)) in
      let lo =
        FStar_Int_Cast.uint32_to_uint8
          (FStar_UInt32.logand x (Stdint.Uint32.of_int (255))) in
      if b = Prims.int_one
      then [lo]
      else (let rx = __encode_fixed32 hi (b - Prims.int_one) in lo :: rx)
let (encode_fixed32 : FStar_UInt32.t -> bytes) =
  fun f -> __encode_fixed32 f (Prims.of_int (4))
let rec (__encode_fixed64 : FStar_UInt64.t -> Prims.pos -> bytes) =
  fun x ->
    fun b ->
      let hi = FStar_UInt64.shift_right x (Stdint.Uint32.of_int (8)) in
      let lo =
        FStar_Int_Cast.uint64_to_uint8
          (FStar_UInt64.logand x (Stdint.Uint64.of_int (255))) in
      if b = Prims.int_one
      then [lo]
      else (let rx = __encode_fixed64 hi (b - Prims.int_one) in lo :: rx)
let (encode_fixed64 : FStar_UInt64.t -> bytes) =
  fun f -> __encode_fixed64 f (Prims.of_int (8))
let (encode_sfixed32 : FStar_Int32.t -> bytes) =
  fun i -> encode_fixed32 (FStar_Int_Cast.int32_to_uint32 i)
let (encode_sfixed64 : FStar_Int64.t -> bytes) =
  fun i -> encode_fixed64 (FStar_Int_Cast.int64_to_uint64 i)
let (encode_bool : Prims.bool -> bytes) = fun b -> if b then [1] else [0]
let encode_implicit :
  'a . 'a -> 'a -> ('a -> bytes) -> bytes FStar_Pervasives_Native.option =
  fun v ->
    fun d ->
      fun enc ->
        if v = d
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some (enc v)
let encode_packed : 'a . 'a Prims.list -> ('a -> bytes) -> bytes =
  fun l ->
    fun enc_one ->
      let bytes1 =
        FStar_List_Tot_Base.fold_left FStar_List_Tot_Base.append []
          (FStar_List_Tot_Base.map enc_one l) in
      let length =
        Pollux_Proto_Varint.encode
          (nat_to_u64 (FStar_List_Tot_Base.length bytes1)) in
      FStar_List_Tot_Base.op_At length bytes1
let rec (encode_utf8_char : FStar_UInt32.t -> bytes) =
  fun x ->
    let hi = FStar_UInt32.shift_right x (Stdint.Uint32.of_int (8)) in
    let lo =
      FStar_Int_Cast.uint32_to_uint8
        (FStar_UInt32.logand x (Stdint.Uint32.of_int (255))) in
    if FStar_UInt32.lte hi Stdint.Uint32.zero
    then [lo]
    else (let rx = encode_utf8_char hi in lo :: rx)
let (encode_string : Prims.string -> bytes) =
  fun s ->
    encode_packed
      (FStar_List_Tot_Base.map FStar_Char.u32_of_char
         (FStar_String.list_of_string s)) encode_utf8_char
let (encode_bytes : bytes -> bytes) = fun b -> encode_packed b (fun x -> [x])
let (v_measure : Pollux_Proto_Descriptors.vty -> Prims.nat) =
  fun v ->
    match v with
    | Pollux_Proto_Descriptors.VDOUBLE v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VFLOAT v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VINT32 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VINT64 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VUINT32 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VUINT64 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VSINT32 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VSINT64 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VFIXED32 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VFIXED64 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VSFIXED32 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VSFIXED64 v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VBOOL v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VSTRING v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VBYTES v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VMSG v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
    | Pollux_Proto_Descriptors.VENUM v' ->
        (match v' with
         | Pollux_Proto_Descriptors.VIMPLICIT uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VOPTIONAL uu___ -> Prims.int_zero
         | Pollux_Proto_Descriptors.VREPEATED l ->
             FStar_List_Tot_Base.length l)
let rec (encode_field :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.vf -> bytes FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun field ->
      op_let_Question
        (encode_header msg_d
           (FStar_Pervasives_Native.__proj__Mktuple2__item___1 field))
        (fun header ->
           let header_bytes = Pollux_Proto_Varint.encode header in
           op_let_Question (encode_value msg_d field)
             (fun value ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.op_At header_bytes value)))
and (encode_value :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.vf -> bytes FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun field ->
      match FStar_Pervasives_Native.__proj__Mktuple2__item___2 field with
      | Pollux_Proto_Descriptors.VDOUBLE (Pollux_Proto_Descriptors.VIMPLICIT
          v') ->
          encode_implicit v' Pollux_Proto_Descriptors.double_z (fun x -> x)
      | Pollux_Proto_Descriptors.VDOUBLE (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some v'
      | Pollux_Proto_Descriptors.VDOUBLE (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) (fun x -> x))
      | Pollux_Proto_Descriptors.VFLOAT (Pollux_Proto_Descriptors.VIMPLICIT
          v') ->
          encode_implicit v' Pollux_Proto_Descriptors.float_z (fun x -> x)
      | Pollux_Proto_Descriptors.VFLOAT (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some v'
      | Pollux_Proto_Descriptors.VFLOAT (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) (fun x -> x))
      | Pollux_Proto_Descriptors.VINT32 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Int32.zero encode_int32
      | Pollux_Proto_Descriptors.VINT32 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_int32 v')
      | Pollux_Proto_Descriptors.VINT32 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_int32)
      | Pollux_Proto_Descriptors.VINT64 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Int64.zero encode_int64
      | Pollux_Proto_Descriptors.VINT64 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_int64 v')
      | Pollux_Proto_Descriptors.VINT64 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_int64)
      | Pollux_Proto_Descriptors.VUINT32 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Uint32.zero encode_uint32
      | Pollux_Proto_Descriptors.VUINT32 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_uint32 v')
      | Pollux_Proto_Descriptors.VUINT32 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_uint32)
      | Pollux_Proto_Descriptors.VUINT64 (Pollux_Proto_Descriptors.VIMPLICIT
          v') ->
          encode_implicit v' Stdint.Uint64.zero Pollux_Proto_Varint.encode
      | Pollux_Proto_Descriptors.VUINT64 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (Pollux_Proto_Varint.encode v')
      | Pollux_Proto_Descriptors.VUINT64 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) Pollux_Proto_Varint.encode)
      | Pollux_Proto_Descriptors.VSINT32 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Int32.zero encode_sint32
      | Pollux_Proto_Descriptors.VSINT32 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_sint32 v')
      | Pollux_Proto_Descriptors.VSINT32 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_sint32)
      | Pollux_Proto_Descriptors.VSINT64 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Int64.zero encode_sint64
      | Pollux_Proto_Descriptors.VSINT64 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_sint64 v')
      | Pollux_Proto_Descriptors.VSINT64 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_sint64)
      | Pollux_Proto_Descriptors.VFIXED32 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Uint32.zero encode_fixed32
      | Pollux_Proto_Descriptors.VFIXED32 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_fixed32 v')
      | Pollux_Proto_Descriptors.VFIXED32 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_fixed32)
      | Pollux_Proto_Descriptors.VFIXED64 (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' Stdint.Uint64.zero encode_fixed64
      | Pollux_Proto_Descriptors.VFIXED64 (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_fixed64 v')
      | Pollux_Proto_Descriptors.VFIXED64 (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_fixed64)
      | Pollux_Proto_Descriptors.VSFIXED32
          (Pollux_Proto_Descriptors.VIMPLICIT v') ->
          encode_implicit v' Stdint.Int32.zero encode_sfixed32
      | Pollux_Proto_Descriptors.VSFIXED32
          (Pollux_Proto_Descriptors.VOPTIONAL (FStar_Pervasives_Native.Some
          v')) -> FStar_Pervasives_Native.Some (encode_sfixed32 v')
      | Pollux_Proto_Descriptors.VSFIXED32
          (Pollux_Proto_Descriptors.VREPEATED (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_sfixed32)
      | Pollux_Proto_Descriptors.VSFIXED64
          (Pollux_Proto_Descriptors.VIMPLICIT v') ->
          encode_implicit v' Stdint.Int64.zero encode_sfixed64
      | Pollux_Proto_Descriptors.VSFIXED64
          (Pollux_Proto_Descriptors.VOPTIONAL (FStar_Pervasives_Native.Some
          v')) -> FStar_Pervasives_Native.Some (encode_sfixed64 v')
      | Pollux_Proto_Descriptors.VSFIXED64
          (Pollux_Proto_Descriptors.VREPEATED (vh::vt)) ->
          FStar_Pervasives_Native.Some
            (encode_packed (vh :: vt) encode_sfixed64)
      | Pollux_Proto_Descriptors.VBOOL (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' false encode_bool
      | Pollux_Proto_Descriptors.VBOOL (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_bool v')
      | Pollux_Proto_Descriptors.VBOOL (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          FStar_Pervasives_Native.Some (encode_packed (vh :: vt) encode_bool)
      | Pollux_Proto_Descriptors.VSTRING (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' "" encode_string
      | Pollux_Proto_Descriptors.VSTRING (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_string v')
      | Pollux_Proto_Descriptors.VSTRING (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          let rest =
            Pollux_Proto_Descriptors.VSTRING
              (Pollux_Proto_Descriptors.VREPEATED vt) in
          let renc =
            encode_field msg_d
              ((FStar_Pervasives_Native.__proj__Mktuple2__item___1 field),
                rest) in
          (match renc with
           | FStar_Pervasives_Native.None ->
               FStar_Pervasives_Native.Some (encode_string vh)
           | FStar_Pervasives_Native.Some r ->
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.op_At (encode_string vh) r))
      | Pollux_Proto_Descriptors.VBYTES (Pollux_Proto_Descriptors.VIMPLICIT
          v') -> encode_implicit v' [] encode_bytes
      | Pollux_Proto_Descriptors.VBYTES (Pollux_Proto_Descriptors.VOPTIONAL
          (FStar_Pervasives_Native.Some v')) ->
          FStar_Pervasives_Native.Some (encode_bytes v')
      | Pollux_Proto_Descriptors.VBYTES (Pollux_Proto_Descriptors.VREPEATED
          (vh::vt)) ->
          let rest =
            Pollux_Proto_Descriptors.VBYTES
              (Pollux_Proto_Descriptors.VREPEATED vt) in
          let renc =
            encode_field msg_d
              ((FStar_Pervasives_Native.__proj__Mktuple2__item___1 field),
                rest) in
          (match renc with
           | FStar_Pervasives_Native.None ->
               FStar_Pervasives_Native.Some (encode_bytes vh)
           | FStar_Pervasives_Native.Some r ->
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.op_At (encode_bytes vh) r))
      | uu___ -> FStar_Pervasives_Native.None
let opt_append :
  'a .
    'a Prims.list ->
      'a Prims.list FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun l1 ->
    fun l2 ->
      match l2 with
      | FStar_Pervasives_Native.None -> l1
      | FStar_Pervasives_Native.Some l2' -> FStar_List_Tot_Base.op_At l1 l2'
let (encode_message :
  Pollux_Proto_Descriptors.md -> Pollux_Proto_Descriptors.msg -> bytes) =
  fun md ->
    fun msg ->
      let encoder = encode_field md in
      FStar_List_Tot_Base.fold_left opt_append []
        (FStar_List_Tot_Base.map encoder msg)
