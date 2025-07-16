open Prims
let (nat_to_u8 : Prims.nat -> FStar_UInt8.t) =
  fun n -> FStar_UInt8.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (8)) n)
let (nat_to_u32 : Prims.nat -> FStar_UInt32.t) =
  fun n ->
    FStar_UInt32.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (32)) n)
let (nat_to_u64 : Prims.nat -> FStar_UInt64.t) =
  fun n ->
    FStar_UInt64.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (64)) n)
let (int_to_i32 : Prims.int -> FStar_Int32.t) =
  fun z -> FStar_Int32.int_to_t (FStar_Int.to_int_t (Prims.of_int (32)) z)
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
    | Pollux_Proto_Descriptors.P_FIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) -> LEN
    | Pollux_Proto_Descriptors.P_SFIXED
        (uu___, Pollux_Proto_Descriptors.P_REPEATED) -> LEN
    | Pollux_Proto_Descriptors.P_FLOAT (Pollux_Proto_Descriptors.P_REPEATED)
        -> LEN
    | Pollux_Proto_Descriptors.P_DOUBLE (Pollux_Proto_Descriptors.P_REPEATED)
        -> LEN
    | Pollux_Proto_Descriptors.P_INT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_UINT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_SINT (uu___, uu___1) -> VARINT
    | Pollux_Proto_Descriptors.P_BOOL uu___ -> VARINT
    | Pollux_Proto_Descriptors.P_ENUM uu___ -> VARINT
    | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_SFIXED (uu___, uu___1) when
        uu___ = (Prims.of_int (32)) -> I32
    | Pollux_Proto_Descriptors.P_FLOAT uu___ -> I32
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
      Pollux_Proto_Prelude.op_let_Question (find_field_string msg_d name)
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
let (u64_of_s32 : Prims.int -> FStar_UInt64.t) =
  fun s ->
    nat_to_u64 (sint_uint (Prims.of_int (32)) (FStar_Int32.v (int_to_i32 s)))
let (u64_of_s64 : Prims.int -> FStar_UInt64.t) =
  fun s ->
    nat_to_u64 (sint_uint (Prims.of_int (64)) (FStar_Int64.v (int_to_i64 s)))
let (encode_int32 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun i ->
    Pollux_Proto_Varint.encode
      (FStar_Int_Cast.int64_to_uint64 (int_to_i64 i))
let (encode_int64 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun i ->
    Pollux_Proto_Varint.encode
      (FStar_Int_Cast.int64_to_uint64 (int_to_i64 i))
let (encode_uint32 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun u ->
    Pollux_Proto_Varint.encode
      (FStar_Int_Cast.int64_to_uint64 (int_to_i64 u))
let (encode_uint64 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun u ->
    Pollux_Proto_Varint.encode
      (FStar_Int_Cast.int64_to_uint64 (int_to_i64 u))
let (encode_sint32 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun s -> Pollux_Proto_Varint.encode (u64_of_s32 s)
let (encode_sint64 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun s -> Pollux_Proto_Varint.encode (u64_of_s64 s)
let rec (__encode_fixed32 :
  FStar_UInt32.t -> Prims.pos -> Pollux_Proto_Prelude.bytes) =
  fun x ->
    fun b ->
      let hi = FStar_UInt32.shift_right x (Stdint.Uint32.of_int (8)) in
      let lo =
        FStar_Int_Cast.uint32_to_uint8
          (FStar_UInt32.logand x (Stdint.Uint32.of_int (255))) in
      if b = Prims.int_one
      then [lo]
      else (let rx = __encode_fixed32 hi (b - Prims.int_one) in lo :: rx)
let (encode_fixed32 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun f ->
    __encode_fixed32 (FStar_Int_Cast.int32_to_uint32 (int_to_i32 f))
      (Prims.of_int (4))
let rec (__encode_fixed64 :
  FStar_UInt64.t -> Prims.pos -> Pollux_Proto_Prelude.bytes) =
  fun x ->
    fun b ->
      let hi = FStar_UInt64.shift_right x (Stdint.Uint32.of_int (8)) in
      let lo =
        FStar_Int_Cast.uint64_to_uint8
          (FStar_UInt64.logand x (Stdint.Uint64.of_int (255))) in
      if b = Prims.int_one
      then [lo]
      else (let rx = __encode_fixed64 hi (b - Prims.int_one) in lo :: rx)
let (encode_fixed64 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun f ->
    __encode_fixed64 (FStar_Int_Cast.int64_to_uint64 (int_to_i64 f))
      (Prims.of_int (8))
let (encode_sfixed32 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun i -> encode_fixed32 i
let (encode_sfixed64 : Prims.int -> Pollux_Proto_Prelude.bytes) =
  fun i -> encode_fixed64 i
let (encode_bool : Prims.bool -> Pollux_Proto_Prelude.bytes) =
  fun b -> if b then [1] else [0]
let encode_implicit :
  'a .
    'a ->
      'a ->
        ('a -> Pollux_Proto_Prelude.bytes) ->
          Pollux_Proto_Prelude.bytes FStar_Pervasives_Native.option
  =
  fun v ->
    fun d ->
      fun enc ->
        if v = d
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some (enc v)
let encode_packed :
  'a .
    'a Prims.list ->
      ('a -> Pollux_Proto_Prelude.bytes) -> Pollux_Proto_Prelude.bytes
  =
  fun l ->
    fun enc_one ->
      let bytes =
        FStar_List_Tot_Base.fold_left FStar_List_Tot_Base.append []
          (FStar_List_Tot_Base.map enc_one l) in
      let length =
        Pollux_Proto_Varint.encode
          (nat_to_u64 (FStar_List_Tot_Base.length bytes)) in
      FStar_List_Tot_Base.op_At length bytes
let rec (encode_utf8_char : FStar_UInt32.t -> Pollux_Proto_Prelude.bytes) =
  fun x ->
    let hi = FStar_UInt32.shift_right x (Stdint.Uint32.of_int (8)) in
    let lo =
      FStar_Int_Cast.uint32_to_uint8
        (FStar_UInt32.logand x (Stdint.Uint32.of_int (255))) in
    if FStar_UInt32.lte hi Stdint.Uint32.zero
    then [lo]
    else (let rx = encode_utf8_char hi in lo :: rx)
let (encode_string : Prims.string -> Pollux_Proto_Prelude.bytes) =
  fun s ->
    encode_packed
      (FStar_List_Tot_Base.map FStar_Char.u32_of_char
         (FStar_String.list_of_string s)) encode_utf8_char
let (encode_bytes : Pollux_Proto_Prelude.bytes -> Pollux_Proto_Prelude.bytes)
  = fun b -> encode_packed b (fun x -> [x])
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
    | Pollux_Proto_Descriptors.VINT v' ->
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
let encode_dec_packed :
  'a .
    'a Pollux_Proto_Descriptors.dvty ->
      'a ->
        ('a -> Pollux_Proto_Prelude.bytes) ->
          Pollux_Proto_Prelude.bytes FStar_Pervasives_Native.option
  =
  fun field ->
    fun def ->
      fun encode_one ->
        match field with
        | Pollux_Proto_Descriptors.VIMPLICIT v' ->
            encode_implicit v' def encode_one
        | Pollux_Proto_Descriptors.VOPTIONAL (FStar_Pervasives_Native.Some
            v') -> FStar_Pervasives_Native.Some (encode_one v')
        | Pollux_Proto_Descriptors.VREPEATED (vh::vt) ->
            FStar_Pervasives_Native.Some
              (encode_packed (vh :: vt) encode_one)
        | uu___ -> FStar_Pervasives_Native.None
let (find_encode_one :
  Pollux_Proto_Descriptors.md ->
    Prims.string ->
      (Prims.int -> Pollux_Proto_Prelude.bytes)
        FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun name ->
      Pollux_Proto_Prelude.op_let_Question (find_field_string msg_d name)
        (fun f ->
           match FStar_Pervasives_Native.__proj__Mktuple3__item___3 f with
           | Pollux_Proto_Descriptors.P_INT (uu___, uu___1) when
               uu___ = (Prims.of_int (32)) ->
               FStar_Pervasives_Native.Some encode_int32
           | Pollux_Proto_Descriptors.P_INT (uu___, uu___1) when
               uu___ = (Prims.of_int (64)) ->
               FStar_Pervasives_Native.Some encode_int64
           | Pollux_Proto_Descriptors.P_UINT (uu___, uu___1) when
               uu___ = (Prims.of_int (32)) ->
               FStar_Pervasives_Native.Some encode_uint32
           | Pollux_Proto_Descriptors.P_UINT (uu___, uu___1) when
               uu___ = (Prims.of_int (64)) ->
               FStar_Pervasives_Native.Some encode_uint64
           | Pollux_Proto_Descriptors.P_SINT (uu___, uu___1) when
               uu___ = (Prims.of_int (32)) ->
               FStar_Pervasives_Native.Some encode_sint32
           | Pollux_Proto_Descriptors.P_SINT (uu___, uu___1) when
               uu___ = (Prims.of_int (64)) ->
               FStar_Pervasives_Native.Some encode_sint64
           | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
               uu___ = (Prims.of_int (32)) ->
               FStar_Pervasives_Native.Some encode_fixed32
           | Pollux_Proto_Descriptors.P_FIXED (uu___, uu___1) when
               uu___ = (Prims.of_int (64)) ->
               FStar_Pervasives_Native.Some encode_fixed64
           | Pollux_Proto_Descriptors.P_SFIXED (uu___, uu___1) when
               uu___ = (Prims.of_int (32)) ->
               FStar_Pervasives_Native.Some encode_sfixed32
           | Pollux_Proto_Descriptors.P_SFIXED (uu___, uu___1) when
               uu___ = (Prims.of_int (64)) ->
               FStar_Pervasives_Native.Some encode_sfixed64
           | uu___ -> FStar_Pervasives_Native.None)
let rec (encode_field :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.vf ->
      Pollux_Proto_Prelude.bytes FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun field ->
      Pollux_Proto_Prelude.op_let_Question
        (encode_header msg_d
           (FStar_Pervasives_Native.__proj__Mktuple2__item___1 field))
        (fun header ->
           let header_bytes = Pollux_Proto_Varint.encode header in
           Pollux_Proto_Prelude.op_let_Question (encode_value msg_d field)
             (fun value ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.op_At header_bytes value)))
and (encode_value :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.vf ->
      Pollux_Proto_Prelude.bytes FStar_Pervasives_Native.option)
  =
  fun msg_d ->
    fun field ->
      match FStar_Pervasives_Native.__proj__Mktuple2__item___2 field with
      | Pollux_Proto_Descriptors.VDOUBLE v' ->
          encode_dec_packed v' Pollux_Proto_Descriptors.double_z (fun x -> x)
      | Pollux_Proto_Descriptors.VFLOAT v' ->
          encode_dec_packed v' Pollux_Proto_Descriptors.float_z (fun x -> x)
      | Pollux_Proto_Descriptors.VINT v' ->
          Pollux_Proto_Prelude.op_let_Question
            (find_encode_one msg_d
               (FStar_Pervasives_Native.__proj__Mktuple2__item___1 field))
            (fun encode_one -> encode_dec_packed v' Prims.int_zero encode_one)
      | Pollux_Proto_Descriptors.VBOOL v' ->
          encode_dec_packed v' false encode_bool
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
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.msg -> Pollux_Proto_Prelude.bytes)
  =
  fun md ->
    fun msg ->
      let encoder = encode_field md in
      FStar_List_Tot_Base.fold_left opt_append []
        (FStar_List_Tot_Base.map encoder msg)
let (tag_from_num : FStar_UInt64.t -> tag FStar_Pervasives_Native.option) =
  fun n ->
    match n with
    | uu___ when uu___ = Stdint.Uint64.zero ->
        FStar_Pervasives_Native.Some VARINT
    | uu___ when uu___ = Stdint.Uint64.one ->
        FStar_Pervasives_Native.Some I64
    | uu___ when uu___ = (Stdint.Uint64.of_int (2)) ->
        FStar_Pervasives_Native.Some LEN
    | uu___ when uu___ = (Stdint.Uint64.of_int (5)) ->
        FStar_Pervasives_Native.Some I32
    | uu___ -> FStar_Pervasives_Native.None
let (decode_header :
  Pollux_Proto_Prelude.bytes ->
    (Prims.nat * tag * Pollux_Proto_Prelude.bytes)
      FStar_Pervasives_Native.option)
  =
  fun enc ->
    Pollux_Proto_Prelude.op_let_Question
      (Pollux_Proto_Varint.extract_varint enc)
      (fun uu___ ->
         match uu___ with
         | (header_bytes, bs) ->
             let header = Pollux_Proto_Varint.decode header_bytes in
             let fid =
               FStar_UInt64.v
                 (FStar_UInt64.shift_right header (Stdint.Uint32.of_int (3))) in
             let tag_n =
               FStar_UInt64.logand header (Stdint.Uint64.of_int (7)) in
             Pollux_Proto_Prelude.op_let_Question (tag_from_num tag_n)
               (fun tag1 -> FStar_Pervasives_Native.Some (fid, tag1, bs)))
let (find_field :
  Pollux_Proto_Descriptors.md ->
    Prims.nat -> Pollux_Proto_Descriptors.fd FStar_Pervasives_Native.option)
  =
  fun md ->
    fun id ->
      FStar_List_Tot_Base.find
        (fun f -> (FStar_Pervasives_Native.__proj__Mktuple3__item___2 f) = id)
        md.Pollux_Proto_Descriptors.fields
let rec take :
  'a .
    Prims.nat ->
      'a Prims.list ->
        ('a Prims.list * 'a Prims.list) FStar_Pervasives_Native.option
  =
  fun n ->
    fun l ->
      if n = Prims.int_zero
      then FStar_Pervasives_Native.Some ([], l)
      else
        (match l with
         | [] -> FStar_Pervasives_Native.None
         | hd::tl ->
             Pollux_Proto_Prelude.op_let_Question
               (take (n - Prims.int_one) tl)
               (fun uu___1 ->
                  match uu___1 with
                  | (l1, l2) -> FStar_Pervasives_Native.Some ((hd :: l1), l2)))
let (decode_value :
  tag ->
    Pollux_Proto_Prelude.bytes ->
      (Pollux_Proto_Prelude.bytes * Pollux_Proto_Prelude.bytes)
        FStar_Pervasives_Native.option)
  =
  fun t ->
    fun enc ->
      match t with
      | VARINT ->
          Pollux_Proto_Prelude.op_let_Question
            (Pollux_Proto_Varint.extract_varint enc)
            (fun v ->
               let vint =
                 FStar_Pervasives_Native.__proj__Mktuple2__item___1 v in
               let byt = FStar_Pervasives_Native.__proj__Mktuple2__item___2 v in
               FStar_Pervasives_Native.Some (vint, byt))
      | I64 ->
          (match take (Prims.of_int (8)) enc with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (i64, b) ->
               FStar_Pervasives_Native.Some (i64, b))
      | LEN ->
          Pollux_Proto_Prelude.op_let_Question
            (Pollux_Proto_Varint.extract_varint enc)
            (fun uu___ ->
               match uu___ with
               | (len_byt, enc_byt) ->
                   let len = Pollux_Proto_Varint.decode len_byt in
                   if FStar_UInt64.eq len Stdint.Uint64.zero
                   then FStar_Pervasives_Native.Some ([], enc_byt)
                   else
                     (match take (FStar_UInt64.v len) enc_byt with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some tak ->
                          let len_byt1 = FStar_Pervasives_Native.fst tak in
                          let rest_byt = FStar_Pervasives_Native.snd tak in
                          FStar_Pervasives_Native.Some (len_byt1, rest_byt)))
      | I32 ->
          (match take (Prims.of_int (4)) enc with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (i32, b) ->
               FStar_Pervasives_Native.Some (i32, b))
      | uu___ -> FStar_Pervasives_Native.None
let (decode_field :
  Pollux_Proto_Prelude.bytes ->
    (Prims.nat * Pollux_Proto_Prelude.bytes * Pollux_Proto_Prelude.bytes)
      FStar_Pervasives_Native.option)
  =
  fun enc ->
    match decode_header enc with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (fid, t, bs) ->
        (match decode_value t bs with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (v, b) ->
             FStar_Pervasives_Native.Some (fid, v, b))
let rec (decode_fields :
  Pollux_Proto_Prelude.bytes ->
    ((Prims.nat * Pollux_Proto_Prelude.bytes) Prims.list *
      Pollux_Proto_Prelude.bytes))
  =
  fun enc ->
    match enc with
    | [] -> ([], [])
    | enc1 ->
        (match decode_field enc1 with
         | FStar_Pervasives_Native.None -> ([], enc1)
         | FStar_Pervasives_Native.Some (fid, fbs, bs) ->
             let uu___ = decode_fields bs in
             (match uu___ with
              | (rest_fields, rest_byt) ->
                  (((fid, fbs) :: rest_fields), rest_byt)))
type 'a field_parser =
  Pollux_Proto_Prelude.bytes ->
    ('a * Pollux_Proto_Prelude.bytes) FStar_Pervasives_Native.option
let rec (assemble_nat : Pollux_Proto_Prelude.bytes -> Prims.nat) =
  fun b ->
    match b with
    | [] -> Prims.int_zero
    | hd::tl ->
        let rest = (Prims.pow2 (Prims.of_int (8))) * (assemble_nat tl) in
        (FStar_UInt8.v hd) + rest
let (parse_double : Pollux_Proto_Descriptors.double field_parser) =
  fun b ->
    match take (Prims.of_int (8)) b with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some db ->
        FStar_Pervasives_Native.Some
          ((FStar_Pervasives_Native.fst db),
            (FStar_Pervasives_Native.snd db))
let (parse_float : Pollux_Proto_Descriptors.float field_parser) =
  fun b ->
    match take (Prims.of_int (4)) b with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some db ->
        FStar_Pervasives_Native.Some
          ((FStar_Pervasives_Native.fst db),
            (FStar_Pervasives_Native.snd db))
let (parse_int : Pollux_Proto_Descriptors.width -> Prims.int field_parser) =
  fun w ->
    fun b ->
      match Pollux_Proto_Varint.extract_varint b with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some vint ->
          let raw_v =
            FStar_UInt64.v
              (Pollux_Proto_Varint.decode (FStar_Pervasives_Native.fst vint)) in
          let v = uint_int w (uint_change_w w raw_v) in
          FStar_Pervasives_Native.Some
            (v, (FStar_Pervasives_Native.snd vint))
let (parse_uint : Pollux_Proto_Descriptors.width -> Prims.int field_parser) =
  fun w ->
    fun b ->
      match Pollux_Proto_Varint.extract_varint b with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some vint ->
          let raw_v =
            FStar_UInt64.v
              (Pollux_Proto_Varint.decode (FStar_Pervasives_Native.fst vint)) in
          let v = uint_change_w w raw_v in
          FStar_Pervasives_Native.Some
            (v, (FStar_Pervasives_Native.snd vint))
let (parse_sint : Pollux_Proto_Descriptors.width -> Prims.int field_parser) =
  fun w ->
    fun b ->
      match Pollux_Proto_Varint.extract_varint b with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some vint ->
          let raw_v =
            FStar_UInt64.v
              (Pollux_Proto_Varint.decode (FStar_Pervasives_Native.fst vint)) in
          let v = uint_sint w (uint_change_w w raw_v) in
          FStar_Pervasives_Native.Some
            (v, (FStar_Pervasives_Native.snd vint))
let (parse_fixed : Pollux_Proto_Descriptors.width -> Prims.int field_parser)
  =
  fun w ->
    fun b ->
      let n = w / (Prims.of_int (8)) in
      match take n b with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some db ->
          FStar_Pervasives_Native.Some
            ((assemble_nat (FStar_Pervasives_Native.fst db)),
              (FStar_Pervasives_Native.snd db))
let (parse_sfixed : Pollux_Proto_Descriptors.width -> Prims.int field_parser)
  =
  fun w ->
    fun b ->
      let n = w / (Prims.of_int (8)) in
      match take n b with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some db ->
          FStar_Pervasives_Native.Some
            ((uint_int w (assemble_nat (FStar_Pervasives_Native.fst db))),
              (FStar_Pervasives_Native.snd db))
let (parse_bool : Prims.bool field_parser) =
  fun b ->
    match b with
    | uu___::tl when uu___ = 0 -> FStar_Pervasives_Native.Some (false, tl)
    | uu___::tl when uu___ = 1 -> FStar_Pervasives_Native.Some (true, tl)
    | uu___ -> FStar_Pervasives_Native.None
let (parse_string : Prims.string field_parser) =
  fun b ->
    if FStar_List_Tot_Base.isEmpty b
    then FStar_Pervasives_Native.None
    else
      (let s =
         FStar_String.string_of_list
           (FStar_List_Tot_Base.map
              (fun b1 -> FStar_Char.char_of_int (FStar_UInt8.v b1)) b) in
       FStar_Pervasives_Native.Some (s, []))
let (parse_bytes : Pollux_Proto_Prelude.bytes field_parser) =
  fun b ->
    if FStar_List_Tot_Base.isEmpty b
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some (b, [])
let rec parse_list :
  'a .
    Pollux_Proto_Prelude.bytes ->
      'a field_parser -> 'a Prims.list FStar_Pervasives_Native.option
  =
  fun payload ->
    fun parse_one ->
      match parse_one payload with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (a1, bs) ->
          if FStar_List_Tot_Base.isEmpty bs
          then FStar_Pervasives_Native.Some [a1]
          else
            (let rest = parse_list bs parse_one in
             match rest with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some r ->
                 FStar_Pervasives_Native.Some (a1 :: r))
let parse_dec :
  'a .
    Pollux_Proto_Descriptors.pdec ->
      Pollux_Proto_Prelude.bytes ->
        'a field_parser ->
          'a Pollux_Proto_Descriptors.dvty FStar_Pervasives_Native.option
  =
  fun dec ->
    fun payload ->
      fun parse_one ->
        match dec with
        | Pollux_Proto_Descriptors.P_IMPLICIT ->
            Pollux_Proto_Prelude.op_let_Question (parse_one payload)
              (fun uu___ ->
                 match uu___ with
                 | (one, uu___1) ->
                     FStar_Pervasives_Native.Some
                       (Pollux_Proto_Descriptors.VIMPLICIT one))
        | Pollux_Proto_Descriptors.P_OPTIONAL ->
            Pollux_Proto_Prelude.op_let_Question (parse_one payload)
              (fun uu___ ->
                 match uu___ with
                 | (one, uu___1) ->
                     FStar_Pervasives_Native.Some
                       (Pollux_Proto_Descriptors.VOPTIONAL
                          (FStar_Pervasives_Native.Some one)))
        | Pollux_Proto_Descriptors.P_REPEATED ->
            Pollux_Proto_Prelude.op_let_Question
              (parse_list payload parse_one)
              (fun many ->
                 FStar_Pervasives_Native.Some
                   (Pollux_Proto_Descriptors.VREPEATED many))
let (parse_field :
  Pollux_Proto_Descriptors.pty ->
    Pollux_Proto_Prelude.bytes ->
      Pollux_Proto_Descriptors.vty FStar_Pervasives_Native.option)
  =
  fun ty ->
    fun payload ->
      match ty with
      | Pollux_Proto_Descriptors.P_DOUBLE p' ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload parse_double)
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VDOUBLE vdec))
      | Pollux_Proto_Descriptors.P_FLOAT p' ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload parse_float)
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VFLOAT vdec))
      | Pollux_Proto_Descriptors.P_INT (w, p') ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload (parse_int w))
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VINT vdec))
      | Pollux_Proto_Descriptors.P_UINT (w, p') ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload (parse_uint w))
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VINT vdec))
      | Pollux_Proto_Descriptors.P_SINT (w, p') ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload (parse_sint w))
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VINT vdec))
      | Pollux_Proto_Descriptors.P_FIXED (w, p') ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload (parse_fixed w))
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VINT vdec))
      | Pollux_Proto_Descriptors.P_SFIXED (w, p') ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload (parse_sfixed w))
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VINT vdec))
      | Pollux_Proto_Descriptors.P_BOOL p' ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload parse_bool)
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VBOOL vdec))
      | Pollux_Proto_Descriptors.P_STRING p' ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload parse_string)
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VSTRING vdec))
      | Pollux_Proto_Descriptors.P_BYTES p' ->
          Pollux_Proto_Prelude.op_let_Question
            (parse_dec p' payload parse_bytes)
            (fun vdec ->
               FStar_Pervasives_Native.Some
                 (Pollux_Proto_Descriptors.VBYTES vdec))
      | uu___ -> FStar_Pervasives_Native.None
let update_field :
  'a .
    Prims.string ->
      'a Pollux_Proto_Descriptors.dvty ->
        'a Pollux_Proto_Descriptors.dvty -> 'a Pollux_Proto_Descriptors.dvty
  =
  fun name ->
    fun ori_v ->
      fun new_v ->
        match (ori_v, new_v) with
        | (Pollux_Proto_Descriptors.VIMPLICIT uu___,
           Pollux_Proto_Descriptors.VIMPLICIT v') ->
            Pollux_Proto_Descriptors.VIMPLICIT v'
        | (Pollux_Proto_Descriptors.VOPTIONAL uu___,
           Pollux_Proto_Descriptors.VOPTIONAL v') ->
            Pollux_Proto_Descriptors.VOPTIONAL v'
        | (Pollux_Proto_Descriptors.VREPEATED v',
           Pollux_Proto_Descriptors.VREPEATED value') ->
            Pollux_Proto_Descriptors.VREPEATED
              (FStar_List_Tot_Base.op_At v' value')
        | uu___ -> ori_v
let rec (update_msg :
  Pollux_Proto_Descriptors.msg ->
    Prims.string ->
      Pollux_Proto_Descriptors.vty -> Pollux_Proto_Descriptors.msg)
  =
  fun msg ->
    fun name ->
      fun value ->
        match msg with
        | [] -> []
        | hd::tl ->
            let n = FStar_Pervasives_Native.fst hd in
            let v = FStar_Pervasives_Native.snd hd in
            if n = name
            then
              (n,
                ((match (v, value) with
                  | (Pollux_Proto_Descriptors.VDOUBLE orig,
                     Pollux_Proto_Descriptors.VDOUBLE newv) ->
                      Pollux_Proto_Descriptors.VDOUBLE
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VFLOAT orig,
                     Pollux_Proto_Descriptors.VFLOAT newv) ->
                      Pollux_Proto_Descriptors.VFLOAT
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VINT orig,
                     Pollux_Proto_Descriptors.VINT newv) ->
                      Pollux_Proto_Descriptors.VINT
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VBOOL orig,
                     Pollux_Proto_Descriptors.VBOOL newv) ->
                      Pollux_Proto_Descriptors.VBOOL
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VSTRING orig,
                     Pollux_Proto_Descriptors.VSTRING newv) ->
                      Pollux_Proto_Descriptors.VSTRING
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VBYTES orig,
                     Pollux_Proto_Descriptors.VBYTES newv) ->
                      Pollux_Proto_Descriptors.VBYTES
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VMSG orig,
                     Pollux_Proto_Descriptors.VMSG newv) ->
                      Pollux_Proto_Descriptors.VMSG
                        (update_field n orig newv)
                  | (Pollux_Proto_Descriptors.VENUM orig,
                     Pollux_Proto_Descriptors.VENUM newv) ->
                      Pollux_Proto_Descriptors.VENUM
                        (update_field n orig newv)
                  | uu___ -> v)))
              :: tl
            else (let r = update_msg tl name value in hd :: r)
let (merge_field :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Descriptors.msg FStar_Pervasives_Native.option ->
      (Prims.nat * Pollux_Proto_Prelude.bytes) ->
        Pollux_Proto_Descriptors.msg FStar_Pervasives_Native.option)
  =
  fun m ->
    fun msg ->
      fun f ->
        Pollux_Proto_Prelude.op_let_Question msg
          (fun msg1 ->
             let uu___ = f in
             match uu___ with
             | (fid, payload) ->
                 let field_desc = find_field m fid in
                 (match field_desc with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.Some msg1
                  | FStar_Pervasives_Native.Some (n, f1, ty) ->
                      Pollux_Proto_Prelude.op_let_Question
                        (parse_field ty payload)
                        (fun typed_payload ->
                           let new_msg = update_msg msg1 n typed_payload in
                           FStar_Pervasives_Native.Some new_msg)))
let (parse :
  Pollux_Proto_Descriptors.md ->
    Pollux_Proto_Prelude.bytes ->
      Pollux_Proto_Descriptors.msg FStar_Pervasives_Native.option)
  =
  fun m ->
    fun enc ->
      let uu___ = decode_fields enc in
      match uu___ with
      | (raw_fields, leftover_byt) ->
          if leftover_byt <> []
          then FStar_Pervasives_Native.None
          else
            (let msg = Pollux_Proto_Descriptors.init_msg m in
             let field_merge = merge_field m in
             FStar_List_Tot_Base.fold_left field_merge
               (FStar_Pervasives_Native.Some msg) raw_fields)
