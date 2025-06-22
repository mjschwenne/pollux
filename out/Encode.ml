open Prims
let rec (valid : FStar_UInt8.t Prims.list -> Prims.bool) =
  fun v ->
    match v with
    | [] -> false
    | msb::[] -> FStar_UInt.fits (FStar_UInt8.v msb) (Prims.of_int (7))
    | msb::rest ->
        (FStar_UInt.msb (Prims.of_int (8)) (FStar_UInt8.v msb)) &&
          (valid rest)
type varint = FStar_UInt8.t Prims.list
let rec (encode : FStar_UInt64.t -> varint) =
  fun x ->
    let nextByte =
      FStar_Int_Cast.uint64_to_uint8
        (FStar_UInt64.logand x (Stdint.Uint64.of_int (0x7F))) in
    let rest = FStar_UInt64.shift_right x (Stdint.Uint32.of_int (7)) in
    if FStar_UInt64.lte rest Stdint.Uint64.zero
    then [nextByte]
    else
      (let nextByte1 = FStar_UInt8.add nextByte 128 in
       let restEnc = encode rest in
       FStar_List_Tot_Base.append [nextByte1] restEnc)
let rec (decode : varint -> FStar_UInt64.t) =
  fun bs ->
    match bs with
    | msb::[] -> FStar_Int_Cast.uint8_to_uint64 msb
    | msb::rest ->
        let msbx = FStar_UInt8.logand msb 0x7F in
        let msx = FStar_Int_Cast.uint8_to_uint64 msbx in
        let rx = decode rest in
        let y =
          FStar_UInt64.logand msx
            (FStar_UInt64.shift_left rx (Stdint.Uint32.of_int (7))) in
        y
let (test_msg : Proto3.msg) =
  {
    Proto3.name = "Test";
    Proto3.reserved = (FStar_Set.empty ());
    Proto3.fields =
      [("field1", Prims.int_one,
         (Proto3.INT
            ((Prims.of_int (32)),
              (Proto3.IMPLICIT
                 (FStar_Pervasives_Native.Some (Prims.of_int (10)))))));
      ("field2", (Prims.of_int (2)),
        (Proto3.STRING
           (Proto3.OPTIONAL (FStar_Pervasives_Native.Some "Test String"))));
      ("field3", (Prims.of_int (3)),
        (Proto3.UINT
           ((Prims.of_int (64)),
             (Proto3.OPTIONAL FStar_Pervasives_Native.None))))]
  }
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
let (tag_func : Proto3.proto_ty -> tag) =
  fun p ->
    match p with
    | Proto3.INT (uu___, uu___1) -> VARINT
    | Proto3.UINT (uu___, uu___1) -> VARINT
    | Proto3.SINT (uu___, uu___1) -> VARINT
    | Proto3.BOOL uu___ -> VARINT
    | Proto3.ENUM -> VARINT
    | Proto3.FIXED (uu___, uu___1) when uu___ = (Prims.of_int (32)) -> I32
    | Proto3.SFIXED (uu___, uu___1) when uu___ = (Prims.of_int (32)) -> I32
    | Proto3.FLOAT -> I32
    | Proto3.FIXED (uu___, uu___1) when uu___ = (Prims.of_int (64)) -> I64
    | Proto3.SFIXED (uu___, uu___1) when uu___ = (Prims.of_int (64)) -> I64
    | Proto3.DOUBLE -> I64
    | uu___ -> LEN
let (nat_to_u64 : Prims.nat -> FStar_UInt64.t) =
  fun n ->
    FStar_UInt64.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (64)) n)
let (int_to_i64 : Prims.int -> FStar_Int64.t) =
  fun z -> FStar_Int64.int_to_t (FStar_Int.to_int_t (Prims.of_int (64)) z)
let (nat_to_u32 : Prims.nat -> FStar_UInt32.t) =
  fun n ->
    FStar_UInt32.uint_to_t (FStar_UInt.to_uint_t (Prims.of_int (32)) n)
let (tag_num : tag -> FStar_UInt64.t) =
  fun t ->
    match t with
    | VARINT -> nat_to_u64 Prims.int_zero
    | I64 -> nat_to_u64 Prims.int_one
    | LEN -> nat_to_u64 (Prims.of_int (2))
    | I32 -> nat_to_u64 (Prims.of_int (5))
let (byte_list_of_string : Prims.string -> FStar_UInt8.t Prims.list) =
  fun s ->
    FStar_List_Tot_Base.map
      (fun c ->
         FStar_UInt8.uint_to_t
           (FStar_UInt.to_uint_t (Prims.of_int (8))
              (FStar_Char.int_of_char c))) (FStar_String.list_of_string s)
let (encode_field : Proto3.field -> FStar_UInt8.t Prims.list) =
  fun f ->
    let tagn =
      tag_num
        (tag_func (FStar_Pervasives_Native.__proj__Mktuple3__item___3 f)) in
    let id_u64 =
      nat_to_u64 (FStar_Pervasives_Native.__proj__Mktuple3__item___2 f) in
    let header_u64 =
      FStar_UInt64.logor
        (FStar_UInt64.shift_left id_u64 (nat_to_u32 (Prims.of_int (3)))) tagn in
    let header_enc = encode header_u64 in
    let body_enc =
      match FStar_Pervasives_Native.__proj__Mktuple3__item___3 f with
      | Proto3.UINT (uu___, Proto3.IMPLICIT (FStar_Pervasives_Native.Some v))
          -> encode (nat_to_u64 v)
      | Proto3.UINT (uu___, Proto3.OPTIONAL (FStar_Pervasives_Native.Some v))
          -> encode (nat_to_u64 v)
      | Proto3.INT (uu___, Proto3.IMPLICIT (FStar_Pervasives_Native.Some v))
          -> encode (FStar_Int_Cast.int64_to_uint64 (int_to_i64 v))
      | Proto3.INT (uu___, Proto3.OPTIONAL (FStar_Pervasives_Native.Some v))
          -> encode (FStar_Int_Cast.int64_to_uint64 (int_to_i64 v))
      | Proto3.SINT (uu___, Proto3.IMPLICIT (FStar_Pervasives_Native.Some v))
          -> encode (FStar_Int_Cast.int64_to_uint64 (int_to_i64 v))
      | Proto3.SINT (uu___, Proto3.OPTIONAL (FStar_Pervasives_Native.Some v))
          -> encode (FStar_Int_Cast.int64_to_uint64 (int_to_i64 v))
      | Proto3.STRING (Proto3.IMPLICIT (FStar_Pervasives_Native.Some v)) ->
          FStar_List_Tot_Base.append
            (encode (nat_to_u64 (FStar_String.strlen v)))
            (byte_list_of_string v)
      | Proto3.STRING (Proto3.OPTIONAL (FStar_Pervasives_Native.Some v)) ->
          FStar_List_Tot_Base.append
            (encode (nat_to_u64 (FStar_String.strlen v)))
            (byte_list_of_string v)
      | uu___ -> [] in
    if body_enc = []
    then []
    else FStar_List_Tot_Base.append header_enc body_enc
let (encode_msg : Proto3.msg -> FStar_UInt8.t Prims.list) =
  fun m ->
    FStar_List_Tot_Base.fold_left FStar_List_Tot_Base.append []
      (FStar_List_Tot_Base.map encode_field m.Proto3.fields)
let (bin_to_str : FStar_UInt8.t Prims.list -> Prims.string) =
  fun e ->
    FStar_String.string_of_list
      (FStar_List_Tot_Base.map
         (fun b -> FStar_Char.char_of_int (FStar_UInt8.v b)) e)
let (main : unit -> unit) =
  fun uu___ ->
    let enc = encode_msg test_msg in
    let enc_str =
      FStar_String.string_of_list
        (FStar_List_Tot_Base.map
           (fun b -> FStar_Char.char_of_int (FStar_UInt8.v b)) enc) in
    FStar_IO.print_string enc_str
let (uu___0 : unit) = main ()
