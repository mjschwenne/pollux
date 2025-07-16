open Prims
let rec (valid : FStar_UInt8.t Prims.list -> Prims.bool) =
  fun v ->
    match v with
    | [] -> false
    | msb::[] -> FStar_UInt.fits (FStar_UInt8.v msb) (Prims.of_int (7))
    | msb::rest ->
        (FStar_UInt.msb (Prims.of_int (8)) (FStar_UInt8.v msb)) &&
          (valid rest)
type varint = Pollux_Proto_Prelude.bytes
let (set_msb_u8 : FStar_UInt8.t -> FStar_UInt8.t) =
  fun b -> let r = FStar_UInt8.add b 128 in r
let (unset_msb_u8 : FStar_UInt8.t -> FStar_UInt8.t) =
  fun b -> let r = FStar_UInt8.sub b 128 in r
let rec (decode : varint -> FStar_UInt64.t) =
  fun bs ->
    match bs with
    | msb::[] -> FStar_Int_Cast.uint8_to_uint64 msb
    | msb::rest ->
        let msbx = unset_msb_u8 msb in
        let msx = FStar_Int_Cast.uint8_to_uint64 msbx in
        let rx = decode rest in
        let y =
          FStar_UInt64.logor
            (FStar_UInt64.shift_left rx (Stdint.Uint32.of_int (7))) msx in
        y
let rec (extract_varint :
  FStar_UInt8.t Prims.list ->
    (varint * Pollux_Proto_Prelude.bytes) FStar_Pervasives_Native.option)
  =
  fun bs ->
    match bs with
    | [] -> FStar_Pervasives_Native.None
    | h::tl ->
        if FStar_UInt8.lte h 127
        then FStar_Pervasives_Native.Some ([h], tl)
        else
          (let rest = extract_varint tl in
           match rest with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (v, rest1) ->
               FStar_Pervasives_Native.Some ((h :: v), rest1))
let (split :
  Prims.pos ->
    Obj.t FStar_UInt.uint_t ->
      Prims.pos -> (Obj.t FStar_UInt.uint_t * Obj.t FStar_UInt.uint_t))
  =
  fun b ->
    fun x ->
      fun n ->
        let lo = FStar_UInt.logand b x ((Prims.pow2 n) - Prims.int_one) in
        let hi = FStar_UInt.shift_right b x n in (hi, lo)
let (split64 :
  FStar_UInt64.t ->
    Prims.pos -> (Obj.t FStar_UInt.uint_t * Obj.t FStar_UInt.uint_t))
  = fun x -> fun n -> split (Prims.of_int (64)) (FStar_UInt64.v x) n
let (split_lo_to_u8 : unit -> Obj.t FStar_UInt.uint_t -> FStar_UInt8.t) =
  fun x ->
    fun lo -> FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.uint_to_t lo)
let rec (encode : FStar_UInt64.t -> varint) =
  fun x ->
    let uu___ = split64 x (Prims.of_int (7)) in
    match uu___ with
    | (hi, lo) ->
        let hi64 = FStar_UInt64.uint_to_t hi in
        if FStar_UInt64.lte hi64 Stdint.Uint64.zero
        then [split_lo_to_u8 () lo]
        else
          (let lo8 = split_lo_to_u8 () lo in
           let rx = encode hi64 in (set_msb_u8 lo8) :: rx)
