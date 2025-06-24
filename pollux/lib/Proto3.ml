open Prims
type byte = FStar_String.char
type bytes = byte Prims.list
let (empty_bytes : bytes) = []
type width = Prims.int
type 'w zw = Prims.int
let (zwz : width -> Obj.t zw) = fun w -> Prims.int_zero
type 'w uw = Prims.nat
let (uwz : width -> Obj.t uw) = fun w -> Prims.int_zero
type 'a proto_dec =
  | IMPLICIT of 'a FStar_Pervasives_Native.option 
  | OPTIONAL of 'a FStar_Pervasives_Native.option 
  | REPEATED of 'a Prims.list 
let uu___is_IMPLICIT : 'a . 'a proto_dec -> Prims.bool =
  fun projectee ->
    match projectee with | IMPLICIT _0 -> true | uu___ -> false
let __proj__IMPLICIT__item___0 :
  'a . 'a proto_dec -> 'a FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | IMPLICIT _0 -> _0
let uu___is_OPTIONAL : 'a . 'a proto_dec -> Prims.bool =
  fun projectee ->
    match projectee with | OPTIONAL _0 -> true | uu___ -> false
let __proj__OPTIONAL__item___0 :
  'a . 'a proto_dec -> 'a FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | OPTIONAL _0 -> _0
let uu___is_REPEATED : 'a . 'a proto_dec -> Prims.bool =
  fun projectee ->
    match projectee with | REPEATED _0 -> true | uu___ -> false
let __proj__REPEATED__item___0 : 'a . 'a proto_dec -> 'a Prims.list =
  fun projectee -> match projectee with | REPEATED _0 -> _0
let is_IMPLICIT_v : 't . 't proto_dec -> 't -> Prims.bool =
  fun d ->
    fun v ->
      match d with
      | IMPLICIT (FStar_Pervasives_Native.Some e) -> e = v
      | uu___ -> false
let is_OPTIONAL_v : 't . 't proto_dec -> 't -> Prims.bool =
  fun d ->
    fun v ->
      match d with
      | OPTIONAL (FStar_Pervasives_Native.Some e) -> e = v
      | uu___ -> false
let is_REPEATED_v : 't . 't proto_dec -> 't Prims.list -> Prims.bool =
  fun d -> fun v -> match d with | REPEATED e -> e = v | uu___ -> false
type proto_ty =
  | DOUBLE 
  | FLOAT 
  | INT of width * Obj.t zw proto_dec 
  | UINT of width * Obj.t uw proto_dec 
  | SINT of width * Obj.t zw proto_dec 
  | FIXED of width * Obj.t uw proto_dec 
  | SFIXED of width * Obj.t zw proto_dec 
  | BOOL of Prims.bool proto_dec 
  | STRING of Prims.string proto_dec 
  | BYTES of bytes proto_dec 
  | MSG 
  | ENUM 
let (uu___is_DOUBLE : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | DOUBLE -> true | uu___ -> false
let (uu___is_FLOAT : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | FLOAT -> true | uu___ -> false
let (uu___is_INT : proto_ty -> Prims.bool) =
  fun projectee ->
    match projectee with | INT (w, _1) -> true | uu___ -> false
let (__proj__INT__item__w : proto_ty -> width) =
  fun projectee -> match projectee with | INT (w, _1) -> w
let (__proj__INT__item___1 : proto_ty -> Obj.t zw proto_dec) =
  fun projectee -> match projectee with | INT (w, _1) -> _1
let (uu___is_UINT : proto_ty -> Prims.bool) =
  fun projectee ->
    match projectee with | UINT (w, _1) -> true | uu___ -> false
let (__proj__UINT__item__w : proto_ty -> width) =
  fun projectee -> match projectee with | UINT (w, _1) -> w
let (__proj__UINT__item___1 : proto_ty -> Obj.t uw proto_dec) =
  fun projectee -> match projectee with | UINT (w, _1) -> _1
let (uu___is_SINT : proto_ty -> Prims.bool) =
  fun projectee ->
    match projectee with | SINT (w, _1) -> true | uu___ -> false
let (__proj__SINT__item__w : proto_ty -> width) =
  fun projectee -> match projectee with | SINT (w, _1) -> w
let (__proj__SINT__item___1 : proto_ty -> Obj.t zw proto_dec) =
  fun projectee -> match projectee with | SINT (w, _1) -> _1
let (uu___is_FIXED : proto_ty -> Prims.bool) =
  fun projectee ->
    match projectee with | FIXED (w, _1) -> true | uu___ -> false
let (__proj__FIXED__item__w : proto_ty -> width) =
  fun projectee -> match projectee with | FIXED (w, _1) -> w
let (__proj__FIXED__item___1 : proto_ty -> Obj.t uw proto_dec) =
  fun projectee -> match projectee with | FIXED (w, _1) -> _1
let (uu___is_SFIXED : proto_ty -> Prims.bool) =
  fun projectee ->
    match projectee with | SFIXED (w, _1) -> true | uu___ -> false
let (__proj__SFIXED__item__w : proto_ty -> width) =
  fun projectee -> match projectee with | SFIXED (w, _1) -> w
let (__proj__SFIXED__item___1 : proto_ty -> Obj.t zw proto_dec) =
  fun projectee -> match projectee with | SFIXED (w, _1) -> _1
let (uu___is_BOOL : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | BOOL _0 -> true | uu___ -> false
let (__proj__BOOL__item___0 : proto_ty -> Prims.bool proto_dec) =
  fun projectee -> match projectee with | BOOL _0 -> _0
let (uu___is_STRING : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | STRING _0 -> true | uu___ -> false
let (__proj__STRING__item___0 : proto_ty -> Prims.string proto_dec) =
  fun projectee -> match projectee with | STRING _0 -> _0
let (uu___is_BYTES : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | BYTES _0 -> true | uu___ -> false
let (__proj__BYTES__item___0 : proto_ty -> bytes proto_dec) =
  fun projectee -> match projectee with | BYTES _0 -> _0
let (uu___is_MSG : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | MSG -> true | uu___ -> false
let (uu___is_ENUM : proto_ty -> Prims.bool) =
  fun projectee -> match projectee with | ENUM -> true | uu___ -> false
let (test_pty : proto_ty) =
  INT
    ((Prims.of_int (32)),
      (REPEATED [(Prims.of_int (3)); (Prims.of_int (4))]))
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
let (idnuw : width -> Prims.bool -> Obj.t uw) =
  fun w -> fun c -> if c then Prims.int_one else Prims.int_zero
let (idnzw : width -> Prims.bool -> Obj.t zw) =
  fun w -> fun c -> if c then Prims.int_one else Prims.int_zero
let (uint_change_w : width -> Prims.int -> Obj.t uw) =
  fun w -> fun v -> v mod (Prims.pow2 w)
let (int_change_w : width -> Prims.int -> Obj.t zw) =
  fun w ->
    fun v ->
      (v mod (Prims.pow2 (w - Prims.int_one))) -
        ((Prims.pow2 (w - Prims.int_one)) *
           (idn
              (((v / (Prims.pow2 (w - Prims.int_one))) mod (Prims.of_int (2)))
                 = Prims.int_one)))
let (sint_change_w : width -> Prims.int -> Obj.t zw) =
  fun w ->
    fun v ->
      (v mod (Prims.pow2 (w - Prims.int_one))) -
        ((Prims.pow2 (w - Prims.int_one)) * (idn (v < Prims.int_zero)))
let (uint_int : width -> Obj.t uw -> Obj.t zw) =
  fun w ->
    fun v ->
      v - ((Prims.pow2 w) * (idn (v >= (Prims.pow2 (w - Prims.int_one)))))
let (int_uint : width -> Obj.t zw -> Obj.t uw) =
  fun w -> fun v -> v + ((Prims.pow2 w) * (idn (v < Prims.int_zero)))
let (uint_sint : width -> Obj.t uw -> Obj.t zw) =
  fun w ->
    fun v ->
      ((parity v) * (v / (Prims.of_int (2)))) - (v mod (Prims.of_int (2)))
let (sint_uint : width -> Obj.t zw -> Obj.t uw) =
  fun w ->
    fun v ->
      ((Prims.of_int (2)) * (Prims.abs v)) - (idn (v < Prims.int_zero))
let (int_sint : width -> Obj.t zw -> Obj.t zw) =
  fun w ->
    fun v ->
      if v >= Prims.int_zero
      then
        ((parity v) * (v / (Prims.of_int (2)))) - (v mod (Prims.of_int (2)))
      else
        (parity v) *
          ((v + (Prims.pow2 (w - Prims.int_one))) - (v / (Prims.of_int (2))))
let (sint_int : width -> Obj.t zw -> Obj.t zw) =
  fun w ->
    fun v ->
      if
        ((- (Prims.pow2 (w - (Prims.of_int (2))))) <= v) &&
          (v < (Prims.pow2 (w - (Prims.of_int (2)))))
      then ((Prims.of_int (2)) * (Prims.abs v)) - (idn (v < Prims.int_zero))
      else
        (((Prims.of_int (2)) * (Prims.abs v)) - (Prims.pow2 w)) -
          (idn (v < Prims.int_zero))
let pty_wrap :
  't1 't2 . ('t1 -> 't2) -> 't2 -> 't1 proto_dec -> 't2 proto_dec =
  fun f ->
    fun d ->
      fun a ->
        match a with
        | IMPLICIT (FStar_Pervasives_Native.Some a') ->
            IMPLICIT (FStar_Pervasives_Native.Some (f a'))
        | IMPLICIT (FStar_Pervasives_Native.None) ->
            IMPLICIT (FStar_Pervasives_Native.Some d)
        | OPTIONAL (FStar_Pervasives_Native.Some a') ->
            OPTIONAL (FStar_Pervasives_Native.Some (f a'))
        | OPTIONAL (FStar_Pervasives_Native.None) ->
            OPTIONAL FStar_Pervasives_Native.None
        | REPEATED l -> REPEATED (FStar_List_Tot_Base.map f l)
let (proto_ty_int_sint32 : Obj.t zw proto_dec -> Obj.t zw proto_dec) =
  pty_wrap (int_sint (Prims.of_int (32))) (zwz (Prims.of_int (32)))
let (proto_ty_int_sint_test_i : Obj.t zw proto_dec) =
  proto_ty_int_sint32
    (IMPLICIT (FStar_Pervasives_Native.Some (Prims.of_int (-9))))
let (proto_ty_int_sint_test_i' : Obj.t zw proto_dec) =
  proto_ty_int_sint32 (IMPLICIT FStar_Pervasives_Native.None)
let (proto_ty_int_sint_test_o : Obj.t zw proto_dec) =
  proto_ty_int_sint32 (OPTIONAL FStar_Pervasives_Native.None)
let (proto_ty_int_sint_test_o' : Obj.t zw proto_dec) =
  proto_ty_int_sint32
    (OPTIONAL (FStar_Pervasives_Native.Some (Prims.of_int (9))))
let (proto_ty_int_sint_test_r : Obj.t zw proto_dec) =
  proto_ty_int_sint32 (REPEATED [(Prims.of_int (-9)); (Prims.of_int (9))])
type ('dummyV0, 'dummyV1) val_rel =
  | ValTrans of proto_ty * proto_ty * proto_ty * (Obj.t, Obj.t) val_rel *
  (Obj.t, Obj.t) val_rel 
  | ValRefl of proto_ty 
  | ValStrByt of Prims.string proto_dec * bytes proto_dec 
  | ValBytStr of bytes proto_dec * Prims.string proto_dec 
  | ValUintChgW of width * width * Obj.t uw proto_dec * Obj.t uw proto_dec 
  | ValIntChgW of width * width * Obj.t zw proto_dec * Obj.t zw proto_dec 
  | ValSintChgW of width * width * Obj.t zw proto_dec * Obj.t zw proto_dec 
  | ValUintInt of width * Obj.t uw proto_dec * Obj.t zw proto_dec 
  | ValIntUint of width * Obj.t zw proto_dec * Obj.t uw proto_dec 
  | ValUintSint of width * Obj.t uw proto_dec * Obj.t zw proto_dec 
  | ValIntSint of width * Obj.t zw proto_dec * Obj.t zw proto_dec 
  | ValSintInt of width * Obj.t zw proto_dec * Obj.t zw proto_dec 
  | ValUintBool of width * Obj.t uw proto_dec * Prims.bool proto_dec 
  | ValBoolUint of width * Prims.bool proto_dec * Obj.t uw proto_dec 
  | ValIntBool of width * Obj.t zw proto_dec * Prims.bool proto_dec 
  | ValBoolInt of width * Prims.bool proto_dec * Obj.t zw proto_dec 
  | ValSintBool of width * Obj.t zw proto_dec * Prims.bool proto_dec 
  | ValBoolSint of width * Prims.bool proto_dec * Obj.t zw proto_dec 
  | ValAddOpt of unit * (Obj.t proto_dec -> proto_ty) * Obj.t * Obj.t
  proto_dec 
  | ValRmOpt of unit * (Obj.t proto_dec -> proto_ty) * Obj.t * Obj.t
  proto_dec 
  | ValAddRep of unit * (Obj.t proto_dec -> proto_ty) * Obj.t * Obj.t
  proto_dec 
let (uu___is_ValTrans :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValTrans (v1, v2, v3, vr1, vr2) -> true
        | uu___2 -> false
let (__proj__ValTrans__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> proto_ty) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValTrans (v1, v2, v3, vr1, vr2) -> v1
let (__proj__ValTrans__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> proto_ty) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValTrans (v1, v2, v3, vr1, vr2) -> v2
let (__proj__ValTrans__item__v3 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> proto_ty) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValTrans (v1, v2, v3, vr1, vr2) -> v3
let (__proj__ValTrans__item__vr1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> (Obj.t, Obj.t) val_rel) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValTrans (v1, v2, v3, vr1, vr2) -> vr1
let (__proj__ValTrans__item__vr2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> (Obj.t, Obj.t) val_rel) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValTrans (v1, v2, v3, vr1, vr2) -> vr2
let (uu___is_ValRefl :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValRefl v -> true | uu___2 -> false
let (__proj__ValRefl__item__v :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> proto_ty) =
  fun uu___ ->
    fun uu___1 -> fun projectee -> match projectee with | ValRefl v -> v
let (uu___is_ValStrByt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValStrByt (v1, v2) -> true | uu___2 -> false
let (__proj__ValStrByt__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.string proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValStrByt (v1, v2) -> v1
let (__proj__ValStrByt__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> bytes proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValStrByt (v1, v2) -> v2
let (uu___is_ValBytStr :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValBytStr (v1, v2) -> true | uu___2 -> false
let (__proj__ValBytStr__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> bytes proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBytStr (v1, v2) -> v1
let (__proj__ValBytStr__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.string proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBytStr (v1, v2) -> v2
let (uu___is_ValUintChgW :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValUintChgW (w1, w2, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValUintChgW__item__w1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValUintChgW (w1, w2, v1, v2) -> w1
let (__proj__ValUintChgW__item__w2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValUintChgW (w1, w2, v1, v2) -> w2
let (__proj__ValUintChgW__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValUintChgW (w1, w2, v1, v2) -> v1
let (__proj__ValUintChgW__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValUintChgW (w1, w2, v1, v2) -> v2
let (uu___is_ValIntChgW :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValIntChgW (w1, w2, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValIntChgW__item__w1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValIntChgW (w1, w2, v1, v2) -> w1
let (__proj__ValIntChgW__item__w2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValIntChgW (w1, w2, v1, v2) -> w2
let (__proj__ValIntChgW__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValIntChgW (w1, w2, v1, v2) -> v1
let (__proj__ValIntChgW__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValIntChgW (w1, w2, v1, v2) -> v2
let (uu___is_ValSintChgW :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValSintChgW (w1, w2, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValSintChgW__item__w1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValSintChgW (w1, w2, v1, v2) -> w1
let (__proj__ValSintChgW__item__w2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValSintChgW (w1, w2, v1, v2) -> w2
let (__proj__ValSintChgW__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValSintChgW (w1, w2, v1, v2) -> v1
let (__proj__ValSintChgW__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValSintChgW (w1, w2, v1, v2) -> v2
let (uu___is_ValUintInt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValUintInt (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValUintInt__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintInt (w, v1, v2) -> w
let (__proj__ValUintInt__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintInt (w, v1, v2) -> v1
let (__proj__ValUintInt__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintInt (w, v1, v2) -> v2
let (uu___is_ValIntUint :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValIntUint (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValIntUint__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntUint (w, v1, v2) -> w
let (__proj__ValIntUint__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntUint (w, v1, v2) -> v1
let (__proj__ValIntUint__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntUint (w, v1, v2) -> v2
let (uu___is_ValUintSint :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValUintSint (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValUintSint__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintSint (w, v1, v2) -> w
let (__proj__ValUintSint__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintSint (w, v1, v2) -> v1
let (__proj__ValUintSint__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintSint (w, v1, v2) -> v2
let (uu___is_ValIntSint :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValIntSint (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValIntSint__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntSint (w, v1, v2) -> w
let (__proj__ValIntSint__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntSint (w, v1, v2) -> v1
let (__proj__ValIntSint__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntSint (w, v1, v2) -> v2
let (uu___is_ValSintInt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValSintInt (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValSintInt__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintInt (w, v1, v2) -> w
let (__proj__ValSintInt__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintInt (w, v1, v2) -> v1
let (__proj__ValSintInt__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintInt (w, v1, v2) -> v2
let (uu___is_ValUintBool :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValUintBool (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValUintBool__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintBool (w, v1, v2) -> w
let (__proj__ValUintBool__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintBool (w, v1, v2) -> v1
let (__proj__ValUintBool__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValUintBool (w, v1, v2) -> v2
let (uu___is_ValBoolUint :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValBoolUint (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValBoolUint__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolUint (w, v1, v2) -> w
let (__proj__ValBoolUint__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolUint (w, v1, v2) -> v1
let (__proj__ValBoolUint__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t uw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolUint (w, v1, v2) -> v2
let (uu___is_ValIntBool :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValIntBool (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValIntBool__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntBool (w, v1, v2) -> w
let (__proj__ValIntBool__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntBool (w, v1, v2) -> v1
let (__proj__ValIntBool__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValIntBool (w, v1, v2) -> v2
let (uu___is_ValBoolInt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValBoolInt (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValBoolInt__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolInt (w, v1, v2) -> w
let (__proj__ValBoolInt__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolInt (w, v1, v2) -> v1
let (__proj__ValBoolInt__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolInt (w, v1, v2) -> v2
let (uu___is_ValSintBool :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValSintBool (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValSintBool__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintBool (w, v1, v2) -> w
let (__proj__ValSintBool__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintBool (w, v1, v2) -> v1
let (__proj__ValSintBool__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValSintBool (w, v1, v2) -> v2
let (uu___is_ValBoolSint :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValBoolSint (w, v1, v2) -> true
        | uu___2 -> false
let (__proj__ValBoolSint__item__w :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> width) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolSint (w, v1, v2) -> w
let (__proj__ValBoolSint__item__v1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolSint (w, v1, v2) -> v1
let (__proj__ValBoolSint__item__v2 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t zw proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValBoolSint (w, v1, v2) -> v2
let (uu___is_ValAddOpt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValAddOpt (t, pty, v, pty1) -> true
        | uu___2 -> false
let (__proj__ValAddOpt__item__pty :
  proto_ty ->
    proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec -> proto_ty)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddOpt (t, pty, v, pty1) -> pty
let (__proj__ValAddOpt__item__v :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddOpt (t, pty, v, pty1) -> v
let (__proj__ValAddOpt__item__pty1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddOpt (t, pty, v, pty1) -> pty1
let (uu___is_ValRmOpt :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValRmOpt (t, pty, v, pty1) -> true
        | uu___2 -> false
let (__proj__ValRmOpt__item__pty :
  proto_ty ->
    proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec -> proto_ty)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValRmOpt (t, pty, v, pty1) -> pty
let (__proj__ValRmOpt__item__v :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ValRmOpt (t, pty, v, pty1) -> v
let (__proj__ValRmOpt__item__pty1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValRmOpt (t, pty, v, pty1) -> pty1
let (uu___is_ValAddRep :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ValAddRep (t, pty, v, pty1) -> true
        | uu___2 -> false
let (__proj__ValAddRep__item__pty :
  proto_ty ->
    proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec -> proto_ty)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddRep (t, pty, v, pty1) -> pty
let (__proj__ValAddRep__item__v :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddRep (t, pty, v, pty1) -> v
let (__proj__ValAddRep__item__pty1 :
  proto_ty -> proto_ty -> (Obj.t, Obj.t) val_rel -> Obj.t proto_dec) =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ValAddRep (t, pty, v, pty1) -> pty1
let (test_str : Prims.string) = "test"
let (test_bytes : FStar_String.char Prims.list) =
  FStar_String.list_of_string test_str
let (test_str_byt : (Obj.t, Obj.t) val_rel) =
  ValStrByt
    ((IMPLICIT (FStar_Pervasives_Native.Some test_str)),
      (IMPLICIT (FStar_Pervasives_Native.Some test_bytes)))
let (test_uint_demotion : (Obj.t, Obj.t) val_rel) =
  ValUintChgW
    ((Prims.of_int (64)), (Prims.of_int (32)),
      (OPTIONAL
         (FStar_Pervasives_Native.Some (Prims.parse_int "34359738370"))),
      (OPTIONAL (FStar_Pervasives_Native.Some (Prims.of_int (2)))))
let (test_uint_int : (Obj.t, Obj.t) val_rel) =
  ValUintInt
    ((Prims.of_int (32)),
      (IMPLICIT (FStar_Pervasives_Native.Some (Prims.parse_int "2147483656"))),
      (IMPLICIT
         (FStar_Pervasives_Native.Some (Prims.parse_int "-2147483640"))))
let (test_uint_big_int : (Obj.t, Obj.t) val_rel) =
  ValTrans
    ((UINT
        ((Prims.of_int (32)),
          (IMPLICIT
             (FStar_Pervasives_Native.Some (Prims.parse_int "2147483656"))))),
      (INT
         ((Prims.of_int (32)),
           (IMPLICIT
              (FStar_Pervasives_Native.Some (Prims.parse_int "-2147483640"))))),
      (INT
         ((Prims.of_int (64)),
           (IMPLICIT
              (FStar_Pervasives_Native.Some (Prims.parse_int "-2147483640"))))),
      test_uint_int,
      (ValIntChgW
         ((Prims.of_int (32)), (Prims.of_int (64)),
           (IMPLICIT
              (FStar_Pervasives_Native.Some (Prims.parse_int "-2147483640"))),
           (IMPLICIT
              (FStar_Pervasives_Native.Some (Prims.parse_int "-2147483640"))))))
let (test_refl : (Obj.t, Obj.t) val_rel) =
  ValRefl
    (UINT
       ((Prims.of_int (32)),
         (IMPLICIT (FStar_Pervasives_Native.Some Prims.int_zero))))
let (test_add_opt : (Obj.t, Obj.t) val_rel) =
  ValAddOpt
    ((),
      (fun uu___ ->
         (fun uu___ ->
            let uu___ = Obj.magic uu___ in
            Obj.magic (UINT ((Prims.of_int (32)), uu___))) uu___),
      (Obj.magic Prims.int_zero),
      (Obj.magic (IMPLICIT (FStar_Pervasives_Native.Some Prims.int_zero))))
let (test_rm_opt : (Obj.t, Obj.t) val_rel) =
  ValRmOpt
    ((),
      (fun uu___ ->
         (fun uu___ ->
            let uu___ = Obj.magic uu___ in
            Obj.magic (SINT ((Prims.of_int (64)), uu___))) uu___),
      (Obj.magic (Prims.parse_int "123456")),
      (Obj.magic
         (OPTIONAL (FStar_Pervasives_Native.Some (Prims.parse_int "123456")))))
let (test_add_rep : (Obj.t, Obj.t) val_rel) =
  ValAddRep
    ((),
      (fun uu___ ->
         (fun uu___ ->
            let uu___ = Obj.magic uu___ in
            Obj.magic (UINT ((Prims.of_int (32)), uu___))) uu___),
      (Obj.magic (Prims.of_int (12))),
      (Obj.magic
         (IMPLICIT (FStar_Pervasives_Native.Some (Prims.of_int (12))))))
let (test_add_rep' : (Obj.t, Obj.t) val_rel) =
  ValAddRep
    ((),
      (fun uu___ ->
         (fun uu___ ->
            let uu___ = Obj.magic uu___ in
            Obj.magic (INT ((Prims.of_int (32)), uu___))) uu___),
      (Obj.magic (Prims.of_int (-23))),
      (Obj.magic
         (OPTIONAL (FStar_Pervasives_Native.Some (Prims.of_int (-23))))))
type field = (Prims.string * Prims.nat * proto_ty)
type msg =
  {
  name: Prims.string ;
  reserved: Prims.nat FStar_Set.set ;
  fields: field Prims.list }
let (__proj__Mkmsg__item__name : msg -> Prims.string) =
  fun projectee -> match projectee with | { name; reserved; fields;_} -> name
let (__proj__Mkmsg__item__reserved : msg -> Prims.nat FStar_Set.set) =
  fun projectee ->
    match projectee with | { name; reserved; fields;_} -> reserved
let (__proj__Mkmsg__item__fields : msg -> field Prims.list) =
  fun projectee ->
    match projectee with | { name; reserved; fields;_} -> fields
