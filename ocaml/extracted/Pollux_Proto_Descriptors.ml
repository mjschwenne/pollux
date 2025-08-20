open Prims
type float = FStar_UInt8.t Prims.list
let (float_z : float) = [0; 0; 0; 0]
type double = FStar_UInt8.t Prims.list
let (double_z : double) = FStar_List_Tot_Base.op_At float_z float_z
type width = Prims.int
type 'w zw = Prims.int
let (zwz : width -> Obj.t zw) = fun w -> Prims.int_zero
type 'w uw = Prims.nat
let (uwz : width -> Obj.t uw) = fun w -> Prims.int_zero
type pdec =
  | P_IMPLICIT 
  | P_OPTIONAL 
  | P_REPEATED 
let (uu___is_P_IMPLICIT : pdec -> Prims.bool) =
  fun projectee -> match projectee with | P_IMPLICIT -> true | uu___ -> false
let (uu___is_P_OPTIONAL : pdec -> Prims.bool) =
  fun projectee -> match projectee with | P_OPTIONAL -> true | uu___ -> false
let (uu___is_P_REPEATED : pdec -> Prims.bool) =
  fun projectee -> match projectee with | P_REPEATED -> true | uu___ -> false
let sort_pair_fst :
  'uuuuu 'uuuuu1 .
    (Prims.string * 'uuuuu) -> (Prims.string * 'uuuuu1) -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      FStar_List_Tot_Base.bool_of_compare FStar_String.compare
        (FStar_Pervasives_Native.fst v1) (FStar_Pervasives_Native.fst v2)
let sort_pair_snd :
  'uuuuu 'uuuuu1 .
    ('uuuuu * Prims.string) -> ('uuuuu1 * Prims.string) -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      FStar_List_Tot_Base.bool_of_compare FStar_String.compare
        (FStar_Pervasives_Native.snd v1) (FStar_Pervasives_Native.snd v2)
let get_pair_fst :
  'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) Prims.list -> 'uuuuu Prims.list =
  fun l -> FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l
let get_pair_snd :
  'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) Prims.list -> 'uuuuu1 Prims.list =
  fun l -> FStar_List_Tot_Base.map FStar_Pervasives_Native.snd l
let sort_triple_fst :
  'a 'b . (Prims.string * 'a * 'b) -> (Prims.string * 'a * 'b) -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      FStar_List_Tot_Base.bool_of_compare FStar_String.compare
        (FStar_Pervasives_Native.__proj__Mktuple3__item___1 v1)
        (FStar_Pervasives_Native.__proj__Mktuple3__item___1 v2)
let get_triple_fst : 'a 'b 'c . ('a * 'b * 'c) Prims.list -> 'a Prims.list =
  fun l ->
    FStar_List_Tot_Base.map
      (fun e -> FStar_Pervasives_Native.__proj__Mktuple3__item___1 e) l
let get_triple_snd : 'a 'b 'c . ('a * 'b * 'c) Prims.list -> 'b Prims.list =
  fun l ->
    FStar_List_Tot_Base.map
      (fun e -> FStar_Pervasives_Native.__proj__Mktuple3__item___2 e) l
let get_triple_thd : 'a 'b 'c . ('a * 'b * 'c) Prims.list -> 'c Prims.list =
  fun l ->
    FStar_List_Tot_Base.map
      (fun e -> FStar_Pervasives_Native.__proj__Mktuple3__item___3 e) l
type pty =
  | P_DOUBLE of pdec 
  | P_FLOAT of pdec 
  | P_INT of width * pdec 
  | P_UINT of width * pdec 
  | P_SINT of width * pdec 
  | P_FIXED of width * pdec 
  | P_SFIXED of width * pdec 
  | P_BOOL of pdec 
  | P_STRING of pdec 
  | P_BYTES of pdec 
  | P_MSG of md * pdec 
  | P_ENUM of pdec 
and md =
  {
  reserved: Prims.nat FStar_Set.set ;
  fields: (Prims.string * Prims.nat * pty) Prims.list }
let (uu___is_P_DOUBLE : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_DOUBLE p -> true | uu___ -> false
let (__proj__P_DOUBLE__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_DOUBLE p -> p
let (uu___is_P_FLOAT : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_FLOAT p -> true | uu___ -> false
let (__proj__P_FLOAT__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_FLOAT p -> p
let (uu___is_P_INT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_INT (w, p) -> true | uu___ -> false
let (__proj__P_INT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_INT (w, p) -> w
let (__proj__P_INT__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_INT (w, p) -> p
let (uu___is_P_UINT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_UINT (w, p) -> true | uu___ -> false
let (__proj__P_UINT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_UINT (w, p) -> w
let (__proj__P_UINT__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_UINT (w, p) -> p
let (uu___is_P_SINT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_SINT (w, p) -> true | uu___ -> false
let (__proj__P_SINT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_SINT (w, p) -> w
let (__proj__P_SINT__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_SINT (w, p) -> p
let (uu___is_P_FIXED : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_FIXED (w, p) -> true | uu___ -> false
let (__proj__P_FIXED__item__w : pty -> width) =
  fun projectee -> match projectee with | P_FIXED (w, p) -> w
let (__proj__P_FIXED__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_FIXED (w, p) -> p
let (uu___is_P_SFIXED : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_SFIXED (w, p) -> true | uu___ -> false
let (__proj__P_SFIXED__item__w : pty -> width) =
  fun projectee -> match projectee with | P_SFIXED (w, p) -> w
let (__proj__P_SFIXED__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_SFIXED (w, p) -> p
let (uu___is_P_BOOL : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_BOOL p -> true | uu___ -> false
let (__proj__P_BOOL__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_BOOL p -> p
let (uu___is_P_STRING : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_STRING p -> true | uu___ -> false
let (__proj__P_STRING__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_STRING p -> p
let (uu___is_P_BYTES : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_BYTES p -> true | uu___ -> false
let (__proj__P_BYTES__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_BYTES p -> p
let (uu___is_P_MSG : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_MSG (m, p) -> true | uu___ -> false
let (__proj__P_MSG__item__m : pty -> md) =
  fun projectee -> match projectee with | P_MSG (m, p) -> m
let (__proj__P_MSG__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_MSG (m, p) -> p
let (uu___is_P_ENUM : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_ENUM p -> true | uu___ -> false
let (__proj__P_ENUM__item__p : pty -> pdec) =
  fun projectee -> match projectee with | P_ENUM p -> p
let (__proj__Mkmd__item__reserved : md -> Prims.nat FStar_Set.set) =
  fun projectee -> match projectee with | { reserved; fields;_} -> reserved
let (__proj__Mkmd__item__fields :
  md -> (Prims.string * Prims.nat * pty) Prims.list) =
  fun projectee -> match projectee with | { reserved; fields;_} -> fields
type fd = (Prims.string * Prims.nat * pty)
type fields = (Prims.string * Prims.nat * pty) Prims.list
type 'v dvty =
  | VIMPLICIT of 'v 
  | VOPTIONAL of 'v FStar_Pervasives_Native.option 
  | VREPEATED of 'v Prims.list 
let uu___is_VIMPLICIT : 'v . 'v dvty -> Prims.bool =
  fun projectee ->
    match projectee with | VIMPLICIT _0 -> true | uu___ -> false
let __proj__VIMPLICIT__item___0 : 'v . 'v dvty -> 'v =
  fun projectee -> match projectee with | VIMPLICIT _0 -> _0
let uu___is_VOPTIONAL : 'v . 'v dvty -> Prims.bool =
  fun projectee ->
    match projectee with | VOPTIONAL _0 -> true | uu___ -> false
let __proj__VOPTIONAL__item___0 :
  'v . 'v dvty -> 'v FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | VOPTIONAL _0 -> _0
let uu___is_VREPEATED : 'v . 'v dvty -> Prims.bool =
  fun projectee ->
    match projectee with | VREPEATED _0 -> true | uu___ -> false
let __proj__VREPEATED__item___0 : 'v . 'v dvty -> 'v Prims.list =
  fun projectee -> match projectee with | VREPEATED _0 -> _0
type vty =
  | VDOUBLE of double dvty 
  | VFLOAT of float dvty 
  | VINT of Prims.int dvty 
  | VBOOL of Prims.bool dvty 
  | VSTRING of Prims.string dvty 
  | VBYTES of Pollux_Proto_Prelude.bytes dvty 
  | VMSG of (Prims.string * vty) Prims.list dvty 
  | VENUM of unit dvty 
let (uu___is_VDOUBLE : vty -> Prims.bool) =
  fun projectee -> match projectee with | VDOUBLE v -> true | uu___ -> false
let (__proj__VDOUBLE__item__v : vty -> double dvty) =
  fun projectee -> match projectee with | VDOUBLE v -> v
let (uu___is_VFLOAT : vty -> Prims.bool) =
  fun projectee -> match projectee with | VFLOAT v -> true | uu___ -> false
let (__proj__VFLOAT__item__v : vty -> float dvty) =
  fun projectee -> match projectee with | VFLOAT v -> v
let (uu___is_VINT : vty -> Prims.bool) =
  fun projectee -> match projectee with | VINT v -> true | uu___ -> false
let (__proj__VINT__item__v : vty -> Prims.int dvty) =
  fun projectee -> match projectee with | VINT v -> v
let (uu___is_VBOOL : vty -> Prims.bool) =
  fun projectee -> match projectee with | VBOOL v -> true | uu___ -> false
let (__proj__VBOOL__item__v : vty -> Prims.bool dvty) =
  fun projectee -> match projectee with | VBOOL v -> v
let (uu___is_VSTRING : vty -> Prims.bool) =
  fun projectee -> match projectee with | VSTRING v -> true | uu___ -> false
let (__proj__VSTRING__item__v : vty -> Prims.string dvty) =
  fun projectee -> match projectee with | VSTRING v -> v
let (uu___is_VBYTES : vty -> Prims.bool) =
  fun projectee -> match projectee with | VBYTES v -> true | uu___ -> false
let (__proj__VBYTES__item__v : vty -> Pollux_Proto_Prelude.bytes dvty) =
  fun projectee -> match projectee with | VBYTES v -> v
let (uu___is_VMSG : vty -> Prims.bool) =
  fun projectee -> match projectee with | VMSG v -> true | uu___ -> false
let (__proj__VMSG__item__v : vty -> (Prims.string * vty) Prims.list dvty) =
  fun projectee -> match projectee with | VMSG v -> v
let (uu___is_VENUM : vty -> Prims.bool) =
  fun projectee -> match projectee with | VENUM v -> true | uu___ -> false
let (__proj__VENUM__item__v : vty -> unit dvty) =
  fun projectee -> match projectee with | VENUM v -> v
type vf = (Prims.string * vty)
type msg = (Prims.string * vty) Prims.list
let (empty_msg : msg) = []
let init_dec : 'a . pdec -> 'a -> 'a dvty =
  fun dec ->
    fun def ->
      match dec with
      | P_IMPLICIT -> VIMPLICIT def
      | P_OPTIONAL -> VOPTIONAL FStar_Pervasives_Native.None
      | P_REPEATED -> VREPEATED []
let rec (init_field : fd -> vf) =
  fun f ->
    ((FStar_Pervasives_Native.__proj__Mktuple3__item___1 f),
      (match FStar_Pervasives_Native.__proj__Mktuple3__item___3 f with
       | P_DOUBLE pd -> VDOUBLE (init_dec pd double_z)
       | P_FLOAT pd -> VFLOAT (init_dec pd float_z)
       | P_INT (uu___, pd) -> VINT (init_dec pd Prims.int_zero)
       | P_UINT (uu___, pd) -> VINT (init_dec pd Prims.int_zero)
       | P_SINT (uu___, pd) -> VINT (init_dec pd Prims.int_zero)
       | P_FIXED (uu___, pd) -> VINT (init_dec pd Prims.int_zero)
       | P_SFIXED (uu___, pd) -> VINT (init_dec pd Prims.int_zero)
       | P_BOOL pd -> VBOOL (init_dec pd false)
       | P_STRING pd -> VSTRING (init_dec pd "")
       | P_BYTES pd -> VBYTES (init_dec pd [])
       | P_MSG (md1, pd) -> VMSG (init_dec pd (init_msg md1))
       | P_ENUM pd -> VENUM (init_dec pd ())))
and (init_fields : fields -> msg) =
  fun fs ->
    match fs with
    | [] -> []
    | hd::tl ->
        let new_field = init_field hd in
        let rest_fields = init_fields tl in
        let fields1 = new_field :: rest_fields in fields1
and (init_msg : md -> msg) = fun m -> init_fields m.fields
