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
  | P_MSG of pdec 
  | P_ENUM of pdec 
let (uu___is_P_DOUBLE : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_DOUBLE _0 -> true | uu___ -> false
let (__proj__P_DOUBLE__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_DOUBLE _0 -> _0
let (uu___is_P_FLOAT : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_FLOAT _0 -> true | uu___ -> false
let (__proj__P_FLOAT__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_FLOAT _0 -> _0
let (uu___is_P_INT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_INT (w, _1) -> true | uu___ -> false
let (__proj__P_INT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_INT (w, _1) -> w
let (__proj__P_INT__item___1 : pty -> pdec) =
  fun projectee -> match projectee with | P_INT (w, _1) -> _1
let (uu___is_P_UINT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_UINT (w, _1) -> true | uu___ -> false
let (__proj__P_UINT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_UINT (w, _1) -> w
let (__proj__P_UINT__item___1 : pty -> pdec) =
  fun projectee -> match projectee with | P_UINT (w, _1) -> _1
let (uu___is_P_SINT : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_SINT (w, _1) -> true | uu___ -> false
let (__proj__P_SINT__item__w : pty -> width) =
  fun projectee -> match projectee with | P_SINT (w, _1) -> w
let (__proj__P_SINT__item___1 : pty -> pdec) =
  fun projectee -> match projectee with | P_SINT (w, _1) -> _1
let (uu___is_P_FIXED : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_FIXED (w, _1) -> true | uu___ -> false
let (__proj__P_FIXED__item__w : pty -> width) =
  fun projectee -> match projectee with | P_FIXED (w, _1) -> w
let (__proj__P_FIXED__item___1 : pty -> pdec) =
  fun projectee -> match projectee with | P_FIXED (w, _1) -> _1
let (uu___is_P_SFIXED : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_SFIXED (w, _1) -> true | uu___ -> false
let (__proj__P_SFIXED__item__w : pty -> width) =
  fun projectee -> match projectee with | P_SFIXED (w, _1) -> w
let (__proj__P_SFIXED__item___1 : pty -> pdec) =
  fun projectee -> match projectee with | P_SFIXED (w, _1) -> _1
let (uu___is_P_BOOL : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_BOOL _0 -> true | uu___ -> false
let (__proj__P_BOOL__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_BOOL _0 -> _0
let (uu___is_P_STRING : pty -> Prims.bool) =
  fun projectee ->
    match projectee with | P_STRING _0 -> true | uu___ -> false
let (__proj__P_STRING__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_STRING _0 -> _0
let (uu___is_P_BYTES : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_BYTES _0 -> true | uu___ -> false
let (__proj__P_BYTES__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_BYTES _0 -> _0
let (uu___is_P_MSG : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_MSG _0 -> true | uu___ -> false
let (__proj__P_MSG__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_MSG _0 -> _0
let (uu___is_P_ENUM : pty -> Prims.bool) =
  fun projectee -> match projectee with | P_ENUM _0 -> true | uu___ -> false
let (__proj__P_ENUM__item___0 : pty -> pdec) =
  fun projectee -> match projectee with | P_ENUM _0 -> _0
type fd = (Prims.string * Prims.nat * pty)
type md =
  {
  name: Prims.string ;
  reserved: Prims.nat FStar_Set.set ;
  fields: fd Prims.list }
let (__proj__Mkmd__item__name : md -> Prims.string) =
  fun projectee -> match projectee with | { name; reserved; fields;_} -> name
let (__proj__Mkmd__item__reserved : md -> Prims.nat FStar_Set.set) =
  fun projectee ->
    match projectee with | { name; reserved; fields;_} -> reserved
let (__proj__Mkmd__item__fields : md -> fd Prims.list) =
  fun projectee ->
    match projectee with | { name; reserved; fields;_} -> fields
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
  | VINT32 of FStar_Int32.t dvty 
  | VINT64 of FStar_Int64.t dvty 
  | VUINT32 of FStar_UInt32.t dvty 
  | VUINT64 of FStar_UInt64.t dvty 
  | VSINT32 of FStar_Int32.t dvty 
  | VSINT64 of FStar_Int64.t dvty 
  | VFIXED32 of FStar_UInt32.t dvty 
  | VFIXED64 of FStar_UInt64.t dvty 
  | VSFIXED32 of FStar_Int32.t dvty 
  | VSFIXED64 of FStar_Int64.t dvty 
  | VBOOL of Prims.bool dvty 
  | VSTRING of Prims.string dvty 
  | VBYTES of FStar_UInt8.t Prims.list dvty 
  | VMSG of unit dvty 
  | VENUM of unit dvty 
let (uu___is_VDOUBLE : vty -> Prims.bool) =
  fun projectee -> match projectee with | VDOUBLE _0 -> true | uu___ -> false
let (__proj__VDOUBLE__item___0 : vty -> double dvty) =
  fun projectee -> match projectee with | VDOUBLE _0 -> _0
let (uu___is_VFLOAT : vty -> Prims.bool) =
  fun projectee -> match projectee with | VFLOAT _0 -> true | uu___ -> false
let (__proj__VFLOAT__item___0 : vty -> float dvty) =
  fun projectee -> match projectee with | VFLOAT _0 -> _0
let (uu___is_VINT32 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VINT32 _0 -> true | uu___ -> false
let (__proj__VINT32__item___0 : vty -> FStar_Int32.t dvty) =
  fun projectee -> match projectee with | VINT32 _0 -> _0
let (uu___is_VINT64 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VINT64 _0 -> true | uu___ -> false
let (__proj__VINT64__item___0 : vty -> FStar_Int64.t dvty) =
  fun projectee -> match projectee with | VINT64 _0 -> _0
let (uu___is_VUINT32 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VUINT32 _0 -> true | uu___ -> false
let (__proj__VUINT32__item___0 : vty -> FStar_UInt32.t dvty) =
  fun projectee -> match projectee with | VUINT32 _0 -> _0
let (uu___is_VUINT64 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VUINT64 _0 -> true | uu___ -> false
let (__proj__VUINT64__item___0 : vty -> FStar_UInt64.t dvty) =
  fun projectee -> match projectee with | VUINT64 _0 -> _0
let (uu___is_VSINT32 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VSINT32 _0 -> true | uu___ -> false
let (__proj__VSINT32__item___0 : vty -> FStar_Int32.t dvty) =
  fun projectee -> match projectee with | VSINT32 _0 -> _0
let (uu___is_VSINT64 : vty -> Prims.bool) =
  fun projectee -> match projectee with | VSINT64 _0 -> true | uu___ -> false
let (__proj__VSINT64__item___0 : vty -> FStar_Int64.t dvty) =
  fun projectee -> match projectee with | VSINT64 _0 -> _0
let (uu___is_VFIXED32 : vty -> Prims.bool) =
  fun projectee ->
    match projectee with | VFIXED32 _0 -> true | uu___ -> false
let (__proj__VFIXED32__item___0 : vty -> FStar_UInt32.t dvty) =
  fun projectee -> match projectee with | VFIXED32 _0 -> _0
let (uu___is_VFIXED64 : vty -> Prims.bool) =
  fun projectee ->
    match projectee with | VFIXED64 _0 -> true | uu___ -> false
let (__proj__VFIXED64__item___0 : vty -> FStar_UInt64.t dvty) =
  fun projectee -> match projectee with | VFIXED64 _0 -> _0
let (uu___is_VSFIXED32 : vty -> Prims.bool) =
  fun projectee ->
    match projectee with | VSFIXED32 _0 -> true | uu___ -> false
let (__proj__VSFIXED32__item___0 : vty -> FStar_Int32.t dvty) =
  fun projectee -> match projectee with | VSFIXED32 _0 -> _0
let (uu___is_VSFIXED64 : vty -> Prims.bool) =
  fun projectee ->
    match projectee with | VSFIXED64 _0 -> true | uu___ -> false
let (__proj__VSFIXED64__item___0 : vty -> FStar_Int64.t dvty) =
  fun projectee -> match projectee with | VSFIXED64 _0 -> _0
let (uu___is_VBOOL : vty -> Prims.bool) =
  fun projectee -> match projectee with | VBOOL _0 -> true | uu___ -> false
let (__proj__VBOOL__item___0 : vty -> Prims.bool dvty) =
  fun projectee -> match projectee with | VBOOL _0 -> _0
let (uu___is_VSTRING : vty -> Prims.bool) =
  fun projectee -> match projectee with | VSTRING _0 -> true | uu___ -> false
let (__proj__VSTRING__item___0 : vty -> Prims.string dvty) =
  fun projectee -> match projectee with | VSTRING _0 -> _0
let (uu___is_VBYTES : vty -> Prims.bool) =
  fun projectee -> match projectee with | VBYTES _0 -> true | uu___ -> false
let (__proj__VBYTES__item___0 : vty -> FStar_UInt8.t Prims.list dvty) =
  fun projectee -> match projectee with | VBYTES _0 -> _0
let (uu___is_VMSG : vty -> Prims.bool) =
  fun projectee -> match projectee with | VMSG _0 -> true | uu___ -> false
let (__proj__VMSG__item___0 : vty -> unit dvty) =
  fun projectee -> match projectee with | VMSG _0 -> _0
let (uu___is_VENUM : vty -> Prims.bool) =
  fun projectee -> match projectee with | VENUM _0 -> true | uu___ -> false
let (__proj__VENUM__item___0 : vty -> unit dvty) =
  fun projectee -> match projectee with | VENUM _0 -> _0
type vf = (Prims.string * vty)
let (sort_vf : vf -> vf -> Prims.bool) =
  fun v1 ->
    fun v2 ->
      (FStar_String.compare
         (FStar_Pervasives_Native.__proj__Mktuple2__item___1 v1)
         (FStar_Pervasives_Native.__proj__Mktuple2__item___1 v2))
        <= Prims.int_zero
type msg = vf Prims.list
let (empty_msg : msg) = []
let (msg_field_names : msg -> Prims.string Prims.list) =
  fun m ->
    FStar_List_Tot_Base.map
      (fun f -> FStar_Pervasives_Native.__proj__Mktuple2__item___1 f) m
