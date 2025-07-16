open Prims
type bytes = FStar_UInt8.t Prims.list
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
