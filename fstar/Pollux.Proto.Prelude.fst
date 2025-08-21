module Pollux.Proto.Prelude 

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

type bytes = list U8.t
let empty_bytes : bytes = []
type dbytes (b:bytes) = d:bytes{length d < length b}
type debytes (b:bytes) = d:bytes{length d <= length b}

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
