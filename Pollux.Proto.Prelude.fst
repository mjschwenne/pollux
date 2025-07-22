module Pollux.Proto.Prelude 

module U8 = FStar.UInt8

type bytes = list U8.t
type dbytes (b:bytes) = d:bytes{FStar.List.length d < FStar.List.length b}
type debytes (b:bytes) = d:bytes{FStar.List.length d <= FStar.List.length b}

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
