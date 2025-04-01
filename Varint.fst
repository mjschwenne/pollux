module Varint
open FStar.UInt
open FStar.UInt64
open FStar.UInt8
open FStar.List.Tot

let uint8_to_64 (u:UInt8.t) : UInt64.t = UInt64.uint_to_t (UInt8.v u)

let rec encodes (v:list UInt8.t) (n:UInt64.t) : bool = 
  match v with 
  | [] -> false
  | msb :: [] -> UInt8.v msb = UInt64.v n
  | msb :: rest -> let continuation = ((msb &^ 0b10000000uy) = 128uy) in 
                 let n_rest : UInt64.t = UInt64.sub (UInt64.sub n 127uL) (uint8_to_64 (msb |^ 0b01111111uy)) in
                 continuation && encodes rest n_rest

let varint = v:list UInt8.t{length v >= 1 /\ length v <= 10 /\ exists (n:UInt64.t). encodes v n}
