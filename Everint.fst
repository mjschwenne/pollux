module Everint 
open FStar.Ghost
open FStar.UInt
open FStar.UInt8
open FStar.UInt16
open FStar.UInt32
open FStar.UInt64
open FStar.Int.Cast.Full
open FStar.Seq
open FStar.List.Tot
open FStar.Mul
open FStar.Tactics.V2

module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast.Full
module Seq = FStar.Seq
module List = FStar.List.Tot

(* 
  Like Varint.fist, this module seeks to develop a parser for a protobuf variable length integer. 

  However, this is more directly based off the ASN1* U32 identifier file, which is more principled 
  and actually acknowledges that its a proof assistant and not just a programming language with 
  complicated assertions.

  I've tweaked the formulas for lower and upper bounds so that indexing starts at 1 and for the 
  lower bound to allow varints to encode zero, which ASN1 identifiers can't do apparently.
*)

let byte = U8.t 

(* 
  Returns the minimum value which requires exactly n bytes to encode.

  TODO we'll see if this is the correct approach for a malleable encoding.
*)
let varint_lowerbound (n : pos) = 
  if n = 1 then 
    (0)
  else
    pow2 ((n - 1) * 7)

let vlb_one = varint_lowerbound 1                          (* 0 *)
let vlb_two = varint_lowerbound 2                        (* 128 *)
let vlb_three = varint_lowerbound 3                    (* 16384 *)
let vlb_four = varint_lowerbound 4                   (* 2097152 *) 
let vlb_five = varint_lowerbound 5                 (* 268435456 *)
let vlb_six = varint_lowerbound 6                (* 34359738368 *)
let vlb_seven = varint_lowerbound 7            (* 4398046511104 *)
let vlb_eight = varint_lowerbound 8          (* 562949953421312 *)
let vlb_nine = varint_lowerbound 9         (* 72057594037927936 *)
let vlb_ten = varint_lowerbound 10       (* 9223372036854775808 *)
let u64_max = U.max_int 64              (* 18446844073709551616 *)
let vlb_eleven = varint_lowerbound 11 (* 1180591620717411303424 *)

(* varint_lowerbound is monotonic *)
let lemma_varint_lowerbound_mono (n m : pos) : Lemma 
  (requires m <= n)
  (ensures varint_lowerbound m <= varint_lowerbound n) = 
    Math.Lemmas.pow2_le_compat (n * 7) (m * 7); ()

(* Returns one more than the maximum value which can be encoded into n bytes. *)
let varint_upperbound (n : pos) = 
  pow2 (n * 7) - 1

let vub_one = varint_upperbound 1                      (* 127 *)
let vub_two = varint_upperbound 2                    (* 16383 *)
let vub_three = varint_upperbound 3                (* 2097151 *)
let vub_four = varint_upperbound 4               (* 268435455 *) 
let vub_five = varint_upperbound 5             (* 34359738367 *)
let vub_six = varint_upperbound 6            (* 4398046511103 *)
let vub_seven = varint_upperbound 7        (* 562949953421311 *)
let vub_eight = varint_upperbound 8      (* 72057594037927935 *)
let vub_nine = varint_upperbound 9     (* 9223372036854775807 *)
let vub_ten = varint_upperbound 10  (* 1180591620717411303423 *)

(* 
  Two varints of different lengths encode different values. 

  Note that we're using the raw integer values here, so we're interesting in 
  if we /can/ encode v into n bytes, not that we will or always have to encode 
  into n bytes, while v' /has/ to be encoded into at least n+1 bytes. 
*)
let varint_bound_separation (n : pos) (v : U64.t) (v' : U64.t) : Lemma 
  (requires (
    U64.v v <= varint_upperbound n /\
    varint_lowerbound (n + 1) <= U64.v v'
  ))
  (ensures (U64.v v < U64.v v')) = 
  ()

(* Checks if a value can be minimally encoded into n bytes *)
let varint_in_bound (n : pos) (v : nat) = 
  varint_lowerbound n <= v /\ v <= varint_upperbound n

let varint_bound_u64 (u : U64.t) : Pure pos
  (requires True)
  (ensures (fun n -> n <= 10 /\ varint_in_bound n (U64.v u))) = 
  let v = U64.v u in 
  if v <= varint_upperbound 1 then 
    (1)
  else 
    (if v <= varint_upperbound 2 then 
       (2)
     else 
       (if v <= varint_upperbound 3 then 
          (3)
        else
          (if v <= varint_upperbound 4 then
             (4)
           else 
             (if v <= varint_upperbound 5 then 
                (5)
              else 
                (if v <= varint_upperbound 6 then
                   (6)
                 else
                   (if v <= varint_upperbound 7 then
                      (7)
                    else
                      (if v <= varint_upperbound 8 then 
                         (8)
                       else 
                         (if v <= varint_upperbound 9 then 
                            (9)
                          else 
                             (assert v <= varint_upperbound 10; 10)))))))))

#push-options "--z3rlimit 128 --fuel 0 --ifuel 0"

(*
  To be honest, I'm not exactly sure what this is useful for. We already require that 
  varint_in_bound is true, and that's for a big part of the post condition when you unwrap 
  varint_bound_u64. I suppose we learn that n <= 10, which is helpful in it's own right.
*)
let lemma_varint_bound_intro (u : U64.t) (n : pos) : 
  Lemma (requires (varint_in_bound n (U64.v u)))
        (ensures (varint_bound_u64 u = n)) =
  let v = U64.v u in 
  let _ = 
    Math.Lemmas.pow2_lt_compat 7 0;
    Math.Lemmas.pow2_lt_compat 14 7;
    Math.Lemmas.pow2_lt_compat 21 14;
    Math.Lemmas.pow2_lt_compat 28 21;
    Math.Lemmas.pow2_lt_compat 35 28;
    Math.Lemmas.pow2_lt_compat 42 35;
    Math.Lemmas.pow2_lt_compat 49 42;
    Math.Lemmas.pow2_lt_compat 56 49;
    Math.Lemmas.pow2_lt_compat 63 56;
    Math.Lemmas.pow2_lt_compat 70 63
  in
  match n with 
  | 1 -> _
  | 2 -> _
  | 3 -> _
  | 4 -> _
  | 5 -> _
  | 6 -> _
  | 7 -> _
  | 8 -> _
  | 9 -> _
  | 10 -> _
  | _ -> Math.Lemmas.pow2_le_compat ((n - 1) * 7) 70;
        assert (pow2 70 <= v)


// Local Variables:
// jinx-local-words: "lowerbound varint"
// End:
