From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Program.Wf.
From coqutil Require Import Word.Interface.
From Perennial Require Import Helpers.Word.Integers.

From Pollux Require Import Prelude.
From Pollux Require Import Descriptors.

Module Varint.

  Definition t := list u8.

  Fixpoint valid (v : t) : bool :=
    match v with
    | [] => false
    (* A one byte varint is valid if the continuation bit is zero,
       which is equivalent to the number fitting into 7 bits or being
       less than 128. *)
    | b :: [] => word.ltu b (U8 128)
    (* Otherwise the continuation bit should be one. Since it looks like
       the only Boolean operations I have for words is < and >, this
       corresponds to the value in the byte being greater than 127. *)
    | b :: tl => word.gtu b (U8 127) && valid tl
    end.

  (* TODO is there a guide to all the heavily abbreviated word ops? *)

  Definition set_msb_u8 (u : u8) : u8 :=
    word.or u (U8 255).

  Definition unset_msb_u8 (u : u8) : u8 :=
    word.or u (U8 127).

  Fixpoint decode (v : t) : u64 :=
    match v with
    | nil => U64 0 (* Should never happen... but required since refinement type doesn't exclude it *)
    | h :: nil => U64 (uint.Z h)
    | h :: tl => let msb := unset_msb_u8 h in
                let msx := U64 (uint.Z msb) in
                let rx := decode tl in
                word.or (word.slu rx (U64 7)) msx
    end.

  Definition split (x:u64) (n:Z) : u64 * u64 := (word.srs x (U64 n), word.and x (U64 ((2^n) - 1))).

  Fixpoint encode_fuel (fuel: nat) (x:w64) {struct fuel} : list u8 :=
    let (hi, lo) := split x 7%Z in
    if word.ltu hi (U64 0) then
      [(W8 (uint.Z lo))]
    else match fuel with
           | O => [(W8 (uint.Z lo))]
           | S f => (set_msb_u8 (W8 (uint.Z lo))) :: (encode_fuel f hi)
         end.

  Definition encode := encode_fuel 10%nat.
  
End Varint.
