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
  
End Varint.
