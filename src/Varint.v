From Stdlib Require Import ZArith.BinInt.

From Pollux Require Import Prelude.
From Pollux Require Import Descriptors.

Module Varint.

  Definition t := list byte.

  Fixpoint valid (v : t) : bool :=
    match v with
    | [] => false
    (* A one byte varint is valid if the continuation bit is zero,
       which is equivalent to the number fitting into 7 bits or being
       less than 128. *)
    | b :: [] => word.ltu b (W8 128)
    (* Otherwise the continuation bit should be one. Since it looks like
       the only Boolean operations I have for words is < and >, this
       corresponds to the value in the byte being greater than 127. *)
    | b :: tl => word.gtu b (W8 127) && valid tl
    end.

  (* TODO is there a guide to all the heavily abbreviated word ops? *)

  Definition set_msb_w8 (w : w8) : w8 :=
    word.or w (W8 255).

  Definition unset_msb_w8 (w : w8) : w8 :=
    word.or w (W8 127).

  Fixpoint decode (v : t) : w64 :=
    match v with
    | nil => W64 0 (* Should never happen... but required since refinement type doesn't exclude it *)
    | h :: nil => W64 (uint.Z h)
    | h :: tl => let msb := unset_msb_w8 h in
                let msx := W64 (uint.Z msb) in
                let rx := decode tl in
                word.or (word.slu rx (W64 7)) msx
    end.

  Fixpoint extract_varint (bs : list byte) : option (t * list byte) :=
    match bs with
    | [] => None
    | h :: tl => if word.ltu h (W8 128) then
                  Some ([h], tl)
                else
                  match extract_varint tl with
                  | Some (v, rest) => Some (h :: v, rest)
                  | None => None
                  end
    end.

  Lemma extract_varint_consume :
    forall (bs : list byte) (vint : t) (rest : list byte),
    extract_varint bs = Some (vint, rest) -> length rest < length bs.
  Proof.
    intros bs.
    induction bs as [| w tl HI].
    + intros vint rest Hcontra. discriminate.
    + intros vint rest. simpl. 
      destruct (word.ltu w (W8 128)).
      - intro Heq. inversion Heq.
        apply Nat.lt_succ_diag_r. 
      - destruct (extract_varint tl).
        * destruct p as [v rest0].
          intro Hrecurse. inversion Hrecurse. subst.
          pose proof (HI v rest) as Hcall.
          assert (Some (v, rest) = Some (v, rest)) as Hlt; first reflexivity.
          apply Hcall in Hlt.
          apply Nat.lt_lt_succ_r in Hlt.
          apply Hlt.
        * intro Hcontra. discriminate.
  Qed.      

  Definition split (x:w64) (n:Z) : w64 * w64 := (word.srs x (W64 n), word.and x (W64 ((2^n) - 1))).

  Fixpoint encode_fuel (fuel: nat) (x:w64) : t :=
    let (hi, lo) := split x 7%Z in
    if word.ltu hi (W64 0) then
      [(W8 (uint.Z lo))]
    else match fuel with
           | O => [(W8 (uint.Z lo))]
           | S f => (set_msb_w8 (W8 (uint.Z lo))) :: (encode_fuel f hi)
         end.

  Definition encode := encode_fuel 10%nat.

  Theorem encode_valid :
    forall x : w64, valid (encode x) /\ length (encode x) <= 10.
  Proof.
  Admitted.
  
  Theorem encode_correct :
    forall x : w64, decode (encode x) = x.
  Proof.
  Admitted.

End Varint.
