From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Stdlib Require Import Structures.Equalities.

From Stdlib Require Import Program.Wf.
From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.
From Flocq Require Import Core.Raux.
From Equations Require Import Equations.

Module Parse.

  Include Descriptors.
  Notation "x %% y" := (Z.modulo x y) (at level 35) : Z_scope.
  Notation "x == y" := (decide (eq x y)) (no associativity, at level 70).

  Definition parity (z : Z) : Z :=
    if ((z %% 2) == 0%Z) then 1 else (-1).

  Definition idn__p {P} (c : {P} + {¬ P}) : Z := if c then 1 else 0.
  Definition idn__b (c : bool) : Z := if c then 1 else 0.

  Definition uint_change_w (w : Width) (v : Z) : Z := v %% (2^(unwrap_width w)).
  Definition int_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                     (v %% pow2__w - pow2__w * idn__p (( v / pow2__w) %% 2 == 1%Z)).
  Definition sint_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                      (v %% pow2__w - pow2__w * idn__b (Z.ltb v 0)).
  Definition uint_int (w : Width) (v : Z) : Z := v - (2^(unwrap_width w)) *
                                                       (idn__b (Z.geb v (2^(unwrap_width w - 1))%Z)).
  Definition int_uint (w : Width) (v : Z) : Z := v + (2^(unwrap_width w)) * (idn__b (Z.ltb v 0)).
  Definition uint_sint (w : Width) (v : Z) : Z := parity v * (v / 2) - (v %% 2).
  Definition sint_uint (w : Width) (v : Z) : Z := 2 * (Z.abs v) - idn__b (Z.ltb v 0).
  Definition int_sint (w : Width) (v : Z) : Z := if Z.geb v 0 then
                                                   parity v * (v / 2) - (v %% 2)
                                                 else
                                                   parity v * (v + (2^(unwrap_width w - 1)) - (v / 2)).
  Definition sint_int (w : Width) (v : Z) : Z := if Z.leb (- 2^(unwrap_width w - 2)) v &&
                                                      Z.leb v (2^(unwrap_width w - 2)) then
                                                   2 * (Z.abs v) - idn__b (Z.ltb v 0)
                                                 else
                                                   2 * (Z.abs v) - (2^(unwrap_width w)) - idn__b (Z.ltb v 0).

    (* NOTE: Compared to the F* version, these functions no longer have type-level assurances
       that the resulting integer is in-bounds for the given width. Now, the F* functions only
       had this assurance, so the formula could still be wrong, which is why there were / are
       tested against the official protobuf implementation.
     *)

  Inductive Tag :=
  | VARINT
  | I64
  | LEN
  | I32.
  
  Definition tag_num (t:Tag) : Z :=
    match t with
    | VARINT => 0
    | I64 => 1
    | LEN => 2
    | I32 => 5
    end.
  
  Definition find_field_string (msg : MsgDesc) (id : string) : option FieldDesc :=
   find (fun f => String.eqb (field_desc_get_name f) id) (msg_desc_get_fields msg). 
  
  Definition find_tag (d : ValDesc) : Tag :=
    match d with
    | D_INT _ D_REPEATED
    | D_UINT _ D_REPEATED
    | D_SINT _ D_REPEATED
    | D_BOOL D_REPEATED
    | D_ENUM D_REPEATED
    | D_FIXED _ D_REPEATED
    | D_SFIXED _ D_REPEATED
    | D_FLOAT D_REPEATED
    | D_DOUBLE D_REPEATED => LEN
    | D_INT _ _
    | D_UINT _ _
    | D_SINT _ _
    | D_BOOL _
    | D_ENUM _ => VARINT
    | D_FIXED (exist _ 32%Z _) _
    | D_SFIXED (exist _ 32%Z _) _
    | D_FLOAT _ => I32
    | D_FIXED (exist _ 64%Z _) _
    | D_SFIXED (exist _ 64%Z _) _
    | D_DOUBLE _ => I64
    | _ => LEN
    end.

  Definition encode_header (msg : MsgDesc) (name : string) : option w64 :=
    (* TODO: Check tag number. Valid numbers are 1 to 536870911 excluding 19000 - 19999 *)
    match find_field_string msg name with
      | Some f => let id_n := W64 $ Z.of_nat (field_desc_get_id f) in
                 let tag_n := W64 (tag_num (find_tag (field_desc_get_val f))) in
                 Some (word.or (word.slu id_n (W64 3)) tag_n)
      | None => None
    end.

  (* Since W64 handles cases like negative numbers correctly, explicitly casting from signed
     to unsigned isn't needed. *)

  Definition encode_int (z : Z) : list byte := Varint.encode $ W64 z.
  Definition encode_sint32 (s : Z) : list byte := encode_int $ sint_uint width32 (uint.Z (W32 s)).
  Definition encode_sint64 (s : Z) : list byte := encode_int $ sint_uint width64 (uint.Z (W64 s)).

  Definition encode_fixed32 (f : Z) : list byte := u32_le $ W32 f.
  Definition encode_fixed64 (f : Z) : list byte := u64_le $ W64 f.
  Definition encode_bool (b : bool) : list byte := if b then [(W8 1)] else [(W8 0)].
  (* FIXME: Is the rev needed? This should shift us back to big-endian which I think (?)
     we need for encoding a float... *)
  Definition encode_float (f : f32) : list byte := rev (u32_le $ W32 (bits_of_b32 f)).
  Definition encode_double (f : f64) : list byte := rev (u64_le $ W64 (bits_of_b64 f)).
  Definition float_eqb (f1 : f32) (f2 : f32) : bool :=
    match b32_compare f1 f2 with
    | Some comp => match comp with
                  | Eq => true
                  | _ => false
                  end
    (* May not be the best choice, but the reflection proof need two NaNs to be equal... *)
    | None => true
    end.
  Definition double_eqb (f1 : f64) (f2 : f64) : bool :=
    match b64_compare f1 f2 with
    | Some comp => match comp with
                  | Eq => true
                  | _ => false
                  end
    | None => true
    end.

  Definition double_eqb' (f1 : f64) (f2 : f64) : bool :=
    match f1, f2 with
    | B754_zero _ _ s1, B754_zero _ _ s2 => eqb s1 s2
    | B754_infinity _ _ s1, B754_infinity _ _ s2 => eqb s1 s2
    | B754_nan _ _ s1 pl1 _, B754_nan _ _ s2 pl2 _ => andb (eqb s1 s2) (Pos.eqb pl1 pl2)
    | B754_finite _ _ s1 m1 e1 _, B754_finite _ _ s2 m2 e2 _ => andb (eqb s1 s2)
                                                                 (andb (Pos.eqb m1 m2) (Z.eqb e1 e2))
    | _, _ => false
    end.

  Lemma double_reflect' : forall x y, reflect (x = y) (double_eqb' x y).
  Proof.
    intros.
    apply iff_reflect.
    split.
    - intro. subst.
      destruct y eqn:Hy.
      + simpl. rewrite eqb_reflx. reflexivity.
      + simpl. rewrite eqb_reflx. reflexivity.
      + simpl. rewrite eqb_reflx. rewrite Pos.eqb_refl. done.
      + simpl. rewrite eqb_reflx. rewrite Pos.eqb_refl. rewrite Z.eqb_refl. done. 
    - destruct x, y; try (simpl; intro; discriminate).
      + simpl. intro. apply eqb_prop in H. congruence.
      + simpl. intro. apply eqb_prop in H. congruence.
      + simpl. intro. apply andb_prop in H. destruct H as [Hs Hpl].
        apply eqb_prop in Hs. apply Peqb_true_eq in Hpl. subst.
        assert (e = e0) as He. { admit. } congruence.
      + simpl. intro. apply andb_prop in H. destruct H as [Hs Hrest].
        apply andb_prop in Hrest. destruct Hrest as [Hm He].
        apply eqb_prop in Hs. apply Peqb_true_eq in Hm. apply Zeq_bool_eq in He.
        subst.
        assert (e0 = e2) as He'. { admit. } congruence.
  Admitted.

  Lemma float_reflect : forall x y, reflect (x = y) (float_eqb x y).
  Proof.
    intros.
    apply iff_reflect.
    split.
    - intro.
      unfold float_eqb.
      unfold b32_compare.
      destruct (Bcompare 24 128 x y) eqn:Hbcomp; last reflexivity.
      rewrite H in Hbcomp.
      destruct y eqn:Hy.
      + assert (is_finite 24 128 y = true) as Hfin. { rewrite Hy. reflexivity. }
        rewrite <- Hy in Hbcomp.
        apply (Bcompare_correct _ _ y y) in Hfin; last assumption.
        rewrite Hbcomp in Hfin. inversion Hfin as [Hcomp].
        destruct (Rcompare (B2R 24 128 y) (B2R 24 128 y)) eqn:Hrcomp; first reflexivity.
        * apply Rcompare_Lt_inv in Hrcomp. 
          pose proof (RIneq.Rlt_irrefl (B2R 24 128 y)) as Hcontra.
          contradiction.
        * apply Rcompare_Gt_inv in Hrcomp.
          pose proof (RIneq.Rlt_irrefl (B2R 24 128 y)) as Hcontra.
          contradiction.
      + vm_compute in Hbcomp. destruct s.
        * inversion Hbcomp. reflexivity.
        * inversion Hbcomp. reflexivity.
      + vm_compute in Hbcomp. discriminate.
      + assert (is_finite 24 128 y = true) as Hfin. { rewrite Hy. reflexivity. }
        rewrite <- Hy in Hbcomp.
        apply (Bcompare_correct _ _ y y) in Hfin; last assumption.
        rewrite Hbcomp in Hfin. inversion Hfin as [Hcomp].
        destruct (Rcompare (B2R 24 128 y) (B2R 24 128 y)) eqn:Hrcomp; first reflexivity.
        * apply Rcompare_Lt_inv in Hrcomp. 
          pose proof (RIneq.Rlt_irrefl (B2R 24 128 y)) as Hcontra.
          contradiction.
        * apply Rcompare_Gt_inv in Hrcomp.
          pose proof (RIneq.Rlt_irrefl (B2R 24 128 y)) as Hcontra.
          contradiction.
    - admit.
  Admitted.

  Definition float_dec (x y : f32) : {x = y} + {~(x = y)}.
    destruct (float_reflect x y) as [P|Q].
    + left. apply P.
    + right. apply Q.
  Defined.

  Instance float_decide : EqDecision f32 := float_dec.

  Lemma double_reflect : forall x y, reflect (x = y) (double_eqb x y).
  Proof.
    intros.
    apply iff_reflect.
    split.
    - admit.
    - unfold double_eqb. 
      destruct x, y.
      + simpl. intro H.
      (*
        So this just isn't going to work. The b64_compare function traces down to SFcompare in

        https://rocq-prover.org/doc/V9.0.0/corelib/Corelib.Floats.SpecFloat.html#SFcompare

        Consider the S754_zero case, which is "| S754_zero _, S754_zero _ => Some Eq" and notice
        that the boolean included in the constructor (positive or negative zero) is lost here, so
        double_eqb would actually return true for two 'different' floating point numbers, making the
        theorem I'm trying to prove false.
       *)
  Admitted.

  Definition double_dec (x y : f64) : {x = y} + {~(x = y)}.
    destruct (double_reflect x y) as [P|Q].
    + left. apply P.
    + right. apply Q.
  Defined.

  Instance double_decide : EqDecision f64 := double_dec.

  Definition len_prefix (b : list byte) : list byte :=
    let length := encode_int (Z.of_nat $ length b) in
    length ++ b.

  Definition len_prefix_opt (b : option (list byte)) : option (list byte) :=
    match b with
    | Some b => Some (len_prefix b)
    | None => None
    end.

  Definition prefix_opt (pfx : list byte) (b : option (list byte)) : option (list byte) :=
    match b with
    | Some b => Some (pfx ++ b)
    | None => None
    end.

  Definition opt_prefix_opt (pfx : option (list byte)) (b : option (list byte)) : option (list byte) :=
    match pfx, b with
    | Some pfx, Some b => Some (pfx ++ b)
    | Some pfx, None => Some pfx
    | None, Some b => Some b
    | None, None => None
    end.

  (* Add the length prefix, using a separate function for consistency *)
  Definition encode_bytes := len_prefix.
  Fixpoint bytes_eqb (b1 : list byte) (b2 : list byte) : bool :=
    match b1, b2 with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | (h1 :: t1), (h2 :: t2) => if (word.eqb h1 h2) then
                                 bytes_eqb t1 t2
                               else
                                 false
    end.

  Lemma bytes_reflect : forall x y, reflect (x = y) (bytes_eqb x y).
  Proof.
    intros.
    apply iff_reflect.
    split.
    - intros. subst.
      induction y.
      + reflexivity.
      + simpl. assert (a = a); first reflexivity.
        apply Properties.word.eqb_eq in H. rewrite H.
        apply IHy.
    - generalize dependent y.
      induction x.
      + intros. destruct y.
        * reflexivity.
        * discriminate.
      + intros y. simpl.
        destruct y.
        * discriminate.
        * destruct (word.eqb a w) eqn:Heq.
          ** apply Properties.word.eqb_true in Heq. subst.
             intro H. apply IHx in H. congruence.
          ** discriminate.
  Qed.

  Definition bytes_dec (x y : list byte) : {x = y} + {~(x = y)}.
    destruct (bytes_reflect x y) as [P|Q].
    + left. apply P.
    + right. apply Q.
  Defined.

  Instance bytes_decide : EqDecision (list byte) := bytes_dec.
  
  (* WARN looks like we may have lost native UTF-8 support,
     although this blog post seems to suggest otherwise:

     https://ju-sh.github.io/blog/coq-strings.html
   *)
  Definition encode_string (s : string) : list byte := len_prefix
                                                         (* This collection of casts is ugly... *)
                                                         (map (fun b => W8 (Z.of_nat $ Byte.to_nat b))
                                                            (list_byte_of_string s)).

  (* Higher order encoding functions *)
  Definition encode_implicit {A: Type} `{EqDecision A} (v : A) (d : A) (enc : A -> list byte) :
    option (list byte) := 
    if v == d then Some [] else Some (enc v).

  Definition encode_packed {A : Type} (l : list A) (enc_one : A -> list byte) : list byte :=
    len_prefix $ fold_left (++) (map enc_one l) [].

  Definition encode_unpacked {A : Type} (l : list A) (header : list byte) (enc_one : A -> list byte) :
    list byte :=
    fold_left (fun bytes next => bytes ++ header ++ next) (map enc_one l) [].

  Fixpoint encode_unpacked_opt {A : Type} (l : list A) (header : list byte)
    (enc_one : A -> option (list byte)) : option (list byte) :=
    match l with
    | [] => None
    | v :: tl => match encode_unpacked_opt tl header enc_one with
               | None => None
               | Some rest => match enc_one v with
                             | Some next => Some (header ++ next ++ rest)
                             | None => None
                             end
               end
    end.

  Definition encode_deco_packed {A : Type} `{EqDecision A} (deco : DecoVal A) (def : A)
    (enc_one : A -> list byte) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v => encode_implicit v def enc_one
    | V_OPTIONAL (Some v) => Some (header ++ enc_one v)
    | V_REPEATED (vh :: vt) => Some (header ++ encode_packed (vh :: vt) enc_one)
    | _ => Some []
    end.

  Definition encode_deco_unpacked {A : Type} `{EqDecision A} (deco : DecoVal A) (def : A)
    (enc_one : A -> list byte) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v
    | V_OPTIONAL (Some v) => if v == def then None else Some (enc_one v)
    | V_REPEATED (vh :: vt) => Some (encode_unpacked (vh :: vt) header enc_one)
    | _ => None
    end.

  Definition encode_deco_unpacked_opt {A : Type} `{EqDecision A} (deco : DecoVal A) (def : A)
    (enc_one : A -> option (list byte)) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v
    | V_OPTIONAL (Some v) => if v == def then None else enc_one v
    | V_REPEATED (vh :: vt) => encode_unpacked_opt (vh :: vt) header enc_one
    | _ => None
    end.

  Definition find_int_enc_one (m : MsgDesc) (name : string) : option (Z -> list byte) :=
    match find_field_string m name with
    | Some f => (match field_desc_get_val f with
                | D_INT _ _ => Some encode_int
                | D_UINT _ _ => Some encode_int
                | D_SINT (exist _ 32%Z _) _ => Some encode_sint32
                | D_SINT (exist _ 64%Z _) _ => Some encode_sint64
                | D_FIXED (exist _ 32%Z _) _
                | D_SFIXED (exist _ 32%Z _) _ => Some encode_fixed32
                | D_FIXED (exist _ 64%Z _) _
                | D_SFIXED (exist _ 64%Z _) _ => Some encode_fixed64
                | _ => None
                end)
    | None => None
    end.

  Definition opt_append {A : Type} (l1 : list A) (l2 : option (list A)) : list A :=
    match l2 with
    | None => l1
    | Some l2 => l1 ++ l2
    end.

  Definition opt_append_opt {A : Type} (l1 : option (list A)) (l2 : option (list A)) : option (list A) :=
    match l1, l2 with 
    | None, None => None
    | None, Some l => Some l
    | Some l, None => Some l
    | Some l1', Some l2' => Some (l1' ++ l2')
    end.

  Fixpoint find_nested_md_f (fs : list FieldDesc) (f : FieldVal) : option MsgDesc :=
    match fs with
    | [] => None
    | h :: t => if ((field_desc_get_name h) =? (field_val_get_name f))%string then
                 match field_desc_get_val h with
                 | D_MSG m _ => Some m
                 | _ => None
                 end
               else
                 find_nested_md_f t f
    end.

  Definition find_nested_msg_desc (m : MsgDesc) (f : FieldVal) : option MsgDesc :=
    find_nested_md_f (msg_desc_get_fields m) f.

  Equations field_desc_measure (f : FieldDesc) : nat :=
    field_desc_measure (D_FIELD _ _ (D_MSG (D_MESSAGE _ fs') _)) :=
      1 + fields_desc_measure fs';
    field_desc_measure (D_FIELD _ _ _) := 0;
  where fields_desc_measure (fs : list FieldDesc) : nat :=
    fields_desc_measure [] := 0;
    fields_desc_measure (f :: ftl) := field_desc_measure f + fields_desc_measure ftl.

  (* This measure counts the number of nested message descriptors in a message descriptor. *)
  Definition message_desc_measure (msg : MsgDesc) : nat := fields_desc_measure $ msg_desc_get_fields msg.

  (* This measure over-counts the number of values that need to be encoded in a field. *)
  Equations field_val_measure (f : FieldVal) : nat :=
    field_val_measure (V_FIELD _ (V_DOUBLE d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_FLOAT d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_INT d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_BOOL d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_STRING d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_BYTES d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_MSG d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      };
    field_val_measure (V_FIELD _ (V_ENUM d)) with d => {
      | V_REPEATED l => length l
      | _ => 1
      }.

  (* This measure over-counts the number of values to be encoded in a list of fields *)
  Fixpoint fields_val_measure (fs : list FieldVal) : nat :=
    match fs with
    | [] => 0
    | h :: tl => field_val_measure h + fields_val_measure tl
    end.

  (* This measure over-counts the number of values to be encoded in a list of messages *)
  Definition message_val_measure (msg : MsgVal) : nat := fields_val_measure $ msg_val_get_fields msg.

  (* I'm not sure that this is any better than the last one (well, it is a little bit, but it's still not great)
     Hopefully the equations plugin will provide some better reasoning principles though...
   *)
  Equations encode_field' (m : MsgDesc) (f : FieldVal) : option (list byte) := 
    encode_field' m (V_FIELD n (V_DOUBLE v)) with encode_header m n => {
      | Some header => encode_deco_packed v f64_zero encode_double (Varint.encode header)
      | None => None 
      };
    encode_field' m (V_FIELD n (V_FLOAT v)) with encode_header m n => {
      | Some header => encode_deco_packed v f32_zero encode_float (Varint.encode header)
      | None => None 
      };
    encode_field' m (V_FIELD n (V_INT v)) with encode_header m n, find_int_enc_one m n => {
      | Some header, Some enc_one => encode_deco_packed v 0%Z enc_one (Varint.encode header)
      | _, _ => None
      };
    encode_field' m (V_FIELD n (V_BOOL v)) with encode_header m n => {
      | Some header => encode_deco_packed v false encode_bool (Varint.encode header)
      | None => None 
      };
    encode_field' m (V_FIELD n (V_STRING v)) with encode_header m n => {
      | Some header => encode_deco_unpacked v EmptyString encode_string (Varint.encode header)
      | None => None
      };
    encode_field' m (V_FIELD n (V_BYTES v)) with encode_header m n => {
      | Some header => encode_deco_unpacked v [] encode_bytes (Varint.encode header)
      | None => None
      };
    encode_field' m (V_FIELD n (V_MSG (V_IMPLICIT msg))) with encode_header m n,
      find_nested_msg_desc m (V_FIELD n (V_MSG (V_IMPLICIT msg))) => {
      | Some header, Some m' => prefix_opt (Varint.encode header) $ len_prefix_opt $ encode_message m' msg
      | _, _ => None
      };
    encode_field' m (V_FIELD n (V_MSG (V_OPTIONAL (Some msg)))) with encode_header m n,
      find_nested_msg_desc m (V_FIELD n (V_MSG (V_OPTIONAL (Some msg)))) => {
      | Some header, Some m' => prefix_opt (Varint.encode header) $ len_prefix_opt $ encode_message m' msg
      | _, _ => None
      };
    encode_field' m (V_FIELD n (V_MSG (V_REPEATED msgs))) with encode_header m n,
      find_nested_msg_desc m (V_FIELD n (V_MSG (V_REPEATED msgs))) => {
      | Some header, Some m' =>
          let encode_prefix_message := fun m' msg => prefix_opt (Varint.encode header) $ len_prefix_opt $
                                                    encode_message m' msg in
          fold_left opt_append_opt (map (encode_prefix_message m') msgs) None
      | _, _ => None
      };
    encode_field' m (V_FIELD n _) with encode_header m n => {
      | Some header => None
      | None => None
      };
  where encode_message (md : MsgDesc) (msgv : MsgVal) : option (list byte) :=
    encode_message md msgv := fold_left opt_append_opt (map (encode_field' md) (msg_val_get_fields msgv)) None.

  Definition tag_from_num (n : Z) : option Tag :=
    match n with
    | 0%Z => Some VARINT
    | 1%Z => Some I64
    | 2%Z => Some LEN
    | 5%Z => Some I32
    | _ => None
    end.

  Definition decode_header (enc : list byte) : option (Z * Tag * list byte) :=
    match Varint.extract_varint enc with
    | Some (header_bytes, bs) => let header : w64 := Varint.decode header_bytes in
                                let fid : Z := uint.Z $ word.sru header (U64 3) in
                                let tag_n : Z := uint.Z $ word.and header (U64 7) in
                                match tag_from_num tag_n with
                                | None => None
                                | Some tag => Some (fid, tag, bs)
                                end
    | None => None
    end.

  Lemma decode_header_consume (enc : list byte) (fid : Z) (tag : Tag) (rest : list byte) :
    decode_header enc = Some (fid, tag, rest) -> length rest < length enc.
  Proof.
    unfold decode_header.
    destruct (Varint.extract_varint enc) as [Hexr |] eqn:Hex.
    + destruct Hexr as [header_bytes bs].
      pose proof (Varint.extract_varint_consume enc header_bytes bs).
      apply H in Hex.
      destruct (tag_from_num (uint.Z (word.and (Varint.decode header_bytes) (W64 7)))).
      - intro Heq. inversion Heq. subst. apply Hex.
      - discriminate.
    + discriminate.
  Qed.
       
  Definition find_field (m : MsgDesc) (id : Z) : option FieldDesc :=
    (* Hide the recursion on the fields via a nested fix *)
    let find_field := (fix find_field (fs : list FieldDesc) : option FieldDesc :=
                         match fs with
                         | [] => None
                         | h :: t => if (Nat.eqb (Z.to_nat id) $ field_desc_get_id h) then
                                     Some h
                                   else
                                     find_field t
                         end
                      ) in
    find_field (msg_desc_get_fields m).

  (* Try to split the input list into a list with the n elements, then the rest.
     Return None if there aren't n elements in the list. *)
  Definition consume {A : Type} (n : nat) (l : list A) : option (list A * list A) :=
    let prefix := take n l in
    let suffix := drop n l in
    if Nat.eqb n $ length prefix then
      Some (prefix, suffix)
    else
      None.

  Lemma consume_consume {A : Type} (n : nat) (l : list A) (p : list A) (s : list A) :
    n > 0 -> consume n l = Some (p, s) -> length p = n /\ length s < length l.
  Proof.
    intros Hn.
    unfold consume.
    destruct (n =? length (take n l)) eqn:Hlen.
    + apply Nat.eqb_eq in Hlen. intros Heq. inversion Heq. subst.
      split.
      - symmetry. apply Hlen.
      - rewrite length_drop. symmetry in Hlen. apply Nat.sub_lt.
        * rewrite length_take in Hlen. rewrite Nat.min_l_iff in Hlen. apply Hlen.
        * done.
    + discriminate.
  Qed.

  Definition decode_value (t : Tag) (enc : list byte) : option (list byte * list byte) :=
    match t with
    | VARINT => Varint.extract_varint enc
    | I64 => consume 8 enc
    | LEN => match Varint.extract_varint enc with
            | Some (len_byt, enc_byt) => let len : nat := uint.nat (Varint.decode len_byt) in
                                        if Nat.eqb 0 len then
                                          Some ([], enc_byt)
                                        else
                                          consume len enc_byt
            | None => None
            end
    | I32 => consume 4 enc
    end.

  Lemma decode_value_consume (t : Tag) (enc : list byte) (fenc : list byte) (rest : list byte) :
    decode_value t enc = Some (fenc, rest) -> length rest < length enc.
  Proof.
    unfold decode_value.
    destruct t.
    + apply Varint.extract_varint_consume.
    + apply consume_consume. lia.
    + destruct (Varint.extract_varint enc) as [[len_byt enc_byt] |] eqn:Hex.
      - destruct (0 =? uint.nat (Varint.decode len_byt)) eqn:Hlen.
        * apply Varint.extract_varint_consume in Hex.
          intro Heq. inversion Heq. subst. apply Hex.
        * intro Hconsume. 
          apply Varint.extract_varint_consume in Hex.
          apply consume_consume in Hconsume as [_ Hconsume].
          { lia. } { apply Nat.eqb_neq in Hlen. lia. }
      - discriminate.
    + apply consume_consume. lia.
  Qed.

  Definition decode_field (enc : list byte) : option (Z * list byte * list byte) :=
    match decode_header enc with
    | Some (fid, t, bs) => match decode_value t bs with
                          | Some (v, b) => Some (fid, v, b)
                          | None => None
                          end
    | None => None
    end.

  Lemma decode_field_consume (enc : list byte) (fid : Z) (field_enc : list byte) (rest_enc : list byte) :
    decode_field enc = Some (fid, field_enc, rest_enc) -> length rest_enc < length enc.
  Proof.
    unfold decode_field.
    destruct (decode_header enc) as [[[fid__h t__h] bs__h] |] eqn:Hhd.
    + destruct (decode_value t__h bs__h) as [[v b] |] eqn:Hvl.
      - apply decode_header_consume in Hhd. apply decode_value_consume in Hvl.
        intro Heq. inversion Heq. subst. lia.
      - discriminate.
    + discriminate.
  Qed.
  
  (* While deocde_field performs one chunk, this decodes until either
     - The remaining bytes are empty
     - Something fails to chunk. *)
  Program Fixpoint decode_fields (enc : list byte) {measure (length enc)} :
    option (list (Z * list byte) * list byte) :=
    match enc with
    | [] => None
    | enc => match decode_field enc with
            | Some (fid, fbs, bs) => match decode_fields bs with
                                    | Some (rfs, rbyt) => Some ((fid, fbs) :: rfs, rbyt)
                                    | None => Some ([(fid, fbs)], bs)
                                    end
            | None => None
            end
    end.
  Next Obligation.
    symmetry in Heq_anonymous. apply decode_field_consume in Heq_anonymous. apply Heq_anonymous.
  Qed.
  Next Obligation.
    apply measure_wf.
    apply lt_wf.
  Qed.

  Fixpoint assemble_Z (enc : list byte) : Z :=
    match enc with
    | [] => 0
    | h :: tl => (2^(uint.Z h) * assemble_Z tl) + (uint.Z h)
    end.

  Class FieldParser (A : Type) := {
      parse : list byte -> option (A * list byte);
      consume_proof : forall enc a rest, parse enc = Some (a, rest) -> length rest < length enc;
    }.

  Definition parse_double (enc : list byte) : option (f64 * list byte) :=
    match consume 8 enc with
    | Some (byt, rest) => Some (b64_of_bits $ assemble_Z byt, rest)
    | None => None
    end.

  Program Instance double_field_parser : FieldParser f64 := {| parse := parse_double |}.
  Next Obligation.
    unfold parse_double in H.
    destruct (consume 8 enc) as [[byt__c rest__c] |] eqn:Hconsume in H.
    + inversion H. subst. apply consume_consume in Hconsume as [_ Hlen].
      * assumption.
      * lia.
    + discriminate.
  Qed.

  Definition parse_float (enc : list byte) : option (f32 * list byte) :=
    match consume 4 enc with
    | Some (byt, rest) => Some (b32_of_bits $ assemble_Z byt, rest)
    | None => None
    end.

  Program Instance float_field_parser : FieldParser f32 := {| parse := parse_float |}.
  Next Obligation.
    unfold parse_float in H.
    destruct (consume 4 enc) as [[byt__c rest__c] |] eqn:Hconsume in H.
    + inversion H. subst. apply consume_consume in Hconsume as [_ Hlen].
      * assumption.
      * lia.
    + discriminate.
  Qed.

  Definition parse_int (w : Width) (enc : list byte) : option (Z * list byte) :=
    match Varint.extract_varint enc with
    | Some (vint, rest) => Some (uint_int w $ uint_change_w w $ uint.Z $ Varint.decode vint, rest)
    | None => None
    end.

  Program Instance int_field_parser (w : Width) : FieldParser Z := {| parse := parse_int w |}.
  Next Obligation.
    unfold parse_int in H.
    destruct (Varint.extract_varint enc) as [[vint rest__b] |] eqn:Hconsume in H.
    + inversion H. subst. apply Varint.extract_varint_consume in Hconsume.
      assumption.
    + discriminate.
  Qed.

  Definition parse_uint (w : Width) (enc : list byte) : option (Z * list byte) :=
    match Varint.extract_varint enc with
    | Some (vint, rest) => Some (uint_change_w w $ uint.Z $ Varint.decode vint, rest)
    | None => None
    end.

  Program Instance uint_field_parser (w : Width) : FieldParser Z := {| parse := parse_uint w |}.
  Next Obligation.
    unfold parse_uint in H.
    destruct (Varint.extract_varint enc) as [[vint rest__b] |] eqn:Hconsume in H.
    + inversion H. subst. apply Varint.extract_varint_consume in Hconsume.
      assumption.
    + discriminate.
  Qed.

  Definition parse_sint (w : Width) (enc : list byte) : option (Z * list byte) :=
    match Varint.extract_varint enc with
    | Some (vint, rest) => Some (uint_sint w $ uint_change_w w $ uint.Z $ Varint.decode vint, rest)
    | None => None
    end.

  Program Instance sint_field_parser (w : Width) : FieldParser Z := {| parse := parse_sint w |}.
  Next Obligation.
    unfold parse_sint in H.
    destruct (Varint.extract_varint enc) as [[vint rest__b] |] eqn:Hconsume in H.
    + inversion H. subst. apply Varint.extract_varint_consume in Hconsume.
      assumption.
    + discriminate.
  Qed.
    
  Definition parse_fixed  (w : Width) (enc : list byte) : option (Z * list byte) :=
    match consume (Z.to_nat (unwrap_width w)) enc with
    | Some (byt, rest) => Some (assemble_Z byt, rest)
    | None => None
    end.

  Program Instance fixed_field_parser (w : Width) : FieldParser Z := {| parse := parse_fixed w |}.
  Next Obligation.
    unfold parse_fixed in H.
    destruct (consume (Z.to_nat (unwrap_width w)) enc) as [[byt__c rest__c] |] eqn:Hconsume.
    + inversion H. subst. apply consume_consume in Hconsume as [_ Hlen].
      * assumption.
      * destruct w. unfold WidthProp in w. simpl. lia.
    + discriminate.
  Qed.

  Definition parse_sfixed  (w : Width) (enc : list byte) : option (Z * list byte) :=
    match consume (Z.to_nat (unwrap_width w)) enc with
    | Some (byt, rest) => Some (uint_int w $ assemble_Z byt, rest)
    | None => None
    end.

  Program Instance sfixed_field_parser (w : Width) : FieldParser Z := {| parse := parse_sfixed w |}.
  Next Obligation.
    unfold parse_sfixed in H.
    destruct (consume (Z.to_nat (unwrap_width w)) enc) as [[byt__c rest__c] |] eqn:Hconsume.
    + inversion H. subst. apply consume_consume in Hconsume as [_ Hlen].
      * assumption.
      * destruct w. unfold WidthProp in w. simpl. lia.
    + discriminate.
  Qed.

  Definition parse_bool (enc : list byte) : option (bool * list byte) :=
    match enc with
    | [] => None
    | h :: tl => if word.eqb h (W8 0) then Some (false, tl) else Some (true, tl)
    end.

  Program Instance bool_field_parser : FieldParser bool := {| parse := parse_bool |}.
  Next Obligation.
    unfold parse_bool in H.
    destruct enc.
    + discriminate.
    + destruct (word.eqb w (W8 0)).
      * inversion H. subst. simpl. lia.
      * inversion H. subst. simpl. lia.
  Qed.

  Definition parse_string (enc : list byte) : option (string * list byte) :=
    match enc with
    | [] => None
    | bytes => Some (string_of_list_ascii (map Properties.u8_to_ascii bytes) , [])
    end.

  Program Instance string_field_parser : FieldParser string := {| parse := parse_string |}.
  Next Obligation.
    unfold parse_string in H.
    destruct enc.
    + discriminate.
    + inversion H. subst. simpl. lia.
  Qed.

  Definition parse_bytes (enc : list byte) : option (list byte * list byte) :=
    match enc with
    | [] => None
    | bytes => Some (bytes, [])
    end.

  Program Instance bytes_field_parser : FieldParser (list byte) := {| parse := parse_bytes |}.
  Next Obligation.
    unfold parse_bytes.
    destruct enc.
    + discriminate.
    + inversion H. subst. simpl. lia.
  Qed.

  Definition update_field {A : Type} (name : string) (ori_v : DecoVal A) (new_v : DecoVal A) : DecoVal A :=
    match ori_v, new_v with
    | V_IMPLICIT _, V_IMPLICIT v => V_IMPLICIT v
    | V_OPTIONAL _, V_OPTIONAL v => V_OPTIONAL v
    | V_REPEATED v', V_REPEATED v => V_REPEATED (v' ++ v)                                       
    | _, _ => ori_v (* Incompatible update, should never happen *)
    end.

   Definition update_message (m : MsgVal) (name : string) (value : ValVal) : MsgVal :=
    let update_fields := (fix update_fields (fs : list FieldVal) : list FieldVal :=
                            match fs with
                            | [] => []
                            | (V_FIELD n v) :: tl => if String.eqb n name then
                                                      (V_FIELD n (match v, value with
                                                                  | V_DOUBLE orig, V_DOUBLE newv =>
                                                                      V_DOUBLE (update_field n orig newv)
                                                                  | V_FLOAT orig, V_FLOAT newv =>
                                                                      V_FLOAT (update_field n orig newv)
                                                                  | V_INT orig, V_INT newv =>
                                                                      V_INT (update_field n orig newv)
                                                                  | V_BOOL orig, V_BOOL newv =>
                                                                      V_BOOL (update_field n orig newv)
                                                                  | V_STRING orig, V_STRING newv =>
                                                                      V_STRING (update_field n orig newv)
                                                                  | V_BYTES orig, V_BYTES newv =>
                                                                      V_BYTES (update_field n orig newv)
                                                                  | V_MSG orig, V_MSG newv =>
                                                                      V_MSG (update_field n orig newv)
                                                                  | V_ENUM orig, V_ENUM newv =>
                                                                      V_ENUM (update_field n orig newv)
                                                                  | _, _ => v
                                                                  end) :: tl)
                                                    else
                                                      (V_FIELD n v) :: update_fields tl
                            end) in
    V_MESSAGE (update_fields (msg_val_get_fields m)).

   Equations? parse_packed {A : Type} (payload : list byte) (parse_one : FieldParser A) :
     option (list A) by wf (length payload) lt :=
     parse_packed pyl parse_one with inspect (parse_one.(parse) pyl) := {
       | Some (a, []) eqn:Hp => Some [a]
       | Some (a, bs) eqn:Hp => match parse_packed bs parse_one with
                              | Some r => Some (a :: r)
                              | None => None
                              end
       | None eqn:Hp => None
       }.
   Proof.
     apply parse_one.(consume_proof) in Hp. 
     replace bs with (w :: l); done.
   Qed.
        
   Definition parse_deco {A : Type} (deco : DecoDesc) (payload : list byte) (parse_one : FieldParser A)
     : option (DecoVal A) :=
     match deco with
     | D_IMPLICIT => match parse_one.(parse) payload with
                    | Some (one, _) => Some (V_IMPLICIT one)
                    | None => None
                    end
     | D_OPTIONAL => match parse_one.(parse) payload with
                    | Some (one, _) => Some (V_OPTIONAL (Some one))
                    | None => None
                    end
     | D_REPEATED => match parse_packed payload parse_one with
                    | Some many => Some (V_REPEATED many)
                    | None => None
                    end
     end.

   Equations? parse_message' (m : MsgDesc) (msg : option MsgVal) (enc : list byte) :
     option (MsgVal * list byte) by wf (length enc) lt :=
     parse_message' m (Some msg) enc with inspect (decode_field enc) := {
       | Some (fid, payload, rest) eqn:Hf => match find_field m fid with
                                            | Some (D_FIELD name fid vdesc) =>
                                                match vdesc with 
                                                | D_DOUBLE dd =>
                                                    match parse_deco dd payload double_field_parser with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_DOUBLE vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_FLOAT dd =>
                                                    match parse_deco dd payload float_field_parser with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_FLOAT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_INT w dd =>
                                                    match parse_deco dd payload (int_field_parser w) with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_INT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_UINT w dd =>
                                                    match parse_deco dd payload (uint_field_parser w) with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_INT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_SINT w dd =>
                                                    match parse_deco dd payload (sint_field_parser w) with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_INT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_FIXED w dd =>
                                                    match parse_deco dd payload (fixed_field_parser w) with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_INT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_SFIXED w dd =>
                                                    match parse_deco dd payload (sfixed_field_parser w) with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_INT vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_BOOL dd =>
                                                    match parse_deco dd payload bool_field_parser with 
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_BOOL vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_STRING dd =>
                                                    match parse_deco dd payload string_field_parser with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_STRING vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_BYTES dd =>
                                                    match parse_deco dd payload bytes_field_parser with
                                                    | Some vdeco =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_BYTES vdeco))) rest
                                                    | None => None
                                                    end
                                                | D_MSG md dd =>
                                                    match dd, parse_message' md (Some (init_msg md)) rest with
                                                    | D_IMPLICIT, Some (msg, _) =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_MSG (V_IMPLICIT msg))))
                                                          rest
                                                    | D_OPTIONAL, Some (msg, _) =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_MSG (V_OPTIONAL
                                                                                            (Some msg))))) rest
                                                    | D_REPEATED, Some (msg, _) =>
                                                        parse_message' m (Some (update_message msg name
                                                                                  (V_MSG (V_REPEATED [msg]))))
                                                          rest
                                                    | _, None => None
                                                    end
                                                | D_ENUM _ => None
                                                end
                                            | None => None
                                            end
       | None eqn:Hf => None
       };
     parse_message' _ None _ := None.
   Proof.
     all: apply decode_field_consume in Hf; assumption.
   Qed.

   Definition parse_message (m : MsgDesc) (enc : list byte) : option MsgVal :=
     match parse_message' m (Some (init_msg m)) enc with
     | Some (msg, _) => Some msg
     | None => None
     end.

   Lemma consuming_message (m : MsgDesc) (msg : option MsgVal) : 
    forall enc a rest, parse_message' m msg enc = Some (a, rest) -> length rest < length enc.
   Proof.
     intros enc rmsg rest.
     funelim (parse_message' m msg enc); try discriminate.
     cbn. clear H9. apply decode_field_consume in Hf.
     destruct (find_field m fid); last discriminate.
     destruct f eqn:Hfd. destruct val eqn:Hval.
     * destruct (parse_deco deco payload double_field_parser) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H f _ id val deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload float_field_parser) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H0 f _ id val deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload (int_field_parser w)) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H1 f _ id val w deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload (uint_field_parser w)) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H1 f _ id val w deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload (sint_field_parser w)) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H1 f _ id val w deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload (fixed_field_parser w)) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H1 f _ id val w deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload (sfixed_field_parser w)) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H1 f _ id val w deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload bool_field_parser) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H2 f _ id val deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload string_field_parser) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H3 f _ id val deco _ _ rest0 Hcall) as H'. lia.
     * destruct (parse_deco deco payload bytes_field_parser) eqn:Hdeco; last discriminate.
       intro Hcall. pose proof (H4 f _ id val deco _ _ rest0 Hcall) as H'. lia.
     * destruct deco eqn:Hdeco.
       - destruct (parse_message' msg0 (Some (init_msg msg0)) rest) eqn:Hmsg; last discriminate.
         destruct p eqn:Hp. intro Hcall.
         pose proof (H6 f _ id val msg0 deco p _ payload rmsg rest0 Hcall) as H'. lia.
       - destruct (parse_message' msg0 (Some (init_msg msg0)) rest) eqn:Hmsg; last discriminate.
         destruct p eqn:Hp. intro Hcall.
         pose proof (H7 f _ id val msg0 deco p _ payload rmsg rest0 Hcall) as H'. lia.
       - destruct (parse_message' msg0 (Some (init_msg msg0)) rest) eqn:Hmsg; last discriminate.
         destruct p eqn:Hp. intro Hcall.
         pose proof (H8 f _ id val msg0 deco p _ payload rmsg rest0 Hcall) as H'. lia.
     * discriminate.
   Qed.
   
End Parse.
