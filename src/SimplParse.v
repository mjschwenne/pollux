(** Simple Parser, to establish some of the theory *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.
From Equations Require Import Equations.

From Pollux Require Import Parser.
From Pollux Require Import Input.

Open Scope Z_scope.

Module SimplParser.
  Module ByteParsers := Parsers(ByteInput).
  Import ByteInput.
  Import ByteParsers.

  (* Taken from Section 9.3 of Certified Programming with Dependent Types *)
  Section hlist.
    Variable A : Set.
    Variable B : A -> Type.

    Fixpoint fhlist (ls : list A) : Type :=
      match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
      end%type.

    Variable elm : A.
    Fixpoint fmember (ls : list A) : Type :=
      match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + fmember ls'
      end%type.

    Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
      match ls with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
                     match idx with
                     | inl pf => match pf with
                                | eq_refl => fst mls
                                end
                     | inr idx' => fhget ls' (snd mls) idx'
                     end
      end.

  End hlist.
  Arguments fhget [A B elm ls] _ _.

  Section Desc.

    (* A descriptor is either a base field, or two nested descriptors. *)
    Inductive Desc : Set :=
    | D_BOOL
    | D_INT
    | D_NEST (d1 : Desc) (d2 : Desc).

    Inductive Val : Set :=
    | V_BOOL (b : bool) : Val
    | V_INT (i : Z) : Val
    | V_NEST (v1 : Val) (v2 : Val) : Val.

    Fixpoint Schema (v : Val) : Desc :=
      match v with
      | V_BOOL _ => D_BOOL
      | V_INT _ => D_INT
      | V_NEST v1 v2 => D_NEST (Schema v1) (Schema v2)
      end.

    Compute Schema (V_INT 0%Z).
    Compute Schema (V_BOOL true).
    Compute Schema (V_NEST (V_INT 0%Z) (V_BOOL true)).

    Inductive subtermVal : Val -> Val -> Prop :=
    | st_nest_left (v1 : Val) (v2 : Val) : subtermVal v1 (V_NEST v1 v2)
    | st_nest_right (v1 : Val) (v2 : Val) : subtermVal v2 (V_NEST v1 v2).

    Instance Val_EqDecision : EqDecision Val.
    Proof. solve_decision. Defined. 

    Definition subtermVal_dec (x y : Val) : {subtermVal x y} + {~subtermVal x y}.
    Proof.
      refine (
          match y with
          | V_NEST v1 v2 => if decide (x = v1) then
                             left _
                           else if decide (x = v2) then
                                  left _
                                else right _
          | _ => right _
          end
        ).
      - intro H; inversion H.
      - intro H; inversion H.
      - subst; constructor.
      - subst; constructor.
      - intro H; inversion H; congruence.
    Defined.

  End Desc.

  (** ENCODING FORMAT *)

  (*
    While this is a simple descriptor setup, it is important to define what the binary format
    will be.

    Each descriptor will be serialized as a tag for the type
    - Base descriptor => 0
    - Nested descriptor => 1

    For the base descriptors, the next byte is another tag for the type of the field
    - Integer field => 0
    - Boolean field => 1

    (Note: This could be removed if integer and Boolean fields both used the same [length] encoding)

    The integer's will be encoded into a 4-byte little endian blob while the Booleans are
    encoded as 1-byte with 0 for false and any positive number for true.

    Nested messages will be length prefixed with the number of bytes the rest of the message
    takes and then the encoded message.
   *)

  Section Parser.

    Definition ParseByte : Parser byte :=
      fun inp => match inp with
              | byt :: rest => ParseSuccess byt rest
              | [] => ParseFailure Recoverable (mkFailureData "No more data to parse" inp None)
              end.

    Definition ParseUnsigned : Parser Z := ParseMap ParseByte word.unsigned.

    Definition ParseNat : Parser nat := ParseMap ParseByte (fun b => Z.to_nat $ word.unsigned b).

    (* Parse n bytes into an unsigned integer *)
    Definition ParseZN (n : nat) := ParseMap (RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                       (n + 8, new ≪ n + v))
                                         n (0, 0))
                                    (fun ret => let (_, z) := ret in z).

    Definition ParseZ32 := ParseZN 4%nat.

    Definition ParseBool : Parser bool := ParseMap ParseUnsigned (fun z => z >? 0).

    Definition ParseBaseDesc : Parser Val :=
        ParseBind ParseUnsigned
          (fun z => match z with
                 | 0 => ParseMap ParseZ32 (fun z => V_INT z)
                 | 1 => ParseMap ParseBool (fun b => V_BOOL b)
                 | _ => ParseFailWith "Unknown field tag" Recoverable
                 end).

    Compute ParseBaseDesc [W8 1; W8 32; W8 0; W8 0; W8 0].
    Compute ParseBaseDesc [W8 0; W8 32; W8 0; W8 0; W8 0].

    Definition ParseVal' (pd : Parser Val) : Parser Val :=
      ParseBind ParseUnsigned
        (fun z => 
           match z with
           | 0 => ParseBaseDesc
           | 1 => ParseMap (ParseLen ParseNat (ParseConcat pd pd))
                   (fun vs => let (v1, v2) := vs in V_NEST v1 v2)
           | _ => ParseFailWith "Unknown tag" Recoverable
           end).

    Definition ParseVal : Parser Val :=
      ParseRecursive ParseVal'.

    Definition to_enc (l : list Z) : list byte := map (fun n => W8 n) l.

    Definition test_enc1 := to_enc [0; 0; 32; 0; 0; 0].
    Compute ParseVal test_enc1.

    Definition test_enc2 := to_enc [1; 9; 0; 0; 1; 0; 0; 0; 0; 1; 1].
    Compute ParseVal test_enc2.

    Definition test_enc3 := to_enc [1; 17; 0; 0; 32; 0; 0; 0; 1; 9; 0; 0; 64; 0; 0; 0; 0; 1; 0].
    Compute ParseVal test_enc3.

    Definition test_enc4 := to_enc [1; 22;
                                    1; 9; 0; 0; 2; 0; 0; 0; 0; 1; 0;
                                    1; 9; 0; 0; 4; 0; 0; 0; 0; 1; 1].
    Compute ParseVal test_enc4.
  End Parser.

  Section Serializer.

    Definition SerialByte : Serializer byte serial_trivial_wf :=
      fun b => SerialSuccess [b].

    Definition Z__next (z : Z) : Z :=
      z ≫ 8.

    (* Create an n-byte little-endian list of z.
       If z doesn't fit into n bytes, the first n bytes are returned.
       If z fits into less than n bytes, the list is padded with zeros.
     *)
    Fixpoint Z_to_list (z : Z) (n : nat) : list byte :=
      match n with
      | O => []
      | S n' => W8 z :: Z_to_list (Z__next z) n'
      end.

    Compute Z_to_list 16777215 4.

    Definition SerialZ_Wf (n : nat) (z : Z) : Prop :=
      (0 <= z < 2^(8 * Z.of_nat n)).

    Definition SerialZN (n : nat) : Serializer Z (SerialZ_Wf n) :=
      fun z => SerialRep SerialByte (Z_to_list z n).

    Definition SerialZ32 := SerialZN 4%nat.

    Compute SerialZ32 16777215.

    Definition SerialBool : Serializer bool serial_trivial_wf :=
      fun b => if b then
              SerialByte (W8 1)
            else
              SerialByte (W8 0).

    Compute SerialBool true.
    Compute SerialBool false.

    Definition SerialMsgLen : Serializer nat (fun n => (Z.of_nat n) < 256) :=
      fun n =>
        SerialByte (W8 $ Z.of_nat n).

    Fixpoint ValDepth (v : Val) : nat :=
      match v with
      | V_BOOL _ => 0
      | V_INT _ => 0
      | V_NEST v1 v2 => 1 + max (ValDepth v1) (ValDepth v2)
      end.

    Definition SerialUnsigned : Serializer Z (fun z => 0 <= z < 256) :=
      fun z => SerialByte $ W8 z.

    Definition SerialNat : Serializer nat (fun n => (0 <= n < 256)%nat) :=
      fun n => SerialByte $ W8 (Z.of_nat n).

    Definition mkSerializer {R : Type} (s : R -> SerializeResult) (wf : R -> Prop) : Serializer R wf := s.

    Definition Restrict {R : Type} {wf : R -> Prop} (ser : Serializer R wf) (new : R -> Prop) :
      Serializer R (fun r => new r /\ wf r) := ser.

    Fixpoint ValEncLen (v : Val) : nat :=
      match v with
      | V_BOOL _ => 3 (* Two header bytes, one payload byte *)
      | V_INT _ => 6 (* Two header bytes, four payload bytes *)
      | V_NEST v1 v2 => 2 + (ValEncLen v1) + (ValEncLen v2)
      end.

    Definition OuterTag (v : Val) : Z :=
      match v with
      | V_NEST _ _ => 1
      | _ => 0
      end.

    Definition InnerTag (v : Val) : Z :=
      match v with
      | V_INT _ => 0
      | V_BOOL _ => 1
      | V_NEST v1 v2 => Z.of_nat (ValEncLen v1) + Z.of_nat (ValEncLen v2)
      end.

    Definition Len (vs: Val * Val) : nat := let (v1, v2) := vs in Z.to_nat $ InnerTag (V_NEST v1 v2).

    Definition tag_wf (v : Val) : Prop := 0 <= OuterTag v < 256 /\ 0 <= InnerTag v < 256.

    Fixpoint val_wf (v : Val) : Prop :=
      match v with
      | V_INT z => 0 <= z < 2^32
      | V_BOOL b => True
      | V_NEST v1 v2 => val_wf v1 /\ val_wf v2
      end.

    (* Definition SerialBaseDesc (ser : Serializer Val val_wf) : *)
    (*   Serializer Val (fun v => 0 <= InnerTag v < 256 /\ val_wf v) := *)
    (*   SerialBind' InnerTag SerialUnsigned *)
    (*     (mkSerializer *)
    (*        (fun v => match v with *)
    (*               | V_BOOL b => SerialBool b *)
    (*               | V_INT z => SerialZ32 z *)
    (*               | V_NEST v1 v2 => SerialLimit (SerialMap (SerialConcat ser ser) $ fun _ => (v1, v2)) Len v *)
    (*               end) val_wf). *)

    Definition SerialBaseDesc' (ser : Serializer Val val_wf) :
      Serializer Val (fun v => 0 <= InnerTag v < 256 /\ val_wf v) :=
      (fun v => match v with
             | V_BOOL b => SerialBind' (fun _ => 1) SerialUnsigned SerialBool b
             | V_INT z => SerialBind' (fun _ => 0) SerialUnsigned SerialZ32 z
             | V_NEST v1 v2 => SerialMap (SerialLen Len SerialNat (SerialConcat ser ser)) (fun _ => (v1, v2)) v
             end).

    Definition SerialVal'
      (ser : Serializer Val (fun v => 0 <= OuterTag v < 256 /\ 0 <= InnerTag v < 256 /\ val_wf v)) :=
      SerialBind' OuterTag SerialUnsigned (SerialBaseDesc' ser).

    Definition SerialVal : Serializer Val (fun v => 0 <= OuterTag v < 256 /\ 0 <= InnerTag v < 256 /\ val_wf v) :=
      SerialRecursive SerialVal' ValDepth.

    Definition enc_eq (v : Val) (e : Output) : bool :=
      match SerialVal v with
      | SerialSuccess enc => if decide (enc = e) then true else false
      | SerialFailure _ _ => false
      end.

    Definition test_val1 := V_INT 32.
    Compute SerialVal test_val1.
    Compute enc_eq test_val1 test_enc1.
                                    
    Definition test_val2 := (V_NEST (V_INT 1) (V_BOOL true)).
    Compute SerialVal test_val2.
    Compute enc_eq test_val2 test_enc2.

    Definition test_val3 := (V_NEST (V_INT 32) (V_NEST (V_INT 64) (V_BOOL false))).
    Compute SerialVal test_val3.
    Compute enc_eq test_val3 test_enc3.

    Definition test_val4 := (V_NEST (V_NEST (V_INT 2) (V_BOOL false)) (V_NEST (V_INT 4) (V_BOOL true))).
    Compute SerialVal test_val4.
    Compute enc_eq test_val4 test_enc4.

  End Serializer.

  Section Theorems.

    Ltac comp_add := 
      repeat match goal with
        | |- context[Z.add ?n ?m] =>
            match n with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
            match m with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
            let r := eval compute in (Z.add n m) in 
              change (Z.add n m) with r
        end.

    Ltac invc H := inversion H; subst; clear H.

    Theorem ByteParseOk : ParseOk ParseByte SerialByte.
    Proof.
      intros x enc rest _.
      unfold SerialByte.
      intro H. invc H.
      reflexivity.
    Qed.

    Theorem BoolParseOk : ParseOk ParseBool SerialBool.
    Proof.
      intros x enc rest _.
      destruct x.
      - unfold SerialBool. intro H. invc H.
        vm_compute. reflexivity.
      - unfold SerialBool. intro H. invc H.
        vm_compute. reflexivity.
    Qed.

    (* Modularity Test *)
    Definition ParseTest := ParseConcat ParseByte ParseBool.
    Definition SerialTest := SerialConcat SerialByte SerialBool.

    Theorem TestParseOk : ParseOk ParseTest SerialTest.
    Proof.
      unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
      intros [x b] enc rest _.
      unfold SerialTest, SerialConcat.
      destruct (SerialByte x) eqn:Hbyte; last discriminate.
      destruct (SerialBool b) eqn:Hbool; last discriminate.
      intros H. invc H.
      unfold ParseTest, ParseConcat.
      rewrite App_assoc.
      apply (ByteParseOk _ _ (App out0 rest)) in Hbyte; last reflexivity.
      rewrite Hbyte.
      apply (BoolParseOk _ _ rest) in Hbool; last reflexivity.
      rewrite Hbool.
      reflexivity.
    Qed.

    Theorem TestParseOk' : ParseOk ParseTest SerialTest.
    Proof.
      unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
      intros [x b] enc rest _ Hser.
      apply SerialConcatInversion in Hser.
      destruct Hser as (out__a & out__b & Ha & Hb & Henc).
      subst. rewrite App_assoc.
      unfold ParseTest, ParseConcat.
      apply (ByteParseOk _ _ (App out__b rest)) in Ha; last reflexivity.
      apply (BoolParseOk _ _ rest) in Hb; last reflexivity.
      rewrite Ha. rewrite Hb. reflexivity.
    Qed.

    Theorem TestParseOk'' : ParseOk ParseTest SerialTest.
    Proof.
      apply ConcatCorrect.
      - apply ByteParseOk.
      - apply BoolParseOk.
    Qed.
    (* Well that's definitely the cleanest proof of the lot *)

    Theorem Z32ParseOk : ParseOk ParseZ32 SerialZ32.
    Proof.
    Admitted.

    Theorem UnsignedParseOk : ParseOk ParseUnsigned SerialUnsigned.
    Proof.
      intros x enc rest wf.
      unfold SerialUnsigned, SerialByte.
      intros H. invc H.
      unfold ParseUnsigned, ParseMap.
      simpl. f_equal. word.
    Qed.

    Theorem NatParseOk : ParseOk ParseNat SerialNat.
    Proof.
      intros x enc rest wf.
      unfold SerialNat, SerialByte.
      intros H. invc H.
      unfold ParseNat, ParseMap.
      simpl. f_equal. word.
    Qed.

    Lemma ValLen_Length (v : Val) :
      forall enc, SerialVal v = SerialSuccess enc -> Length enc = ValEncLen v.
    Proof.
      induction v.
      - intros enc Hser. destruct b; vm_compute in Hser; inversion Hser; reflexivity.
      - intros enc Hser. vm_compute in Hser; inversion Hser; reflexivity.
      - intros enc. unfold SerialVal, SerialRecursive.
        rewrite ser_recur_unfold. unfold SerialVal'.
        intro Hser.
        apply SerialConcatInversion in Hser as (enc__ot & enc__rest & Hot_ok & Hrest_ok & Henc).
        unfold SerialBaseDesc', SerialMap in Hrest_ok.
        apply SerialConcatInversion in Hrest_ok as (enc__it & enc__v & Hit_ok & Hv_ok & Henc__v).
        unfold SerialLimit in Hv_ok.
        apply SerialConcatInversion in Hv_ok as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__vs).
        destruct (decide (ValDepth v1 < ValDepth (V_NEST v1 v2))%nat) as [Hdepth__v1 | Hcontra__v1] in Hv1_ok;
          last (unfold ValDepth in Hcontra__v1; lia).
        destruct (decide (ValDepth v2 < ValDepth (V_NEST v1 v2))%nat) as [Hdepth__v2 | Hcontra__v2] in Hv2_ok;
          last (unfold ValDepth in Hcontra__v2; lia).
        specialize IHv1 with enc__v1.
        specialize IHv2 with enc__v2.
        apply IHv1 in Hv1_ok.
        apply IHv2 in Hv2_ok.
        rewrite Henc__v, Henc__vs in Henc.
        rewrite Henc, !App_Length, !Nat.add_assoc.
        simpl. rewrite Hv1_ok, Hv2_ok.
        vm_compute in Hot_ok; inversion Hot_ok as [Hot_enc].
        unfold SerialNat, SerialByte in Hit_ok. inversion Hit_ok as [Hit_enc].
        reflexivity.
    Qed.

    Lemma SerialValInversion (v1 v2 : Val) :
      forall enc,
      SerialVal (V_NEST v1 v2) = SerialSuccess enc ->
      exists enc__v1 enc__v2, SerialVal v1 = SerialSuccess enc__v1 /\ SerialVal v2 = SerialSuccess enc__v2.
    Proof.
      intros enc.
      unfold SerialVal at 1, SerialRecursive, SerialVal'.
      rewrite ser_recur_unfold.
    Admitted.

    Theorem SimplParseOk' : ParseOk ParseVal SerialVal.
    Proof.
      intros x enc__x rest__x Hwf__x Hser__x.
      pose proof (ValLen_Length x enc__x Hser__x) as Hlength.
      unfold ParseVal, SerialVal in *.
      apply (RecursiveCorrect ParseVal' SerialVal' subtermVal ValDepth); try done.
      * unfold SerialRecursiveOk.
        intros r ser_rec. unfold SerialVal'.
        destruct (SerialBind' _ _ _ _) as [ enc |] eqn:Houter; last trivial.
        intros r_next Hst. destruct Hst as [v1 v2 | v1 v2].
        + intros Hwf.
          apply SerialConcatInversion in Houter as (enc__ot & enc__rest & Hot_ok & Hrest_ok & Henc).
          apply SerialConcatInversion in Hrest_ok as (enc__it & enc__v & Hit_ok & Hv_ok & Henc__rest).
          rewrite Henc__rest in Henc.
          destruct (ser_rec v1) as [enc__rec |] eqn:Hrec; last trivial.
          unfold mkSerializer in Hv_ok.
          apply SerialConcatInversion in Hv_ok as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__v).
          rewrite Hv1_ok in Hrec. inversion Hrec. subst.
          exists (App enc__ot enc__it), enc__v2. rewrite !App_assoc.
          split; first reflexivity.
          unfold SerialUnsigned, SerialByte in *.
          inversion Hot_ok. inversion Hit_ok.
          rewrite App_Length. 
          unfold Length. simpl. lia.
        + intros Hwf.
          apply SerialConcatInversion in Houter as (enc__ot & enc__rest & Hot_ok & Hrest_ok & Henc).
          apply SerialConcatInversion in Hrest_ok as (enc__it & enc__v & Hit_ok & Hv_ok & Henc__rest).
          rewrite Henc__rest in Henc.
          destruct (ser_rec v2) as [enc__rec |] eqn:Hrec; last trivial.
          unfold mkSerializer in Hv_ok.
          apply SerialConcatInversion in Hv_ok as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__v).
          rewrite Hv2_ok in Hrec. inversion Hrec. subst.
          exists (App enc__ot (App enc__it enc__v1)), Input_default.
          rewrite !App_assoc.
          rewrite App_nil_r.
          split; first reflexivity.
          unfold SerialUnsigned, SerialByte in *.
          inversion Hot_ok. inversion Hit_ok.
          rewrite App_Length. 
          unfold Length. simpl. lia.
      * intros p s Hps_ok.
        intros x'.
        apply (@BindCorrect' Z Val _ (λ v : Val, 0 ≤ InnerTag v < 256 ∧ val_wf v)
                 _ SerialUnsigned
                 _ _ _ _);
          first apply UnsignedParseOk.
        destruct x' eqn:Hx.
        + simpl.
          intros enc rest [Hit_wf Hb_wf].
          unfold SerialBaseDesc'.
          intros Hser.
          apply SerialConcatInversion in Hser as (enc__it & enc__b & Hit_ok & Hb_ok & Henc).
          unfold ParseBaseDesc, ParseBind.
          rewrite Henc, App_assoc.
          pose proof (UnsignedParseOk 1 enc__it (App enc__b rest) Hit_wf Hit_ok) as Hu_ok.
          rewrite Hu_ok.
          unfold ParseMap.
          pose proof (BoolParseOk b enc__b rest Hb_wf Hb_ok) as Hser_b.
          rewrite Hser_b.
          reflexivity.
        + simpl.
          intros enc rest [Hit_wf Hz_wf].
          unfold SerialBaseDesc'.
          intros Hser.
          apply SerialConcatInversion in Hser as (enc__it & enc__z & Hit_ok & Hvz_ok & Henc).
          unfold ParseBaseDesc, ParseBind.
          rewrite Henc, App_assoc.
          pose proof (UnsignedParseOk 0 enc__it (App enc__z rest) Hit_wf Hit_ok) as Hu_ok.
          rewrite Hu_ok.
          unfold ParseMap.
          pose proof (Z32ParseOk i enc__z rest Hz_wf Hvz_ok) as Hser_z.
          rewrite Hser_z.
          reflexivity.
        + simpl.
          unfold SerialBaseDesc'.
          intros enc rest [wf_tag [wf_v1 wf_v2]] Hser.
          unfold ParseMap.
          unfold SerialMap in Hser.
          pose proof (LenCorrect SerialNat ParseNat Len
                        (SerialConcat s s)
                        (ParseConcat p p)) as Hser_len.
          specialize (Hser_len (v1, v2) NatParseOk).
          assert (LimitParseOk (SerialConcat s s) (ParseConcat p p)) as Hlim_ok.
          {
            unfold LimitParseOk.
            intros [x__l1 x__l2] enc__l wf__l.
            unfold CallbackParseOk in Hps_ok.
            intros Hser__l.
            apply SerialConcatInversion in Hser__l as (enc__l1 & enc__l2 & Hl1_ok & Hl2_ok & Henc__l).
            unfold ParseConcat.
            admit.
          }
          assert (LenOk (SerialConcat s s) Len (v1, v2)) as Hlen.
          {
            unfold LenOk. intro enc'.
            unfold Len, InnerTag.
            intro Hser_cat. 
            apply SerialConcatInversion in Hser_cat as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__vs).
            unfold InnerTag in wf_tag.
            pose proof (ValLen_Length v1 enc__v1) as Hv1_len.
            pose proof (ValLen_Length v2 enc__v2) as Hv2_len.
            rewrite Henc__vs, App_Length.
            unfold CallbackParseOk in Hps_ok.
            assert (x = x') as Heqx. { admit. }
            rewrite Heqx, Hx in Hser__x.
            apply SerialValInversion in Hser__x.
            admit.
          }
          specialize (Hser_len Hlim_ok Hlen enc rest) as Hp_ok.
          rewrite Hp_ok; try done.
    Abort.

  (* FIXME:
     Well, this is extremely frustrating. I feel like I'm close to having this correctness
     theorem proven, but the gaps remains. Here's what the issues are right now:
     - The definition of CallbackParseOk is basically unusable do the the existential quantifier,
       but changing it to a universal quantifier makes using it the RecursiveCorrect theorem
       unusable.
     - The current setup requires me to prove properties about any possible callback. While this is
       fine in general, it becomes a problem specifically with the length limiting combinators since
       these require me to manually reason about the length of encoding coming from an opaque serializer.
       The encoding format cannot be changed to break up nested messages and length prefixing since that's
       a common real world feature of binary formats. This does suggest that using SerialLen' is the
       correct move, since then I don't have to prove the correctness of the provided length function.
       However, the issue there is the well-formed condition of that combinator. We have to show, basically,
       that the length of the payload fits in one byte. This should be possible with some of the new
       length based lemmas I've proved.
     - Honestly, I think I could focus this proof on the serializer (using induction on depth)
       WITHOUT the RecursiveCorrect theorem except for dealing with the difficulties of the
       recursive parser combinator. While there is a link between decreasing depth and decreasing
       encoding length, it is extremely hard to enumerate in a format generic way.
     - I'm considering trying to name the currently anonymous callbacks in par_recur and ser_recur, but
       having to pass around the whole closure is really messy. The advantage here is that then the
       recursive combinator correctness theorem could use those callbacks rather than a generic one.
       It might prove fruitful since I know that these callbacks are correct, but it is possible to
       write ones that aren't. Then the actual callback would be exposed in my proof here. That's bad
       encapsulation, but might just let the proof be completed...
   *)

  End Theorems.

End SimplParser.
