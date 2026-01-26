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
             | V_NEST v1 v2 => SerialMap (SerialLen' SerialNat (SerialConcat ser ser)) (fun _ => (v1, v2)) v
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
        apply SerialLen'Inversion in Hrest_ok as (enc__it & enc__v & Hit_ok & Hv_ok & Henc__v).
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
      intro Hser.
      apply SerialConcatInversion in Hser as (enc__ot & enc__rest & Hot_ok & Hrest_ok & Henc).
      unfold SerialBaseDesc', SerialMap in Hrest_ok.
      apply SerialLen'Inversion in Hrest_ok as (enc__it & enc__v & Hit_ok & Hv_ok & Henc__v).
      apply SerialConcatInversion in Hv_ok as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__vs).
      destruct (decide (ValDepth v1 < ValDepth (V_NEST v1 v2))%nat) as [Hdepth__v1 | Hcontra__v1] in Hv1_ok;
        last (unfold ValDepth in Hcontra__v1; lia).
      destruct (decide (ValDepth v2 < ValDepth (V_NEST v1 v2))%nat) as [Hdepth__v2 | Hcontra__v2] in Hv2_ok;
        last (unfold ValDepth in Hcontra__v2; lia).
      exists enc__v1, enc__v2.
      split.
      - apply Hv1_ok.
      - apply Hv2_ok.
    Qed.

    Lemma ValLen_Nest (v1 v2 : Val) :
      forall enc,
      SerialVal (V_NEST v1 v2) = SerialSuccess enc ->
      exists enc__v1 enc__v2, SerialVal v1 = SerialSuccess enc__v1 /\ SerialVal v2 = SerialSuccess enc__v2 ->
             (Length enc > Length enc__v1 /\ Length enc > Length enc__v2)%nat.
    Proof.
      intros.
      pose proof (ValLen_Length (V_NEST v1 v2) enc H) as Hv_len.
      apply SerialValInversion in H as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok).
      exists enc__v1, enc__v2. intros _.
      pose proof (ValLen_Length v1 enc__v1 Hv1_ok) as Hv1_len.
      pose proof (ValLen_Length v2 enc__v2 Hv2_ok) as Hv2_len.
      unfold ValEncLen in Hv_len.
      fold (ValEncLen v1) in Hv_len.
      fold (ValEncLen v2) in Hv_len.
      rewrite !Hv_len.
      lia.
    Qed.

    Lemma ValEncLen_InnerTag (v : Val) :
      0 <= InnerTag v <= Z.of_nat $ ValEncLen v.
    Proof.
      destruct v.
      - unfold ValEncLen, InnerTag. lia.
      - unfold ValEncLen, InnerTag. lia. 
      - unfold ValEncLen, InnerTag.
        fold (ValEncLen v1); fold (ValEncLen v2).
        lia.
    Qed.

    Theorem SimplParseOk : ParseOk ParseVal SerialVal.
    Proof.
      apply RecursiveCorrect.
      intros x enc rest (wf_ot & wf_it & wf_val) IH.
      unfold ser_recur_step, par_recur_step.
      intros Hser.
      destruct x eqn:Hx.
      - revert Hser.
        apply BindCorrect'; first apply UnsignedParseOk; last repeat (split; try word || assumption).
        simpl.
        intros enc__v rest__v [Hit_wf Hb_wf].
        unfold SerialBaseDesc'.
        intros Hser.
        apply SerialConcatInversion in Hser as (enc__it & enc__b & Hit_ok & Hb_ok & Henc).
        unfold ParseBaseDesc, ParseBind.
        rewrite Henc, App_assoc.
        pose proof (UnsignedParseOk 1 enc__it (App enc__b rest__v) Hit_wf Hit_ok) as Hu_ok.
        rewrite Hu_ok.
        unfold ParseMap.
        pose proof (BoolParseOk b enc__b rest__v Hb_wf Hb_ok) as Hser_b.
        rewrite Hser_b.
        reflexivity.
      - revert Hser.
        apply BindCorrect'; first apply UnsignedParseOk; last repeat (split; try word || assumption).
        simpl.
        intros enc__v rest__v [Hit_wf Hz_wf].
        unfold SerialBaseDesc'.
        intros Hser.
        apply SerialConcatInversion in Hser as (enc__it & enc__z & Hit_ok & Hvz_ok & Henc).
        unfold ParseBaseDesc, ParseBind.
        rewrite Henc, App_assoc.
        pose proof (UnsignedParseOk 0 enc__it (App enc__z rest__v) Hit_wf Hit_ok) as Hu_ok.
        rewrite Hu_ok.
        unfold ParseMap.
        pose proof (Z32ParseOk i enc__z rest__v Hz_wf Hvz_ok) as Hser_z.
        rewrite Hser_z.
        reflexivity.
      - remember 
          (λ r__next : Val,
             if decide (ValDepth r__next < ValDepth (V_NEST v1 v2))%nat
             then ser_recur SerialVal' ValDepth r__next
             else SerialRecursiveProgressError "Serial.Recursive" ValDepth (V_NEST v1 v2) r__next)
          as s.
        remember
          (λ inp__next : Input,
             if decide (Length inp__next < Length (App enc rest))%nat
             then par_recur ParseVal' inp__next
             else RecursiveProgressError "Parser.Recursive" (App enc rest) inp__next)
          as p.
        unfold SerialVal' in Hser.
        apply SerialConcatInversion in Hser as (enc__ot & enc__rest & Hot_ok & Hrest_ok & Henc).
        unfold SerialBaseDesc', SerialMap in Hrest_ok.
        set (SerialVal_wf := fun v => 0 <= InnerTag v < 256 /\ val_wf v).
        unfold ParseVal', ParseBind.
        rewrite Henc, App_assoc.
        apply (UnsignedParseOk _ _ (App enc__rest rest)) in Hot_ok as Hot_succ; last word.
        vm_compute in Hot_ok.
        rewrite Hot_succ. simpl.
        pose proof (@LenCorrect'Weakened _ (Concat_wf val_wf val_wf) _ SerialNat ParseNat
                      (SerialConcat s s)
                      (ParseConcat p p) (v1, v2) NatParseOk) as Hser_len.
        assert (LimitParseOkWeak (@SerialConcat _ _ val_wf val_wf s s) (ParseConcat p p) (v1, v2))
          as Hps_ok.
        {
          unfold LimitParseOkWeak.
          intros enc__xs wf_xs.
          destruct wf_xs as (wf_x1, wf_x2).
          intros Hser__xs.
          apply SerialLen'Inversion in Hrest_ok as (enc__len & enc__xs' & Hlen_ok & Hcxs & Henc__rest).
          rewrite Hser__xs in Hcxs; inversion Hcxs as [Heqenc]; clear Hcxs.
          symmetry in Heqenc.
          apply SerialConcatInversion in Hser__xs as (enc__x1 & enc__x2 & Hx1_ok & Hx2_ok & Henc__xs).
          rewrite Heqs in Hx1_ok, Hx2_ok.
          destruct (decide _) in Hx1_ok;
            last (
                unfold SerialRecursiveProgressError in Hx1_ok;
                destruct (ValDepth _ == ValDepth _) in Hx1_ok; discriminate
              ).
          destruct (decide _) in Hx2_ok;
            last (
                unfold SerialRecursiveProgressError in Hx2_ok;
                destruct (ValDepth _ == ValDepth _) in Hx2_ok; discriminate
              ).
          rewrite Heqenc, Henc__xs.
          unfold ParseConcat. rewrite Heqp.
          rewrite Henc, Henc__rest, Heqenc, Henc__xs.
          inversion Hot_ok as [Hot__enc]; symmetry in Hot__enc.
          apply IH with (rest__next := enc__x2) in Hx1_ok.
          - destruct (decide (Length (App enc__x1 enc__x2) < _)%nat).
            + rewrite Hx1_ok.
              destruct (decide (Length enc__x2 < _))%nat.
              * apply IH with (rest__next := []) in Hx2_ok.
                ** rewrite App_nil_r in Hx2_ok. rewrite Hx2_ok. reflexivity.
                ** rewrite Henc, Henc__rest, Heqenc, Henc__xs, Hot__enc. lia.
                ** done.
                ** split; first (destruct v2; simpl; word). 
                   split; last assumption.
                   unfold InnerTag in wf_it.
                   pose proof (ValEncLen_InnerTag v2) as Htag_v2.
                   lia.
              * rewrite !App_assoc, !App_Length, !Nat.add_assoc in n. unfold Length in n. simpl in n. lia.
            + rewrite !App_assoc, !App_Length, !Nat.add_assoc in n. unfold Length in n. simpl in n. lia.
          - rewrite Henc, Henc__rest, Heqenc, Henc__xs, Hot__enc.
            rewrite !App_assoc, !App_Length, !Nat.add_assoc. unfold Length. simpl. lia.
          - done.
          - split; first (destruct v1; simpl; word).
            split; last assumption.
            unfold InnerTag in wf_it. 
            pose proof (ValEncLen_InnerTag v1) as Htag_v1.
            lia.
        }
        specialize (Hser_len Hps_ok).
        apply (Hser_len _ rest) in Hrest_ok as Hser_ok.
        + unfold ParseMap. rewrite Hser_ok. reflexivity.
        + unfold SerialLen'_wf.
          apply SerialLen'Inversion in Hrest_ok as (enc__len & enc__pay & Hlen_ok & Hpay_ok & Henc__rest).
          rewrite Hpay_ok. rewrite Hlen_ok.
          split; last done.
          apply SerialConcatInversion in Hpay_ok as (enc__v1 & enc__v2 & Hv1_ok & Hv2_ok & Henc__pay).
          rewrite Heqs in Hv1_ok, Hv2_ok.
          destruct (decide _) in Hv1_ok;
            last (
                unfold SerialRecursiveProgressError in Hv1_ok;
                destruct (ValDepth _ == ValDepth _) in Hv1_ok; discriminate
              ).
          destruct (decide _) in Hv2_ok;
            last (
                unfold SerialRecursiveProgressError in Hv2_ok;
                destruct (ValDepth _ == ValDepth _) in Hv2_ok; discriminate
              ).
          rewrite Henc__pay, App_Length.
          unfold InnerTag in wf_it.
          pose proof (ValLen_Length v1 enc__v1 Hv1_ok) as Hv1_len.
          pose proof (ValLen_Length v2 enc__v2 Hv2_ok) as Hv2_len.
          lia.
    Qed.

  End Theorems.

End SimplParser.
