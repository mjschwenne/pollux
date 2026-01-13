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

    Definition ParseUnsigned : Parser Z := Map ParseByte word.unsigned.

    (* Parse n bytes into an unsigned integer *)
    Definition ParseZN (n : nat) := Map (RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                       (n + 8, new ≪ n + v))
                                         n (0, 0))
                                    (fun ret => let (_, z) := ret in z).

    Definition ParseZ32 := ParseZN 4%nat.

    Definition ParseBool : Parser bool := Map ParseUnsigned (fun z => z >? 0).

    Definition ParseBaseDesc : Parser Val :=
        ParseBind ParseUnsigned
          (fun z => match z with
                 | 0 => Map ParseZ32 (fun z => V_INT z)
                 | 1 => Map ParseBool (fun b => V_BOOL b)
                 | _ => ParseFailWith "Unknown field tag" Recoverable
                 end).

    Compute ParseBaseDesc [W8 1; W8 32; W8 0; W8 0; W8 0].
    Compute ParseBaseDesc [W8 0; W8 32; W8 0; W8 0; W8 0].

    Definition LenLimit {R : Type} (underlying : Parser R) : Parser R := 
      ParseBind ParseUnsigned
                (fun len => ParseLimit underlying (Z.to_nat len)).

    Definition ParseVal : Parser Val :=
           ParseRecursive (fun pd =>
                             ParseBind ParseUnsigned
                               (fun z => 
                                  match z with
                                  | 0 => ParseBaseDesc
                                  | 1 => LenLimit (Map (ParseConcat pd pd)
                                                    (fun vs => let (v1, v2) := vs in V_NEST v1 v2))
                                  | _ => ParseFailWith "Unknown tag" Recoverable
                                  end)).

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

    Definition SerialZ4 := SerialZN 4%nat.

    Compute SerialZ4 16777215.

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


    Definition SerialUnsigned : Serializer Z (fun z => 0 <= z < 0) :=
      fun z => SerialByte $ W8 z.

    About SerialBind.

    Definition Restrict {R : Type} {wf : R -> Prop} (ser : Serializer R wf) (new : R -> Prop) :
      Serializer R (fun r => new r /\ wf r) := ser.

    Definition SerialVal : Serializer Val serial_trivial_wf :=
      SerialRecursive
        (fun ser v => match v with
                   | V_BOOL b => SerialBind (fun _ => 0) (fun z => Restrict SerialUnsigned (fun z => z = 0))
                                  (SerialBind (fun _ => 1) (fun z => Restrict SerialUnsigned (fun z => z = 1))
                                     SerialBool) b
                   | V_INT z => SerialBind (fun _ => 0) (fun z => Restrict SerialUnsigned (fun z => z = 0))
                                  (SerialBind (fun _ => 0) (fun z => Restrict SerialUnsigned (fun z => z = 0))
                                     SerialZ4) z
                   | V_NEST v1 v2 => SerialBind (fun _ => 1) (fun z => Restrict SerialUnsigned (fun z => z = 1))
                                      (SerialLen SerialMsgLen $ SerialConcat ser ser)
                                      (v1, v2)
                   end) ValDepth.

    Definition SerialVal' : Serializer Val serial_trivial_wf :=
      SerialRecursive
        (fun ser v => match v with
             | V_BOOL b => SerialConcat SerialBlob SerialBool ([W8 0; W8 1], b)
             | V_INT z => SerialConcat SerialBlob SerialZ4 ([W8 0; W8 0], z)
             | V_NEST v1 v2 => SerialConcat SerialBlob
                                (SerialLen SerialMsgLen $ SerialConcat ser ser)
                                ([W8 1], (v1, v2))
             end) ValDepth.

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

    Theorem SimplParseOk : ParseOk (ParseVal) (SerialVal).
      unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
      intros x enc rest wf.

    Theorem SimplParseOk : forall (d : Desc), ParseOk (ParseDesc d) (SerialDesc' d).
    Proof.
      intros.
      unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
      induction d.
      - intros v enc rest wf_ok.
        destruct f eqn:Hf.
        + simpl in v. destruct v as (v__n, v__z). simpl in wf_ok.
          destruct wf_ok as [? wf_z]. subst. simpl.
          intro HSucc. invc HSucc.
          unfold ParseBind. simpl.
          change (uint.Z $ W8 0) with 0.
          unfold ParseBaseDesc, ParseBind. simpl.
          change (uint.Z $ W8 0) with 0.
          unfold ParseIntField, ParseBind. simpl. 
          repeat f_equal.
          unfold Z__next. rewrite ?Z.shiftr_shiftr; try done.
          comp_add.
          admit.
        + simpl in v. destruct v as (v__n, v__b). simpl in wf_ok. subst.
          unfold SerialDesc'. intros Hser. apply SerialConcatInversion in Hser.
          destruct Hser as (enc__tag & enc__bool & Htag & Hbool & Henc).
          apply (BoolParseOk _ _ rest) in Hbool; last easy.
          simpl in Htag. inversion Htag.
          subst. rewrite App_assoc. simpl.
          unfold ParseBind. simpl.
          change (uint.Z (W8 0)) with 0.
          simpl. unfold ParseBaseDesc.
          unfold ParseBind. simpl.
          change (uint.Z (W8 1)) with 1. simpl.
          unfold ParseBoolField.
          unfold ParseBind. rewrite Hbool.
          reflexivity.
      - intros v enc rest wf_ok.
        simpl in v. destruct v as (v1, v2).
        simpl in wf_ok. destruct wf_ok as [wf_v1 wf_v2].
        unfold SerialDesc'; fold SerialDesc'.
        unfold SerialConcat; simpl.
        unfold SerialLen.
        destruct (SerialDesc' d1 v1) as [v1_enc|] eqn:Hv1; last discriminate.
        destruct (SerialDesc' d2 v2) as [v2_enc|] eqn:Hv2; last discriminate.
        unfold SerialMsgLen; simpl.
        intro HSucc. invc HSucc.
        unfold ParseBind; simpl.
        change (uint.Z (W8 1)) with 1.
        unfold LenLimit, ParseBind; simpl.
        unfold ParseLimit.
    Abort.

  End Theorems.

End SimplParser.
