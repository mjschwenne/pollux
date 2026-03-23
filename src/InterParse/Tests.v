(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux.parse Require Import Input.
From Pollux.InterParse Require Import Descriptor.
From Pollux.InterParse Require Import Parser.
From Pollux.InterParse Require Import Serializer.
From Pollux.parse Require Import Castor.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Import Descriptor.
Import Parser.C.
Import Parser.
Import Serializer.

(*** Tests *)

(*! Descriptor Tests *)
Section DescTests.
  Definition desc1 := DESC (list_to_map [
                                (1, F_BOOL);
                                (2, F_INT)
                        ]).
  Definition val1 := VALUE (list_to_map [
                                (1, V_BOOL false);
                                (2, V_INT 0)
                       ]).

  Example test_valid1 : Valid desc1 val1.
  Proof.
    vm_compute. rewrite ?Logic.and_assoc.
    split; first trivial.
    split; first (exists false; reflexivity).
    exists 0; reflexivity.
  Qed.

  Definition init1 := VALUE $ list_to_map [(1, V_MISSING); (2, V_MISSING)].
  Example test_init1 : Init desc1 = init1.
  Proof. vm_compute; reflexivity. Qed.

  Definition desc2 := DESC (list_to_map [
                                (1, F_MSG desc1);
                                (2, F_BOOL)
                        ]).
  Definition val2 := VALUE (list_to_map [
                                (1, V_MSG val1);
                                (2, V_BOOL false)
                       ]).
  Example test_valid2 : Valid desc2 val2.
  Proof.
    vm_compute.
    rewrite ?Logic.and_assoc.
    split; first trivial.
    split; last (exists false; reflexivity).
    exists val1. split; first reflexivity.
    apply test_valid1.
  Qed.

  Definition init2 := VALUE $ list_to_map [(1, V_MSG init1); (2, V_MISSING)].
  Example test_init2 : Init desc2 = init2.
  Proof. vm_compute; reflexivity. Qed.
End DescTests.

(*! Parser Tests *)

Section ParserTests.
  Definition dummy_msg_parser := fun _ : Desc => P.SucceedWith (VALUE $ gmap_empty).

  Definition fenc1 := to_enc [1; 0; 0; 0; 0].
  Example parse_val1 : ParseVal dummy_msg_parser desc1 fenc1 = Success (1, V_BOOL false) [].
  Proof. vm_compute; reflexivity. Qed.

  Definition fenc2 := to_enc [2; 255; 255; 255; 0].
  Example parse_val2 : ParseVal dummy_msg_parser desc1 fenc2 = Success (2, V_INT 16777215) [].
  Proof. vm_compute; reflexivity. Qed.

  Definition fenc3 := to_enc [1; 8; 0; 0; 0; 0; 0; 0; 0; 0].
  Example parse_val3 : ParseVal dummy_msg_parser desc2 fenc3 =
                       Success (1, V_MSG (VALUE ∅)) $
                         ToInput $ to_enc [0; 0; 0; 0; 0; 0; 0; 0].
  Proof. vm_compute; reflexivity. Qed.

  Definition enc2 := to_enc [1; 10;
                             1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                             2; 0; 0; 0; 0].
  Definition enc2' := to_enc [1; 10;
                              1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                              2; 0; 0; 0; 0;
                              (* Extra field, which is dropped *)
                              3; 0; 0; 0; 0].

  Example parse_value1 : ParseValue desc2 enc2 = Success val2 [].
  Proof. vm_compute; reflexivity. Qed.
  Example parse_value2 : ParseValue desc2 enc2' = Success val2 [].
  Proof. vm_compute; reflexivity. Qed.
  Example parse_value3 : ParseValue desc2 enc2' = ParseValue desc2 enc2.
  Proof. vm_compute; reflexivity. Qed.

  Definition desc3 := DESC (list_to_map [
                                (1, F_INT);
                                (2, F_BOOL);
                                (3, F_MSG desc1);
                                (4, F_MSG desc2)
                        ]).
  Definition val3 := VALUE (list_to_map [
                                (1, V_INT 16777215);
                                (2, V_BOOL false);
                                (3, V_MSG $ VALUE (list_to_map [
                                                       (1, V_BOOL true);
                                                       (2, V_INT 3668)
                                ]));
                                (4, V_MSG $ VALUE (list_to_map [
                                                       (1, V_MSG val1);
                                                       (2, V_BOOL true)
                                ]))
                       ]).
  Definition enc3 := to_enc [
                         1; 255; 255; 255; 0;
                         2; 0; 0; 0; 0;
                         3; 10;
                         1; 0; 0; 0; 1;
                         2; 84; 14; 0; 0;
                         4; 17;
                         1; 10;
                         1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                         2; 0; 0; 0; 1
                       ].
  Definition result3 := fst $ (Extract (ParseValue desc3 enc3) I).
  Example parse_value4 : result3 = val3.
  Proof. vm_compute; reflexivity. Qed.

  Definition val3' := VALUE (list_to_map [
                                 (1, V_INT 16777215);
                                 (2, V_MISSING);
                                 (3, V_MSG $ VALUE (list_to_map [
                                                        (1, V_BOOL true);
                                                        (2, V_MISSING)
                                 ]));
                                 (4, V_MSG $ VALUE (list_to_map [
                                                        (1, V_MSG val1);
                                                        (2, V_BOOL true)
                                 ]))
                        ]).
  Definition enc3' := to_enc [
                          1; 255; 255; 255; 0;
                          3; 5;
                          1; 0; 0; 0; 1;
                          4; 17;
                          1; 10;
                          1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                          2; 0; 0; 0; 1
                        ].
  Definition result3' := fst $ (Extract (ParseValue desc3 enc3') I).
  Example parse_value5 : result3' = val3'.
  Proof. vm_compute; reflexivity. Qed.
End ParserTests.

(*! Serializer Tests *)
Section SerializerTests.
  Example depth1 : ValueDepth val1 = 0%nat. 
  Proof. vm_compute; reflexivity. Qed.
  Example depth2 : ValueDepth val2 = 1%nat.
  Proof. vm_compute; reflexivity. Qed.
  Example depth3 : ValueDepth val3 = 2%nat.
  Proof. vm_compute; reflexivity. Qed.

  Example Length1 : ValueEncLen val1 = length fenc3.
  Proof. reflexivity. Qed.

  Example Length2 : ValueEncLen val2 = length enc2.
  Proof. reflexivity. Qed.

  Example Length3 : ValueEncLen val3 = length enc3.
  Proof. reflexivity. Qed.

  Example Length3' : ValueEncLen val3' = length enc3'.
  Proof. reflexivity. Qed.

  Definition enc_eq (d : Desc) (v : Value) (e : Input) : bool :=
    match SerialValue d v with
    | Success _ enc => if decide (enc = e) then true else false
    | Failure _ _ => false
    end.

  Definition round_trip (d : Desc) (v : Value) : Prop :=
    match SerialValue d v with
    | Success _ enc => match ParseValue d enc with
                      | Parser.C.R.Success v' _ => v = v'
                      | Parser.C.R.Failure _ _ => False
                      end
    | Failure _ _ => False
    end.

  Definition check_multi_enc (d : Desc) (enc1 enc2 : Input) : Prop :=
    match ParseValue d enc1, ParseValue d enc2 with
    | Parser.C.R.Success v1 _, Parser.C.R.Success v2 _ => v1 = v2
    | _, _ => False
    end.

  Example serial_value1 : SerialValue desc1 val1 = S.mkSuccess $ to_enc [2; 0; 0; 0; 0; 1; 0; 0; 0; 0].
  Proof. reflexivity. Qed.
  Example serial_value_rt1 : round_trip desc1 val1.
  Proof. vm_compute; reflexivity. Qed.
  Example serial_value_me1 : check_multi_enc desc1
                               (to_enc [1; 0; 0; 0; 0; 2; 0; 0; 0; 0])
                               (to_enc [2; 0; 0; 0; 0; 1; 0; 0; 0; 0]).
  Proof. vm_compute; reflexivity. Qed.

  Example serial_value2 : SerialValue desc2 val2 =
                          S.mkSuccess $ to_enc
                            [2; 0; 0; 0; 0; 1; 10; 2; 0; 0; 0; 0; 1; 0; 0 ; 0; 0].
  Proof. vm_compute; reflexivity. Qed.
  Example serial_value_rt2 : round_trip desc2 val2.
  Proof. vm_compute; reflexivity. Qed.

  Example serial_value3 : SerialValue desc3 val3 =
                          S.mkSuccess $ to_enc
                            [3; 10; 2; 84; 14; 0; 0; 1; 1; 0; 0; 0; 4;
                             17; 2; 1; 0; 0; 0; 1; 10; 2; 0; 0; 0; 0;
                             1; 0; 0; 0; 0; 2; 0; 0; 0; 0; 1; 255; 255; 255; 0].
  Proof. vm_compute; reflexivity. Qed.
  Example serial_value_rt3 : round_trip desc3 val3.
  Proof. vm_compute; reflexivity. Qed.

  Example serial_value4 : SerialValue desc3 val3' =
                          S.mkSuccess $ to_enc
                            [3; 5; 1; 1; 0; 0; 0; 4; 17; 2; 1; 0; 0; 0;
                             1; 10; 2; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1;
                             255; 255; 255; 0].
  Proof. vm_compute; reflexivity. Qed.
  Example serial_value_rt4 : round_trip desc3 val3'.
  Proof. vm_compute; reflexivity. Qed.
  
  Example LengthOk1 :
    forall enc, SerialValue desc1 val1 = S.mkSuccess enc -> ValueEncLen val1 = Length enc.
  Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

  Example LengthOk2 :
    forall enc, SerialValue desc2 val2 = S.mkSuccess enc -> ValueEncLen val2 = Length enc.
  Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

  Example LengthOk3 :
    forall enc, SerialValue desc3 val3 = S.mkSuccess enc -> ValueEncLen val3 = Length enc.
  Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

  Example LengthOk3' :
    forall enc, SerialValue desc3 val3' = S.mkSuccess enc -> ValueEncLen val3' = Length enc.
  Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.
End SerializerTests.
