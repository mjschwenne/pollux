(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Input.
From Pollux Require Import Failure.
From Pollux Require Import Parser.
From Pollux Require Import Serializer.
From Pollux Require Import Theorems.

Open Scope Z_scope.

Module InterParse.
  Module F := Failures(ByteInput).
  Module P := Parsers(ByteInput).
  Module S := Serializers(ByteInput).
  Module T := Theorems(ByteInput).
  Import ByteInput.
  Import T.

  (*** Intermediate Complexity Format *)

  (*
    This format is designed to build on what I've learned from the simple recursive format
    (SimplParse.v) by adding these features:
    - Encoding uses tagged key-value pairs which can be read in any order
    - Uses a single default value for everything / supports optional fields
    - Does not accept repeated fields
    - Drops unknown fields without error

    All of these features will be required for protobuf, and will mandate using the RecursiveState 
    combinator to have access to and change the descriptor during the parsing / serializing process.
   *)

  Section Desc.

    (* A descriptor is a primitive or a map from w8 to descriptor *)
    Inductive Desc' : Set := 
    | D_BOOL
    | D_INT
    | D_NEST (fields : gmap Z Desc').

    (* The "problem" with this definition is that it combines incomplete
     primitive fields with nested ones, i.e. we can have D_BOOL as a stand-alone
     descriptor but that can't be serialized without knowing what the field
     number is. *)

    Inductive Desc : Set := DESC (fs : gmap Z Field)
    with
      Field :=
    | F_MSG (d : Desc)
    | F_BOOL
    | F_INT.
    
    Definition Fields (d : Desc) : gmap Z Field :=
      match d with
      | DESC fs => fs
      end.
    
    (* Instead, use a mutually recursive type so that fields and descriptors
     (fields with an identifier) are distinct. *)

    Inductive Value : Set := VALUE (vs : gmap Z Val)
    with
      Val :=
    | V_MSG (v : Value)
    | V_BOOL (b : bool)
    | V_INT (b : Z)
    | V_MISSING.

    Definition Vals (v : Value) : gmap Z Val :=
      match v with
      | VALUE vs => vs
      end.

    (* We will also need be able to make an empty value for each descriptor *)

    Fixpoint Init (d : Desc) : Value :=
      match d with
      | DESC fs => VALUE $ map_fold (Init__fold) gmap_empty fs
      end
    with Init__fold (k : Z) (f : Field) (acc : gmap Z Val) : gmap Z Val :=
           match f with
           | F_MSG d => <[ k := V_MSG (Init d) ]> acc
           | _ => <[ k := V_MISSING ]> acc
           end.

    (* Fixpoint Eqb (v1 v2 : Value) : bool := *)
    (*   match v1, v2 with *)
    (*   | VALUE vs1, VALUE vs2 => andb (map_fold (Eqb__fold vs1) true vs2) *)
    (*                                 (map_fold (Eqb__fold vs2) true vs1) *)
    (*   end *)
    (* with Eqb__fold (vs : gmap Z Val) (k : Z) (v : Val) (acc : bool) : bool := *)
    (*        if negb acc then *)
    (*          (* If we already know it isn't a subset, just feed forward *) *)
    (*          acc *)
    (*        else *)
    (*          match vs !! k with *)
    (*          | Some (V_BOOL b') => match v with *)
    (*                              | V_BOOL b => bool_eq b' b *)
    (*                              | _ => false *)
    (*                              end *)
    (*          | Some (V_INT z') => match v with *)
    (*                             | V_INT z => Z.eqb z' z *)
    (*                             | _ => false *)
    (*                             end *)
    (*          | Some V_MISSING => match v with *)
    (*                             | V_MISSING => true *)
    (*                             | _ => false *)
    (*                             end *)
    (*          | Some (V_MSG v') => match v with *)
    (*                              | V_MSG v'' => Eqb v' v'' *)
    (*                              | _ => false *)
    (*                              end *)
    (*          | None => false *)
    (*          end. *)
    (* FIXME: Error: Cannot guess decreasing argument of fix. *)

    (* Define a Value type which matches the structure of the descriptor, with
     an extra option for missing values, which will also be used as a default
     value when creating an empty value. *)
    
    (* Now in order to use the RecursiveState combinator we need a proposition
     linking a Value to it's Descriptor. Valid : Desc -> Value -> Prop *)

    (* Specifically, this requires that each field in the descriptor exists in
     the value, has the correct type and isn't missing. Values are allowed to have
     more fields than the descriptor under this definition. That should be OK, since
     those unknown fields will be dropped during the parsing process. *)

    Fixpoint Valid (d : Desc) (v : Value) : Prop :=
      match d, v with
      | DESC fs, VALUE vs => map_fold (Valid__fold vs) True fs
      end
    with Valid__fold (vs : gmap Z Val) (k : Z) (f : Field) (acc : Prop) : Prop :=
           match f with
           | F_BOOL => acc /\ exists b, vs !! k = Some (V_BOOL b)
           | F_INT => acc /\ exists z, vs !! k = Some (V_INT z)
           | F_MSG d => acc /\ exists v, vs !! k = Some (V_MSG v) /\ Valid d v
           end.
    Opaque Valid.

    Definition desc1 := DESC (list_to_map [
                                  (1, F_BOOL);
                                  (2, F_INT)
                          ]).
    Definition val1 := VALUE (list_to_map [
                                  (1, V_BOOL false);
                                  (2, V_INT 0)
                         ]).

    Lemma test_valid1 : Valid desc1 val1.
    Proof.
      vm_compute. rewrite ?Logic.and_assoc.
      split; first trivial.
      split; first (exists false; reflexivity).
      exists 0; reflexivity.
    Qed.

    Compute Init desc1.

    Definition desc2 := DESC (list_to_map [
                                  (1, F_MSG desc1);
                                  (2, F_BOOL)
                          ]).
    Definition val2 := VALUE (list_to_map [
                                (1, V_MSG val1);
                                (2, V_BOOL false)
                         ]).
    Lemma test_valid2 : Valid desc2 val2.
    Proof.
      vm_compute.
      rewrite ?Logic.and_assoc.
      split; first trivial.
      split; last (exists false; reflexivity).
      exists val1. split; first reflexivity.
      apply test_valid1.
    Qed.

    Compute Init desc2.

  End Desc.

  (** Encoding format *)

  (*
    Both integer and boolean fields will be encoded into a 4-byte integer so that the descriptor is
    required to cast them into the correct final form.

    Each primitive field is tagged with the field number as a 1-byte integer, then the 4-byte payload.

    Nested messages still start with a 1-byte field number, and then are followed with a 4-byte length
    which represents the total encoding length of the nested message.

    Many of the low-level parsers, bytes, integers, bools, etc are taken from SimplParse.v.
   *)

  Definition to_enc (l : list Z) : list byte := map (fun n => W8 n) l.

  Section Parse.
    Definition ParseByte : P.Parser byte :=
      fun inp => match inp with
              | byt :: rest => P.Success byt rest
              | [] => P.Failure P.Failure.Recoverable (P.Failure.mkData "No more data to parse" inp None)
              end.

    Definition ParseUnsigned : P.Parser Z := P.Map ParseByte word.unsigned.

    Definition ParseNat : Parser nat := P.Map ParseByte (fun b => Z.to_nat $ word.unsigned b).

    (* Parse n bytes into an unsigned integer *)
    Definition ParseZN (n : nat) := P.Map (P.RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                       (n + 8, new ≪ n + v))
                                         n (0, 0))
                                    (fun ret => let (_, z) := ret in z).

    Definition ParseZ32 := ParseZN 4%nat.

    Definition ParseBool : Parser bool := P.Map ParseZ32 (fun z => z >? 0).

    Definition ParseVal (parse__msg : Desc -> Parser Value) (d : Desc) : Parser (Z * Val) :=
      P.Bind ParseUnsigned
        (fun z =>
           match (Fields d) !! z with
           | Some f => match f with
                      | F_BOOL => P.Map ParseBool (fun b => (z, V_BOOL b))
                      | F_INT => P.Map ParseZ32 (fun z' => (z, V_INT z'))
                      | F_MSG d' => P.Map (P.Len ParseNat $ parse__msg d') (fun v => (z, V_MSG v))
                      end
           | None => P.SucceedWith (z, V_MISSING)
           end).

    Definition dummy_msg_parser := fun _ : Desc => P.SucceedWith (VALUE $ gmap_empty).

    Definition fenc1 := to_enc [1; 0; 0; 0; 0].
    Compute ParseVal dummy_msg_parser desc1 fenc1.

    Definition fenc2 := to_enc [2; 255; 255; 255; 0].
    Compute ParseVal dummy_msg_parser desc1 fenc2.

    Definition fenc3 := to_enc [1; 8; 0; 0; 0; 0; 0; 0; 0; 0].
    Compute ParseVal dummy_msg_parser desc2 fenc3.

    Definition Merge (acc : Value) (new : Z * Val) : Value :=
      let (id, val) := new in
      (* Only update if the field is already present to drop bad fields *)
      match (Vals acc) !! id with
      | Some _ => VALUE $ <[ id := val ]> (Vals acc)
      | None => acc
      end.

    Definition ParseValue' (self : Desc -> P.Parser Value) (d : Desc) : Parser Value :=
      P.Rep (ParseVal self d) Merge (Init d).

    Definition ParseValue (d : Desc) : Parser Value :=
      P.RecursiveState ParseValue' d.

    Definition enc2 := to_enc [1; 8; 0; 0; 0; 0; 0; 0; 0; 0;
                               2; 0; 0; 0; 1;
                               (* Extra field, which is dropped *)
                               3; 0; 0; 0; 0].
    Compute ParseValue desc2 enc2.

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
                                  (3, V_MSG $ VALUE (list_to_map [
                                                         (1, V_MSG val1);
                                                         (2, V_BOOL true)
                                  ]))
                         ]).
    Definition enc3 := to_enc [
                           1; 255; 255; 255; 0;
                           2; 0; 0; 0; 1;
                           3; 10;
                                1; 0; 0; 0; 1;
                                2; 84; 14; 0; 0;
                           4; 15;
                                1; 8; 0; 0; 0; 0; 0; 0; 0; 0;
                                2; 0; 0; 0; 1
                         ].
    Definition result3 := fst $ P.Extract (ParseValue desc3 enc3) I.
    Compute decide (result3 = val3).
  End Parse.

  Section Serial.
    Definition SerialByte : S.Serializer byte S.Trivial_wf :=
      fun b => S.Success [b].

    Definition SerialUnsigned : S.Serializer Z (fun z => 0 <= z < 256) :=
      fun z => SerialByte $ W8 z.

    Definition SerialNat : S.Serializer nat (fun n => (0 <= n < 256)%nat) :=
      fun n => SerialByte $ W8 (Z.of_nat n).

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

    Definition SerialZ_wf (n : nat) (z : Z) : Prop :=
      (0 <= z < 2^(8 * Z.of_nat n)).

    Definition SerialZN (n : nat) : S.Serializer Z (SerialZ_wf n) :=
      fun z => S.Rep SerialByte (Z_to_list z n).

    Definition SerialZ32 := SerialZN 4%nat.

    Definition SerialBool : S.Serializer bool S.Trivial_wf :=
      fun b => if b then
              SerialZ32 1
            else
              SerialZ32 0.

  End Serial.

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

    Theorem UnsignedParseOk : ParseOk ParseUnsigned SerialUnsigned.
    Proof.
      intros x enc rest wf.
      unfold SerialUnsigned, SerialByte.
      intros H. invc H.
      unfold ParseUnsigned, P.Map.
      simpl. f_equal. word.
    Qed.

    Theorem NatParseOk : ParseOk ParseNat SerialNat.
    Proof.
      intros x enc rest wf.
      unfold SerialNat, SerialByte.
      intros H. invc H.
      unfold ParseNat, P.Map.
      simpl. f_equal. word.
    Qed.

    Theorem Z32ParseOk : ParseOk ParseZ32 SerialZ32.
    Proof.
    Admitted.

    Theorem BoolParseOk : ParseOk ParseBool SerialBool.
    Proof.
      intros x enc rest _.
      destruct x.
      - unfold SerialBool. intro H. invc H.
        vm_compute. reflexivity.
      - unfold SerialBool. intro H. invc H.
        vm_compute. reflexivity.
    Qed.

  End Theorems.

End InterParse.
