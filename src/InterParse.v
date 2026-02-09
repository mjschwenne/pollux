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

    (* v1 ⊆ v2 *)
    Fixpoint Subset (v1 v2 : Value) : bool :=
      match v1, v2 with
      | VALUE vs1, VALUE vs2 => map_fold (Subset__fold vs2) true vs1
      end
    with Subset__fold (vs : gmap Z Val) (k : Z) (v : Val) (acc : bool) : bool :=
           if negb acc then
             (* If we already know it isn't a subset, just feed forward *)
             acc
           else
             match vs !! k with
             | Some (V_BOOL b') => match v with
                                 | V_BOOL b => bool_eq b' b
                                 | _ => false
                                 end
             | Some (V_INT z') => match v with
                                | V_INT z => Z.eqb z' z
                                | _ => false
                                end
             | Some V_MISSING => match v with
                                | V_MISSING => true
                                | _ => false
                                end
             | Some (V_MSG v') => match v with
                                 | V_MSG v'' => Subset v'' v'
                                 | _ => false
                                 end
             | None => false
             end.

    Definition Eqb (v1 v2 : Value) : bool := andb (Subset v1 v2) (Subset v2 v1).

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

    Fixpoint Valid' (d : Desc) (v : Value) : Prop :=
      match d, v with
      | DESC fs, VALUE vs => map_fold (Valid'__fold fs) True vs
      end
    with Valid'__fold (fs : gmap Z Field) (k : Z) (v : Val) (acc : Prop) : Prop :=
           match v with
           | V_BOOL _ => fs !! k = Some F_BOOL /\ acc
           | V_INT _ => fs !! k = Some F_INT /\ acc
           | V_MSG value => (exists d, fs !! k = Some (F_MSG d) /\ Valid' d value) /\ acc
           | V_MISSING => True /\ acc (* While the True isn't needed, the uniform structure helps proofs *)
           end.

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

    Definition list_to_value (d : Desc) (vs : list (Z * Val)) : Value :=
      foldl Merge (Init d) vs.

    (* TODO: Rewrite to use list_to_map after filtering. Still won't add defaults... *)
    Definition ParseValue' (self : Desc -> P.Parser Value) (d : Desc) : Parser Value :=
      P.Map (P.Rep (ParseVal self d)) (fun vs => list_to_value d vs).

    Definition ParseValue (d : Desc) : Parser Value :=
      P.RecursiveState ParseValue' d.

    Definition enc2 := to_enc [1; 10;
                                    1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                               2; 0; 0; 0; 1].
    Definition enc2' := to_enc [1; 10;
                                    1; 0; 0; 0; 0; 2; 0; 0; 0; 0;
                               2; 0; 0; 0; 1;
                               (* Extra field, which is dropped *)
                               3; 0; 0; 0; 0].
    Compute ParseValue desc2 enc2.
    Compute ParseValue desc2 enc2'.
    Compute match ParseValue desc2 enc2, ParseValue desc2 enc2' with
            | P.Success v2 _, P.Success v2' _ => Eqb v2 v2'
            | _, _ => false
            end.

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
    Definition result3 := fst $ (P.Extract (ParseValue desc3 enc3) I).
    Compute Eqb result3 val3.
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
    Definition result3' := fst $ (P.Extract (ParseValue desc3 enc3') I).
    Compute Eqb result3' val3'.
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

    Fixpoint ValueDepth (v : Value) : nat :=
      match v with
      | VALUE vs => (map_fold ValueDepth__fold 0 vs)%nat
      end
    with ValueDepth__fold (k : Z) (v : Val) (acc : nat) :=
           match v with
           | V_BOOL _
           | V_INT _
           | V_MISSING => acc
           | V_MSG v' => acc `max` (ValueDepth v' + 1)
           end.

    Compute ValueDepth val1. 
    Compute ValueDepth val2.
    Compute ValueDepth val3.

    Fixpoint ValueEncLen (v : Value) : nat :=
      match v with
      | VALUE vs => (map_fold ValueEncLen__fold 0 vs)%nat
      end
    with ValueEncLen__fold (k : Z) (v : Val) (acc : nat) :=
           match v with
           | V_BOOL _ => (acc + 5)%nat
           | V_INT _ => (acc + 5)%nat
           | V_MISSING => acc
           | V_MSG v' => (acc + 2 + ValueEncLen v')%nat
           end.

    Fixpoint ValueEncLen' (d : Desc) (v : Value) : nat :=
      match v, d with
      | VALUE vs, DESC ds => (map_fold (ValueEncLen'__fold ds) 0 vs)%nat
      end
    with ValueEncLen'__fold (ds : gmap Z Field) (k : Z) (v : Val) (acc : nat) : nat :=
           match ds !! k, v with
           | None, _ => acc
           | Some _, V_BOOL _ => (acc + 5)%nat
           | Some _, V_INT _ => (acc + 5)%nat
           | Some (F_MSG d), V_MSG val => (acc + 2 + ValueEncLen' d val)%nat
           | Some _, _ => acc
           end.

    Compute ValueEncLen val1.
    Example Length1 : ValueEncLen val1 = length fenc3.
    Proof. reflexivity. Qed.

    Compute ValueEncLen val2.
    Example Length2 : ValueEncLen val2 = length enc2.
    Proof. reflexivity. Qed.

    Compute ValueEncLen val3.
    Example Length3 : ValueEncLen val3 = length enc3.
    Proof. reflexivity. Qed.

    Compute ValueEncLen val3'.
    Example Length3' : ValueEncLen val3' = length enc3'.
    Proof. reflexivity. Qed.

    Definition Value_wf (v : Value) : Prop := True.
    Definition Val_wf (v : Z * Val) : Prop := True.

    Definition SerialVal (serial__msg : Desc -> S.Serializer Value Value_wf) (d : Desc) :
      Serializer (Z * Val) Val_wf := 
      fun val => let (id, v) := val in
              match (Fields d) !! id with
              | Some F_BOOL => match v with
                              | V_BOOL b => S.Bind' (fun _ => id) SerialUnsigned SerialBool b
                              | V_MISSING => S.Success []
                              | _ => S.Failure S.Failure.Recoverable
                                      (S.Failure.mkData "Expected Boolean" Input_default None)
                              end
              | Some F_INT => match v with
                             | V_INT z => S.Bind' (fun _ => id) SerialUnsigned SerialZ32 z
                             | V_MISSING => S.Success []
                             | _ => S.Failure S.Failure.Recoverable
                                     (S.Failure.mkData "Expected Integer" Input_default None)
                             end
              | Some (F_MSG d') => match v with
                                  | V_MSG z => S.Bind' (fun _ => id) SerialUnsigned
                                                      (S.Len' SerialNat (serial__msg d')) z
                                  | V_MISSING => S.Success []
                                  | _ => S.Failure S.Failure.Recoverable
                                          (S.Failure.mkData "Expected nested message" Input_default None)
                                  end
              | None => S.Success Input_default
              end.

    Definition ValList (v : Value) : list (Z * Val) :=
      map_to_list (Vals v).
      
    Definition SerialValue' (self : Desc -> Serializer Value Value_wf) (d : Desc) : Serializer Value Value_wf :=
      S.Map (S.Rep (SerialVal self d : S.Serializer _ Val_wf)) ValList.

    Definition SerialValue (d : Desc) : Serializer Value Value_wf :=
      S.RecursiveState SerialValue' ValueDepth d.

    Definition enc_eq (d : Desc) (v : Value) (e : Input) : bool :=
      match SerialValue d v with
      | S.Success enc => if decide (enc = e) then true else false
      | S.Failure _ _ => false
      end.

    Definition round_trip (d : Desc) (v : Value) : bool :=
      match SerialValue d v with
      | S.Success enc => match ParseValue d enc with
                        | P.Success v' _ => Eqb v v'
                        | P.Failure _ _ => false
                        end
      | S.Failure _ _ => false
      end.

    Definition check_multi_enc (d : Desc) (enc1 enc2 : Input) : bool :=
      match ParseValue d enc1, ParseValue d enc2 with
      | P.Success v1 _, P.Success v2 _ => Eqb v1 v2
      | _, _ => false
      end.

    Compute SerialValue desc1 val1.
    Compute round_trip desc1 val1.
    Compute check_multi_enc desc1
      (to_enc [1; 0; 0; 0; 0; 2; 0; 0; 0; 0])
      (to_enc [2; 0; 0; 0; 0; 1; 0; 0; 0; 0]).

    Compute SerialValue desc2 val2.
    Compute round_trip desc2 val2.

    Compute SerialValue desc3 val3.
    Compute round_trip desc3 val3.

    Compute SerialValue desc3 val3'.
    Compute round_trip desc3 val3'.
    
    Example LengthOk1 :
      forall enc, SerialValue desc1 val1 = S.Success enc -> ValueEncLen val1 = Length enc.
    Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

    Example LengthOk2 :
      forall enc, SerialValue desc2 val2 = S.Success enc -> ValueEncLen val2 = Length enc.
    Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

    Example LengthOk3 :
      forall enc, SerialValue desc3 val3 = S.Success enc -> ValueEncLen val3 = Length enc.
    Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.

    Example LengthOk3' :
      forall enc, SerialValue desc3 val3' = S.Success enc -> ValueEncLen val3' = Length enc.
    Proof. vm_compute. intros x' H. inversion H. reflexivity. Qed.
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

    Lemma ValidBool (d : Desc) (vs : gmap Z Val) :
      forall z b, Valid d (VALUE (<[z := V_BOOL b]> vs)) -> 
             Fields d !! z = Some F_BOOL.
    Proof.
      intros z b. destruct d.
      induction fs as [| z__d f__d fs Hno Hfst] using map_first_key_ind.
      - vm_compute. intros _. admit.
      - unfold Valid. rewrite map_fold_insert_first_key by assumption.
        simpl.
        Admitted.

    Lemma ValidDropFirst (d : Desc) :
      forall z v vs,
      vs !! z = None -> map_first_key (<[z := v]> vs) z ->
      Valid' d (VALUE $ <[z := v]> vs) -> Valid' d (VALUE vs).
    Proof.
      intros z v vs Hno Hfst. destruct d.
      unfold Valid' at 1; simpl.
      rewrite map_fold_insert_first_key by assumption.
      destruct v eqn:Hv; intros (_ & H); done.
    Qed.

    Lemma ValueDepthDropFirst :
      forall z v vs,
      vs !! z = None -> map_first_key (<[z := v]> vs) z ->
      (forall v', v <> V_MSG v') ->
      ValueDepth (VALUE $ <[z := v]> vs) = ValueDepth (VALUE vs).
    Proof.
      intros z v vs Hno Hfst HnotMsg.
      destruct v; first (specialize (HnotMsg v); contradiction).
      all: (
             unfold ValueDepth at 1;
             rewrite map_fold_insert_first_key by assumption;
             reflexivity
           ).
    Qed.

    Lemma ValueDepthDropFirstMsg :
      forall z v vs,
      vs !! z = None -> map_first_key (<[z := V_MSG v]> vs) z ->
      (ValueDepth (VALUE vs) <= ValueDepth (VALUE $ <[z := V_MSG v]> vs))%nat.
    Proof.
      intros z v vs Hno Hfst.
      unfold ValueDepth at 2.
      rewrite map_fold_insert_first_key by assumption.
      fold (ValueDepth (VALUE vs)).
      fold (ValueDepth v).
      lia.
    Qed.

    Lemma ValueEncLength_Length (d : Desc) (v : Value) :
      forall enc,
      Valid' d v ->
      SerialValue d v = S.Success enc ->
      Length enc = ValueEncLen' d v.
    Proof.
      destruct v.
      unfold SerialValue, S.RecursiveState.
      rewrite ser_recur_st_unfold. unfold SerialValue', S.Map, S.Rep.
      revert d.
      induction vs as [| z v m Hno Hfst] using map_first_key_ind.
      - intros d enc Hvalid Hser.
        vm_compute in Hser. inversion Hser.
        destruct d. reflexivity.
      - intros d enc Hvalid.
        unfold ValList, Vals.
        rewrite map_to_list_insert_first_key by assumption.
        rewrite ser_rep'_unfold.
        destruct v as [v' | b | z' |] eqn:Hv.
        + simpl. destruct d.
          destruct (Fields (DESC fs) !! z) eqn:Hf.
          * destruct f.
            -- destruct (S.Bind' _ _ _ v') eqn:Hv'; last (destruct (S.rep' _ (map_to_list m)); discriminate). 
               destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               pose proof (ValueDepthDropFirstMsg z v' m Hno Hfst) as Hv__drop.
               admit.
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
          * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
            admit.
        + simpl. destruct d.
          destruct (Fields (DESC fs) !! z) eqn:Hf.
          * destruct f.
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
            -- destruct (S.Bind' _ _ _ b) eqn:Hb; last (destruct (S.rep' _ (map_to_list m)); discriminate).
               destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               intros Henc. invc Henc.
               rewrite App_Length.
               unfold S.Bind' in Hb.
               rewrite SerialConcatInversion in Hb.
               destruct Hb as (enc__id & enc__b & Hok__id & Hok__b & Henc__f).
               unfold SerialUnsigned, SerialByte in Hok__id.
               vm_compute in Hok__b.
               pose proof (ValidDropFirst (DESC fs) z (V_BOOL b) m Hno Hfst Hvalid) as Hv__drop.
               assert (forall v', V_BOOL b <> V_MSG v') as Hneq by done.
               pose proof (ValueDepthDropFirst z (V_BOOL b) m Hno Hfst Hneq) as Hd__drop.
               simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
               unfold S.RecursiveProgressError in Hser, IHvs.
               simpl in Hser.
               rewrite Hd__drop in Hser.
               specialize (IHvs (DESC fs) out0 Hv__drop Hser).
               destruct b; (
                             rewrite Henc__f, App_Length; invc Hok__id; invc Hok__b;
                             unfold Length; simpl;
                             rewrite map_fold_insert_first_key by assumption;
                             simpl in *; rewrite Hf, <- IHvs; unfold Length; lia
                           ).
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
          * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
            pose proof (ValidDropFirst (DESC fs) z (V_BOOL b) m Hno Hfst Hvalid) as Hv__drop.
            assert (forall v', V_BOOL b <> V_MSG v') as Hneq by done.
            pose proof (ValueDepthDropFirst z (V_BOOL b) m Hno Hfst Hneq) as Hd__drop.
            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
            unfold S.RecursiveProgressError in Hser, IHvs.
            simpl in Hser.
            rewrite Hd__drop in Hser.
            specialize (IHvs (DESC fs) out Hv__drop Hser).
            intros Henc'. invc Henc'.
            rewrite map_fold_insert_first_key by assumption.
            simpl in *. rewrite Hf. assumption.
        + simpl. destruct d.
          destruct (Fields (DESC fs) !! z) eqn:Hf.
          * destruct f.
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
            -- destruct (S.rep' _ (map_to_list m)); discriminate.
            -- destruct (S.Bind' _ _ _ z') eqn:Hz'; last (destruct (S.rep' _ (map_to_list m)); discriminate).
               destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               intros Henc. invc Henc.
               rewrite App_Length.
               unfold S.Bind' in Hz'.
               rewrite SerialConcatInversion in Hz'.
               destruct Hz' as (enc__id & enc__z' & Hok__id & Hok__z' & Henc__f).
               unfold SerialUnsigned, SerialByte in Hok__id.
               pose proof (ValidDropFirst (DESC fs) z (V_INT z') m Hno Hfst Hvalid) as Hv__drop.
               assert (forall v', V_INT z' <> V_MSG v') as Hneq by done.
               pose proof (ValueDepthDropFirst z (V_INT z') m Hno Hfst Hneq) as Hd__drop.
               simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
               unfold S.RecursiveProgressError in Hser, IHvs.
               simpl in Hser.
               rewrite Hd__drop in Hser.
               specialize (IHvs (DESC fs) out0 Hv__drop Hser).
               rewrite Henc__f, App_Length. invc Hok__id. invc Hok__z'.
               unfold Length; simpl.
               rewrite map_fold_insert_first_key by assumption.
               simpl in *; rewrite Hf, <- IHvs; unfold Length. lia.
          * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
            pose proof (ValidDropFirst (DESC fs) z (V_INT z') m Hno Hfst Hvalid) as Hv__drop.
            assert (forall v', V_INT z' <> V_MSG v') as Hneq by done.
            pose proof (ValueDepthDropFirst z (V_INT z') m Hno Hfst Hneq) as Hd__drop.
            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
            unfold S.RecursiveProgressError in Hser, IHvs.
            simpl in Hser.
            rewrite Hd__drop in Hser.
            specialize (IHvs (DESC fs) out Hv__drop Hser).
            intros Henc'. invc Henc'.
            rewrite map_fold_insert_first_key by assumption.
            simpl in *. rewrite Hf. assumption.
        + simpl. destruct (Fields d !! z).
          * destruct f.
            -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               destruct d.
               pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop.
               assert (forall v', V_MISSING <> V_MSG v') as Hneq by done.
               pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop.
               simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
               unfold S.RecursiveProgressError in Hser, IHvs.
               simpl in Hser.
               rewrite Hd__drop in Hser.
               specialize (IHvs (DESC fs) out Hv__drop Hser).
               intros Henc'. invc Henc'.
               rewrite map_fold_insert_first_key by assumption.
               simpl in *. destruct (fs !! z); last assumption.
               destruct f; assumption.
            -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               destruct d.
               pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop.
               assert (forall v', V_MISSING <> V_MSG v') as Hneq by done.
               pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop.
               simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
               unfold S.RecursiveProgressError in Hser, IHvs.
               simpl in Hser.
               rewrite Hd__drop in Hser.
               specialize (IHvs (DESC fs) out Hv__drop Hser).
               intros Henc'. invc Henc'.
               rewrite map_fold_insert_first_key by assumption.
               simpl in *. destruct (fs !! z); last assumption.
               destruct f; assumption.
            -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
               destruct d.
               pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop.
               assert (forall v', V_MISSING <> V_MSG v') as Hneq by done.
               pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop.
               simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
               unfold S.RecursiveProgressError in Hser, IHvs.
               simpl in Hser.
               rewrite Hd__drop in Hser.
               specialize (IHvs (DESC fs) out Hv__drop Hser).
               intros Henc'. invc Henc'.
               rewrite map_fold_insert_first_key by assumption.
               simpl in *. destruct (fs !! z); last assumption.
               destruct f; assumption.
          * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate.
            destruct d.
            pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop.
            assert (forall v', V_MISSING <> V_MSG v') as Hneq by done.
            pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop.
            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser.
            unfold S.RecursiveProgressError in Hser, IHvs.
            simpl in Hser.
            rewrite Hd__drop in Hser.
            specialize (IHvs (DESC fs) out Hv__drop Hser).
            intros Henc'. invc Henc'.
            rewrite map_fold_insert_first_key by assumption.
            simpl in *. destruct (fs !! z); last assumption.
            destruct f; assumption.
    Admitted.

  End Theorems.

End InterParse.
