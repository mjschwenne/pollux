(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Input.
From Pollux Require Import Result.
From Pollux Require Import Parser.
From Pollux Require Import Serializer.
From Pollux Require Import Theorems.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Module InterParse.
  Module R := Result(ByteInput).
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
      | DESC fs => VALUE $ map_fold (InitFold) gmap_empty fs
      end
    with InitFold (k : Z) (f : Field) (acc : gmap Z Val) : gmap Z Val :=
           match f with
           | F_MSG d => <[ k := V_MSG (Init d) ]> acc
           | _ => <[ k := V_MISSING ]> acc
           end.

    Definition Init_eq := mk_eq Init.
    Definition InitFold_eq := mk_eq InitFold.

    (* v1 ⊆ v2 *)
    Fixpoint Subset (v1 v2 : Value) : bool :=
      match v1, v2 with
      | VALUE vs1, VALUE vs2 => map_fold (SubsetFold vs2) true vs1
      end
    with SubsetFold (vs : gmap Z Val) (k : Z) (v : Val) (acc : bool) : bool :=
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
    Definition Subset_eq := mk_eq Subset.
    Definition SubsetFold_eq := mk_eq SubsetFold.

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
      | DESC fs, VALUE vs => map_fold (ValidFold vs) True fs
      end
    with ValidFold (vs : gmap Z Val) (k : Z) (f : Field) (acc : Prop) : Prop :=
           match f with
           | F_BOOL => acc /\ exists b, vs !! k = Some (V_BOOL b)
           | F_INT => acc /\ exists z, vs !! k = Some (V_INT z)
           | F_MSG d => acc /\ exists v, vs !! k = Some (V_MSG v) /\ Valid d v
           end.
    Definition Valid_eq := mk_eq Valid.
    Definition ValidFold_eq := mk_eq ValidFold.

    Fixpoint Valid' (d : Desc) (v : Value) : Prop :=
      match d, v with
      | DESC fs, VALUE vs => map_fold (Valid'Fold fs) True vs
      end
    with Valid'Fold (fs : gmap Z Field) (k : Z) (v : Val) (acc : Prop) : Prop :=
           match v with
           | V_BOOL _ => fs !! k = Some F_BOOL /\ acc
           | V_INT _ => fs !! k = Some F_INT /\ acc
           | V_MSG value => (exists d, fs !! k = Some (F_MSG d) /\ Valid' d value) /\ acc
             (* While the True isn't needed, the uniform structure helps proofs *)
           | V_MISSING => True /\ acc
           end.

    Definition Valid'_eq := mk_eq Valid'.
    Definition Valid'Fold_eq := mk_eq Valid'Fold.

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

  Section Desc_Field_ind.

    (** Structural size metrics for well-founded induction **)
    Fixpoint Desc_size (d : Desc) : nat :=
      match d with
      | DESC fs => 1 + map_fold (fun _ v acc => Field_size v + acc)%nat 0%nat fs
      end
    with Field_size (f : Field) : nat :=
           match f with
           | F_MSG d => 1 + Desc_size d
           | F_BOOL => 1
           | F_INT => 1
           end.

    Definition Desc_size_eq := mk_eq Desc_size.
    Definition Field_size_eq := mk_eq Field_size.

    (** Every Field has positive size *)
    Lemma Field_size_positive : ∀ f, (Field_size f > 0)%nat.
    Proof. 
      destruct f; simpl; lia. 
    Qed.
    
    (** Every Desc has positive size *)
    Lemma Desc_size_positive : ∀ d, (Desc_size d > 0)%nat.
    Proof. 
      destruct d; simpl; lia. 
    Qed.
    
    (** Fields in a map are smaller than the containing descriptor *)
    Lemma Field_in_map_smaller : 
      ∀ (m : gmap Z Field) k f, 
      m !! k = Some f -> 
      (Field_size f < S (map_fold (λ _ v acc, Field_size v + acc) 0 m))%nat.
    Proof.
      intros m k v.
      induction m as [| k' v' m' Hno Hfst] using map_first_key_ind.
      - (* Empty map case: contradiction *)
        rewrite lookup_empty. discriminate.
      - (* Non-empty map case *)
        rewrite lookup_insert.
        case_decide as Heq.
        + (* k = k': we found the element *)
          intro Hlookup. inversion Hlookup; subst; clear Hlookup.
          rewrite map_fold_insert_L.
          * simpl. lia.
          * intros; lia.
          * assumption.
        + (* k ≠ k': element is in the rest *)
          intro Hlookup.
          rewrite map_fold_insert_L.
          * simpl.
            specialize (IHm Hlookup).
            lia.
          * intros; lia.
          * assumption.
    Qed.

    (** When we insert a new field, elements from the old map remain smaller *)
    Lemma map_elem_size_bound :
      ∀ k f (fs : gmap Z Field) x,
      fs !! k = None ->
      (match x with
       | inl d' => Desc_size d'
       | inr f' => Field_size f'
       end < S (map_fold (λ _ v acc, Field_size v + acc) 0 fs))%nat ->
      (match x with
       | inl d' => Desc_size d'
       | inr f' => Field_size f'
       end < S (map_fold (λ _ v acc, Field_size v + acc) 0 (<[k := f]> fs)))%nat.
    Proof.
      intros k f fs x Hno Hsize.
      rewrite map_fold_insert_L.
      - destruct x; simpl in *; 
          pose proof (Field_size_positive f); lia.
      - intros; lia.
      - assumption.
    Qed.
    
    (** ============================================
      PART 2: Induction Principle Setup
      ============================================ **)
    
    (** The predicates we want to prove for each type *)
    Variable P_Desc : Desc -> Prop.
    Variable P_Field : Field -> Prop.
    
    (** Constructor cases that must be proven **)
    
    (** For DESC: if all fields satisfy P_Field, then the descriptor satisfies P_Desc *)
    Hypothesis DESC_case : 
      ∀ fs, map_Forall (λ _ f, P_Field f) fs -> P_Desc (DESC fs).
    
    (** For F_MSG: if the nested descriptor satisfies P_Desc, then the field satisfies P_Field *)
    Hypothesis F_MSG_case : 
      ∀ d, P_Desc d -> P_Field (F_MSG d).
    
    (** For F_BOOL: the field satisfies P_Field *)
    Hypothesis F_BOOL_case : 
      P_Field F_BOOL.
    
    (** For F_INT: the field satisfies P_Field *)
    Hypothesis F_INT_case : 
      P_Field F_INT.

    (** 
    Mutual induction principle for Desc and Field.
    
    PROOF STRATEGY:
    1. Combine both predicates (P_Desc and P_Field) into a single predicate 
       over the sum type (Desc + Field)
    2. Apply well-founded induction on the size measure
    3. Case split on whether we have a Desc (inl) or Field (inr)
    4. For Desc: use map induction to prove P_Field for all fields in the map
    5. For Field: handle each constructor (F_MSG, F_BOOL, F_INT)
    6. All inductive calls are justified by strictly decreasing size
    
     **)
    Theorem Desc_Field_ind_raw : (∀ d, P_Desc d) ∧ (∀ f, P_Field f).
    Proof.
      (** Step 1: Combine predicates into one over sum type **)
      set (P_sum := λ x : Desc + Field, 
             match x with 
             | inl d => P_Desc d 
             | inr f => P_Field f 
             end).
      
      (* We'll prove ∀ x, P_sum x, then split back into the conjunction *)
      cut (∀ x, P_sum x).
      { intros H; split; intros; apply (H (inl _)) || apply (H (inr _)). }
      
      (** Step 2: Apply well-founded induction on size **)
      apply (well_founded_ind 
               (measure_wf lt_wf 
                  (λ x : Desc + Field, 
                     match x with 
                     | inl d => Desc_size d 
                     | inr f => Field_size f 
                     end))).
      
      (* Now we have: ∀ x, (∀ y, size(y) < size(x) -> P_sum y) -> P_sum x *)
      intros [d | f] IH; simpl in *.
      
      (** Step 3a: DESC case **)
      - destruct d as [fs].
        apply DESC_case.
        
        (* Use map induction to prove P_Field for all elements *)
        induction fs as [| k f fs Hno Hfst] using map_first_key_ind.
        
        + (* Base case: empty map *)
          apply map_Forall_empty.
          
        + (* Inductive case: map with first key k *)
          rewrite map_Forall_insert; last assumption.
          split.
          
          * (* Prove P_Field f for the first field *)
            apply (IH (inr f)).
            unfold Desc_size, MR.
            rewrite map_fold_insert_L.
            -- rewrite Field_size_eq; simpl;
                 pose proof (Field_size_positive f); lia.
            -- rewrite !Field_size_eq; simpl; intros; lia.
            -- assumption.
               
          * (* Prove P_Field for all remaining fields using IHfs *)
            apply IHfs.
            intros x Hsize.
            unfold MR in Hsize; simpl in Hsize.
            apply (IH x).
            apply map_elem_size_bound; auto.
            
      (** Step 3b: Field cases **)
      - destruct f.
        
        + (* F_MSG case *)
          apply F_MSG_case.
          apply (IH (inl d)).
          unfold Desc_size, MR.
          rewrite Desc_size_eq; simpl. lia.
          
        + (* F_BOOL case *)
          apply F_BOOL_case.
          
        + (* F_INT case *)
          apply F_INT_case.
    Defined.

    (** ============================================
      PART 5: Extracted Principles
      ============================================ **)
    
    (** Induction principle for Desc alone *)

    Definition Descriptor_ind := proj1 Desc_Field_ind_raw.

    (** Induction principle for Field alone *)
    Definition Field_ind' : ∀ f, P_Field f := 
    proj2 Desc_Field_ind_raw.
    
    (** Combined mutual induction principle *)
    Definition Desc_Field_ind := Desc_Field_ind_raw.

  End Desc_Field_ind.

  Section Value_Val_ind.

    (** Structural size metrics for well-founded induction ***)
    Fixpoint Value_size (v : Value) : nat :=
      match v with
      | VALUE vs => 1 + map_fold (fun _ v acc => Val_size v + acc)%nat 0%nat vs
      end
    with Val_size (v : Val) : nat :=
           match v with
           | V_MSG val => 1 + Value_size val
           | V_BOOL _ => 1
           | V_INT _ => 1
           | V_MISSING => 1
           end.

    Definition Value_size_eq := mk_eq Value_size.
    Definition Val_size_eq := mk_eq Val_size.

    (** Every Val has positive size **)
    Lemma Val_size_positive : ∀ v, (Val_size v > 0)%nat.
    Proof.
      destruct v; simpl; lia.
    Qed.

    (** Every Value has positive size **)
    Lemma Value_size_positive : ∀ v, (Value_size v > 0)%nat.
    Proof.
      destruct v; simpl; lia.
    Qed.

    (** Vals in a map are smaller than the containing value **)
    Lemma Val_in_map_smaller :
      ∀ (m : gmap Z Val) k v,
      m !! k = Some v ->
      (Val_size v < S (map_fold (λ _ v acc, Val_size v + acc) 0 m))%nat.
    Proof.
      intros m k v.
      induction m as [| k' v' m' Hno Hfst] using map_first_key_ind.
      - (* Empty map case: contradiction *)
        rewrite lookup_empty. discriminate.
      - (* Non-empty map case *)
        rewrite lookup_insert.
        case_decide as Heq.
        + (* k = k': we found the element *)
          intro Hlookup. inversion Hlookup; subst; clear Hlookup.
          rewrite map_fold_insert_L.
          * simpl. lia.
          * intros; lia.
          * assumption.
        + (* k ≠ k': element is in the rest *)
          intro Hlookup.
          rewrite map_fold_insert_L.
          * simpl.
            specialize (IHm Hlookup).
            lia.
          * intros; lia.
          * assumption.
    Qed.

    (** When we insert a new val, elements from the old map remain smaller **)
    Lemma val_map_elem_size_bound :
      ∀ k v (vs : gmap Z Val) x,
      vs !! k = None ->
      (match x with
       | inl val' => Value_size val'
       | inr v' => Val_size v'
       end < S (map_fold (λ _ v acc, Val_size v + acc) 0 vs))%nat ->
      (match x with
       | inl val' => Value_size val'
       | inr v' => Val_size v'
       end < S (map_fold (λ _ v acc, Val_size v + acc) 0 (<[k := v]> vs)))%nat.
    Proof.
      intros k v vs x Hno Hsize.
      rewrite map_fold_insert_L.
      - destruct x; simpl in *;
          pose proof (Val_size_positive v); lia.
      - intros; lia.
      - assumption.
    Qed.

    (** ============================================
      PART 2: Induction Principle Setup
      ============================================ ***)

    (** The predicates we want to prove for each type **)
    Variable P_Value : Value -> Prop.
    Variable P_Val : Val -> Prop.

    (** Constructor cases that must be proven ***)

    (** For VALUE: if all vals satisfy P_Val, then the value satisfies P_Value **)
    Hypothesis VALUE_case :
      ∀ vs, map_Forall (λ _ v, P_Val v) vs -> P_Value (VALUE vs).

    (** For V_MSG: if the nested value satisfies P_Value, then the val satisfies P_Val **)
    Hypothesis V_MSG_case :
      ∀ v, P_Value v -> P_Val (V_MSG v).

    (** For V_BOOL: the val satisfies P_Val **)
    Hypothesis V_BOOL_case :
      ∀ b, P_Val (V_BOOL b).

    (** For V_INT: the val satisfies P_Val **)
    Hypothesis V_INT_case :
      ∀ z, P_Val (V_INT z).

    (** For V_MISSING: the val satisfies P_Val **)
    Hypothesis V_MISSING_case :
      P_Val V_MISSING.

    (**
    Mutual induction principle for Value and Val.

    PROOF STRATEGY:
    1. Combine both predicates (P_Value and P_Val) into a single predicate
       over the sum type (Value + Val)
    2. Apply well-founded induction on the size measure
    3. Case split on whether we have a Value (inl) or Val (inr)
    4. For Value: use map induction to prove P_Val for all vals in the map
    5. For Val: handle each constructor (V_MSG, V_BOOL, V_INT, V_MISSING)
    6. All inductive calls are justified by strictly decreasing size

     ***)
    Theorem Value_Val_ind_raw : (∀ v, P_Value v) ∧ (∀ v, P_Val v).
    Proof.
      (** Step 1: Combine predicates into one over sum type ***)
      set (P_sum := λ x : Value + Val,
             match x with
             | inl v => P_Value v
             | inr v => P_Val v
             end).

      (* We'll prove ∀ x, P_sum x, then split back into the conjunction *)
      cut (∀ x, P_sum x).
      { intros H; split; intros; apply (H (inl _)) || apply (H (inr _)). }

      (** Step 2: Apply well-founded induction on size ***)
      apply (well_founded_ind
               (measure_wf lt_wf
                  (λ x : Value + Val,
                     match x with
                     | inl v => Value_size v
                     | inr v => Val_size v
                     end))).

      (* Now we have: ∀ x, (∀ y, size(y) < size(x) -> P_sum y) -> P_sum x *)
      intros [v | v] IH; simpl in *.

      (** Step 3a: VALUE case ***)
      - destruct v as [vs].
        apply VALUE_case.

        (* Use map induction to prove P_Val for all elements *)
        induction vs as [| k v vs Hno Hfst] using map_first_key_ind.

        + (* Base case: empty map *)
          apply map_Forall_empty.

        + (* Inductive case: map with first key k *)
          rewrite map_Forall_insert; last assumption.
          split.

          * (* Prove P_Val v for the first val *)
            apply (IH (inr v)).
            unfold Value_size, MR.
            rewrite map_fold_insert_L.
            -- rewrite ?Val_size_eq; simpl;
                 pose proof (Val_size_positive v); lia.
            -- rewrite !Val_size_eq; simpl; intros; lia.
            -- assumption.

          * (* Prove P_Val for all remaining vals using IHvs *)
            apply IHvs.
            intros x Hsize.
            unfold MR in Hsize; simpl in Hsize.
            apply (IH x).
            apply val_map_elem_size_bound; auto.

      (** Step 3b: Val cases ***)
      - destruct v.

        + (* V_MSG case *)
          apply V_MSG_case.
          apply (IH (inl v)).
          unfold Value_size, MR.
          rewrite Value_size_eq; simpl. lia.

        + (* V_BOOL case *)
          apply V_BOOL_case.

        + (* V_INT case *)
          apply V_INT_case.

        + (* V_MISSING case *)
          apply V_MISSING_case.
    Defined.

    (** ============================================
      PART 5: Extracted Principles
      ============================================ ***)

    (** Induction principle for Value alone **)
    Definition Value_ind' := proj1 Value_Val_ind_raw.

    (** Induction principle for Val alone **)
    Definition Val_ind' : ∀ v, P_Val v :=
      proj2 Value_Val_ind_raw.

    (** Combined mutual induction principle **)
    Definition Value_Val_ind := Value_Val_ind_raw.

  End Value_Val_ind.

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
              | byt :: rest => P.R.Success byt rest
              | [] => P.R.Failure P.R.Recoverable (P.R.mkData "No more data to parse" inp None)
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
            | P.R.Success v2 _, P.R.Success v2' _ => Eqb v2 v2'
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
    Definition result3 := fst $ (P.R.Extract (ParseValue desc3 enc3) I).
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
    Definition result3' := fst $ (P.R.Extract (ParseValue desc3 enc3') I).
    Compute Eqb result3' val3'.
  End Parse.

  Section Serial.
    Definition SerialByte : S.Serializer byte S.Trivial_wf :=
      fun b => S.mkSuccess [b].

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
      | VALUE vs => (map_fold ValueDepthFold 0 vs)%nat
      end
    with ValueDepthFold (k : Z) (v : Val) (acc : nat) :=
           match v with
           | V_BOOL _
           | V_INT _
           | V_MISSING => acc
           | V_MSG v' => acc `max` (ValueDepth v' + 1)
           end.

    Definition ValueDepth_eq := mk_eq ValueDepth.
    Definition ValueDepthFold_eq := mk_eq ValueDepthFold.

    Compute ValueDepth val1. 
    Compute ValueDepth val2.
    Compute ValueDepth val3.

    Fixpoint ValueEncLen (v : Value) : nat :=
      match v with
      | VALUE vs => (map_fold ValueEncLenFold 0 vs)%nat
      end
    with ValueEncLenFold (k : Z) (v : Val) (acc : nat) :=
           match v with
           | V_BOOL _ => (acc + 5)%nat
           | V_INT _ => (acc + 5)%nat
           | V_MISSING => acc
           | V_MSG v' => (acc + 2 + ValueEncLen v')%nat
           end.

    Definition ValueEncLen_eq := mk_eq ValueEncLen.
    Definition ValueEncLenFold_eq := mk_eq ValueEncLenFold.

    Fixpoint ValueEncLen' (d : Desc) (v : Value) : nat :=
      match v, d with
      | VALUE vs, DESC ds => (map_fold (ValueEncLen'Fold ds) 0 vs)%nat
      end
    with ValueEncLen'Fold (ds : gmap Z Field) (k : Z) (v : Val) (acc : nat) : nat :=
           match ds !! k, v with
           | None, _ => acc
           | Some _, V_BOOL _ => (acc + 5)%nat
           | Some _, V_INT _ => (acc + 5)%nat
           | Some (F_MSG d), V_MSG val => (acc + 2 + ValueEncLen' d val)%nat
           | Some _, _ => acc
           end.

    Definition ValueEncLen'_eq := mk_eq ValueEncLen'.
    Definition ValueEncLen'Fold_eq := mk_eq ValueEncLen'Fold.

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

    Fixpoint Value_wf (d : Desc) (v : Value) : Prop :=
      match v, d with
      | VALUE vs, DESC ds => map_fold (Val_wf_fold ds) True vs
      end
    with Val_wf_fold (ds : gmap Z Field) (k : Z) (v : Val) (acc : Prop) : Prop :=
           match ds !! k, v with
           | None, _ => acc (* Skip fields that will be dropped *)
           | Some F_BOOL, V_BOOL _ => acc (* All Booleans are intrinsically well-formed *)
           | Some F_INT, V_INT z => acc /\ 0 <= z < 2^32 (* Integer fits in bounds *)
           | Some (F_MSG d), V_MSG val => acc /\ Value_wf d val (* Nested message is also well-formed *)
           | _, _ => False
           end.
        
    Definition Value_wf_eq := mk_eq Value_wf.
    Definition Val_wf_fold_eq := mk_eq Val_wf_fold.

    Lemma Val_wf_fold_unfold :
      forall d key val,
      Val_wf_fold (Fields d) key val True =
      match (Fields d) !! key, val with
      | None, _ => True (* Skip fields that will be dropped *)
      | Some F_BOOL, V_BOOL _ => True (* All Booleans are intrinsically well-formed *)
      | Some F_INT, V_INT z => True /\ 0 <= z < 2^32 (* Integer fits in bounds *)
      | Some (F_MSG d), V_MSG val => True /\ Value_wf d val (* Nested message is also well-formed *)
      | _, _ => False
      end.
    Proof using Type.
      intros [ds] k v.
      unfold Val_wf_fold, Fields.
      destruct v; destruct (ds !! k) eqn:Hin_d; try reflexivity.
    Qed.

    (* Helper definition to shim between Val_wf_fold and Serializer API *)
    Definition Val_wf (d : Desc) (v : Z * Val) : Prop :=
      let (key, val) := v in  
      Val_wf_fold (Fields d) key val True.

    Definition SerialVal (serial__msg : forall d : Desc, S.Serializer Value $ Value_wf d) (d : Desc) :
      Serializer (Z * Val) (Val_wf d) := 
      fun val => let (id, v) := val in
              match (Fields d) !! id with
              | Some F_BOOL => match v with
                              | V_BOOL b => S.Bind' (fun _ => id) SerialUnsigned SerialBool b
                              | V_MISSING => S.mkSuccess []
                              | _ => S.R.Failure S.R.Recoverable
                                      (S.R.mkData "Expected Boolean" Input_default None)
                              end
              | Some F_INT => match v with
                             | V_INT z => S.Bind' (fun _ => id) SerialUnsigned SerialZ32 z
                             | V_MISSING => S.mkSuccess []
                             | _ => S.R.Failure S.R.Recoverable
                                     (S.R.mkData "Expected Integer" Input_default None)
                             end
              | Some (F_MSG d') => match v with
                                  | V_MSG z => S.Bind' (fun _ => id) SerialUnsigned
                                                      (S.Len' SerialNat (serial__msg d')) z
                                  | V_MISSING => S.mkSuccess []
                                  | _ => S.R.Failure S.R.Recoverable
                                          (S.R.mkData "Expected nested message" Input_default None)
                                  end
              | None => S.mkSuccess Input_default
              end.

    Definition ValList_filter_p (d : Desc) (kv : Z * Val) : Prop :=
      match (Fields d) !! (fst kv), (snd kv) with
      | Some _, V_MISSING => False
      | None, _ => False
      | _, _ => True
      end.

    Global Instance ValList_filter_Decision (d : Desc) : forall kv : Z * Val, Decision (ValList_filter_p d kv).
    Proof.
      intros [k v].
      unfold ValList_filter_p, fst, snd.
      destruct (Fields d !! k); last apply False_dec.
      destruct v; (apply True_dec || apply False_dec).
    Defined.
      
    Definition ValList (d : Desc) (v : Value) : list (Z * Val) :=
      filter (ValList_filter_p d) (map_to_list (Vals v)).
      
    Definition field_val_match (f : Field) (v : Val) : Prop :=
      match v, f with
      | V_BOOL _, F_BOOL
      | V_INT _, F_INT
      | V_MSG _, F_MSG _ => True
      | _, _ => False
      end.

    Definition WillEncode (d : Desc) (kv : Z * Val) : Prop :=
      exists f, (Fields d) !! (fst kv) = Some f /\ Val_wf d kv. 

    Definition SerialValueList_wf (d : Desc) (vs : list (Z * Val)) : Prop :=
      Forall (WillEncode d) vs.

    Definition SerialValue' (self : forall d : Desc, Serializer Value $ Value_wf d) (d : Desc) :
      Serializer Value $ Value_wf d :=
      S.Map (S.Rep (SerialVal self d : S.Serializer _ (WillEncode d))) (ValList d).

    Definition SerialValue (d : Desc) : Serializer Value $ Value_wf d :=
      S.RecursiveState SerialValue' ValueDepth d.

    Definition enc_eq (d : Desc) (v : Value) (e : Input) : bool :=
      match SerialValue d v with
      | S.R.Success _ enc => if decide (enc = e) then true else false
      | S.R.Failure _ _ => false
      end.

    Definition round_trip (d : Desc) (v : Value) : bool :=
      match SerialValue d v with
      | S.R.Success _ enc => match ParseValue d enc with
                        | P.R.Success v' _ => Eqb v v'
                        | P.R.Failure _ _ => false
                        end
      | S.R.Failure _ _ => false
      end.

    Definition check_multi_enc (d : Desc) (enc1 enc2 : Input) : bool :=
      match ParseValue d enc1, ParseValue d enc2 with
      | P.R.Success v1 _, P.R.Success v2 _ => Eqb v1 v2
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

    Lemma UnsignedLength : forall x enc, SerialUnsigned x = S.mkSuccess enc -> Length enc = 1%nat.
    Proof.
      intros x enc.
      unfold SerialUnsigned, SerialByte.
      intros Hser; invc Hser.
      unfold Length; simpl.
      reflexivity.
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

    Lemma Z32Length : forall x enc, SerialZ32 x = S.mkSuccess enc -> Length enc = 4%nat.
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
      (ValueDepth (VALUE vs) <= ValueDepth (VALUE $ <[z := v]> vs))%nat.
    Proof.
      intros z v vs Hno Hfst.
      destruct v;
        unfold ValueDepth at 2;
        rewrite map_fold_insert_first_key by assumption.
      - fold (ValueDepth (VALUE vs)).
        fold (ValueDepth v).
        lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
    Qed.

    Lemma ValidInsert (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) :
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      Valid' d (VALUE (<[k := v]> m)) <-> Valid'Fold (Fields d) k v True /\ Valid' d (VALUE m).
    Proof.
      intros Hnone Hfst.
      split.
      - destruct d; unfold Valid' at 1.
        rewrite map_fold_insert_first_key by assumption.
        rewrite Valid'Fold_eq. intros Hvalid.
        split.
        + destruct v;
            (split; last easy);
            unfold Valid'Fold at 1 in Hvalid;
            destruct Hvalid as [Hvalid  _]; assumption.
        + destruct v; unfold Valid'Fold at 1 in Hvalid;
            destruct Hvalid as [_ Hvalid]; assumption.
      - intros [Hfst_valid Hrest_valid].
        destruct d; unfold Valid'.
        rewrite map_fold_insert_first_key by assumption.
        rewrite Valid'Fold_eq.
        destruct v;
          unfold Valid'Fold at 1;
          destruct Hfst_valid as [Hfst_valid _] in Hfst_valid;
          unfold Valid' in Hrest_valid; split; assumption.
    Qed.

    Lemma ValueEncLen'Fold_linear :
      forall (fs : gmap Z Field) k v acc,
        ValueEncLen'Fold fs k v acc = (ValueEncLen'Fold fs k v 0 + acc)%nat.
    Proof.
      intros fs k v acc.
      destruct (fs !! k) eqn:Hfield; [destruct f|]; destruct v;
        simpl; rewrite ?Hfield; lia.
    Qed.

    Lemma ValueEncLength_unfold (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) :
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      ValueEncLen' d (VALUE (<[k := v]> m)) =
      (ValueEncLen'Fold (Fields d) k v 0 + ValueEncLen' d (VALUE m))%nat.
    Proof.
      intros Hnone Hfst.
      destruct d as [fs].
      unfold Fields, ValueEncLen' at 1.
      rewrite map_fold_insert_first_key by assumption.
      unfold ValueEncLen'.
      rewrite ValueEncLen'Fold_linear.
      reflexivity.
    Qed.

    (** Values nested in a map have strictly smaller depth **)
    Lemma Val_in_map_smaller_depth :
      forall (m : gmap Z Val) k v,
      m !! k = Some (V_MSG v) ->
      (ValueDepth v < ValueDepth (VALUE m))%nat.
    Proof.
      intros m k v.
      induction m as [| k' v' m' Hno Hfst] using map_first_key_ind.
      - (* Empty map case: contradiction *)
        rewrite lookup_empty. discriminate.
      - (* Non-empty map case *)
        rewrite lookup_insert.
        case_decide as Heq.
        + (* k = k': we found the element *)
          intro Hlookup. inversion Hlookup; subst; clear Hlookup.
          unfold ValueDepth at 2.
          rewrite map_fold_insert_L.
          * rewrite ValueDepth_eq, ValueDepthFold_eq.
            lia.
          * intros. simpl. rewrite ValueDepthFold_eq.
            destruct z1, z2; unfold ValueDepthFold; lia.
          * assumption.
        + (* k ≠ k': element is in the rest *)
          intro Hlookup.
          unfold ValueDepth at 2.
          rewrite map_fold_insert_L.
          * simpl.
            specialize (IHm Hlookup).
            rewrite ValueDepthFold_eq.
            change (map_fold ValueDepthFold 0%nat m') with (ValueDepth (VALUE m')).
            destruct v'; unfold ValueDepthFold; lia.
          * intros; simpl; rewrite ValueDepthFold_eq.
            destruct z1, z2; unfold ValueDepthFold; lia.
          * assumption.
    Qed.

    Infix "ₛ≡ᵣ" := S.R.result_equiv (at level 70):type_scope.
    Lemma SerialValWeakenDepth (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) : 
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      forall kv,
      kv ∈ ValList d (VALUE m) ->
      SerialVal (λ (st__n : Desc) (x__n : Value),
                   if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
                   then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                   else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n)
        d kv ₛ≡ᵣ
      SerialVal (λ (st__n : Desc) (x__n : Value),
                   if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
                   then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                   else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n)
        d kv.
    Proof.
      intros Hnone Hfst [key val] Hin.
      unfold SerialVal.
      (* The serializers only differ in recursive calls on V_MSG values *)
      destruct ((Fields d) !! key); try done.
      destruct f; try reflexivity.
      (* For F_MSG, we need to show the depth checks evaluate the same *)
      destruct val as [val | z | b |]; try reflexivity.
      (* For V_MSG v0, both depth checks should be true since v0 comes from m *)
      unfold S.Bind', S.Concat, S.Len'.
      (* Show that both decide expressions evaluate to true *)
      unfold ValList, Vals in Hin.
      rewrite list_elem_of_filter in Hin.
      destruct Hin as [Hfilter Hin].
      rewrite elem_of_map_to_list in Hin.
      pose proof (ValueDepthDropFirst k v m Hnone Hfst) as Hdepth. 
      destruct (decide (ValueDepth val < ValueDepth (VALUE m))%nat) eqn:Hm.
      - destruct (decide (ValueDepth val < ValueDepth (VALUE (<[k := v]> m)))%nat) eqn:Hn;
          (reflexivity || lia).
      - destruct (decide (ValueDepth val < ValueDepth (VALUE (<[k := v]> m)))%nat) eqn:Hn.
        + pose proof (Val_in_map_smaller_depth m key val Hin). lia.
        + unfold S.RecursiveProgressError.
          destruct (ValueDepth val == ValueDepth (VALUE m)),
                     (ValueDepth val == ValueDepth (VALUE (<[k := v]> m))); try done.
    Qed.

    Lemma SerialValueInversion (d : Desc) :
      forall k v (m : gmap Z Val) enc,
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      SerialValue d (VALUE (<[k := v]> m)) = S.mkSuccess enc <->
      exists enc__v enc__rest, SerialValue d (VALUE m) = S.mkSuccess enc__rest /\
                      SerialVal (SerialValue) d (k, v) = S.mkSuccess enc__v /\
                      enc = App enc__v enc__rest.
    Proof.
      intros k v m enc Hnone Hfst.
      split.
      - unfold SerialValue at 1, S.RecursiveState.
        rewrite ser_recur_st_unfold.
        unfold SerialValue', S.Map, ValList, Vals.
        rewrite map_to_list_insert_first_key by assumption.
        rewrite filter_cons.
        destruct (decide (ValList_filter_p d (k, v))) as [Hfilter_in | Hfilter_out].
        + intros Hser. rewrite SerialRepInversion_First in Hser.
          destruct Hser as (enc__v & enc__rest & Hv_ok & Hrest_ok & Henc).
          subst. exists enc__v, enc__rest.
          split.
          * unfold SerialValue, S.RecursiveState.
            rewrite ser_recur_st_unfold.
            unfold SerialValue', S.Map, ValList, Vals, S.mkSuccess.
            rewrite <- S.R.ResultEquivSuccessIff with (r := S.Rep _ _).
            unfold S.mkSuccess in Hrest_ok.
            rewrite <- Hrest_ok.
            (* Need to show that the depth bound difference doesn't matter *)
            (* because all elements in map_to_list m have depth < ValueDepth (VALUE m) *)
            (* Fortunately, that's exactly what SerialValWeakenDepth tells us. *)
            (* Now we need to show S.rep' with both serializers gives the same result *)
            change (
                (λ (self : forall d : Desc, Serializer Value $ Value_wf d) (d0 : Desc) (a : Value),
                   S.Rep (SerialVal self d0) (map_to_list match a with
                                                | VALUE vs => vs
                                                end))
              ) with SerialValue'.
            rewrite SerialRepSubst with
              (ser2 :=
                 (SerialVal
                    (λ (st__n : Desc) (x__n : Value),
                       if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
                       then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                       else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n)
                    d)
              ); first reflexivity.
            symmetry.
            apply SerialValWeakenDepth; assumption.
          * split; last reflexivity.
            change (
                (λ (self : forall d : Desc, Serializer Value $ Value_wf d) (d : Desc) (a : Value),
                   S.Rep (SerialVal self d) (map_to_list match a with
                                               | VALUE vs => vs
                                               end))
              ) with SerialValue' in Hv_ok.
            rewrite <- Hv_ok.
            unfold SerialVal.
            destruct (Fields d !! k); last reflexivity.
            destruct f; try reflexivity.
            destruct v; try reflexivity.
            unfold S.Bind', S.Concat, S.Len'.
            case_eq (decide (ValueDepth v < ValueDepth (VALUE (<[k := V_MSG v]> m))))%nat.
            -- intros Hdep _. unfold SerialValue, S.RecursiveState. reflexivity.
            -- intros Hdep _. pose proof (lookup_insert_eq m k (V_MSG v)) as Hlookup.
               pose proof (Val_in_map_smaller_depth (<[k := V_MSG v]> m) k v Hlookup).
               contradiction.
        + destruct (filter (ValList_filter_p d) (map_to_list m)) eqn:Hlst.
          * rewrite ser_rep_unfold. intros Hser. invc Hser.
            exists S.Output_default, S.Output_default.
            split.
            -- unfold SerialValue, S.RecursiveState.
               rewrite ser_recur_st_unfold.
               unfold SerialValue', S.Map, ValList, Vals.
               rewrite Hlst. reflexivity.
            -- split; last (unfold S.Output_default; rewrite App_nil_r; reflexivity).
               unfold ValList_filter_p, fst, snd in Hfilter_out.
               unfold SerialVal. destruct (Fields d !! k); last reflexivity.
               destruct f; destruct v; (reflexivity || specialize (Hfilter_out I); contradiction).
          * intro Hser. exists Input_default, enc. 
            split.
            -- unfold SerialValue, S.RecursiveState.
               rewrite ser_recur_st_unfold.
               unfold SerialValue', S.Map, ValList, Vals, S.mkSuccess.
               rewrite <- Hlst in Hser. 
               rewrite <- S.R.ResultEquivSuccessIff with (r := S.Rep _ _).
               unfold S.mkSuccess in Hser.
               rewrite <- Hser.
               rewrite SerialRepSubst with
                 (ser2 :=
                    (SerialVal
                       (λ (st__n : Desc) (x__n : Value),
                          if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
                          then
                            S.recur_st
                              (λ (self : ∀ d0 : Desc, Serializer Value (Value_wf d0)) (d0 : Desc) (a : Value),
                                 @S.Rep _ (WillEncode d0) (SerialVal self d0)
                                   (filter (ValList_filter_p d0) (map_to_list match a with
                                                                    | VALUE vs => vs
                                                                    end)))
                              ValueDepth st__n x__n
                          else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n)
                       d)
                 ); first reflexivity.
               symmetry.
               apply SerialValWeakenDepth; assumption.
            -- split; last (rewrite App_nil_l; reflexivity).
               unfold ValList_filter_p, fst, snd in Hfilter_out.
               unfold SerialVal. destruct (Fields d !! k); last reflexivity.
               destruct f; destruct v; (reflexivity || specialize (Hfilter_out I); contradiction).
          
      - (* Reverse direction: <- *)
        intros (enc__v & enc__rest & Hrest_ok & Hv_ok & Henc).
        unfold SerialValue, S.RecursiveState.
        rewrite ser_recur_st_unfold.
        unfold SerialValue', S.Map, ValList, Vals.
        rewrite map_to_list_insert_first_key by assumption.
        change (
            (λ (self : forall d : Desc, Serializer Value $ Value_wf d) (d0 : Desc) (a : Value),
               S.Rep (SerialVal self d0) (map_to_list match a with
                                            | VALUE vs => vs
                                            end))
          ) with SerialValue'.
        rewrite filter_cons.
        destruct (decide (ValList_filter_p d (k, v))) as [Hfilter_in | Hfilter_out].
        + rewrite SerialRepInversion_First.
          exists enc__v, enc__rest. subst. split.
          * (* Use Hv_ok to show (k, v) meets the depth requirement *)
            (* Since the if is embedded in a lambda term, we chase down
             until it's been applied and then show recursive call is
             always made. *)
            rewrite <- Hv_ok.
            unfold SerialVal.
            destruct (Fields d !! k); last reflexivity.
            destruct f; try reflexivity.
            destruct v; try reflexivity.
            unfold S.Bind', S.Concat, S.Len'.
            case_eq (decide (ValueDepth v < ValueDepth (VALUE (<[k:=V_MSG v]> m)))%nat).
            -- intros Hdep _. unfold SerialValue, S.RecursiveState. reflexivity.
            -- intros Hdep _. pose proof (lookup_insert_eq m k (V_MSG v)) as Hlookup.
               pose proof (Val_in_map_smaller_depth (<[k := V_MSG v]> m) k v Hlookup).
               contradiction.
          * split; last reflexivity. revert Hrest_ok.
            unfold SerialValue, S.RecursiveState.
            rewrite ser_recur_st_unfold. 
            unfold SerialValue', S.Map, ValList, Vals, S.mkSuccess.
            change (
                (λ (self : forall d : Desc, Serializer Value $ Value_wf d) (d : Desc) (a : Value),
                   S.Rep (SerialVal self d) (map_to_list match a with
                                               | VALUE vs => vs
                                               end))
              ) with SerialValue'.
            intros Hrest_ok. 
            rewrite <- S.R.ResultEquivSuccessIff with (r := S.Rep _ _).
            rewrite <- Hrest_ok.
            rewrite SerialRepSubst with
              (ser2 :=
                 (SerialVal
                    (λ (st__n : Desc) (x__n : Value),
                       if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
                       then
                         @S.recur_st _ _ Value_wf SerialValue'
                           ValueDepth st__n x__n
                       else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n)
                    d)
              ); first reflexivity.
            apply SerialValWeakenDepth; assumption.
        + unfold ValList_filter_p, fst, snd in Hfilter_out.
          unfold SerialVal in Hv_ok.
          unfold SerialValue, S.RecursiveState in Hrest_ok.
          rewrite ser_recur_st_unfold in Hrest_ok.
          destruct (Fields d !! k) eqn:Hin_d.
          * (* v was dropped for being V_MISSING *) 
            destruct v; try (reflexivity || specialize (Hfilter_out I); contradiction).
            destruct f;
              invc Hv_ok; rewrite App_nil_l; unfold S.mkSuccess in *;
              rewrite <- S.R.ResultEquivSuccessIff with (r := S.Rep _ _);
              rewrite <- Hrest_ok;
              rewrite SerialRepSubst with
              (ser2 :=
                 (SerialVal
                    (λ (st__n : Desc) (x__n : Value),
                       if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
                       then
                         @S.recur_st _ _ Value_wf SerialValue'
                           ValueDepth st__n x__n
                       else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n)
                    d)
              ); first reflexivity.
            -- apply SerialValWeakenDepth; assumption.
            -- unfold SerialValue', S.Map, ValList, Vals. reflexivity.
            -- apply SerialValWeakenDepth; assumption.
            -- unfold SerialValue', S.Map, ValList, Vals. reflexivity.
            -- apply SerialValWeakenDepth; assumption.
          * (* v dropped for being unknown *)
            unfold S.mkSuccess in *.
            invc Hv_ok. rewrite App_nil_l.
            rewrite <- S.R.ResultEquivSuccessIff with (r := S.Rep _ _).
            rewrite <- Hrest_ok.
            rewrite SerialRepSubst with
              (ser2 :=
                 (SerialVal
                    (λ (st__n : Desc) (x__n : Value),
                       if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
                       then
                         @S.recur_st _ _ Value_wf SerialValue'
                           ValueDepth st__n x__n
                       else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n)
                    d)
              ); first reflexivity.
            apply SerialValWeakenDepth; assumption.
    Qed.

    Definition ValueEncLength_P (v : Value) :=
      forall d enc,
      Valid' d v ->
      SerialValue d v = S.mkSuccess enc ->
      Length enc = ValueEncLen' d v.

    Definition ValEncLength_P (v : Val) :=
      forall d k enc,
      Valid'Fold (Fields d) k v True ->
      SerialVal SerialValue d (k, v) = S.mkSuccess enc ->
      Length enc = ValueEncLen'Fold (Fields d) k v 0.

    Lemma ValueEncLength_Length : forall v, ValueEncLength_P v.
    Proof.
      induction v as [vs IHv | v__n | b | x |] using Value_ind' with
        (P_Value := ValueEncLength_P)
        (P_Val := ValEncLength_P).
      - (* Prove the main statement about Values, using nested induction. *)
        revert IHv. induction vs as [| k v m Hno Hfst ] using map_first_key_ind.
        + intros _ d enc Hvalid Hser; vm_compute in Hser.
          inversion Hser. destruct d; reflexivity.
        + intros IHv d enc Hvalid Hser; unfold S.Output in *. 
          apply SerialValueInversion in Hser; try assumption.
          destruct Hser as (enc__v & enc__rest & Hrest_ok & Hv_ok & Henc).
          rewrite ValidInsert in Hvalid by assumption.
          destruct Hvalid as [Hfst_valid Hrest_valid].
          unfold ValueEncLength_P in IHvs.
          rewrite map_Forall_insert in IHv by assumption.
          destruct IHv as [Hlen_v' Hlen_rest].
          specialize (IHvs Hlen_rest d enc__rest Hrest_valid Hrest_ok).
          rewrite ValueEncLength_unfold by assumption.
          rewrite <- IHvs. destruct d; simpl.
          subst. rewrite App_Length. f_equal.
          unfold ValEncLength_P in Hlen_v'.
          rewrite Hlen_v' with (d := DESC fs) (k := k); done.
      - (* Val case : V_MSG *)
        intros [fs] k enc Hvalid. 
        unfold ValueEncLength_P in IHv__n.
        unfold SerialVal, Fields; simpl.
        destruct (fs !! k) eqn:Hfound.
        + destruct f; try discriminate. 
          intro Hv_ok.
          apply SerialConcatInversion in Hv_ok.
          destruct Hv_ok as (enc__tag & enc__rest & Htag_ok & Hrest_ok & Henc).
          apply SerialLen'Inversion in Hrest_ok. subst.
          destruct Hrest_ok as (enc__len & enc__pay & Hlen_ok & Hpay_ok & Henc).
          subst. rewrite !App_Length.
          apply UnsignedLength in Htag_ok.
          apply UnsignedLength in Hlen_ok.
          unfold Valid'Fold in Hvalid.
          destruct Hvalid as [(d__n & Hfound' & Hvalid__n) _].
          unfold Fields in Hfound'. rewrite Hfound' in Hfound.
          invc Hfound. rewrite Valid'_eq in Hvalid__n.
          rewrite IHv__n with (d := d) (enc := enc__pay) by assumption.
          lia.
        + intro Hv_ok; invc Hv_ok. apply Length_default.
      - (* Val case : V_BOOL *)
        intros [fs] k enc _. 
        unfold SerialVal, Fields; simpl.
        destruct (fs !! k).
        + (* Either the field is in the descriptor, and we output an encoding... *)
          destruct f; try discriminate.
          intros Hv_ok.
          apply SerialConcatInversion in Hv_ok.
          destruct Hv_ok as (enc__tag & enc__pay & Htag_ok & Hpay_ok & Henc).
          subst. apply UnsignedLength in Htag_ok.
          destruct b; apply Z32Length in Hpay_ok;
            rewrite App_Length; lia.
        + (* ... or it isn't and we output nothing. *)
          intros Hv_ok; invc Hv_ok. apply Length_default. 
      - (* Val case : V_INT *)
        intros [fs] k enc _.
        unfold SerialVal, Fields; simpl.
        destruct (fs !! k).
        + destruct f; try discriminate.
          intro Hv_ok.
          apply SerialConcatInversion in Hv_ok.
          destruct Hv_ok as (enc__tag & enc__pay & Htag_ok & Hpay_ok & Henc).
          subst. apply UnsignedLength in Htag_ok.
          apply Z32Length in Hpay_ok.
          rewrite App_Length; lia.
        + intros Hv_ok; invc Hv_ok. apply Length_default.
      - (* Val case : V_MISSING *)
        intros [fs] k enc _.
        unfold SerialVal, Fields; simpl.
        destruct (fs !! k).
        + destruct f; try discriminate; (intros Hv_ok; invc Hv_ok; apply Length_default).
        + intros Hv_ok; invc Hv_ok; apply Length_default.
    Qed.

    Lemma WillEncode_NonEmpty :
      forall d k v enc,
      WillEncode d (k, v) ->
      SerialVal SerialValue d (k, v) = S.mkSuccess enc ->
      (Length enc > 0)%nat.
    Proof.
      (* Proof basically argues that whenever we encode a field, one byte will be the id field... *)
      intros [ds] k v enc wf.
      unfold SerialVal.
      destruct wf as [f [Hin_d Hval_wf]].
      unfold fst in Hin_d. rewrite Hin_d.
      destruct f.
      - unfold Val_wf, Val_wf_fold in Hval_wf.
        rewrite Val_wf_fold_eq in Hval_wf.
        rewrite Val_wf_fold_unfold in Hval_wf.
        rewrite Hin_d in Hval_wf.
        destruct v.
        + intros Hser.
          apply SerialConcatInversion in Hser.
          destruct Hser as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
          subst. rewrite App_Length.
          apply UnsignedLength in Hl_ok.
          lia.
        + intros Hcontra; contradiction.
        + intros Hcontra; contradiction.
        + contradiction.
      - unfold Val_wf, Val_wf_fold in Hval_wf.
        rewrite Val_wf_fold_eq in Hval_wf.
        rewrite Val_wf_fold_unfold in Hval_wf.
        rewrite Hin_d in Hval_wf.
        destruct v.
        + intros Hcontra; contradiction.
        + intros Hser.
          apply SerialConcatInversion in Hser.
          destruct Hser as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
          subst. rewrite App_Length.
          apply UnsignedLength in Hl_ok.
          lia.
        + intros Hcontra; contradiction.
        + contradiction.
      - unfold Val_wf, Val_wf_fold in Hval_wf.
        rewrite Val_wf_fold_eq in Hval_wf.
        rewrite Val_wf_fold_unfold in Hval_wf.
        rewrite Hin_d in Hval_wf.
        destruct v.
        + intros Hcontra; contradiction.
        + intros Hcontra; contradiction.
        + intros Hser.
          apply SerialConcatInversion in Hser.
          destruct Hser as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
          subst. rewrite App_Length.
          apply UnsignedLength in Hl_ok.
          lia.
        + contradiction.
    Qed.

    Program Fixpoint SchemaCorrect (d : Desc) (v : Value) {measure (Desc_size d)} : Prop :=
      match d, v with
      | DESC fs, VALUE vs =>
          (* Every field in the value is in the descriptor *)
          (forall k val, vs !! k = Some val -> exists f, fs !! k = Some f) /\
          (* Every field in the descriptor is in the value *)
          (forall k f, fs !! k = Some f -> exists val, vs !! k = Some val) /\
          (* Every field in the value is not V_MISSING *)
          (forall k, vs !! k <> Some V_MISSING) /\
          (* Nested messages are also correct *)
          map_Forall (fun k v => let f : option Field := fs !! k in 
                              match f, v with
                              | Some (F_MSG d'), V_MSG v' => SchemaCorrect d' v'
                              | _, _ => True
                              end) vs
      end.
    Next Obligation.
    Proof.
      symmetry in Heq_f.
      apply Field_in_map_smaller in Heq_f.
      unfold Desc_size.
      rewrite Desc_size_eq.
      rewrite Field_size_eq.
      unfold Field_size at 1 in Heq_f.
      rewrite Desc_size_eq in Heq_f.
      lia.
    Qed.

  Lemma SchemaCorrect_unfold (d : Desc) (v : Value) : 
    SchemaCorrect d v =
      match d, v with
      | DESC fs, VALUE vs =>
          (* Every field in the value is in the descriptor *)
          (forall k val, vs !! k = Some val -> exists f, fs !! k = Some f) /\
          (* Every field in the descriptor is in the value *)
          (forall k f, fs !! k = Some f -> exists val, vs !! k = Some val) /\
          (* Every field in the value is not V_MISSING *)
          (forall k, vs !! k <> Some V_MISSING) /\
          (* Nested messages are also correct *)
          map_Forall (fun k v => let f : option Field := fs !! k in 
                              match f, v with
                              | Some (F_MSG d'), V_MSG v' => SchemaCorrect d' v'
                              | _, _ => True
                              end) vs
      end.
  Proof.
  Admitted.

    Definition SchemaCorrect_eq := mk_eq SchemaCorrect.
    (* Definition SchemaCorrectFold_eq := mk_eq SchemaCorrectFold. *)

    (* Use this relation to relate the input value to serialization
       to the output value of parsing. At the moment, we require
       that each value be fully described by the linked descriptor. *)
    (* Naturally, for the moment we're doing to have d1 = d2 which should
       imply v1 = v2. *)
    Inductive Compatible : Desc -> Value -> Desc -> Value -> Prop :=
    | CompatID (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value) :
      SchemaCorrect d1 v1 -> SchemaCorrect d2 v2 -> Compatible d1 v1 d2 v2.
      
    Notation "⟨ d1 , v1 ⟩ ⪯ ⟨ d2 , v2 ⟩" := (Compatible d1 v1 d2 v2) (at level 70).

    Lemma SchemaCorrect_Drop_Field (ds : gmap Z Field) (vs : gmap Z Val) :
      forall k v, vs !! k = None ->
      SchemaCorrect (DESC ds) (VALUE $ <[k := v]> vs) ->
      SchemaCorrect (DESC $ delete k ds) (VALUE vs).
    Proof.
      intros k v Hnone.
      unfold SchemaCorrect.
      intros (Hvd & Hdv & Hmissing & Hnest). 
      split_and!.
      - intros k' v' Hin.
        specialize (Hvd k' v').
        rewrite lookup_insert in Hvd.
        destruct (k == k') as [Heq | Hneq].
        + subst k'. rewrite Hin in Hnone. discriminate.
        + specialize (Hvd Hin).
          destruct Hvd as [f' Hinf].
          exists f'. 
          rewrite lookup_delete_ne by assumption.
          assumption.
      - intros k' f' Hin.
        specialize (Hdv k' f').
        rewrite lookup_delete in Hin.
        destruct (k == k') as [Heq | Hneq].
        + discriminate.
        + specialize (Hdv Hin).
          destruct Hdv as [v' Hinv].
          exists v'. rewrite lookup_insert_ne in Hinv by assumption.
          assumption.
      - intros k'.
        specialize (Hmissing k').
        rewrite lookup_insert in Hmissing.
        destruct (k == k').
        + subst k'. rewrite Hnone. done.
        + assumption.
      -
    Admitted.
    
    (*     rewrite map_fold_insert_L in Hnest. *)
    (*     + destruct v; unfold SchemaCorrectFold in Hnest. *)
    (*       * rewrite SchemaCorrectFold_eq, SchemaCorrect_eq in Hnest. *)
            
    (*     induction vs as [| k' v' vs' Hno_vs Hfst_vs IHvs ] using map_first_key_ind. *)
    (*     + rewrite delete_empty, map_fold_empty. trivial. *)
    (*     + rewrite delete_insert. *)
    (*       destruct (k == k'). *)
    (*       * apply IHvs. *)
    (*         -- intros k'' v'' Hin. *)
    (*            specialize (Hvd k'' v''). *)
    (*            rewrite lookup_insert in Hvd. *)
    (*            destruct (k' == k'') as [Heq | Hneq]. *)
    (*            ++ subst k'. rewrite Hin in Hno_vs. discriminate. *)
    (*            ++ specialize (Hvd Hin). *)
    (*               destruct Hvd as [f'' Hinv]. *)
    (*               exists f''.  *)
    (*               assumption. *)
    (*         -- intros k'' v'' Hin. *)
    (*            specialize (Hdv k'' v''). *)
    (*            rewrite lookup_insert in Hdv. *)
    (*            destruct (k == k'') as [Heq | Hneq]. *)
    (*            ++ subst k''. rewrite lookup_insert_eq in Hin. *)
    (*               invc Hin. specialize (Hdv eq_refl). *)
    (*               destruct Hdv as [val Hdv]. *)
    (*     ++ specialize (Hdv Hin). *)
    (*       destruct Hdv as [f' Hinv]. *)
    (*       exists f'. rewrite lookup_delete_ne by assumption. *)
    (*       assumption. *)
    (*         -- admit. *)
    (*         -- admit. *)
    (*       * rewrite map_fold_insert_first_key. *)
    (*         -- destruct v'; unfold SchemaCorrectFold; rewrite SchemaCorrectFold_eq. *)
    (*            ++ rewrite SchemaCorrect_eq. *)
    (*               destruct (ds !! k') as [f' |] eqn:Hk'. *)
    (*               ** destruct f'. *)
    (*                  --- split. *)
    (*                      +++ apply IHvs. *)
    (*                          *** intros k'' v'' Hin. *)
    (*                              specialize (Hvd k'' v''). *)
    (*                              rewrite lookup_insert in Hvd. *)
    (*                              destruct (k' == k'') as [Heq | Hneq]. *)
    (*                              ---- subst k'. rewrite Hin in Hno_vs. discriminate. *)
    (*                              ---- specialize (Hvd Hin). *)
    (*                                   destruct Hvd as [f'' Hinv]. *)
    (*                                   exists f''.  *)
    (*                                   assumption. *)
    (*                          ***   *)
    (*   - induction (delete k vs) as [| k' v' vs' Hno_vs Hfst_vs IHvs ] using map_first_key_ind. *)
    (*     + rewrite map_fold_empty. trivial. *)
    (*     + rewrite map_fold_insert_first_key by assumption.   *)
    (*       destruct v'; unfold SchemaCorrectFold; rewrite SchemaCorrectFold_eq. *)
    (*       * rewrite SchemaCorrect_eq. *)
    (*         destruct (ds !! k'); last assumption. *)
    (*         destruct f0; try assumption. *)
    (*         split; first assumption. *)
    (* Admitted. *)

    Lemma Compatible_Drop_Field (d : gmap Z Field) (v1 v2 : gmap Z Val) :
      forall k v, ⟨ DESC $ <[k := v]> d, VALUE v1 ⟩ ⪯ ⟨ DESC $ <[k := v]> d, VALUE v2 ⟩ ->
             ⟨ DESC d, VALUE $ delete k v1 ⟩ ⪯ ⟨ DESC d, VALUE $ delete k v2 ⟩.
    Proof.
      intros k v H.
      inversion H as [d1' v1' d2' v2' Hschema1 Hsechma2]; subst.
      apply CompatID.
      - 
    Admitted.

    Theorem Compatible_Identity :
      forall d1 d2 v1 v2,
      d1 = d2 ->
      ⟨ d1, v1 ⟩ ⪯ ⟨ d2, v2 ⟩ ->
      v1 = v2.
    Proof.
      intros [ds].
      induction ds as [| k f ds Hnone__d Hfst__d IHds ] using map_first_key_ind.
      - intros d' v1 v2 Heq Hcompat. 
        inversion Hcompat as [d1' v1' d2' v2' Hschema1 Hschema2]; subst.
        destruct v1 as [vs1]; destruct v2 as [vs2].
        f_equal. rewrite SchemaCorrect_unfold in *.
        destruct Hschema1 as (Hin_v1 & Hin_d1 & Hmissing1 & Hnested1).
        destruct Hschema2 as (Hin_v2 & Hin_d2 & Hmissing2 & Hnested2).
        destruct vs1 as [| i x m Hnone Hfst _ ] using map_first_key_ind.
        + destruct vs2 as [| i x m Hnone Hfst _ ]using map_first_key_ind.
          * reflexivity.
          * specialize Hin_v2 with (k := i) (val := x).
            rewrite lookup_insert_eq in Hin_v2.
            specialize (Hin_v2 eq_refl).
            destruct Hin_v2 as [f Hin_v2].
            rewrite lookup_empty in Hin_v2.
            discriminate.
        + specialize Hin_v1 with (k := i) (val := x).
          rewrite lookup_insert_eq in Hin_v1.
          specialize (Hin_v1 eq_refl).
          rewrite lookup_empty in Hin_v1.
          destruct Hin_v1 as [f Hin_v1].
          discriminate.
      - intros d2 v1 v2 Heq_d Hcompat. subst d2.
        inversion Hcompat as [d1' v1' d2' v2' Hschema1 Hschema2]; subst.
        destruct v1 as [vs1]; destruct v2 as [vs2].
        f_equal. rewrite SchemaCorrect_unfold in *.
        destruct Hschema1 as (Hin_v1 & Hin_d1 & Hmissing1 & Hnested1).
        destruct Hschema2 as (Hin_v2 & Hin_d2 & Hmissing2 & Hnested2).
        destruct vs1 as [| k1 v1 m1 Hnone1 Hfst1 _ ] using map_first_key_ind.
        + destruct vs2 as [| k2 v2 m2 Hnone2 Hfst2 _ ] using map_first_key_ind.
          * reflexivity. 
          * specialize Hin_v2 with (k := k2) (val := v2). 
            rewrite lookup_insert_eq in Hin_v2.
            specialize (Hin_v2 eq_refl).
            destruct Hin_v2 as [f' Hin_v2].
            specialize (Hin_d1 k2 f' Hin_v2).
            destruct Hin_d1 as [v' Hin_d1].
            rewrite lookup_empty in Hin_d1.
            discriminate.
        + destruct vs2 as [| k2 v2 m2 Hnone2 Hfst2 _ ] using map_first_key_ind.
          * specialize Hin_v1 with (k := k1) (val := v1).
            rewrite lookup_insert_eq in Hin_v1.
            specialize (Hin_v1 eq_refl).
            destruct Hin_v1 as [f' Hin_v1].
            specialize (Hin_d2 k1 f' Hin_v1).
            destruct Hin_d2 as [v' Hin_d2].
            rewrite lookup_empty in Hin_d2.
            discriminate.
          * assert (⟨ DESC ds, VALUE m1 ⟩ ⪯ ⟨ DESC ds, VALUE m2 ⟩).
            {
              apply CompatID; rewrite SchemaCorrect_unfold.
              - split.
                + intros k' v' Hin.
                  specialize Hin_v1 with (k := k') (val := v').
                  rewrite lookup_insert in Hin_v1. 
                  destruct (k1 == k').
                  * rewrite e in Hnone1. rewrite Hnone1 in Hin.
                    discriminate.
                  * specialize (Hin_v1 Hin).
                    destruct Hin_v1 as [f' Hin_v1].
                    exists f'. rewrite lookup_insert in Hin_v1.
                    destruct (k == k').
                    -- subst k'. 
    Admitted.
    
    Theorem InterParseOk : forall d, ParseOk (ParseValue d) (SerialValue d).
    Proof.
    Abort.

  End Theorems.

End InterParse.
