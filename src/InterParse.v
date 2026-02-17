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

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.

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

  Section Desc_Field_ind.

    Definition map_size_sum (m : gmap Z Field) (f : Field -> nat) : nat :=
      map_fold (λ _ v acc, f v + acc)%nat 0%nat m.

    (** Structural size metrics for well-founded induction **)
    Fixpoint Desc_size (d : Desc) : nat :=
      match d with
      | DESC fs => 1 + map_size_sum fs Field_size
      end
    with Field_size (f : Field) : nat :=
           match f with
           | F_MSG d => 1 + Desc_size d
           | F_BOOL => 1
           | F_INT => 1
           end.

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

    Lemma Desc_size_fold :
      (fix Desc_size (d : Desc) : nat :=
         match d with
         | DESC fs0 => S (map_fold (λ (_ : Z) (v : Field) (acc : nat), Field_size v + acc) 0 fs0)
         end
       with Field_size (f0 : Field) : nat :=
              match f0 with
              | F_MSG d => S (Desc_size d)
              | _ => 1
              end
                for
                Desc_size)%nat = Desc_size.
    Proof using Type.
      reflexivity.
    Qed.

    Lemma Field_size_fold :
      (fix Desc_size (d : Desc) : nat :=
         match d with
         | DESC fs0 => S (map_fold (λ (_ : Z) (v : Field) (acc : nat), Field_size v + acc) 0 fs0)
         end
       with Field_size (f0 : Field) : nat :=
              match f0 with
              | F_MSG d => S (Desc_size d)
              | _ => 1
              end
                for
                Field_size)%nat = Field_size.
    Proof using Type.
      reflexivity.
    Qed.

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
            unfold Desc_size, map_size_sum, MR.
            rewrite map_fold_insert_L.
            -- simpl; rewrite ?Field_size_fold; 
                 pose proof (Field_size_positive f); lia.
            -- simpl; rewrite !Field_size_fold; intros; lia.
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
          unfold Desc_size, map_size_sum, MR.
          simpl; rewrite Desc_size_fold. lia.
          
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

    Definition val_map_size_sum (m : gmap Z Val) (f : Val -> nat) : nat :=
      map_fold (λ _ v acc, f v + acc)%nat 0%nat m.

    (** Structural size metrics for well-founded induction ***)
    Fixpoint Value_size (v : Value) : nat :=
      match v with
      | VALUE vs => 1 + val_map_size_sum vs Val_size
      end
    with Val_size (v : Val) : nat :=
           match v with
           | V_MSG val => 1 + Value_size val
           | V_BOOL _ => 1
           | V_INT _ => 1
           | V_MISSING => 1
           end.

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

    Lemma Value_size_fold :
      (fix Value_size (v : Value) : nat :=
         match v with
         | VALUE vs0 => S (map_fold (λ (_ : Z) (v : Val) (acc : nat), Val_size v + acc) 0 vs0)
         end
       with Val_size (v0 : Val) : nat :=
              match v0 with
              | V_MSG val => S (Value_size val)
              | _ => 1
              end
                for
                Value_size)%nat = Value_size.
    Proof using Type.
      reflexivity.
    Qed.

    Lemma Val_size_fold :
      (fix Value_size (v : Value) : nat :=
         match v with
         | VALUE vs0 => S (map_fold (λ (_ : Z) (v : Val) (acc : nat), Val_size v + acc) 0 vs0)
         end
       with Val_size (v0 : Val) : nat :=
              match v0 with
              | V_MSG val => S (Value_size val)
              | _ => 1
              end
                for
                Val_size)%nat = Val_size.
    Proof using Type.
      reflexivity.
    Qed.

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
            unfold Value_size, val_map_size_sum, MR.
            rewrite map_fold_insert_L.
            -- simpl; rewrite ?Val_size_fold;
                 pose proof (Val_size_positive v); lia.
            -- simpl; rewrite !Val_size_fold; intros; lia.
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
          unfold Value_size, val_map_size_sum, MR.
          simpl; rewrite Value_size_fold. lia.

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

    Lemma Valid'_fold :
      (fix Valid' (d : Desc) (v0 : Value) {struct v0} : Prop :=
         match d with
         | DESC fs0 => match v0 with
                      | VALUE vs => map_fold (Valid'__fold fs0) True vs
                      end
         end
       with Valid'__fold (fs0 : gmap Z Field) (k0 : Z) (v0 : Val) (acc : Prop) {struct v0} : Prop :=
              match v0 with
              | V_MSG value => (∃ d : Desc, fs0 !! k0 = Some (F_MSG d) ∧ Valid' d value) ∧ acc
              | V_BOOL _ => fs0 !! k0 = Some F_BOOL ∧ acc
              | V_INT _ => fs0 !! k0 = Some F_INT ∧ acc
              | V_MISSING => True ∧ acc
              end
                for
                Valid')%nat = Valid'.
    Proof using Type.
      reflexivity.
    Qed.

    Lemma Valid'__fold_fold :
      (fix Valid' (d : Desc) (v0 : Value) {struct v0} : Prop :=
         match d with
         | DESC fs0 => match v0 with
                      | VALUE vs => map_fold (Valid'__fold fs0) True vs
                      end
         end
       with Valid'__fold (fs0 : gmap Z Field) (k0 : Z) (v0 : Val) (acc : Prop) {struct v0} : Prop :=
              match v0 with
              | V_MSG value => (∃ d : Desc, fs0 !! k0 = Some (F_MSG d) ∧ Valid' d value) ∧ acc
              | V_BOOL _ => fs0 !! k0 = Some F_BOOL ∧ acc
              | V_INT _ => fs0 !! k0 = Some F_INT ∧ acc
              | V_MISSING => True ∧ acc
              end
                for
                Valid'__fold)%nat = Valid'__fold.
    Proof using Type.
      reflexivity.
    Qed.

    Lemma ValidInsert (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) :
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      Valid' d (VALUE (<[k := v]> m)) <-> Valid'__fold (Fields d) k v True /\ Valid' d (VALUE m).
    Proof.
      intros Hnone Hfst.
      split.
      - destruct d; unfold Valid' at 1.
        rewrite map_fold_insert_first_key by assumption.
        rewrite Valid'__fold_fold. intros Hvalid.
        split.
        + destruct v;
            (split; last easy);
            unfold Valid'__fold at 1 in Hvalid;
            destruct Hvalid as [Hvalid  _]; assumption.
        + destruct v; unfold Valid'__fold at 1 in Hvalid;
            destruct Hvalid as [_ Hvalid]; assumption.
      - intros [Hfst_valid Hrest_valid].
        destruct d; unfold Valid'.
        rewrite map_fold_insert_first_key by assumption.
        rewrite Valid'__fold_fold.
        destruct v;
          unfold Valid'__fold at 1;
          destruct Hfst_valid as [Hfst_valid _] in Hfst_valid;
          unfold Valid' in Hrest_valid; split; assumption.
    Qed.

    Lemma ValueEncLen'__fold_linear :
      forall (fs : gmap Z Field) k v acc,
        ValueEncLen'__fold fs k v acc = (ValueEncLen'__fold fs k v 0 + acc)%nat.
    Proof.
      intros fs k v acc.
      destruct (fs !! k) eqn:Hfield; [destruct f|]; destruct v; simpl; rewrite ?Hfield; lia.
    Qed.

    Lemma ValueEncLength_unfold (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) :
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      ValueEncLen' d (VALUE (<[k := v]> m)) =
      (ValueEncLen'__fold (Fields d) k v 0 + ValueEncLen' d (VALUE m))%nat.
    Proof.
      intros Hnone Hfst.
      destruct d as [fs].
      unfold Fields, ValueEncLen' at 1.
      rewrite map_fold_insert_first_key by assumption.
      unfold ValueEncLen'.
      rewrite ValueEncLen'__fold_linear.
      reflexivity.
    Qed.

    (** Values nested in a map have strictly smaller depth **)
    Lemma Val_in_map_smaller_depth :
      forall (m : gmap Z Val) k v,
      m !! k = Some (V_MSG v) ->
      (ValueDepth v < ValueDepth (VALUE m))%nat.
    Proof.
      intros m k v Hlookup.
      (* Simplified proof: Just unfold and use the structure of ValueDepth *)
      unfold ValueDepth.
      (* By structural analysis: if m !! k = Some (V_MSG v), then when we fold
         over m, we encounter V_MSG v at key k, which contributes ValueDepth v + 1
         to the accumulator's max. Since the final result is this max, we have
         ValueDepth v < final_result *)
      (* This is actually provable without induction using just the definition *)
      (* For now, admit this - it's intuitively obvious but requires careful reasoning about map_fold *)
      admit.
    Admitted.

    Lemma SerializeValueInversion (d : Desc) :
      forall k v (m : gmap Z Val) enc,
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      SerialValue d (VALUE (<[k := v]> m)) = S.Success enc <->
      exists enc__v enc__rest, SerialValue d (VALUE m) = S.Success enc__rest /\
                      SerialVal (SerialValue) d (k, v) = S.Success enc__v /\
                      enc = App enc__v enc__rest.
    Proof.
      split.
      - unfold SerialValue at 1, S.RecursiveState.
        rewrite ser_recur_st_unfold.
        unfold SerialValue', S.Map, ValList, Vals.
        rewrite map_to_list_insert_first_key by assumption.
        intros Hser. rewrite SerialRepInversion_First in Hser.
        destruct Hser as (enc__v & enc__rest & Hv_ok & Hrest_ok & Henc).
        subst. exists enc__v, enc__rest.
        split.
        * unfold SerialValue, S.RecursiveState.
          rewrite ser_recur_st_unfold.
          unfold SerialValue', S.Map, ValList, Vals, S.Rep.
          (* Key insight: Need to show that the depth bound difference doesn't matter *)
          (* because all elements in map_to_list m have depth < ValueDepth (VALUE m) *)
          (* and ValueDepth (VALUE m) <= ValueDepth (VALUE (<[k:=v]> m)) *)

          (* First establish the depth relationship *)
          assert (Hdepth_le: (ValueDepth (VALUE m) <= ValueDepth (VALUE (<[k:=v]> m)))%nat).
          {
            destruct v eqn:Hv.
            - (* V_MSG case: use ValueDepthDropFirstMsg *)
              apply ValueDepthDropFirstMsg; assumption.
            - (* V_BOOL case: depth stays the same *)
              rewrite ValueDepthDropFirst; try assumption.
              + lia.
              + intros v'. discriminate.
            - (* V_INT case: depth stays the same *)
              rewrite ValueDepthDropFirst; try assumption.
              + lia.
              + intros v'. discriminate.
            - (* V_MISSING case: depth stays the same *)
              rewrite ValueDepthDropFirst; try assumption.
              + lia.
              + intros v'. discriminate.
          }

          (* Now we need to show S.rep' with both serializers gives the same result *)
          (* Key strategy: prove by asserting that for any element in map_to_list m,
             both depth checks will evaluate the same way, so both serializers are equal *)

          (* The proof proceeds by showing that Hrest_ok already gives us what we need,
             just with a looser bound that doesn't affect the result *)

          (* Use generalization to abstract over the specific depth values *)
          assert (Hserializer_equiv: forall kv,
            kv ∈ map_to_list m ->
            SerialVal (λ (st__n : Desc) (x__n : Value),
              if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
              then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
              else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n)
              d kv =
            SerialVal (λ (st__n : Desc) (x__n : Value),
              if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
              then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
              else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n)
              d kv).
          {
            intros [key val] Hin.
            unfold SerialVal.
            (* The serializers only differ in recursive calls on V_MSG values *)
            destruct ((Fields d) !! key); try reflexivity.
            destruct f; try reflexivity.
            (* For F_MSG, we need to show the depth checks evaluate the same *)
            destruct val; try reflexivity.
            (* For V_MSG v0, both depth checks should be true since v0 comes from m *)
            unfold S.Bind', S.Concat.
            destruct (SerialUnsigned key); last reflexivity.
            unfold S.Len'.
            (* Show that both decide expressions evaluate to true *)
            assert (Hlookup: m !! key = Some (V_MSG v0)).
            {
              (* (key, V_MSG v0) ∈ map_to_list m implies m !! key = Some (V_MSG v0) *)
              apply elem_of_map_to_list in Hin.
              assumption.
            }
            destruct (decide (ValueDepth v0 < ValueDepth (VALUE m))%nat) eqn:Hm.
            * destruct (decide (ValueDepth v0 < ValueDepth (VALUE (<[k := v]> m)))%nat) eqn:Hn;
                (reflexivity || lia).
            * destruct (decide (ValueDepth v0 < ValueDepth (VALUE (<[k := v]> m)))%nat) eqn:Hn.
              + pose proof (Val_in_map_smaller_depth m key v0 Hlookup). lia.
              + unfold S.RecursiveProgressError.
                destruct (ValueDepth v0 == ValueDepth (VALUE m)), (ValueDepth v0 == ValueDepth (VALUE (<[k := v]> m))); admit.
          }

          (* Now use the equivalence to transform Hrest_ok into what we need *)
          (* Apply induction on map_to_list m to show both S.rep' calls are equal *)
          (* clear Hdepth_le. (* No longer needed *) *)

          generalize dependent enc__rest.
          induction (map_to_list m) as [|[k' v'] xs IH].
          -- (* Empty map case *)
             intros enc__rest Hrest_ok.
             unfold S.Rep in Hrest_ok.
             rewrite !ser_rep'_unfold in *.
             assumption.
          -- (* Non-empty map case *)
             intros enc__rest Hrest_ok.
             unfold S.Rep in *.
             rewrite !ser_rep'_unfold in *.
             (* Use Hserializer_equiv to rewrite the first element serialization *)
             assert (H_equiv_first:
               SerialVal (λ st__n x__n,
                 if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
                 then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                 else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n) d (k', v') =
               SerialVal (λ st__n x__n,
                 if decide (ValueDepth x__n < ValueDepth (VALUE m))%nat
                 then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                 else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE m) x__n) d (k', v')).
             { apply Hserializer_equiv. apply list_elem_of_here. }
             (* Rewrite the first element serialization using equivalence *)
             unfold SerialValue' in H_equiv_first.
        (*      rewrite <- H_equiv_first in Hrest_ok. *)
        (*      (* Pattern match on serialization results *) *)
        (*      destruct (SerialVal _ d (k', v')) as [enc_first|] eqn:Hser_first; [|discriminate]. *)
        (*      destruct (S.rep' _ xs) as [enc_tail|] eqn:Hser_tail; [|discriminate]. *)
        (*      (* Hrest_ok is now: S.Success (App enc_first enc_tail) = S.Success enc__rest *) *)
        (*      injection Hrest_ok as Henc__rest. subst enc__rest. *)
        (*      (* Now apply IH to show the tail serializes correctly *) *)
        (*      f_equal. *)
        (*      apply IH. *)
        (*      { (* Need to show serializer_equiv for all elements in xs *) *)
        (*        intros kv Hkv_in. *)
        (*        apply Hserializer_equiv. *)
        (*        apply list_elem_of_tail. *)
        (*        assumption. *)
        (*      } *)
        (*      assumption. *)
        (* * split; assumption. *)
             admit.
        * admit.
      - (* Reverse direction: <- *)
        admit.
    Admitted.

    Definition ValueEncLength_P (v : Value) :=
      forall d enc,
      Valid' d v ->
      SerialValue d v = S.Success enc ->
      Length enc = ValueEncLen' d v.

    Definition ValEncLength_P (v : Val) := True.

    Lemma ValueEncLength_Length : forall v, ValueEncLength_P v.
    Proof.
      induction v using Value_ind' with
        (P_Value := ValueEncLength_P)
        (P_Val := ValEncLength_P).
      - induction vs as [| k v m Hno Hfst ] using map_first_key_ind.
        + intros d enc Hvalid Hser; vm_compute in Hser.
          inversion Hser. destruct d; reflexivity.
        + intros d enc Hvalid Hser; unfold S.Output in *. 
          apply SerializeValueInversion in Hser; try assumption.
          destruct Hser as (enc__v & enc__rest & Hv_ok & Henc).
          rewrite ValidInsert in Hvalid by assumption.
          destruct Hvalid as [Hfst_valid Hrest_valid].
          unfold ValueEncLength_P in IHvs.
          rewrite map_Forall_insert in H by assumption.
          destruct H as [Hlen_v' Hlen_rest].
          specialize (IHvs Hlen_rest d enc__rest Hrest_valid Hv_ok).
          rewrite ValueEncLength_unfold by assumption.
          rewrite <- IHvs. destruct d; simpl.
          admit.
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    
    (*   - intros d enc Hvalid Hser. *)
    (*     vm_compute in Hser. inversion Hser. *)
    (*     destruct d. reflexivity. *)
    (*   - intros d enc Hvalid. *)
    (*     unfold ValList, Vals. *)
    (*     rewrite map_to_list_insert_first_key by assumption. *)
    (*     rewrite ser_rep'_unfold. *)
    (*     destruct v as [v' | b | z' |] eqn:Hv. *)
    (*     + simpl. destruct d. *)
    (*       destruct (Fields (DESC fs) !! z) eqn:Hf. *)
    (*       * destruct f. *)
    (*         -- destruct (S.Bind' _ _ _ v') eqn:Hv'; last (destruct (S.rep' _ (map_to_list m)); discriminate).  *)
    (*            destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            pose proof (ValueDepthDropFirstMsg z v' m Hno Hfst) as Hv__drop. *)
    (*            admit. *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*       * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*         admit. *)
    (*     + simpl. destruct d. *)
    (*       destruct (Fields (DESC fs) !! z) eqn:Hf. *)
    (*       * destruct f. *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*         -- destruct (S.Bind' _ _ _ b) eqn:Hb; last (destruct (S.rep' _ (map_to_list m)); discriminate). *)
    (*            destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            intros Henc. invc Henc. *)
    (*            rewrite App_Length. *)
    (*            unfold S.Bind' in Hb. *)
    (*            rewrite SerialConcatInversion in Hb. *)
    (*            destruct Hb as (enc__id & enc__b & Hok__id & Hok__b & Henc__f). *)
    (*            unfold SerialUnsigned, SerialByte in Hok__id. *)
    (*            vm_compute in Hok__b. *)
    (*            pose proof (ValidDropFirst (DESC fs) z (V_BOOL b) m Hno Hfst Hvalid) as Hv__drop. *)
    (*            assert (forall v', V_BOOL b <> V_MSG v') as Hneq by done. *)
    (*            pose proof (ValueDepthDropFirst z (V_BOOL b) m Hno Hfst Hneq) as Hd__drop. *)
    (*            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*            unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*            simpl in Hser. *)
    (*            rewrite Hd__drop in Hser. *)
    (*            specialize (IHvs (DESC fs) out0 Hv__drop Hser). *)
    (*            destruct b; ( *)
    (*                          rewrite Henc__f, App_Length; invc Hok__id; invc Hok__b; *)
    (*                          unfold Length; simpl; *)
    (*                          rewrite map_fold_insert_first_key by assumption; *)
    (*                          simpl in *; rewrite Hf, <- IHvs; unfold Length; lia *)
    (*                        ). *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*       * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*         pose proof (ValidDropFirst (DESC fs) z (V_BOOL b) m Hno Hfst Hvalid) as Hv__drop. *)
    (*         assert (forall v', V_BOOL b <> V_MSG v') as Hneq by done. *)
    (*         pose proof (ValueDepthDropFirst z (V_BOOL b) m Hno Hfst Hneq) as Hd__drop. *)
    (*         simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*         unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*         simpl in Hser. *)
    (*         rewrite Hd__drop in Hser. *)
    (*         specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*         intros Henc'. invc Henc'. *)
    (*         rewrite map_fold_insert_first_key by assumption. *)
    (*         simpl in *. rewrite Hf. assumption. *)
    (*     + simpl. destruct d. *)
    (*       destruct (Fields (DESC fs) !! z) eqn:Hf. *)
    (*       * destruct f. *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*         -- destruct (S.rep' _ (map_to_list m)); discriminate. *)
    (*         -- destruct (S.Bind' _ _ _ z') eqn:Hz'; last (destruct (S.rep' _ (map_to_list m)); discriminate). *)
    (*            destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            intros Henc. invc Henc. *)
    (*            rewrite App_Length. *)
    (*            unfold S.Bind' in Hz'. *)
    (*            rewrite SerialConcatInversion in Hz'. *)
    (*            destruct Hz' as (enc__id & enc__z' & Hok__id & Hok__z' & Henc__f). *)
    (*            unfold SerialUnsigned, SerialByte in Hok__id. *)
    (*            pose proof (ValidDropFirst (DESC fs) z (V_INT z') m Hno Hfst Hvalid) as Hv__drop. *)
    (*            assert (forall v', V_INT z' <> V_MSG v') as Hneq by done. *)
    (*            pose proof (ValueDepthDropFirst z (V_INT z') m Hno Hfst Hneq) as Hd__drop. *)
    (*            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*            unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*            simpl in Hser. *)
    (*            rewrite Hd__drop in Hser. *)
    (*            specialize (IHvs (DESC fs) out0 Hv__drop Hser). *)
    (*            rewrite Henc__f, App_Length. invc Hok__id. invc Hok__z'. *)
    (*            unfold Length; simpl. *)
    (*            rewrite map_fold_insert_first_key by assumption. *)
    (*            simpl in *; rewrite Hf, <- IHvs; unfold Length. lia. *)
    (*       * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*         pose proof (ValidDropFirst (DESC fs) z (V_INT z') m Hno Hfst Hvalid) as Hv__drop. *)
    (*         assert (forall v', V_INT z' <> V_MSG v') as Hneq by done. *)
    (*         pose proof (ValueDepthDropFirst z (V_INT z') m Hno Hfst Hneq) as Hd__drop. *)
    (*         simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*         unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*         simpl in Hser. *)
    (*         rewrite Hd__drop in Hser. *)
    (*         specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*         intros Henc'. invc Henc'. *)
    (*         rewrite map_fold_insert_first_key by assumption. *)
    (*         simpl in *. rewrite Hf. assumption. *)
    (*     + simpl. destruct (Fields d !! z). *)
    (*       * destruct f. *)
    (*         -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            destruct d. *)
    (*            pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop. *)
    (*            assert (forall v', V_MISSING <> V_MSG v') as Hneq by done. *)
    (*            pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop. *)
    (*            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*            unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*            simpl in Hser. *)
    (*            rewrite Hd__drop in Hser. *)
    (*            specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*            intros Henc'. invc Henc'. *)
    (*            rewrite map_fold_insert_first_key by assumption. *)
    (*            simpl in *. destruct (fs !! z); last assumption. *)
    (*            destruct f; assumption. *)
    (*         -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            destruct d. *)
    (*            pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop. *)
    (*            assert (forall v', V_MISSING <> V_MSG v') as Hneq by done. *)
    (*            pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop. *)
    (*            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*            unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*            simpl in Hser. *)
    (*            rewrite Hd__drop in Hser. *)
    (*            specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*            intros Henc'. invc Henc'. *)
    (*            rewrite map_fold_insert_first_key by assumption. *)
    (*            simpl in *. destruct (fs !! z); last assumption. *)
    (*            destruct f; assumption. *)
    (*         -- destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*            destruct d. *)
    (*            pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop. *)
    (*            assert (forall v', V_MISSING <> V_MSG v') as Hneq by done. *)
    (*            pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop. *)
    (*            simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*            unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*            simpl in Hser. *)
    (*            rewrite Hd__drop in Hser. *)
    (*            specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*            intros Henc'. invc Henc'. *)
    (*            rewrite map_fold_insert_first_key by assumption. *)
    (*            simpl in *. destruct (fs !! z); last assumption. *)
    (*            destruct f; assumption. *)
    (*       * destruct (S.rep' _ (map_to_list m)) eqn:Hser; last discriminate. *)
    (*         destruct d. *)
    (*         pose proof (ValidDropFirst (DESC fs) z (V_MISSING) m Hno Hfst Hvalid) as Hv__drop. *)
    (*         assert (forall v', V_MISSING <> V_MSG v') as Hneq by done. *)
    (*         pose proof (ValueDepthDropFirst z (V_MISSING) m Hno Hfst Hneq) as Hd__drop. *)
    (*         simpl in Hd__drop, IHvs; rewrite Hd__drop in Hser. *)
    (*         unfold S.RecursiveProgressError in Hser, IHvs. *)
    (*         simpl in Hser. *)
    (*         rewrite Hd__drop in Hser. *)
    (*         specialize (IHvs (DESC fs) out Hv__drop Hser). *)
    (*         intros Henc'. invc Henc'. *)
    (*         rewrite map_fold_insert_first_key by assumption. *)
    (*         simpl in *. destruct (fs !! z); last assumption. *)
    (*         destruct f; assumption. *)
    (* Admitted. *)

  End Theorems.

End InterParse.
