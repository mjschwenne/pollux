(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux.parse Require Import Input.
From Pollux.parse Require Import Castor.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Module InterParse.
  Module C := Castor (ByteInput).
  Import C.

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
              | byt :: rest => Success byt rest
              | [] => Failure Recoverable (mkData "No more data to parse" inp None)
              end.

    Definition ParseUnsigned : P.Parser Z := P.Map ParseByte word.unsigned.

    Definition ParseNat : P.Parser nat := P.Map ParseByte (fun b => Z.to_nat $ word.unsigned b).

    (* Parse n bytes into an unsigned integer *)
    Definition ParseZN (n : nat) := P.Map (P.RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                       (n + 8, new ≪ n + v))
                                         n (0, 0))
                                    (fun ret => let (_, z) := ret in z).

    Definition ParseZ32 := ParseZN 4%nat.

    Definition ParseBool : P.Parser bool := P.Map ParseZ32 (fun z => z >? 0).

    Definition ParseVal (parse__msg : Desc -> P.Parser Value) (d : Desc) : P.Parser (Z * Val) :=
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
    Definition ParseValue' (self : Desc -> P.Parser Value) (d : Desc) : P.Parser Value :=
      P.Map (P.Rep (ParseVal self d)) (fun vs => list_to_value d vs).

    Definition ParseValue (d : Desc) : P.Parser Value :=
      P.RecursiveState ParseValue' d.

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

    Example depth1 : ValueDepth val1 = 0%nat. 
    Proof. vm_compute; reflexivity. Qed.
    Example depth2 : ValueDepth val2 = 1%nat.
    Proof. vm_compute; reflexivity. Qed.
    Example depth3 : ValueDepth val3 = 2%nat.
    Proof. vm_compute; reflexivity. Qed.

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

    Example Length1 : ValueEncLen val1 = length fenc3.
    Proof. reflexivity. Qed.

    Example Length2 : ValueEncLen val2 = length enc2.
    Proof. reflexivity. Qed.

    Example Length3 : ValueEncLen val3 = length enc3.
    Proof. reflexivity. Qed.

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
      S.Serializer (Z * Val) (Val_wf d) := 
      fun val => let (id, v) := val in
              match (Fields d) !! id with
              | Some F_BOOL => match v with
                              | V_BOOL b => S.Bind' (fun _ => id) SerialUnsigned SerialBool b
                              | V_MISSING => S.mkSuccess []
                              | _ => Failure Recoverable
                                      (mkData "Expected Boolean" Input_default None)
                              end
              | Some F_INT => match v with
                             | V_INT z => S.Bind' (fun _ => id) SerialUnsigned SerialZ32 z
                             | V_MISSING => S.mkSuccess []
                             | _ => Failure Recoverable
                                     (mkData "Expected Integer" Input_default None)
                             end
              | Some (F_MSG d') => match v with
                                  | V_MSG z => S.Bind' (fun _ => id) SerialUnsigned
                                                      (S.Len' SerialNat (serial__msg d')) z
                                  | V_MISSING => S.mkSuccess []
                                  | _ => Failure Recoverable
                                          (mkData "Expected nested message" Input_default None)
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

    Definition SerialValue' (self : forall d : Desc, S.Serializer Value $ Value_wf d) (d : Desc) :
      S.Serializer Value $ Value_wf d :=
      S.Map (S.Rep (SerialVal self d : S.Serializer _ (WillEncode d))) (ValList d).

    Definition SerialValue (d : Desc) : S.Serializer Value $ Value_wf d :=
      S.RecursiveState SerialValue' ValueDepth d.

    Definition enc_eq (d : Desc) (v : Value) (e : Input) : bool :=
      match SerialValue d v with
      | Success _ enc => if decide (enc = e) then true else false
      | Failure _ _ => false
      end.

    Definition round_trip (d : Desc) (v : Value) : Prop :=
      match SerialValue d v with
      | Success _ enc => match ParseValue d enc with
                        | Success v' _ => v = v'
                        | Failure _ _ => False
                        end
      | Failure _ _ => False
      end.

    Definition check_multi_enc (d : Desc) (enc1 enc2 : Input) : Prop :=
      match ParseValue d enc1, ParseValue d enc2 with
      | Success v1 _, Success v2 _ => v1 = v2
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

    Infix "≡ᵣ" := result_equiv (at level 70):type_scope.
    Lemma SerialValWeakenDepth (d : Desc) (k : Z) (v : Val) (m : gmap Z Val) : 
      m !! k = None -> map_first_key (<[k := v]> m) k ->
      forall kv,
      kv ∈ ValList d (VALUE m) ->
      SerialVal (λ (st__n : Desc) (x__n : Value),
                   if decide (ValueDepth x__n < ValueDepth (VALUE (<[k:=v]> m)))%nat
                   then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                   else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (VALUE (<[k:=v]> m)) x__n)
        d kv ≡ᵣ
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
                     (ValueDepth val == ValueDepth (VALUE (<[k := v]> m))); done.
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
            rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
            unfold S.mkSuccess in Hrest_ok.
            rewrite <- Hrest_ok.
            (* Need to show that the depth bound difference doesn't matter *)
            (* because all elements in map_to_list m have depth < ValueDepth (VALUE m) *)
            (* Fortunately, that's exactly what SerialValWeakenDepth tells us. *)
            (* Now we need to show S.rep' with both serializers gives the same result *)
            change (
                (λ (self : ∀ d0 : Desc, S.Serializer Value (Value_wf d0)) (d0 : Desc) (a : Value),
                   S.Rep (SerialVal self d0)
                     (filter (ValList_filter_p d0) (map_to_list match a with
                                                                | VALUE vs => vs
                                                                end)))
              ) with SerialValue'.
            rewrite SerialRepSubst.
            -- reflexivity.
            -- symmetry.
               apply SerialValWeakenDepth; assumption.
          * split; last reflexivity.
            change (
                (λ (self : ∀ d : Desc, S.Serializer Value (Value_wf d)) (d : Desc) (a : Value),
                   S.Rep (SerialVal self d)
                     (filter (ValList_filter_p d) (map_to_list match a with
                                                     | VALUE vs => vs
                                                     end)))
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
               rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
               unfold S.mkSuccess in Hser.
               rewrite <- Hser.
               rewrite SerialRepSubst; first reflexivity.
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
             (λ (self : ∀ d0 : Desc, S.Serializer Value (Value_wf d0)) (d0 : Desc) (a : Value),
                S.Rep (SerialVal self d0)
                  (filter (ValList_filter_p d0) (map_to_list match a with
                                                             | VALUE vs => vs
                                                             end)))
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
               (λ (self : ∀ d0 : Desc, S.Serializer Value (Value_wf d0)) (d0 : Desc) (a : Value),
                  S.Rep (SerialVal self d0)
                    (filter (ValList_filter_p d0) (map_to_list match a with
                                                               | VALUE vs => vs
                                                               end)))
              ) with SerialValue'.
            intros Hrest_ok. 
            rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
            rewrite <- Hrest_ok.
            rewrite SerialRepSubst; first reflexivity.
            apply SerialValWeakenDepth; assumption.
        + unfold ValList_filter_p, fst, snd in Hfilter_out.
          unfold SerialVal in Hv_ok.
          unfold SerialValue, S.RecursiveState in Hrest_ok.
          rewrite ser_recur_st_unfold in Hrest_ok.
          destruct (Fields d !! k) eqn:Hin_d.
          * (* v was dropped for being V_MISSING *) 
            destruct v; try (reflexivity || specialize (Hfilter_out I); contradiction).
            destruct f;
              invc Hv_ok; rewrite App_nil_l; unfold S.mkSuccess, SerialValue', S.Map, ValList, Vals in *;
              rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _);
              rewrite <- Hrest_ok;
              rewrite SerialRepSubst; first reflexivity.
            -- apply SerialValWeakenDepth; assumption.
            -- reflexivity.
            -- apply SerialValWeakenDepth; assumption.
            -- reflexivity.
            -- apply SerialValWeakenDepth; assumption.
          * (* v dropped for being unknown *)
            unfold S.mkSuccess in *.
            invc Hv_ok. rewrite App_nil_l.
            rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
            rewrite <- Hrest_ok.
            unfold SerialValue', S.Map, ValList, Vals.
            rewrite SerialRepSubst; first reflexivity.
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

    (** Helper: Check if a field and value match in type *)
    Definition field_val_type_match (f : Field) (v : Val) : Prop :=
      match f, v with
      | F_BOOL, V_BOOL _ => True
      | F_INT, V_INT _ => True
      | F_MSG _, V_MSG _ => True
      | _, _ => False
      end.

    (** The inductive relation *)
    Inductive SchemaCorrect : Desc -> Value -> Prop :=
    | SC_Empty :
      SchemaCorrect (DESC ∅) (VALUE ∅)

    | SC_Insert : forall k f v ds vs,
      (* The field and value must type-match *)
      field_val_type_match f v ->

      (* If it's a message field, the nested descriptor/value must be correct *)
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> SchemaCorrect d' v') ->

      (* The key must be fresh in both maps *)
      ds !! k = None ->
      vs !! k = None ->

      (* The remaining descriptor/value must be correct *)
      SchemaCorrect (DESC ds) (VALUE vs) ->

      (* Then we can insert the new field/value pair *)
      SchemaCorrect (DESC (<[k := f]> ds)) (VALUE (<[k := v]> vs)).

    Notation "'⟨' v '∷' d '⟩'" := (SchemaCorrect d v) (at level 70).

    (** Insert field lemma - direct by constructor *)
    Lemma SC_insert_field : forall k f v ds vs,
      field_val_type_match f v ->
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> ⟨ v' ∷ d' ⟩) ->
      ds !! k = None ->
      vs !! k = None ->
      ⟨ (VALUE vs) ∷ (DESC ds) ⟩ ->
      ⟨ (VALUE (<[k := v]> vs)) ∷ (DESC (<[k := f]> ds)) ⟩.
    Proof.
      intros. apply SC_Insert; assumption.
    Qed.

    (** Empty case lemma *)
    Lemma SC_empty : ⟨ (VALUE ∅) ∷ (DESC ∅) ⟩.
    Proof.
      constructor.
    Qed.

    (* Add some lemmas about the constructor *)
    Lemma SC_Insert_comm : forall k1 k2 f1 f2 v1 v2 ds vs,
      k1 ≠ k2 ->
      ⟨ (VALUE (<[k1 := v1]> (<[k2 := v2]> vs))) ∷ (DESC (<[k1 := f1]> (<[k2 := f2]> ds))) ⟩ ->
      ⟨ (VALUE (<[k2 := v2]> (<[k1 := v1]> vs))) ∷ (DESC (<[k2 := f2]> (<[k1 := f1]> ds))) ⟩.
    Proof.
      intros k1 k2 f1 f2 v1 v2 ds vs Hneq H.
      rewrite insert_insert_ne, (insert_insert_ne vs); (assumption || symmetry; assumption).
    Qed.

    (** Property 1: Every field in value exists in descriptor *)
    Lemma SC_implies_val_in_desc : forall d v,
      ⟨ v ∷ d ⟩ ->
      forall k val, Vals v !! k = Some val -> exists f, Fields d !! k = Some f.
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' val' Hlookup.
      - (* Empty case *)
        simpl in Hlookup. rewrite lookup_empty in Hlookup. discriminate.
      - (* Insert case - straightforward by case analysis on k = k' *)
        unfold Vals in Hlookup. destruct (k == k') as [Heq | Hneq].
        + subst k'. exists f. unfold Fields. rewrite lookup_insert_eq.
          reflexivity.
        + rewrite lookup_insert_ne in Hlookup by assumption.
          specialize (IH k' val' Hlookup).
          destruct IH as [f' Hsome].
          unfold Fields in *. exists f'.
          rewrite lookup_insert_ne by assumption.
          assumption.
    Qed.

    Lemma SC_implies_val_in_desc_typed : forall d v,
      ⟨ v ∷ d ⟩ ->
      forall k val, Vals v !! k = Some val -> exists f, Fields d !! k = Some f /\ field_val_type_match f val.
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' val' Hlookup.
      - (* Empty case *)
        simpl in Hlookup. rewrite lookup_empty in Hlookup. discriminate.
      - (* Insert case - straightforward by case analysis on k = k' *)
        unfold Vals in Hlookup. destruct (k == k') as [Heq | Hneq].
        + subst k'. exists f. unfold Fields. rewrite lookup_insert_eq.
          split; first reflexivity.
          rewrite lookup_insert_eq in Hlookup. invc Hlookup.
          assumption.
        + rewrite lookup_insert_ne in Hlookup by assumption.
          specialize (IH k' val' Hlookup).
          destruct IH as [f' Hsome].
          unfold Fields in *. exists f'.
          rewrite lookup_insert_ne by assumption.
          assumption.
    Qed.

    (** Property 2: Every field in descriptor exists in value *)
    Lemma SC_implies_desc_in_val : forall d v,
      ⟨ v ∷ d ⟩ ->
      forall k f, Fields d !! k = Some f -> exists val, Vals v !! k = Some val.
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' f' Hlookup.
      - simpl in Hlookup. rewrite lookup_empty in Hlookup. discriminate.
      - simpl in Hlookup. destruct (k == k') as [Heq | Hneq].
        + subst k'. exists v. simpl. rewrite lookup_insert_eq.
          reflexivity.
        + rewrite lookup_insert_ne in Hlookup by assumption.
          specialize (IH k' f' Hlookup).
          destruct IH as [v' Hsome].
          exists v'.
          simpl in Hsome; simpl.
          rewrite lookup_insert_ne by assumption.
          assumption.
    Qed.

    Lemma SC_implies_desc_in_val_typed : forall d v,
      ⟨ v ∷ d ⟩ ->
      forall k f, Fields d !! k = Some f -> exists val, Vals v !! k = Some val /\ field_val_type_match f val.
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' f' Hlookup.
      - simpl in Hlookup. rewrite lookup_empty in Hlookup. discriminate.
      - simpl in Hlookup. destruct (k == k') as [Heq | Hneq].
        + subst k'. exists v. simpl. rewrite lookup_insert_eq.
          split; first reflexivity.
          rewrite lookup_insert_eq in Hlookup. invc Hlookup.
          assumption.
        + rewrite lookup_insert_ne in Hlookup by assumption.
          specialize (IH k' f' Hlookup).
          destruct IH as [v' Hsome].
          exists v'.
          simpl in Hsome; simpl.
          rewrite lookup_insert_ne by assumption.
          assumption.
    Qed.

    (** Property 3: No V_MISSING values *)
    Lemma SC_implies_no_missing : forall d v,
      ⟨ v ∷ d ⟩ ->
      forall k, Vals v !! k ≠ Some V_MISSING.
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hv_none H' IH]; intros k'.
      - simpl. rewrite lookup_empty. done.
      - simpl. destruct (k == k') as [Heq | Hneq].
        + subst k'. rewrite lookup_insert_eq.
          destruct v; try done.
          unfold field_val_type_match in Htype.
          destruct f; contradiction.
        + rewrite lookup_insert_ne by assumption.
          apply IH.
    Qed.

    Definition NestedCorrect (d : Desc) (k : Z) (v : Val) : Prop :=
      match Fields d !! k, v with
      | Some (F_MSG d'), V_MSG v' => ⟨ v' ∷ d' ⟩
      | _, _ => True
      end.

    Lemma map_Forall_impl_local :
      ∀ {K : Type} {M : Type → Type} {H0 : ∀ A : Type, Lookup K A (M A)} {A : Type}
        (P Q : K → A → Prop) (m : M A),
      map_Forall P m → (∀ (i : K) (x : A), m !! i = Some x -> P i x → Q i x) → map_Forall Q m.
    Proof.
      intros K M H0 A P Q m.
      intros Hm Hq i x Hi.
      specialize (Hq i x Hi).
      apply Hq.
      rewrite map_Forall_lookup in Hm.
      apply Hm; assumption.
    Qed.

    Lemma list_filter_iff_local:
      ∀ {A : Type} (P1 P2 : A → Prop) {H : ∀ x : A, Decision (P1 x)} {H0 : ∀ x : A, Decision (P2 x)} (l : list A),
        (∀ x : A, x ∈ l -> (P1 x ↔ P2 x)) → filter P1 l = filter P2 l.
    Proof.
      intros. rename H1 into HPdiff. induction l as [|a l IH]; [done|].
      destruct (decide (P1 a)).
      (* TODO: reduce HPdiff down to P1 x <-> P2 x *)
      (* - rewrite !filter_cons_True by naive_solver. by rewrite IH. *)
      (* - rewrite !filter_cons_False by naive_solver. by rewrite IH. *)
    Abort.

    (** Property 4: Nested messages are correct *)
    Lemma SC_implies_nested_correct : forall d v,
      ⟨ v ∷ d ⟩ ->
      map_Forall (NestedCorrect d) (Vals v).
    Proof.
      intros d v H.
      induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hv_none H' IH].
      - apply map_Forall_empty. 
      - simpl. rewrite map_Forall_insert by assumption.
        split.
        + unfold NestedCorrect; simpl.
          destruct (<[k:=f]> ds !! k) as [f' |] eqn:Hfeq; last trivial.
          destruct f' as [d' | |]; try trivial.
          rewrite lookup_insert_eq in Hfeq. inversion Hfeq as [Hf].
          destruct v; try trivial.
          apply HnestedC; done.
        + simpl in IH. apply map_Forall_impl_local with (P := NestedCorrect (DESC ds)). 
          * assumption.
          * intros i x.
            unfold NestedCorrect; simpl.
            intros H.
            destruct (<[k:=f]> ds !! i) as [f' |] eqn:Hdeq; last trivial.
            destruct f' as [d' | |]; try trivial.
            destruct x; try trivial.
            destruct (k == i) as [Heq | Hneq].
            -- subst i. rewrite H in Hv_none. discriminate.
            -- rewrite lookup_insert_ne in Hdeq by assumption.
               rewrite Hdeq. done.
    Qed.

    (** Combined theorem: inductive implies all four properties *)
    Theorem SC_implies_properties : forall d v,
      ⟨ v ∷ d ⟩ ->
      (forall k val, Vals v !! k = Some val -> exists f, Fields d !! k = Some f) /\
      (forall k f, Fields d !! k = Some f -> exists val, Vals v !! k = Some val) /\
      (forall k, Vals v !! k ≠ Some V_MISSING) /\
      map_Forall (NestedCorrect d) (Vals v).
    Proof.
      intros d v H.
      split_and!.
      - apply SC_implies_val_in_desc. assumption.
      - apply SC_implies_desc_in_val. assumption.
      - apply SC_implies_no_missing with (d := d). assumption.
      - apply SC_implies_nested_correct. assumption.
    Qed.

    Lemma SC_delete_key : forall d v k, ⟨ v ∷ d ⟩ -> ⟨ VALUE (delete k (Vals v)) ∷ DESC (delete k (Fields d))⟩.
    Proof.
      intros d v k H.
      induction H.
      - simpl. rewrite !delete_empty. apply SC_empty.
      - simpl. rewrite !delete_insert.
        destruct (k == k0).
        + apply IHSchemaCorrect.
        + simpl in IHSchemaCorrect.
          apply SC_insert_field; try assumption.
          * rewrite lookup_delete_None. right; assumption.
          * rewrite lookup_delete_None. right; assumption.
    Qed.

    Lemma SC_dom_eq : forall ds vs, ⟨ VALUE vs ∷ DESC ds ⟩ -> dom vs ≡ dom ds.
    Proof.
      intros ds vs Hsc.
      rewrite set_equiv.
      intros k. split.
      - intros Hdom.
        rewrite elem_of_dom in Hdom.
        destruct Hdom as [v Hv].
        apply SC_implies_val_in_desc with (k := k) (val := v) in Hsc as Hvd; last done.
        destruct Hvd as [f Hf]; simpl in Hf.
        rewrite elem_of_dom. exists f. exact Hf.
      - intro Hdom.
        rewrite elem_of_dom in Hdom.
        destruct Hdom as [f Hf].
        apply SC_implies_desc_in_val with (k := k) (f := f) in Hsc as Hdv; last done.
        destruct Hdv as [v Hv]; simpl in Hv.
        rewrite elem_of_dom. exists v. exact Hv.
    Qed.

    Inductive SchemaCorrectOrdered : Desc -> Value -> Prop :=
    | SCO_Empty :
      SchemaCorrectOrdered (DESC ∅) (VALUE ∅)

    | SCO_Insert : forall k f v ds vs,
      field_val_type_match f v ->
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> SchemaCorrectOrdered d' v') ->

      (* Key is fresh *)
      ds !! k = None ->
      vs !! k = None ->

      (* NEW: k is the first key in the result *)
      map_first_key (<[k := f]> ds) k ->
      map_first_key (<[k := v]> vs) k ->

      (* Recursive correctness *)
      SchemaCorrectOrdered (DESC ds) (VALUE vs) ->

      SchemaCorrectOrdered (DESC (<[k := f]> ds)) (VALUE (<[k := v]> vs)).

    Notation "'⟪' v '∷' d '⟫'" := (SchemaCorrectOrdered d v) (at level 70).

    (** Insert field lemma - direct by constructor *)
    Lemma SCO_insert_field : forall k f v ds vs,
      field_val_type_match f v ->
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> ⟪ v' ∷ d' ⟫) ->
      ds !! k = None ->
      vs !! k = None ->
      map_first_key (<[k := f]> ds) k ->
      map_first_key (<[k := v]> vs) k ->
      ⟪ (VALUE vs) ∷ (DESC ds) ⟫ ->
      ⟪ (VALUE (<[k := v]> vs)) ∷ (DESC (<[k := f]> ds)) ⟫.
    Proof.
      intros. apply SCO_Insert; assumption.
    Qed.

    (** Empty case lemma *)
    Lemma SCO_empty : ⟪ (VALUE ∅) ∷ (DESC ∅) ⟫.
    Proof.
      constructor.
    Qed.

    Definition SC_SCO_Value_P (v : Value) :=
      forall d,
      ⟨ v ∷ d ⟩ <-> ⟪ v ∷ d ⟫.

    Definition SC_SCO_Val_P (v : Val) :=
      forall d' v',
      v = V_MSG v' -> ⟨ v' ∷ d' ⟩ <-> ⟪ v' ∷ d' ⟫.

    Lemma SC_SCO : forall v, SC_SCO_Value_P v.
    Proof.
      intros v.
      induction v as [vs IHv | v__n | b | x |] using Value_ind' with
          (P_Value := SC_SCO_Value_P)
          (P_Val := SC_SCO_Val_P).
      - intros d.
        split.
        + revert d.
          induction vs as [| k val vs' Hno_vs Hfst_vs] using map_first_key_ind.
          * intros [ds] Hsc. destruct ds using map_first_key_ind.
            -- constructor.
            -- apply SC_implies_desc_in_val with (k := i) (f := x) in Hsc.
               ++ destruct Hsc as [v Hcontra]; simpl in Hcontra.
                  rewrite lookup_empty in Hcontra. discriminate.
               ++ simpl; rewrite lookup_insert_eq. reflexivity.
          * intros [ds] Hsc. apply SC_implies_val_in_desc_typed with (k := k) (val := val) in Hsc as Hvd.  
            -- destruct Hvd as (f & Hvd & Hty); simpl in Hvd.
               set (ds' := delete k ds). assert (ds = <[k := f]> ds') as Hds_eq.
               { unfold ds'. symmetry. apply insert_delete_id. assumption. }
               rewrite Hds_eq in *. clear Hds_eq.
               apply SC_delete_key with (k := k) in Hsc as Hsc'; simpl in Hsc'.
               apply delete_insert_id with (x := val) in Hno_vs as Hdel_vs.
               rewrite Hdel_vs in Hsc'.
               assert (ds' !! k = None) as Hno_ds.
               { unfold ds'. apply lookup_delete_eq. }
               apply delete_insert_id with (x := f) in Hno_ds as Hdel_ds.
               rewrite Hdel_ds in Hsc'.
               assert (map_first_key (<[k:=f]> ds') k) as Hfst_ds.
               {
                 pose proof (SC_dom_eq (<[k:=f]> ds') (<[k:=val]> vs') Hsc) as Hdom.
                 rewrite map_first_key_dom with (m2 := <[k:=f]> ds') in Hfst_vs; assumption.
               }
               rewrite map_Forall_insert in IHv by assumption.
               destruct IHv as [IHval IHv].
               specialize (IHvs IHv _ Hsc'). apply SCO_insert_field; try assumption.
               intros d' v' Hf Hval; subst.
               apply SC_implies_nested_correct in Hsc as Hn; simpl in Hn.
               rewrite map_Forall_insert in Hn by assumption.
               destruct Hn as [Hcor Hn].
               unfold NestedCorrect in Hcor; simpl in Hcor.
               rewrite lookup_insert_eq in Hcor.
               apply IHval in Hcor; last reflexivity.
               exact Hcor.
            -- simpl; rewrite lookup_insert_eq. reflexivity.
        + intros Hsco. induction Hsco; (constructor; assumption).
      - intros d' v' Heq. invc Heq. apply IHv__n.
      - discriminate.
      - discriminate.
      - discriminate.
    Qed.

    (* Use this relation to relate the input value to serialization
       to the output value of parsing. At the moment, we require
       that each value be fully described by the linked descriptor. *)
    (* Naturally, for the moment we're doing to have d1 = d2 which should
       imply the domains of v1 and v2 are the same and the types line up,
       but it doesn't give use that v1 = v2 without something more. *)
    Instance Value_Lookup : Lookup Z Val Value := fun k '(VALUE vs) => vs !! k.
    Lemma Value_lookup_unfold v k :
      v !! k = match v with VALUE vs => vs !! k end.
    Proof. destruct v. reflexivity. Qed.
    Instance Value_Insert : Insert Z Val Value := fun k v '(VALUE vs) => VALUE $ <[k := v]> vs.
    Lemma Value_insert_unfold v k v' :
      <[k := v']> v = match v with VALUE vs => VALUE $ <[k := v']> vs end.
    Proof. destruct v. reflexivity. Qed.
    Hint Rewrite Value_lookup_unfold Value_insert_unfold : value_unfold.
    Instance Desc_Lookup : Lookup Z Field Desc := fun k '(DESC ds) => ds !! k.
    Lemma Desc_lookup_unfold d k :
      d !! k = match d with DESC ds => ds !! k end.
    Proof. destruct d. reflexivity. Qed.
    Instance Desc_Insert : Insert Z Field Desc := fun k f '(DESC ds) => DESC $ <[k := f]> ds.
    Lemma Desc_insert_unfold d k f :
      <[k := f]> d = match d with DESC ds => DESC $ <[k := f]> ds end.
    Proof. destruct d. reflexivity. Qed.
    Hint Rewrite Desc_lookup_unfold Desc_insert_unfold : desc_unfold.

    Inductive Compatible : Desc -> Desc -> Value -> Value -> Prop :=
    | CompatRefl (d1 d2 : Desc) (v : Value) :
      ⟨ v ∷ d1 ⟩ -> ⟨ v ∷ d2 ⟩ -> Compatible d1 d2 v v
    | CompatAdd (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value) (k : Z)
        (f1 f2 : Field) (v'1 v'2 : Val) :
      (* Current descriptors describe the current values *)
      ⟨ v1 ∷ d1 ⟩ -> ⟨ v2 ∷ d2 ⟩ ->
      Compatible d1 d2 v1 v2 ->
      (* New key is actually new *)
      v1 !! k = None ->
      v2 !! k = None ->
      d1 !! k = None ->
      d2 !! k = None ->
      (* New values align *)
      v'1 = v'2 -> f1 = f2 ->
      Compatible (<[k := f1]> d1) (<[k := f2]> d2)
        (<[k := v'1]> v1) (<[k := v'2]> v2).
    
    Notation "'⟨' v1 '∷' d1 '⟩' '≼' '⟨' v2 '∷' d2 '⟩'" := (Compatible d1 d2 v1 v2) (at level 70).

    Definition SC_D_Inv_Value_P (v : Value) :=
      forall d1 d2,
      ⟨ v ∷ d1 ⟩ -> ⟨ v ∷ d2 ⟩ -> d1 = d2.

    Definition SC_D_Inv_Val_P (v : Val) :=
      forall d1 d2 v',
      v = V_MSG v' -> ⟨ v' ∷ d1 ⟩ -> ⟨ v' ∷ d2 ⟩ -> d1 = d2.

    Lemma SC_Desc_inv : forall v, SC_D_Inv_Value_P v.
    Proof.
      induction v as [vs IHv | v__n | b | x |] using Value_ind' with
        (P_Value := SC_D_Inv_Value_P)
        (P_Val := SC_D_Inv_Val_P).
      - intros [ds1] [ds2] Hsc1 Hsc2; f_equal.
        apply map_eq; intro k.
        destruct (ds1 !! k) as [f1 |] eqn:Heq1.
        + destruct (ds2 !! k) as [f2 |] eqn:Heq2.
          * apply SC_implies_desc_in_val_typed with (k := k) (f := f1) in Hsc1 as Hdv; last done.
            destruct Hdv as (v & Hdv & Hty1); simpl in Hdv.
            apply SC_implies_val_in_desc_typed with (k := k) (v := VALUE vs) (val := v) in Hsc2 as Hvd;
              last done.
            destruct Hvd as ( f' & Hvd & Hty2 ); simpl in Hvd.
            rewrite Hvd in Heq2. rewrite <- Heq2. f_equal.
            destruct v.
            -- unfold field_val_type_match in *.
               destruct f1, f'; try contradiction.
               clear Hty1 Hty2; f_equal.
               apply SC_implies_nested_correct in Hsc1 as Hn1.
               apply SC_implies_nested_correct in Hsc2 as Hn2.
               rewrite map_Forall_lookup in Hn1.
               rewrite map_Forall_lookup in Hn2.
               specialize (Hn1 k (V_MSG v) Hdv).
               specialize (Hn2 k (V_MSG v) Hdv).
               unfold NestedCorrect in *; simpl in *.
               rewrite Heq1 in Hn1; rewrite Hvd in Hn2.
               rewrite map_Forall_lookup in IHv.
               specialize (IHv k (V_MSG v) Hdv).
               unfold SC_D_Inv_Val_P in IHv.
               specialize (IHv d d0 v eq_refl Hn1 Hn2).
               assumption.
            -- unfold field_val_type_match in *.
               destruct f1, f'; (contradiction || reflexivity).
            -- unfold field_val_type_match in *.
               destruct f1, f'; (contradiction || reflexivity).
            -- unfold field_val_type_match in *.
               destruct f1, f'; contradiction.
          * apply SC_implies_desc_in_val with (k := k) (f := f1) in Hsc1 as Hdv; last done.
            destruct Hdv as [v Hdv]; simpl in Hdv.
            apply SC_implies_val_in_desc with (k := k) (v := VALUE vs) (val := v) in Hsc2 as Hvd; last done.
            destruct Hvd as [f Hvd]; simpl in Hvd.
            rewrite Heq2 in Hvd. discriminate.
        + destruct (ds2 !! k) as [f2 |] eqn:Heq2.
          * apply SC_implies_desc_in_val with (k := k) (f := f2) in Hsc2 as Hdv; last done.
            destruct Hdv as [v Hdv]; simpl in Hdv.
            apply SC_implies_val_in_desc with (k := k) (v := VALUE vs) (val := v) in Hsc1 as Hvd; last done.
            destruct Hvd as [f Hvd]; simpl in Hvd.
            rewrite Heq1 in Hvd. discriminate.
          * reflexivity.
      - intros d1 d2 v' Heq. invc Heq. apply IHv__n.
      - intros d1 d2 v' Hcontra. discriminate.
      - intros d1 d2 v' Hcontra. discriminate.
      - intros d1 d2 v' Hcontra. discriminate.
    Qed.

    Lemma CompatibleEqual : forall d1 v1 d2 v2,
      ⟨ v1 ∷ d1 ⟩ ≼ ⟨ v2 ∷ d2 ⟩ -> d1 = d2 -> v1 = v2.
    Proof.
      intros d v1 d2 v2 Hcompat.
      induction Hcompat as [? ? | ? ? ? ? ? ? ? ? ? Hsc1 Hsc2 Hcompat ? Hv1_no Hv2_no Hd1_no Hd2_no Hveq Hfeq].
      - reflexivity.
      - subst. intro Hd. f_equal. apply IHHcompat. 
        destruct d1 as [ds1], d2 as [ds2]; autorewrite with desc_unfold in *.
        inversion Hd as [Hds]; clear Hd.
        f_equal.
        rewrite <- (delete_id ds1 k Hd1_no).
        rewrite <- (delete_id ds2 k Hd2_no).
        rewrite <- delete_insert_eq with (m := ds1) (x := f2).
        rewrite <- delete_insert_eq with (m := ds2) (x := f2).
        f_equal. assumption.
    Qed.

    Definition ParseOk_Value_P (v : Value) :=
      forall d, ⟨ v ∷ d ⟩ -> ParseOkCompat'' Compatible ParseValue SerialValue d d v.

    Definition ParseOk_Val_P (v : Val) :=
      forall d k enc,
      Val_wf d (k, v) ->
      SerialVal SerialValue d (k, v) = S.mkSuccess enc.

    Lemma SC_filter : forall vs d, ⟨ VALUE vs ∷ d ⟩ -> ValList d (VALUE vs) = map_to_list vs.
    Proof.
      intros vs'.
      unfold ValList, Vals.
      intros d Hsc. apply SC_SCO in Hsc.
      dependent induction Hsc.
      - rewrite map_to_list_empty, filter_nil. reflexivity.
      - rename H into Hty,
                 H0 into Hnest,
                   H1 into HnestC,
                     H2 into Hds_no,
                       H3 into Hvs_no,
                         H4 into Hds_fst,
                           H5 into Hvs_fst.
        rewrite map_to_list_insert_first_key by assumption.
        rewrite filter_cons_True.
        + f_equal. admit.
        + unfold ValList_filter_p; simpl.
          rewrite lookup_insert_eq.
          destruct v; try trivial.
          destruct f; unfold field_val_type_match in Hty; assumption.
    Admitted.

    Theorem InterParseOk : forall v, ParseOk_Value_P v.
    Proof.
      intros v d Hsc.
      apply RecursiveStateCompatCorrect with (valid_state := fun d v => ⟨ v ∷ d ⟩); last assumption.
      intros st1 st2 x enc rest Hwf__x Hsc__x IH.
      (* Since this relation is designed for equality, it's OK to use exists x'. *)
      unfold SerialValue', ParseValue', S.Map.
      intros Hser. exists x.
      (* TODO: Prove ⟨ VALUE xs ∷ st__1 ⟩ -> ValList st__1 (VALUE xs) = map_to_list xs *)
      destruct x as [xs] eqn:Hx.
    Abort.

  End Theorems.

End InterParse.
