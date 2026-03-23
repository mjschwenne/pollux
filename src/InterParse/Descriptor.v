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

Global Instance gmap_filter K V `{EqDecision K} `{Countable K} : Filter (K * V) (gmap K V) :=
  fun P _ mt => list_to_map (filter P (map_to_list mt)).

Module Descriptor.
  Section Desc.

    (* A descriptor is a primitive or a map from w8 to descriptor *)
    (* Inductive Desc' : Set :=  *)
    (* | D_BOOL *)
    (* | D_INT *)
    (* | D_NEST (fields : gmap Z Desc'). *)

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

    Global Instance Desc_Lookup : Lookup Z Field Desc := fun k '(DESC ds) => ds !! k.
    Global Instance Desc_Insert : Insert Z Field Desc :=
      fun k f '(DESC ds) => DESC $ <[k := f]> ds.
    Global Instance Desc_Empty : Empty Desc := DESC ∅.
    Global Instance Desc_PartialAlter : PartialAlter Z Field Desc :=
      fun f k '(DESC ds) => DESC $ partial_alter f k ds.
    Global Instance Desc_MapFold : MapFold Z Field Desc := fun _ f b '(DESC ds) => map_fold f b ds.
    Global Instance Desc_Delete : Delete Z Desc :=
      fun k '(DESC fs) => DESC (delete k fs).
    Global Instance Desc_Singleton : Singleton (Z * Field) Desc :=
      fun '(k, f) => DESC {[k := f]}.
    Global Instance Desc_Dom : Dom Desc (gset Z) := fun '(DESC ds) => dom ds.
    Global Instance Desc_Filter : Filter (Z * Field) Desc := fun P _ '(DESC ds) => DESC $ list_to_map
                                                                                  (filter P (map_to_list ds)). 

    (* Break the mutual induction to get something that can implement FinMap *)
    Inductive Desc' (T : Type) := DESC' (fs : gmap Z T).
    Inductive Field' :=
    | F_MSG' (d : Desc' Field')
    | F_BOOL'
    | F_INT'.

    Global Instance Desc'_Lookup (T : Type) : Lookup Z T (Desc' T) := fun k '(DESC' _ ds) => ds !! k.
    Global Instance Desc'_Insert (T : Type) : Insert Z T (Desc' T) :=
      fun k f '(DESC' _ ds) => DESC' T $ <[k := f]> ds.
    Global Instance Desc'_Empty (T : Type) : Empty (Desc' T) := DESC' T ∅.
    Global Instance Desc'_PartialAlter (T : Type) : PartialAlter Z T (Desc' T) :=
      fun f k '(DESC' _ ds) => DESC' T $ partial_alter f k ds.
    Global Instance Desc'_MapFold (T : Type) : MapFold Z T (Desc' T) := fun _ f b '(DESC' _ ds) => map_fold f b ds.
    Global Instance Desc'_OMap : OMap Desc' := fun {A B} f '(DESC' _ ds) => DESC' B $ omap f ds.
    Global Instance Desc'_Merge : Merge Desc' :=
      fun {A B C} f '(DESC' _ d__a) '(DESC' _ d__b) => DESC' C $ merge f d__a d__b.
    Global Instance Desc'_FMap : FMap Desc' := fun {A B} f '(DESC' _ ds) => DESC' B $ fmap f ds.

    Global Instance Desc'_FinMap : FinMap Z Desc'.
    Proof.
      split.
      - intros A [mt1] [mt2] Hlookup. f_equal. apply map_eq; assumption.
      - done.
      - intros A f [mt] i.
        unfold partial_alter, Desc'_PartialAlter.
        unfold lookup, Desc'_Lookup.
        apply lookup_partial_alter_eq. 
      - intros A f [mt] i j H.
        unfold partial_alter, Desc'_PartialAlter.
        unfold lookup, Desc'_Lookup.
        apply lookup_partial_alter_ne; assumption.
      - intros A B f [mt] i.
        unfold fmap, Desc'_FMap.
        unfold lookup, Desc'_Lookup.
        apply lookup_fmap.
      - intros A B f [mt] i.
        unfold omap, Desc'_OMap.
        unfold lookup, Desc'_Lookup.
        apply lookup_omap.
      - intros A B C f [mt1] [mt2] i.
        unfold merge, Desc'_Merge.
        unfold lookup, Desc'_Lookup.
        apply lookup_merge.
      - done.
      - intros A P Hemp Hins [mt].
        apply (map_first_key_ind (M := gmap Z) (fun m => P (DESC' A m))).
        + exact Hemp.
        + intros i x m Hlookup Hfst IH.
          fold (Desc'_Insert A i x (DESC' A m)). 
          fold (insert i x (DESC' A m)).
          apply Hins.
          * unfold lookup, Desc'_Lookup. exact Hlookup.
          * intros A' B f g b x'. simpl.
            unfold map_fold, Desc'_MapFold; simpl.
            change (fun _ : option A' => Some x') with (fun _ : option A' => id (Some x')).
            rewrite <- partial_alter_insert_eq with (f := id); simpl.
            replace (partial_alter id i (<[i:=x']> (g <$> m))) with (<[i:=x']> (g <$> m)).
            2: {
              apply map_eq. intros j.
              destruct (decide (i = j)) as [<- | Hne].
              - rewrite lookup_partial_alter. destruct (i == i); done.
              - rewrite lookup_partial_alter_ne; done.
            }
            apply map_fold_insert_first_key.
            -- rewrite lookup_fmap, Hlookup. done.
            -- eapply (map_first_key_dom (<[i:=x]> m) (<[i:=x']> (g <$> m)) i).
               ++ (* dom (<[i:=x]> m) ≡ dom (<[i:=x']> (g <$> m)) *)
                 rewrite !dom_insert_L, dom_fmap_L. done.
               ++ (* map_first_key (<[i:=x]> m) i *)
                 exact Hfst.
          * exact IH.
    Qed.

    Fixpoint Desc_to_Desc' (d : Desc) : Desc' Field' :=
      match d with
      | DESC fs => DESC' Field' (Field_to_Field' <$> fs)
      end
    with Field_to_Field' (f : Field) : Field' :=
           match f with
           | F_MSG d => F_MSG' (Desc_to_Desc' d)
           | F_BOOL => F_BOOL'
           | F_INT => F_INT'
           end.

    Definition Fields (d : Desc) : gmap Z Field :=
      match d with
      | DESC fs => fs
      end.

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

  Section Desc_lemmas.
    (* ==================== UNFOLDING LEMMAS ==================== *)
    (* Move operations inward to the underlying gmap *)

    Lemma Desc_lookup_unfold (d : Desc) (k : Z) :
      d !! k = match d with DESC fs => fs !! k end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_insert_unfold (d : Desc) (k : Z) (f : Field) :
      <[k := f]> d = match d with DESC fs => DESC (<[k := f]> fs) end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_empty_unfold : (∅ : Desc) = DESC ∅.
    Proof. reflexivity. Qed.

    Lemma Desc_singleton_unfold (k : Z) (f : Field) :
      ({[k := f]} : Desc) = DESC {[k := f]}.
    Proof. reflexivity. Qed.

    Lemma Desc_delete_unfold (d : Desc) (k : Z) :
      delete k d = match d with DESC fs => DESC (delete k fs) end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_alter_unfold (g : Field → Field) (d : Desc) (k : Z) :
      alter g k d = match d with DESC fs => DESC (alter g k fs) end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_partial_alter_unfold (g : option Field → option Field) (d : Desc) (k : Z) :
      partial_alter g k d = match d with DESC fs => DESC (partial_alter g k fs) end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_map_fold_unfold {A} (f : Z → Field → A → A) (acc : A) (d : Desc) :
      map_fold f acc d = match d with DESC fs => map_fold f acc fs end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_filter_unfold (P : Z * Field → bool) (d : Desc) :
      filter P d = match d with DESC fs => DESC (filter P fs) end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_dom_unfold (d : Desc) :
      dom d = match d with DESC fs => dom fs end.
    Proof. destruct d. reflexivity. Qed.

    Lemma Desc_map_to_list_unfold (d : Desc) :
      map_to_list d = match d with DESC fs => map_to_list fs end.
    Proof. destruct d. reflexivity. Qed.

    (* ==================== FOLDING LEMMAS ==================== *)
    (* Move operations outward for applying IH *)

    Lemma Desc_lookup_fold (fs : gmap Z Field) (k : Z) :
      fs !! k = (DESC fs) !! k.
    Proof. reflexivity. Qed.

    Lemma Desc_insert_fold (fs : gmap Z Field) (k : Z) (f : Field) :
      DESC (<[k := f]> fs) = <[k := f]> (DESC fs).
    Proof. reflexivity. Qed.

    Lemma Desc_empty_fold : DESC ∅ = (∅ : Desc).
    Proof. reflexivity. Qed.

    Lemma Desc_singleton_fold (k : Z) (f : Field) :
      DESC {[k := f]} = ({[k := f]} : Desc).
    Proof. reflexivity. Qed.

    Lemma Desc_delete_fold (fs : gmap Z Field) (k : Z) :
      DESC (delete k fs) = delete k (DESC fs).
    Proof. reflexivity. Qed.

    Lemma Desc_alter_fold (g : Field → Field) (fs : gmap Z Field) (k : Z) :
      DESC (alter g k fs) = alter g k (DESC fs).
    Proof. reflexivity. Qed.

    Lemma Desc_partial_alter_fold (g : option Field → option Field) (fs : gmap Z Field) (k : Z) :
      DESC (partial_alter g k fs) = partial_alter g k (DESC fs).
    Proof. reflexivity. Qed.

    Lemma Desc_map_fold_fold {A} (f : Z → Field → A → A) (b : A) (fs : gmap Z Field) :
      map_fold f b fs = map_fold f b (DESC fs).
    Proof. reflexivity. Qed.

    Lemma Desc_filter_fold (P : Z * Field → bool) (fs : gmap Z Field) :
      DESC (filter P fs) = filter P (DESC fs).
    Proof. reflexivity. Qed.

  End Desc_lemmas.

  Section Value.

    Inductive Value : Set := VALUE (vs : gmap Z Val)
    with
      Val :=
    | V_MSG (v : Value)
    | V_BOOL (b : bool)
    | V_INT (z : Z)
    | V_MISSING.

    Global Instance Value_Lookup : Lookup Z Val Value := fun k '(VALUE vs) => vs !! k.
    Global Instance Value_Insert : Insert Z Val Value := fun k v '(VALUE vs) => VALUE $ <[k := v]> vs.
    Global Instance Value_Empty : Empty Value := VALUE ∅.
    Global Instance Value_PartialAlter : PartialAlter Z Val Value :=
      fun f k '(VALUE ds) => VALUE $ partial_alter f k ds.
    Global Instance Value_MapFold : MapFold Z Val Value := fun _ f b '(VALUE ds) => map_fold f b ds.
    Global Instance Value_Delete : Delete Z Value :=
      fun k '(VALUE vs) => VALUE (delete k vs).
    Global Instance Value_Singleton : Singleton (Z * Val) Value :=
      fun '(k, v) => VALUE {[k := v]}.
    Global Instance Value_Dom : Dom Value (gset Z) := fun '(VALUE vs) => dom vs.
    Global Instance Value_Filter : Filter (Z * Val) Value := fun P _ '(VALUE vs) => VALUE $ list_to_map
                                                                                  (filter P (map_to_list vs)). 
    Inductive Value' (T : Type) : Type := VALUE' (vs : gmap Z T).
    (* Break the mutual induction to get something that can implement FinMap *)
    Inductive Val' :=
    | V_MSG' (v : Value' Val')
    | V_BOOL' (b : bool)
    | V_INT' (z : Z)
    | V_MISSING'.

    Global Instance Value'_Lookup (T : Type) : Lookup Z T (Value' T) := fun k '(VALUE' _ ds) => ds !! k.
    Global Instance Value'_Insert (T : Type) : Insert Z T (Value' T) :=
      fun k f '(VALUE' _ ds) => VALUE' T $ <[k := f]> ds.
    Global Instance Value'_Empty (T : Type) : Empty (Value' T) := VALUE' T ∅.
    Global Instance Value'_PartialAlter (T : Type) : PartialAlter Z T (Value' T) :=
      fun f k '(VALUE' _ ds) => VALUE' T $ partial_alter f k ds.
    Global Instance Value'_MapFold (T : Type) : MapFold Z T (Value' T) :=
      fun _ f b '(VALUE' _ ds) => map_fold f b ds.
    Global Instance Value'_OMap : OMap Value' := fun {A B} f '(VALUE' _ ds) => VALUE' B $ omap f ds.
    Global Instance Value'_Merge : Merge Value' :=
      fun {A B C} f '(VALUE' _ d__a) '(VALUE' _ d__b) => VALUE' C $ merge f d__a d__b.
    Global Instance Value'_FMap : FMap Value' := fun {A B} f '(VALUE' _ ds) => VALUE' B $ fmap f ds.

    Global Instance Value'_FinMap : FinMap Z Value'.
    Proof.
      split.
      - intros A [mt1] [mt2] Hlookup. f_equal. apply map_eq; assumption.
      - done.
      - intros A f [mt] i.
        unfold partial_alter, Value'_PartialAlter.
        unfold lookup, Value'_Lookup.
        apply lookup_partial_alter_eq. 
      - intros A f [mt] i j H.
        unfold partial_alter, Value'_PartialAlter.
        unfold lookup, Value'_Lookup.
        apply lookup_partial_alter_ne; assumption.
      - intros A B f [mt] i.
        unfold fmap, Value'_FMap.
        unfold lookup, Value'_Lookup.
        apply lookup_fmap.
      - intros A B f [mt] i.
        unfold omap, Value'_OMap.
        unfold lookup, Value'_Lookup.
        apply lookup_omap.
      - intros A B C f [mt1] [mt2] i.
        unfold merge, Value'_Merge.
        unfold lookup, Value'_Lookup.
        apply lookup_merge.
      - done.
      - intros A P Hemp Hins [mt].
        apply (map_first_key_ind (M := gmap Z) (fun m => P (VALUE' A m))).
        + exact Hemp.
        + intros i x m Hlookup Hfst IH.
          fold (Value'_Insert A i x (VALUE' A m)). 
          fold (insert i x (VALUE' A m)).
          apply Hins.
          * unfold lookup, Value'_Lookup. exact Hlookup.
          * intros A' B f g b x'. simpl.
            unfold map_fold, Value'_MapFold; simpl.
            change (fun _ : option A' => Some x') with (fun _ : option A' => id (Some x')).
            rewrite <- partial_alter_insert_eq with (f := id); simpl.
            replace (partial_alter id i (<[i:=x']> (g <$> m))) with (<[i:=x']> (g <$> m)).
            2: {
              apply map_eq. intros j.
              destruct (decide (i = j)) as [<- | Hne].
              - rewrite lookup_partial_alter. destruct (i == i); done.
              - rewrite lookup_partial_alter_ne; done.
            }
            apply map_fold_insert_first_key.
            -- rewrite lookup_fmap, Hlookup. done.
            -- eapply (map_first_key_dom (<[i:=x]> m) (<[i:=x']> (g <$> m)) i).
               ++ (* dom (<[i:=x]> m) ≡ dom (<[i:=x']> (g <$> m)) *)
                 rewrite !dom_insert_L, dom_fmap_L. done.
               ++ (* map_first_key (<[i:=x]> m) i *)
                 exact Hfst.
          * exact IH.
    Qed.

    Fixpoint Value_to_Value' (v : Value) : Value' Val' :=
      match v with
      | VALUE vs => VALUE' Val' (Val_to_Val' <$> vs)
      end
    with Val_to_Val' (v : Val) : Val' :=
           match v with
           | V_MSG v => V_MSG' (Value_to_Value' v)
           | V_BOOL b => V_BOOL' b
           | V_INT z => V_INT' z
           | V_MISSING => V_MISSING'
           end.

    Definition Vals (v : Value) : gmap Z Val :=
      match v with
      | VALUE vs => vs
      end.

  End Value.

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

Section Value_lemmas.
    (* ==================== UNFOLDING LEMMAS ==================== *)

    Lemma Value_lookup_unfold (v : Value) (k : Z) :
      v !! k = match v with VALUE vs => vs !! k end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_insert_unfold (v : Value) (k : Z) (val : Val) :
      <[k := val]> v = match v with VALUE vs => VALUE (<[k := val]> vs) end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_empty_unfold : (∅ : Value) = VALUE ∅.
    Proof. reflexivity. Qed.

    Lemma Value_singleton_unfold (k : Z) (val : Val) :
      ({[k := val]} : Value) = VALUE {[k := val]}.
    Proof. reflexivity. Qed.

    Lemma Value_delete_unfold (v : Value) (k : Z) :
      delete k v = match v with VALUE vs => VALUE (delete k vs) end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_alter_unfold (g : Val → Val) (v : Value) (k : Z) :
      alter g k v = match v with VALUE vs => VALUE (alter g k vs) end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_partial_alter_unfold (g : option Val → option Val) (v : Value) (k : Z) :
      partial_alter g k v = match v with VALUE vs => VALUE (partial_alter g k vs) end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_map_fold_unfold {A} (f : Z → Val → A → A) (acc : A) (v : Value) :
      map_fold f acc v = match v with VALUE vs => map_fold f acc vs end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_filter_unfold (P : Z * Val → bool) (v : Value) :
      filter P v = match v with VALUE vs => VALUE (filter P vs) end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_dom_unfold (v : Value) :
      dom v = match v with VALUE vs => dom vs end.
    Proof. destruct v. reflexivity. Qed.

    Lemma Value_map_to_list_unfold (v : Value) :
      map_to_list v = match v with VALUE vs => map_to_list vs end.
    Proof. destruct v. reflexivity. Qed.

    (* ==================== FOLDING LEMMAS ==================== *)

    Lemma Value_lookup_fold (vs : gmap Z Val) (k : Z) :
      vs !! k = (VALUE vs) !! k.
    Proof. reflexivity. Qed.

    Lemma Value_insert_fold (vs : gmap Z Val) (k : Z) (val : Val) :
      VALUE (<[k := val]> vs) = <[k := val]> (VALUE vs).
    Proof. reflexivity. Qed.

    Lemma Value_empty_fold : VALUE ∅ = (∅ : Value).
    Proof. reflexivity. Qed.

    Lemma Value_singleton_fold (k : Z) (val : Val) :
      VALUE {[k := val]} = ({[k := val]} : Value).
    Proof. reflexivity. Qed.

    Lemma Value_delete_fold (vs : gmap Z Val) (k : Z) :
      VALUE (delete k vs) = delete k (VALUE vs).
    Proof. reflexivity. Qed.

    Lemma Value_alter_fold (g : Val → Val) (vs : gmap Z Val) (k : Z) :
      VALUE (alter g k vs) = alter g k (VALUE vs).
    Proof. reflexivity. Qed.

    Lemma Value_partial_alter_fold (g : option Val → option Val) (vs : gmap Z Val) (k : Z) :
      VALUE (partial_alter g k vs) = partial_alter g k (VALUE vs).
    Proof. reflexivity. Qed.

    Lemma Value_map_fold_fold {A} (f : Z → Val → A → A) (b : A) (vs : gmap Z Val) :
      map_fold f b vs = map_fold f b (VALUE vs).
    Proof. reflexivity. Qed.

    Lemma Value_filter_fold (P : Z * Val → bool) (vs : gmap Z Val) :
      VALUE (filter P vs) = filter P (VALUE vs).
    Proof. reflexivity. Qed.

  End Value_lemmas.

  (* ==================== HINT DATABASES ==================== *)

  Create HintDb desc_unfold.
  Create HintDb desc_fold.
  Create HintDb value_unfold.
  Create HintDb value_fold.

  (* Desc unfolding *)
  Hint Rewrite Desc_lookup_unfold Desc_insert_unfold Desc_empty_unfold
       Desc_singleton_unfold Desc_delete_unfold Desc_alter_unfold
       Desc_partial_alter_unfold Desc_filter_unfold Desc_dom_unfold
       Desc_map_to_list_unfold : desc_unfold.

  (* Desc folding - each needs its own Hint Rewrite <- *)
  Hint Rewrite <- Desc_lookup_fold : desc_fold.
  Hint Rewrite <- Desc_insert_fold : desc_fold.
  Hint Rewrite <- Desc_empty_fold : desc_fold.
  Hint Rewrite <- Desc_singleton_fold : desc_fold.
  Hint Rewrite <- Desc_delete_fold : desc_fold.
  Hint Rewrite <- Desc_alter_fold : desc_fold.
  Hint Rewrite <- Desc_partial_alter_fold : desc_fold.
  Hint Rewrite <- Desc_filter_fold : desc_fold.

  (* Value unfolding *)
  Hint Rewrite Value_lookup_unfold Value_insert_unfold Value_empty_unfold
       Value_singleton_unfold Value_delete_unfold Value_alter_unfold
       Value_partial_alter_unfold Value_filter_unfold Value_dom_unfold
       Value_map_to_list_unfold : value_unfold.

  (* Value folding *)
  Hint Rewrite <- Value_lookup_fold : value_fold.
  Hint Rewrite <- Value_insert_fold : value_fold.
  Hint Rewrite <- Value_empty_fold : value_fold.
  Hint Rewrite <- Value_singleton_fold : value_fold.
  Hint Rewrite <- Value_delete_fold : value_fold.
  Hint Rewrite <- Value_alter_fold : value_fold.
  Hint Rewrite <- Value_partial_alter_fold : value_fold.
  Hint Rewrite <- Value_filter_fold : value_fold.

  (* ==================== TACTICS ==================== *)

  (* Unfold Desc operations and destruct wrappers *)
  Ltac desc_unfold :=
    autorewrite with desc_unfold in *;
    repeat match goal with
    | d : Desc |- _ => destruct d
    | H : context[match ?d with DESC _ => _ end] |- _ => destruct d
    | |- context[match ?d with DESC _ => _ end] => destruct d
    end;
    simpl in *.

  (* Fold gmap operations back into Desc form *)
  Ltac desc_fold :=
    autorewrite with desc_fold in *.

  (* Unfold Value operations and destruct wrappers *)
  Ltac value_unfold :=
    autorewrite with value_unfold in *;
    repeat match goal with
    | v : Value |- _ => destruct v
    | H : context[match ?v with VALUE _ => _ end] |- _ => destruct v
    | |- context[match ?v with VALUE _ => _ end] => destruct v
    end;
    simpl in *.

  (* Fold gmap operations back into Value form *)
  Ltac value_fold :=
    autorewrite with value_fold in *.

  (* Combined unfold for both *)
  Ltac map_unfold := desc_unfold; value_unfold.

  (* Combined fold for both *)
  Ltac map_fold := desc_fold; value_fold.

  (* Solve simple map goals by unfolding and applying gmap lemmas *)
  Ltac desc_solve :=
    desc_unfold;
    first [ apply lookup_insert
          | apply lookup_insert_ne; [lia || done |]
          | apply lookup_empty
          | apply lookup_delete
          | apply lookup_delete_ne; [lia || done |]
          | apply lookup_singleton
          | apply lookup_singleton_ne; [lia || done |]
          | apply insert_empty
          | apply delete_empty
          | done
          | eauto ].

  Ltac value_solve :=
    value_unfold;
    first [ apply lookup_insert
          | apply lookup_insert_ne; [lia || done |]
          | apply lookup_empty
          | apply lookup_delete
          | apply lookup_delete_ne; [lia || done |]
          | apply lookup_singleton
          | apply lookup_singleton_ne; [lia || done |]
          | apply insert_empty
          | apply delete_empty
          | done
          | eauto ].

  Section Helpers.
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

  End Helpers.
End Descriptor.
