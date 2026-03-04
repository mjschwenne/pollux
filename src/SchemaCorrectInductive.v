(** Draft implementation of SchemaCorrect as an inductive relation.

    This file explores rewriting SchemaCorrect from a Program Fixpoint
    returning Prop to an inductive relation built via insertions from
    the empty descriptor/value pair.
*)

From Pollux Require Import Prelude.
From Pollux Require Import InterParse.

Section InductiveSchemaCorrect.
  Import InterParse.

  (** * Step 1: Define the inductive relation

      The key insight is that we build the relation via insertions,
      starting from empty descriptor and empty value.
  *)

  (** Helper: Check if a field and value match in type *)
  Definition field_val_type_match (f : Field) (v : Val) : Prop :=
    match f, v with
    | F_BOOL, V_BOOL _ => True
    | F_INT, V_INT _ => True
    | F_MSG _, V_MSG _ => True
    | _, _ => False
    end.

  (** The inductive relation *)
  Inductive SchemaCorrectInd : Desc -> Value -> Prop :=
  | SCI_Empty :
      SchemaCorrectInd (DESC ∅) (VALUE ∅)

  | SCI_Insert : forall k f v ds vs,
      (* The field and value must type-match *)
      field_val_type_match f v ->

      (* If it's a message field, the nested descriptor/value must be correct *)
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> SchemaCorrectInd d' v') ->

      (* The key must be fresh in both maps *)
      ds !! k = None ->
      vs !! k = None ->

      (* The remaining descriptor/value must be correct *)
      SchemaCorrectInd (DESC ds) (VALUE vs) ->

      (* Then we can insert the new field/value pair *)
      SchemaCorrectInd (DESC (<[k := f]> ds)) (VALUE (<[k := v]> vs)).

  Notation "'⟨' d ',' v '⟩' 'Correct'" := (SchemaCorrectInd d v) (at level 70).

  (** * Step 2: Prove insertion order independence

      Multiple insertion sequences can lead to the same descriptor/value pair.
      We need to show that insertion is commutative.
  s*)

  Lemma SCI_Insert_comm : forall k1 k2 f1 f2 v1 v2 ds vs,
      k1 ≠ k2 ->
      SchemaCorrectInd (DESC (<[k1 := f1]> (<[k2 := f2]> ds)))
                       (VALUE (<[k1 := v1]> (<[k2 := v2]> vs))) ->
      SchemaCorrectInd (DESC (<[k2 := f2]> (<[k1 := f1]> ds)))
                       (VALUE (<[k2 := v2]> (<[k1 := v1]> vs))).
  Proof.
    intros k1 k2 f1 f2 v1 v2 ds vs Hneq H.
    rewrite insert_insert_ne, (insert_insert_ne vs); (assumption || symmetry; assumption).
  Qed.

  (** * Step 3: Prove equivalence to the old definition properties

      The old SchemaCorrect encoded four properties. We show that our
      inductive implies these properties.
  *)

  (** Property 1: Every field in value exists in descriptor *)
  Lemma SCI_implies_val_in_desc : forall d v,
      SchemaCorrectInd d v ->
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

  (** Property 2: Every field in descriptor exists in value *)
  Lemma SCI_implies_desc_in_val : forall d v,
      SchemaCorrectInd d v ->
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

  (** Property 3: No V_MISSING values *)
  Lemma SCI_implies_no_missing : forall d v,
      SchemaCorrectInd d v ->
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
    | Some (F_MSG d'), V_MSG v' => SchemaCorrectInd d' v'
    | _, _ => True
    end.

  Lemma map_Forall_impl_local :
    ∀ {K : Type} {M : Type → Type} {H0 : ∀ A : Type, Lookup K A (M A)} {A : Type} (P Q : K → A → Prop) (m : M A),
    map_Forall P m → (∀ (i : K) (x : A), m !! i = Some x -> P i x → Q i x) → map_Forall Q m.
  Proof.
    intros K M H0 A P Q m.
    intros Hm Hq i x Hi.
    specialize (Hq i x Hi).
    apply Hq.
    rewrite map_Forall_lookup in Hm.
    apply Hm; assumption.
  Qed.

  (** Property 4: Nested messages are correct *)
  Lemma SCI_implies_nested_correct : forall d v,
      SchemaCorrectInd d v ->
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
  Theorem SCI_implies_properties : forall d v,
      SchemaCorrectInd d v ->
      (forall k val, Vals v !! k = Some val -> exists f, Fields d !! k = Some f) /\
      (forall k f, Fields d !! k = Some f -> exists val, Vals v !! k = Some val) /\
      (forall k, Vals v !! k ≠ Some V_MISSING) /\
      map_Forall (NestedCorrect d) (Vals v).
  Proof.
    intros d v H.
    split_and!.
    - apply SCI_implies_val_in_desc. assumption.
    - apply SCI_implies_desc_in_val. assumption.
    - apply SCI_implies_no_missing with (d := d). assumption.
    - apply SCI_implies_nested_correct. assumption.
  Qed.

  (** * Step 4: Prove the reverse direction

      If the four properties hold, we can construct a SchemaCorrectInd derivation.
      This is more involved and requires building the insertion sequence.
  *)

  (** Helper lemma: If we have the properties, we can peel off one field *)
  Lemma properties_implies_SCI_step : forall ds vs k f v,
      ds !! k = Some f ->
      vs !! k = Some v ->
      field_val_type_match f v ->
      (forall d' v', f = F_MSG d' -> v = V_MSG v' ->
        (forall k' val', vs !! k' = Some val' -> k' ≠ k -> exists f', ds !! k' = Some f') /\
        (forall k' f', ds !! k' = Some f' -> k' ≠ k -> exists val', vs !! k' = Some val') /\
        (forall k', k' ≠ k -> vs !! k' ≠ Some V_MISSING) /\
        map_Forall (fun k' v' =>
          if decide (k' = k) then True
          else
            let f' : option Field := ds !! k' in
            match f', v' with
            | Some (F_MSG d''), V_MSG v'' => SchemaCorrectInd d'' v''
            | _, _ => True
            end) vs ->
        SchemaCorrectInd d' v') ->
      (forall k' val', vs !! k' = Some val' -> exists f', ds !! k' = Some f') ->
      (forall k' f', ds !! k' = Some f' -> exists val', vs !! k' = Some val') ->
      (forall k', vs !! k' ≠ Some V_MISSING) ->
      map_Forall (fun k' v' => let f' : option Field := ds !! k' in
                            match f', v' with
                            | Some (F_MSG d'), V_MSG v' => SchemaCorrectInd d' v'
                            | _, _ => True
                            end) vs ->
      SchemaCorrectInd (DESC ds) (VALUE vs) ->
      True. (* Placeholder - this is getting complex *)
  Proof.
  Admitted.

  (** Main theorem: properties imply inductive (proof by map induction) *)
  Theorem properties_imply_SCI : forall ds vs,
      (forall k val, vs !! k = Some val -> exists f, ds !! k = Some f) ->
      (forall k f, ds !! k = Some f -> exists val, vs !! k = Some val) ->
      (forall k, vs !! k ≠ Some V_MISSING) ->
      map_Forall (NestedCorrect $ DESC ds) vs ->
      SchemaCorrectInd (DESC ds) (VALUE vs).
  Proof.
    (* Proof strategy:
       - Induct on the map structure using map_first_key_ind
       - Empty case: use SCI_Empty
       - Insert case:
         1. Extract a key k with field f and value v
         2. Show field_val_type_match f v from properties
         3. Apply IH to the smaller maps (delete k ds) and (delete k vs)
         4. Use SCI_Insert to build the full derivation
    *)
    intros ds vs Hvals Hfields Hmissing Hnested.
    induction vs using map_first_key_ind.
    - admit.
    - admit.
  Admitted.

  (** * derived lemmas *)

  Lemma SCI_drop_field : forall k f v ds vs,
      SchemaCorrectInd (DESC (<[k := f]> ds)) (VALUE (<[k := v]> vs)) ->
      ds !! k = None ->
      vs !! k = None ->
      SchemaCorrectInd (DESC ds) (VALUE vs).
  Proof.
    intros k f v ds vs Hcorr Hd_none Hv_none.
    inversion Hcorr; subst.
    - admit.  
    - admit.
  Admitted.

  (** Insert field lemma - direct by constructor *)
  Lemma SCI_insert_field : forall k f v ds vs,
      field_val_type_match f v ->
      (forall d' v', f = F_MSG d' -> v = V_MSG v' -> SchemaCorrectInd d' v') ->
      ds !! k = None ->
      vs !! k = None ->
      SchemaCorrectInd (DESC ds) (VALUE vs) ->
      SchemaCorrectInd (DESC (<[k := f]> ds)) (VALUE (<[k := v]> vs)).
  Proof.
    intros. apply SCI_Insert; assumption.
  Qed.

  (** Empty case lemma *)
  Lemma SCI_empty : SchemaCorrectInd (DESC ∅) (VALUE ∅).
  Proof.
    constructor.
  Qed.

End InductiveSchemaCorrect.
