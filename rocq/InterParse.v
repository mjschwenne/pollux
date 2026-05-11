(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux.parse Require Import Input.
From Pollux.InterParse Require Import Descriptor.
From Pollux.InterParse Require Import Parser.
From Pollux.InterParse Require Import Serializer.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Import Descriptor.
Import Parser.
Import Parser.C.
Import Serializer.

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

Ltac comp_add := 
  repeat match goal with
    | |- context[Z.add ?n ?m] =>
        match n with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
        match m with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
        let r := eval compute in (Z.add n m) in 
          change (Z.add n m) with r
    end.

Ltac invc H := inversion H; subst; clear H.

Section Theorems.
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

  Lemma UnsignedNonEmpty : forall x enc, SerialUnsigned x = S.mkSuccess enc -> (Length enc > 0)%nat.
  Proof.
    intros x enc Hser.
    apply UnsignedLength in Hser.
    lia.
  Qed.

  Theorem NatParseOk : ParseOk ParseNat SerialNat.
  Proof.
    intros x enc rest wf.
    unfold SerialNat, SerialByte.
    intros H. invc H.
    unfold ParseNat, P.Map.
    simpl. f_equal. word.
  Qed.

  Theorem NatStrictParseOk : ParseOk ParseNat SerialNatStrict.
  Proof.
    intros x enc rest [Hlow Hhigh].
    unfold SerialNatStrict.
    rewrite <- Nat.ltb_lt in Hhigh.
    rewrite Hhigh.
    rewrite Nat.ltb_lt in Hhigh.
    apply NatParseOk.
    lia.
  Qed.

  Lemma NatStrictStrict : forall x enc, SerialNatStrict x = S.mkSuccess enc -> (0 <= x < 256)%nat.
  Proof.
    intros x enc.
    unfold SerialNatStrict.
    destruct (x <? 256)%nat eqn:Hwf; last discriminate.
    rewrite Nat.ltb_lt in Hwf. intros Hser. lia.
  Qed.

  Lemma NatStrictLength : forall x enc, SerialNatStrict x = S.mkSuccess enc -> Length enc = 1%nat.
  Proof.
    intros x enc.
    unfold SerialNatStrict.
    destruct (x <? 256)%nat; last discriminate.
    apply UnsignedLength.
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
    forall z val v,
    v !! z = None -> map_first_key (<[z := val]> v) z ->
    Valid' d $ <[z := val]> v -> Valid' d v.
  Proof.
    intros z val v Hno Hfst. destruct d.
    unfold Valid' at 1; simpl.
    value_unfold.
    rewrite map_fold_insert_first_key by assumption.
    destruct val eqn:Hv; intros (_ & H); done.
  Qed.

  Lemma ValueDepthDropFirst :
    forall z val v,
    v !! z = None -> map_first_key (<[z := val]> v) z ->
    (ValueDepth v <= ValueDepth (<[z := val]> v))%nat.
  Proof.
    intros z val v Hno Hfst.
    destruct val;
      unfold ValueDepth at 2;
      value_unfold;
      rewrite map_fold_insert_first_key by assumption.
    - fold (ValueDepth (VALUE vs0)).
      rewrite ValueDepthFold_eq.
      lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma ValidInsert (d : Desc) (k : Z) (val : Val) (v : Value) :
    v !! k = None -> map_first_key (<[k := val]> v) k ->
    Valid' d (<[k := val]> v) <-> Valid'Fold (Fields d) k val True /\ Valid' d v.
  Proof.
    intros Hnone Hfst.
    split.
    - destruct d; unfold Valid' at 1.
      value_unfold.
      rewrite map_fold_insert_first_key by assumption.
      rewrite Valid'Fold_eq. intros Hvalid.
      split.
      + destruct val;
          (split; last easy);
          unfold Valid'Fold at 1 in Hvalid;
          destruct Hvalid as [Hvalid  _]; assumption.
      + destruct val; unfold Valid'Fold at 1 in Hvalid;
          destruct Hvalid as [_ Hvalid]; assumption.
    - intros [Hfst_valid Hrest_valid].
      destruct d; unfold Valid'.
      value_unfold.
      rewrite map_fold_insert_first_key by assumption.
      rewrite Valid'Fold_eq.
      destruct val;
        unfold Valid'Fold at 1;
        destruct Hfst_valid as [Hfst_valid _] in Hfst_valid;
        unfold Valid' in Hrest_valid; split; assumption.
  Qed.

  Lemma ValueEncLen'Fold_linear :
    forall d k v acc,
    ValueEncLen'Fold (Fields d) k v acc = (ValueEncLen'Fold (Fields d) k v 0 + acc)%nat.
  Proof.
    intros [fs] k v acc; simpl.
    destruct (fs !! k) eqn:Hfield; [destruct f|]; destruct v;
      simpl; rewrite ?Hfield; lia.
  Qed.

  Lemma ValueEncLength_unfold (d : Desc) (k : Z) (val : Val) (v : Value) :
    v !! k = None -> map_first_key (<[k := val]> v) k ->
    ValueEncLen' d (<[k := val]> v) =
    (ValueEncLen'Fold (Fields d) k val 0 + ValueEncLen' d v)%nat.
  Proof.
    intros Hnone Hfst.
    destruct d as [fs].
    unfold Fields, ValueEncLen' at 1.
    value_unfold.
    rewrite map_fold_insert_first_key by assumption.
    unfold ValueEncLen'.
    rewrite ValueEncLen'Fold_linear with (d := DESC fs).
    reflexivity.
  Qed.

  (** Values nested in a map have strictly smaller depth **)
  Lemma Val_in_map_smaller_depth :
    forall v k val,
    v !! k = Some (V_MSG val) ->
    (ValueDepth val < ValueDepth v)%nat.
  Proof.
    intros v k val; value_unfold. rename vs0 into vs'.
    induction vs' as [| k' v' m' Hno Hfst] using map_first_key_ind.
    - (* Empty map case: contradiction *)
      rewrite lookup_empty. discriminate.
    - (* Non-empty map case *)
      rewrite lookup_insert.
      case_decide as Heq.
      + (* k = k': we found the element *)
        intro Hlookup. inversion Hlookup; subst; clear Hlookup.
        rewrite map_fold_insert_L.
        * value_solve. lia.
        * intros. simpl. 
          destruct z1, z2; unfold ValueDepthFold; lia.
        * assumption.
      + (* k ≠ k': element is in the rest *)
        intro Hlookup.
        rewrite map_fold_insert_L.
        * simpl.
          specialize (IHvs' Hlookup).
          change (map_fold ValueDepthFold 0%nat m') with (ValueDepth (VALUE m')).
          destruct v'; unfold ValueDepthFold; value_solve.
          rewrite ValueDepthFold_eq.
          lia.
        * intros; simpl.
          destruct z1, z2; unfold ValueDepthFold; lia.
        * assumption.
  Qed.

  Lemma kv_in_Filter : forall v d key val,
    (key, val) ∈ ValList' d v -> 
    (key, val) ∈ map_to_list v.
  Proof.
    intros vs d key val.
    unfold ValList', Vals.
    intros Hfilter.
    value_unfold.
    rewrite elem_of_map_to_list. 
    rewrite elem_of_map_to_list in Hfilter.
    pose proof (lookup_merge Filter (Fields d) vs key) as Hlookup.
    rewrite Hfilter in Hlookup. rewrite Hlookup. unfold diag_None.
    destruct (Fields d !! key).
    - unfold Filter. destruct (vs !! key); last discriminate.
      destruct v; try reflexivity.
      unfold diag_None, Filter in Hlookup.
      discriminate.
    - unfold diag_None, Filter in Hlookup. destruct (vs !! key); last reflexivity.
      discriminate.
  Qed.

  Infix "≡ᵣ" := result_equiv (at level 70):type_scope.
  Lemma SerialValWeakenDepth (d : Desc) (k : Z) (v : Val) (m : Value) : 
    m !! k = None -> map_first_key (<[k := v]> m) k ->
    forall kv,
    kv ∈ ValList d m ->
    SerialVal (λ (st__n : Desc) (x__n : Value),
                 if decide (ValueDepth x__n < ValueDepth (<[k:=v]> m))%nat
                 then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                 else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth (<[k:=v]> m) x__n)
      d kv ≡ᵣ
      SerialVal (λ (st__n : Desc) (x__n : Value),
                   if decide (ValueDepth x__n < ValueDepth m)%nat
                   then @S.recur_st _ _ Value_wf SerialValue' ValueDepth st__n x__n
                   else S.RecursiveProgressError "Serial.RecursiveState" ValueDepth m x__n)
      d kv.
  Proof.
    intros Hnone Hfst [key val] Hin.
    value_unfold.
    (* The serializers only differ in recursive calls on V_MSG values *)
    unfold SerialVal.
    destruct ((Fields d) !! (key, val).1); try done.
    destruct f; try reflexivity.
    (* For F_MSG, we need to show the depth checks evaluate the same *)
    destruct val as [val | z | b |]; try reflexivity.
    (* For V_MSG v0, both depth checks should be true since v0 comes from m *)
    unfold S.Bind', S.Concat, S.Len'.
    (* Show that both decide expressions evaluate to true *)
    unfold ValList, Vals in Hin.
    rewrite list_elem_of_filter in Hin.
    destruct Hin as [Hfilter Hin].
    (* apply kv_in_Filter in Hin. *)
    rewrite elem_of_map_to_list in Hin.
    pose proof (ValueDepthDropFirst k v (VALUE vs) Hnone Hfst) as Hdepth. 
    destruct (decide (ValueDepth val < map_fold ValueDepthFold 0 vs)%nat) eqn:Hm; unfold S.PartMap, S.Map, S.Opt.
    - destruct (decide (ValueDepth val < map_fold ValueDepthFold 0 (<[k := v]> vs))%nat) eqn:Hn.
      + value_solve. rewrite Hm. reflexivity.
      + value_solve. lia.
    - destruct (decide (ValueDepth val < map_fold ValueDepthFold 0 (<[k := v]> vs))%nat) eqn:Hn.
      + pose proof (Val_in_map_smaller_depth (VALUE vs) key val Hin). done.
      + unfold S.RecursiveProgressError.
        destruct (ValueDepth val == ValueDepth (VALUE vs)),
                   (ValueDepth val == ValueDepth (VALUE (<[k := v]> vs))); value_solve; by rewrite Hm.
  Qed.

  Lemma SerialValueInversion (d : Desc) :
    forall k v (m : Value) enc,
    m !! k = None -> map_first_key (<[k := v]> m) k ->
    SerialValue d (<[k := v]> m) = S.mkSuccess enc <->
                                     exists enc__v enc__rest, SerialValue d m = S.mkSuccess enc__rest /\
                                                     SerialVal (SerialValue) d (k, v) = S.mkSuccess enc__v /\
                                                     enc = App enc__v enc__rest.
  Proof.
    intros k v m enc Hnone Hfst; value_unfold.
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
          unfold SerialValue', S.Map, ValList, Vals.
          rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
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
             rewrite Value_insert_fold.
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
          destruct (Fields d !! (k, v).1); last reflexivity.
          destruct f; try reflexivity.
          destruct v; try reflexivity.
          unfold S.Bind', S.Concat, S.Len', S.PartMap, S.Map, S.Opt.
          case_eq (decide (ValueDepth v < ValueDepth (VALUE (<[k := V_MSG v]> vs))))%nat.
          -- intros Hdep _. unfold SerialValue, S.RecursiveState. reflexivity.
          -- intros Hdep _. pose proof (lookup_insert_eq vs k (V_MSG v)) as Hlookup.
             pose proof (Val_in_map_smaller_depth (<[k := V_MSG v]> $ VALUE vs) k v Hlookup).
             contradiction.
      + destruct (filter (ValList_filter_p d) (map_to_list vs)) eqn:Hlst.
        * rewrite ser_rep_unfold. intros Hser. invc Hser.
          exists S.Output_default, S.Output_default.
          split.
          -- unfold SerialValue, S.RecursiveState.
             rewrite ser_recur_st_unfold.
             unfold SerialValue', S.Map, ValList, Vals.
             rewrite Hlst. reflexivity.
          -- split; last (unfold S.Output_default; rewrite App_nil_r; reflexivity).
             unfold ValList_filter_p, fst, snd in Hfilter_out.
             unfold SerialVal. destruct (Fields d !! (k, v).1) eqn:Hf; last reflexivity.
             simpl in Hf. rewrite Hf in Hfilter_out.
             destruct f; destruct v; value_solve.
        * intro Hser. exists Input_default, enc. 
          split.
          -- unfold SerialValue, S.RecursiveState.
             rewrite ser_recur_st_unfold.
             unfold SerialValue', S.Map, ValList, Vals.
             rewrite <- Hlst in Hser. 
             rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
             rewrite <- Hser.
             rewrite SerialRepSubst; first reflexivity.
             symmetry.
             rewrite Value_insert_fold.
             apply SerialValWeakenDepth; assumption.
          -- split; last (rewrite App_nil_l; reflexivity).
             unfold ValList_filter_p, fst, snd in Hfilter_out.
             unfold SerialVal. destruct (Fields d !! (k, v).1) eqn:Hf; last reflexivity.
             destruct f; destruct v; simpl in Hf;
               rewrite Hf in Hfilter_out;
               (reflexivity || specialize (Hfilter_out I); contradiction).
             
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
          destruct (Fields d !! (k, v).1); last reflexivity.
          destruct f; try reflexivity.
          destruct v; try reflexivity.
          unfold S.Bind', S.Concat, S.Len', S.Map, S.PartMap, S.Opt.
          case_eq (decide (ValueDepth v < ValueDepth (VALUE (<[k:=V_MSG v]> vs)))%nat).
          -- intros Hdep _. unfold SerialValue, S.RecursiveState. reflexivity.
          -- intros Hdep _. pose proof (lookup_insert_eq vs k (V_MSG v)) as Hlookup.
             pose proof (Val_in_map_smaller_depth (<[k := V_MSG v]> $ VALUE vs) k v Hlookup).
             contradiction.
        * split; last reflexivity. revert Hrest_ok.
          unfold SerialValue, S.RecursiveState.
          rewrite ser_recur_st_unfold. 
          unfold SerialValue', S.Map, ValList, Vals.
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
          rewrite Value_insert_fold.
          fold (Vals $ VALUE vs); fold (ValList d $ VALUE vs).
          apply SerialValWeakenDepth; assumption.
      + unfold ValList_filter_p, fst, snd in Hfilter_out.
        unfold SerialVal in Hv_ok.
        unfold SerialValue, S.RecursiveState in Hrest_ok.
        rewrite ser_recur_st_unfold in Hrest_ok.
        destruct (Fields d !! k) eqn:Hin_d; simpl in Hv_ok.
        * (* v was dropped for being V_MISSING *) 
          destruct v; try (reflexivity || specialize (Hfilter_out I); contradiction).
          destruct f;
            rewrite Hin_d in Hv_ok;
            unfold S.Opt in Hv_ok;
            invc Hv_ok;
            unfold SerialValue', S.Map, ValList, Vals in *;
                                                 rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _);
                                                 rewrite App_nil_l;
                                                 rewrite <- Hrest_ok;
                                                 rewrite SerialRepSubst; first reflexivity.
          -- rewrite Value_insert_fold.
             fold (Vals $ VALUE vs); fold (ValList d $ VALUE vs).
             apply SerialValWeakenDepth; assumption.
          -- reflexivity.
          -- rewrite Value_insert_fold.
             fold (Vals $ VALUE vs); fold (ValList d $ VALUE vs).
             apply SerialValWeakenDepth; assumption.
          -- reflexivity.
          -- rewrite Value_insert_fold.
             fold (Vals $ VALUE vs); fold (ValList d $ VALUE vs).
             apply SerialValWeakenDepth; assumption.
        * (* v dropped for being unknown *)
          rewrite Hin_d in Hv_ok. invc Hv_ok. rewrite App_nil_l.
          rewrite <- ResultEquivSuccessIff with (r := S.Rep _ _).
          rewrite <- Hrest_ok.
          unfold SerialValue', S.Map, ValList, Vals.
          rewrite SerialRepSubst; first reflexivity.
          rewrite Value_insert_fold.
          fold (Vals $ VALUE vs); fold (ValList d $ VALUE vs).
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
      + intros _ d enc Hvalid Hser.
        vm_compute in Hser.
        inversion Hser. destruct d; reflexivity.
      + intros IHv d enc Hvalid Hser; unfold S.Output in *. 
        rewrite Value_insert_fold in *.
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
        apply NatStrictLength in Hlen_ok.
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
    unfold fst in Hin_d. simpl in *; rewrite Hin_d.
    unfold Val_wf, Val_wf_fold in Hval_wf.
    rewrite Val_wf_fold_eq in Hval_wf.
    fold (Fields (DESC ds)) in Hval_wf.
    rewrite Val_wf_fold_unfold in Hval_wf.
    simpl in Hval_wf; rewrite Hin_d in Hval_wf.
    destruct f; destruct v.
    + intros Hser.
      apply SerialConcatInversion in Hser.
      destruct Hser as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
      subst. rewrite App_Length.
      apply UnsignedLength in Hl_ok.
      lia.
    + intros Hcontra; contradiction.
    + intros Hcontra; contradiction.
    + contradiction.
    + intros Hcontra; contradiction.
    + intros Hser.
      apply SerialConcatInversion in Hser.
      destruct Hser as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
      subst. rewrite App_Length.
      apply UnsignedLength in Hl_ok.
      lia.
    + intros Hcontra; contradiction.
    + contradiction.
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
    SchemaCorrect ds vs ->

    (* Then we can insert the new field/value pair *)
    SchemaCorrect (<[k := f]> ds) (<[k := v]> vs).

  Notation "'⟨' v '∷' d '⟩'" := (SchemaCorrect d v) (at level 70).

  (** Insert field lemma - direct by constructor *)
  Lemma SC_insert_field : forall k f val d v,
    field_val_type_match f val ->
    (forall d' v', f = F_MSG d' -> val = V_MSG v' -> ⟨ v' ∷ d' ⟩) ->
    d !! k = None ->
    v !! k = None ->
    ⟨ v ∷ d ⟩ ->
    ⟨ <[k := val]> v ∷ <[k := f]> d ⟩.
  Proof.
    intros. apply SC_Insert; assumption.
  Qed.

  (** Empty case lemma *)
  Lemma SC_empty : ⟨ ∅ ∷ ∅ ⟩.
  Proof.
    constructor.
  Qed.

  (* Add some lemmas about the constructor *)
  Lemma SC_Insert_comm : forall k1 k2 f1 f2 v1 v2 d v,
    k1 ≠ k2 ->
    ⟨ <[k1 := v1]> (<[k2 := v2]> v) ∷ <[k1 := f1]> (<[k2 := f2]> d) ⟩ ->
    ⟨ <[k2 := v2]> (<[k1 := v1]> v) ∷ <[k2 := f2]> (<[k1 := f1]> d) ⟩.
  Proof.
    intros k1 k2 f1 f2 v1 v2 d v Hneq H. map_unfold.
    rewrite insert_insert_ne, (insert_insert_ne vs); (assumption || symmetry; assumption).
  Qed.

  (** Property 1: Every field in value exists in descriptor *)
  Lemma SC_implies_val_in_desc : forall d v,
    ⟨ v ∷ d ⟩ ->
    forall k val, v !! k = Some val -> exists f, d !! k = Some f.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' val' Hlookup.
    - (* Empty case *)
      simpl in Hlookup. value_unfold. rewrite lookup_empty in Hlookup. discriminate.
    - (* Insert case - straightforward by case analysis on k = k' *)
      destruct (k == k') as [Heq | Hneq].
      + subst k'. exists f. desc_unfold. rewrite lookup_insert_eq.
        reflexivity.
      + value_unfold. rewrite lookup_insert_ne in Hlookup by assumption.
        specialize (IH k' val' Hlookup).
        destruct IH as [f' Hsome].
        exists f'. desc_unfold.
        rewrite lookup_insert_ne by assumption.
        assumption.
  Qed.

  Lemma SC_implies_val_in_desc_typed : forall d v,
    ⟨ v ∷ d ⟩ ->
    forall k val, v !! k = Some val -> exists f, d !! k = Some f /\ field_val_type_match f val.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' val' Hlookup.
    - (* Empty case *)
      simpl in Hlookup. value_unfold. rewrite lookup_empty in Hlookup. discriminate.
    - (* Insert case - straightforward by case analysis on k = k' *)
      destruct (k == k') as [Heq | Hneq].
      + subst k'. exists f. desc_unfold. rewrite lookup_insert_eq.
        split; first reflexivity.
        value_unfold. rewrite lookup_insert_eq in Hlookup. invc Hlookup.
        assumption.
      + value_unfold. rewrite lookup_insert_ne in Hlookup by assumption.
        specialize (IH k' val' Hlookup).
        destruct IH as [f' Hsome].
        exists f'. desc_unfold.
        rewrite lookup_insert_ne by assumption.
        assumption.
  Qed.

  (** Property 2: Every field in descriptor exists in value *)
  Lemma SC_implies_desc_in_val : forall d v,
    ⟨ v ∷ d ⟩ ->
    forall k f, d !! k = Some f -> exists val, v !! k = Some val.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH]; intros k' f' Hlookup.
    - desc_unfold. rewrite lookup_empty in Hlookup. discriminate.
    - desc_unfold. destruct (k == k') as [Heq | Hneq].
      + subst k'. exists v. value_unfold. by rewrite lookup_insert_eq.
      + desc_unfold. rewrite lookup_insert_ne in Hlookup by assumption.
        specialize (IH k' f' Hlookup).
        destruct IH as [v' Hsome].
        exists v'. value_unfold.
        rewrite lookup_insert_ne by assumption.
        assumption.
  Qed.

  Lemma SC_implies_desc_in_val_typed : forall d v,
    ⟨ v ∷ d ⟩ ->
    forall k f, d !! k = Some f -> exists val, v !! k = Some val /\ field_val_type_match f val.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hvs_none H' IH];
      intros k' f' Hlookup; desc_unfold.
    - by rewrite lookup_empty in Hlookup. 
    - destruct (k == k') as [Heq | Hneq].
      + subst k'. exists v. value_unfold. rewrite lookup_insert_eq.
        split; first reflexivity.
        rewrite lookup_insert_eq in Hlookup. invc Hlookup.
        assumption.
      + rewrite lookup_insert_ne in Hlookup by assumption.
        specialize (IH k' f' Hlookup).
        destruct IH as [v' Hsome].
        exists v'. value_unfold.
        rewrite lookup_insert_ne by assumption.
        assumption.
  Qed.

  (** Property 3: No V_MISSING values *)
  Lemma SC_implies_no_missing : forall d v,
    ⟨ v ∷ d ⟩ ->
    forall k, v !! k ≠ Some V_MISSING.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hv_none H' IH]; intros k'.
    - value_unfold. rewrite lookup_empty. done.
    - destruct (k == k') as [Heq | Hneq]; value_unfold.
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
    rewrite !filter_cons by naive_solver.
    destruct (decide (P1 a)), (decide (P2 a)).
    - f_equal. apply IH. intros x Hin. apply HPdiff.
      apply list_elem_of_further. exact Hin.
    - specialize (HPdiff a $ list_elem_of_here a l).
      rewrite HPdiff in p. contradiction.
    - specialize (HPdiff a $ list_elem_of_here a l).
      rewrite <- HPdiff in p. contradiction.
    - apply IH. intros x Hin. apply HPdiff.
      apply list_elem_of_further. exact Hin.
  Qed.

  (** Property 4: Nested messages are correct *)
  Lemma SC_implies_nested_correct : forall d v,
    ⟨ v ∷ d ⟩ ->
    (* Can't remove this Vals call and still have access to the required map_Forall lemmas *)
    map_Forall (NestedCorrect d) $ Vals v.
  Proof.
    intros d v H.
    induction H as [| k f v ds vs Htype HnestedC Hnested Hds_none Hv_none H' IH].
    - apply map_Forall_empty. 
    - value_unfold; simpl. rewrite map_Forall_insert by assumption.
      split.
      + unfold NestedCorrect; desc_unfold; simpl.
        destruct (<[k:=f]> fs !! k) as [f' |] eqn:Hfeq; last trivial.
        destruct f' as [d' | |]; try trivial.
        rewrite lookup_insert_eq in Hfeq. inversion Hfeq as [Hf].
        destruct v; try trivial.
        apply HnestedC; done.
      + simpl in IH. apply map_Forall_impl_local with (P := NestedCorrect ds). 
        * assumption.
        * intros i x.
          unfold NestedCorrect; desc_unfold; simpl.
          intros H.
          destruct (<[k:=f]> fs !! i) as [f' |] eqn:Hdeq; last trivial.
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
    (forall k val, v !! k = Some val -> exists f, d !! k = Some f) /\
    (forall k f, d !! k = Some f -> exists val, v !! k = Some val) /\
    (forall k, v !! k ≠ Some V_MISSING) /\
    map_Forall (NestedCorrect d) (Vals v).
  Proof.
    intros d v H.
    split_and!.
    - apply SC_implies_val_in_desc. assumption.
    - apply SC_implies_desc_in_val. assumption.
    - apply SC_implies_no_missing with (d := d). assumption.
    - apply SC_implies_nested_correct. assumption.
  Qed.

  (** Combined theorem: inductive implies all four properties *)
  Theorem SC_implies_properties_typed : forall d v,
    ⟨ v ∷ d ⟩ ->
    (forall k val, v !! k = Some val -> exists f, d !! k = Some f /\ field_val_type_match f val) /\
    (forall k f, d !! k = Some f -> exists val, v !! k = Some val /\ field_val_type_match f val) /\
    (forall k, v !! k ≠ Some V_MISSING) /\
    map_Forall (NestedCorrect d) (Vals v).
  Proof.
    intros d v H.
    split_and!.
    - apply SC_implies_val_in_desc_typed. assumption.
    - apply SC_implies_desc_in_val_typed. assumption.
    - apply SC_implies_no_missing with (d := d). assumption.
    - apply SC_implies_nested_correct. assumption.
  Qed.

  Lemma SC_delete_key : forall d v k, ⟨ v ∷ d ⟩ -> ⟨ delete k v ∷ delete k d ⟩.
  Proof.
    intros d v k H.
    induction H.
    - simpl. map_unfold. rewrite !delete_empty. apply SC_empty.
    - simpl. map_unfold. rewrite !delete_insert.
      destruct (k == k0).
      + apply IHSchemaCorrect.
      + simpl in IHSchemaCorrect.
        rewrite Value_insert_fold, Desc_insert_fold.
        apply SC_insert_field; try assumption; desc_unfold; value_unfold;
          rewrite lookup_delete_None; right; assumption.
  Qed.

  Lemma SC_dom_eq : forall d v, ⟨ v ∷ d ⟩ -> dom v ≡ dom d.
  Proof.
    intros d v Hsc.
    rewrite set_equiv.
    intros k. split.
    - intros Hdom. value_unfold; desc_unfold.
      rewrite elem_of_dom in Hdom.
      destruct Hdom as [v Hv].
      apply SC_implies_val_in_desc with (k := k) (val := v) in Hsc as Hvd; last done.
      destruct Hvd as [f Hf]; simpl in Hf.
      rewrite elem_of_dom. exists f. exact Hf.
    - intro Hdom. value_unfold; desc_unfold.
      rewrite elem_of_dom in Hdom.
      destruct Hdom as [f Hf].
      apply SC_implies_desc_in_val with (k := k) (f := f) in Hsc as Hdv; last done.
      destruct Hdv as [v Hv]; simpl in Hv.
      rewrite elem_of_dom. exists v. exact Hv.
  Qed.

  Inductive SchemaCorrectOrdered : Desc -> Value -> Prop :=
  | SCO_Empty :
    SchemaCorrectOrdered (DESC ∅) (VALUE ∅)

  | SCO_Insert : forall k f val d v,
    field_val_type_match f val ->
    (forall d' v', f = F_MSG d' -> val = V_MSG v' -> SchemaCorrectOrdered d' v') ->

    (* Key is fresh *)
    d !! k = None ->
    v !! k = None ->

    (* NEW: k is the first key in the result *)
    map_first_key (<[k := f]> d) k ->
    map_first_key (<[k := val]> v) k ->

    (* Recursive correctness *)
    SchemaCorrectOrdered d v ->

    SchemaCorrectOrdered (<[k := f]> d) (<[k := val]> v).

  Notation "'⟪' v '∷' d '⟫'" := (SchemaCorrectOrdered d v) (at level 70).

  (** Insert field lemma - direct by constructor *)
  Lemma SCO_insert_field : forall k f val d v,
    field_val_type_match f val ->
    (forall d' v', f = F_MSG d' -> val = V_MSG v' -> ⟪ v' ∷ d' ⟫) ->
    d !! k = None ->
    v !! k = None ->
    map_first_key (<[k := f]> d) k ->
    map_first_key (<[k := val]> v) k ->
    ⟪ v ∷ d ⟫ ->
    ⟪ <[k := val]> v ∷ <[k := f]> d ⟫.
  Proof.
    intros. apply SCO_Insert; assumption.
  Qed.

  Lemma SCO_insert_underlying : forall k f val d v,
    ⟪ <[k := val]> v ∷ <[k := f]> d ⟫ ->
    ⟪ v ∷ d ⟫.
  Proof.
    intros k f val d v Hsco.
    dependent induction Hsco.
    - desc_unfold. pose proof (insert_non_empty fs k f).
      inversion x0. symmetry in H1. contradiction.
    - apply IHHsco with (k := k) (f := f) (val := val).
      + desc_unfold. f_equal. apply map_eq. intros i.
  Abort.

  (** Empty case lemma *)
  Lemma SCO_empty : ⟪ ∅ ∷ ∅ ⟫.
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
                value_unfold. rewrite lookup_empty in Hcontra. discriminate.
             ++ simpl; value_unfold; desc_unfold; by rewrite lookup_insert_eq. 
        * intros [ds] Hsc. apply SC_implies_val_in_desc_typed with (k := k) (val := val) in Hsc as Hvd.  
          -- destruct Hvd as (f & Hvd & Hty); simpl in Hvd.
             set (ds' := delete k ds). assert (ds = <[k := f]> ds') as Hds_eq.
             { unfold ds'. symmetry. apply insert_delete_id. assumption. }
             rewrite Hds_eq in *. clear Hds_eq.
             apply SC_delete_key with (k := k) in Hsc as Hsc'; simpl in Hsc'.
             apply delete_insert_id with (x := val) in Hno_vs as Hdel_vs.
             map_unfold. rewrite Hdel_vs in Hsc'.
             assert (ds' !! k = None) as Hno_ds.
             { unfold ds'. apply lookup_delete_eq. }
             apply delete_insert_id with (x := f) in Hno_ds as Hdel_ds.
             rewrite Hdel_ds in Hsc'.
             assert (map_first_key (<[k:=f]> ds') k) as Hfst_ds.
             {
               pose proof (SC_dom_eq (<[k:=f]> $ DESC ds') (<[k:=val]> $ VALUE vs') Hsc) as Hdom.
               rewrite map_first_key_dom with (m2 := <[k:=f]> ds') in Hfst_vs; assumption.
             }
             rewrite map_Forall_insert in IHv by assumption.
             destruct IHv as [IHval IHv].
             specialize (IHvs IHv _ Hsc'). rewrite Value_insert_fold, Desc_insert_fold.
             apply SCO_insert_field; try assumption.
             intros d' v' Hf Hval; subst.
             apply SC_implies_nested_correct in Hsc as Hn; simpl in Hn.
             rewrite map_Forall_insert in Hn by assumption.
             destruct Hn as [Hcor Hn].
             unfold NestedCorrect in Hcor; simpl in Hcor.
             rewrite lookup_insert_eq in Hcor.
             apply IHval in Hcor; last reflexivity.
             exact Hcor.
          -- value_unfold; rewrite lookup_insert_eq. reflexivity.
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
          map_unfold.
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
          destruct Hvd as [f Hvd]; simpl in Hvd. map_unfold.
          rewrite Heq2 in Hvd. discriminate.
      + destruct (ds2 !! k) as [f2 |] eqn:Heq2.
        * apply SC_implies_desc_in_val with (k := k) (f := f2) in Hsc2 as Hdv; last done.
          destruct Hdv as [v Hdv]; simpl in Hdv.
          apply SC_implies_val_in_desc with (k := k) (v := VALUE vs) (val := v) in Hsc1 as Hvd; last done.
          destruct Hvd as [f Hvd]; simpl in Hvd. map_unfold.
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

  Lemma ValList_drop_ok (v : Value) (k : Z) (d : Desc) :
    forall f, v !! k = None -> ValList (<[k := f]> d) v = ValList d v.
  Proof.
    intros f Hnone.
    unfold ValList.
    apply list_filter_iff_local.
    intros [k' v'] Hin.
    split.
    - unfold ValList_filter_p; unfold Fields; map_unfold.
      rewrite elem_of_map_to_list in Hin.
      destruct (k' == k).
      + subst k. rewrite Hin in Hnone. discriminate.
      + rewrite lookup_insert_ne by done. done.
    - unfold ValList_filter_p; simpl.
      rewrite elem_of_map_to_list in Hin.
      destruct (k' == k); unfold Fields; map_unfold. 
      + subst k. rewrite Hin in Hnone. discriminate.
      + rewrite lookup_insert_ne by done. done.
  Qed.

  Lemma ValList_drop_ok' (v : Value) (k : Z) (d : Desc) :
    v !! k = None -> ValList d v = ValList (delete k d) v.
  Proof.
    intros Hnone.
    unfold ValList; map_unfold.
    apply list_filter_iff_local.
    intros [k' v'] Hin.
    split.
    - unfold ValList_filter_p; simpl.
      rewrite elem_of_map_to_list in Hin.
      assert (k <> k') as Hkneq.
      { intro H. subst. rewrite Hnone in Hin. discriminate. }
      rewrite lookup_delete_ne by assumption.
      destruct (fs !! k'); last done.
      destruct v'; done.
    - unfold ValList_filter_p; simpl.
      rewrite elem_of_map_to_list in Hin.
      assert (k <> k') as Hkneq.
      { intro H. subst. rewrite Hnone in Hin. discriminate. }
      rewrite lookup_delete_ne by assumption.
      destruct (fs !! k'); last done.
      destruct v'; done.
  Qed.

  Lemma ValList_elem_of (v : Value) (d : Desc) (k : Z) (val : Val) :
    (k, val) ∈ ValList d v -> v !! k = Some val.
  Proof.
    unfold ValList. intros Hfil. rewrite list_elem_of_filter in Hfil.
    destruct Hfil as [_ Hin]. value_unfold.
    by rewrite <- elem_of_map_to_list.
  Qed.

  Lemma Fields_idep : forall d, DESC (Fields d) = d.
  Proof. intros [ds]; reflexivity. Qed.

  (* Keeping Vals to match underlying syntax, could state lemma without it though *)
  Lemma SC_filter : forall v d, ⟨ v ∷ d ⟩ -> ValList d v = map_to_list (Vals v).
  Proof.
    intros [vs].
    unfold ValList, Vals.
    intros d Hsc. apply SC_SCO in Hsc.
    dependent induction Hsc.
    - by rewrite map_to_list_empty, filter_nil.
    - rename H into Hty,
               H0 into Hnest,
                 H1 into HnestC,
                   H2 into Hds_no,
                     H3 into Hvs_no,
                       H4 into Hds_fst,
                         H5 into Hvs_fst; map_unfold.
      invc x.
      rewrite map_to_list_insert_first_key by assumption.
      simpl. rewrite filter_cons_True.
      + f_equal. specialize (IHHsc vs0 eq_refl).
        fold (Vals (VALUE vs0)). fold (ValList (DESC (<[k:=f]> fs)) (VALUE vs0)).
        fold (Vals (VALUE vs0)) in IHHsc. fold (ValList (DESC fs) (VALUE vs0)) in IHHsc.
        rewrite <- IHHsc. desc_fold.
        by rewrite ValList_drop_ok by assumption.
      + unfold ValList_filter_p; simpl.
        rewrite lookup_insert_eq.
        destruct val; try trivial.
        destruct f; unfold field_val_type_match in Hty; assumption.
  Qed.

  Lemma SC_Empty_Desc : forall d, ⟨ ∅ ∷ d ⟩ -> d = ∅.
  Proof.
    intros [ds] H. f_equal. desc_unfold; f_equal. apply map_eq. intros i. rewrite lookup_empty.
    destruct (ds !! i) eqn:Heq; last reflexivity.
    apply SC_implies_desc_in_val with (k := i) (f := f) in H; last done.
    destruct H as [v H]; simpl in H. map_unfold. rewrite lookup_empty in H.
    discriminate.
  Qed.

  Lemma ValList_not_in : forall d v k, v !! k = None -> k ∉ (ValList d v).*1.
  Proof.
    intros d v k Hnone.
    rewrite not_elem_of_list_to_map.
    unfold ValList; simpl; value_unfold.
    induction vs using map_first_key_ind.
    - by rewrite map_to_list_empty, filter_nil, list_to_map_nil, lookup_empty.
    - rewrite map_to_list_insert_first_key by assumption.
      rewrite filter_cons. destruct (decide (ValList_filter_p d (i, x))).
      + rewrite list_to_map_cons. destruct (i == k).
        * subst. rewrite lookup_insert_eq in Hnone. discriminate.
        * rewrite lookup_insert_ne by assumption. apply IHvs.
          rewrite lookup_insert_ne in Hnone by assumption.
          exact Hnone.
      + apply IHvs. destruct (i == k).
        * subst. rewrite lookup_insert_eq in Hnone. discriminate.
        * rewrite lookup_insert_ne in Hnone by assumption.
          exact Hnone.
  Qed.

  Lemma merge_insert_eliminated_r `{FinMap K M} {A B C}
    (f : option A → option B → option C) (m1 : M A) (m2 : M B) (i : K) (z : B) :
    f (m1 !! i) (Some z) = None →
    f (m1 !! i) (m2 !! i) = None →  (* also None without z *)
    merge f m1 (<[i:=z]> m2) = merge f m1 m2.
  Proof.
    intros Hfz Hf.
    apply map_eq. intros j.
    rewrite !lookup_merge.
    destruct (decide (i = j)) as [->|Hne].
    - rewrite lookup_insert. destruct (j == j); last reflexivity.
      unfold diag_None. destruct (m1 !! j).
      + by rewrite Hf, Hfz.
      + destruct (m2 !! j); last assumption.
        by rewrite Hf, Hfz.
    - rewrite lookup_insert_ne; auto.
  Qed.

  (* When the merge produces None, the insertion is eliminated *)
  Lemma merge_insert_none_r `{FinMap K M} {A B C}
    (f : option A → option B → option C) (m1 : M A) (m2 : M B) (i : K) (z : B) :
    f (m1 !! i) (Some z) = None →
    merge f m1 (<[i:=z]> m2) = delete i (merge f m1 m2).
  Proof.
    intros Hf.
    apply map_eq. intros j.
    destruct (decide (i = j)) as [->|Hne].
    - (* j = i: the key is deleted *)
      rewrite lookup_delete.
      rewrite lookup_merge.
      rewrite lookup_insert.
      destruct (j == j).
      + unfold diag_None.
        rewrite Hf.
        by destruct (m1 !! j).
      + by rewrite lookup_merge.
    - (* j ≠ i: other keys unchanged *)
      rewrite lookup_delete_ne; auto.
      rewrite !lookup_merge.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma list_to_value_id : forall v d,
    ⟨ v ∷ d ⟩ -> v = list_to_value d (ValList d v).
  Proof.
    intros v d Hsc. apply SC_SCO in Hsc.
    induction Hsc as [| ? ? ? ? ? Hty Hnest HnestC Hds_no Hvs_no Hds_fst Hvs_fst].
    - unfold ValList; simpl.
      rewrite map_to_list_empty, filter_nil.
      unfold list_to_value; simpl.
      by rewrite merge_empty.
    - unfold ValList; simpl; map_unfold.
      rewrite map_to_list_insert_first_key by assumption.
      rewrite filter_cons_True.
      + unfold list_to_value.
        rewrite list_to_map_cons.
        fold (Vals $ VALUE vs);
          fold (ValList (DESC (<[k := f]> fs)) (VALUE vs)); simpl.
        rewrite <- insert_merge with (x := val).
        * rewrite !Value_insert_fold.
          fold (Fields (DESC fs)).
          fold (list_to_value (DESC fs) (ValList (DESC (<[k:=f]> (Fields $ DESC fs))) (VALUE vs))).
          simpl. rewrite Desc_insert_fold, ValList_drop_ok by assumption.
          by rewrite IHHsc at 1.
        * unfold Merge. destruct f; destruct val; unfold field_val_type_match; (contradiction || reflexivity).
      + unfold ValList_filter_p; simpl.
        rewrite lookup_insert_eq.
        destruct f; destruct val; unfold field_val_type_match; (contradiction || reflexivity).
  Qed.

  Lemma SC_filter_self : forall d v, ⟨ v ∷ d ⟩ -> ⟨ list_to_value d (ValList d v) ∷ d⟩.
  Proof.
    intros d v Hsc. by rewrite <- list_to_value_id.
  Qed.

  Lemma FullDescriptor_RoundTrip : forall v d, ⟨ v ∷ d ⟩ -> ⟨ v ∷ d ⟩ ≼ ⟨ list_to_value d (ValList d v) ∷ d ⟩.
  Proof.
    intros v d Hsc. apply SC_SCO in Hsc.
    induction Hsc as [| ? ? ? ? ? Hty Hnest HnestC Hds_no Hvs_no Hds_fst Hvs_fst].
    - unfold ValList; simpl.
      rewrite map_to_list_empty, filter_nil.
      unfold list_to_value; simpl.
      rewrite merge_empty.
      apply CompatRefl; apply SC_Empty.
    - apply CompatibleEqual in IHHsc; last done.
      unfold ValList; simpl; map_unfold.
      rewrite map_to_list_insert_first_key by assumption.
      rewrite filter_cons_True. 
      + unfold list_to_value.
        rewrite list_to_map_cons; simpl.
        rewrite <- insert_merge with (x := val).
        * rewrite !Value_insert_fold, !Desc_insert_fold.
          apply CompatAdd; try done.
          -- by apply SC_SCO in Hsc.
          -- fold (Vals (VALUE vs)); fold (ValList (<[k:=f]> (DESC fs)) (VALUE vs)).
             rewrite Desc_insert_unfold. rewrite Desc_insert_fold, ValList_drop_ok by assumption.
             fold (Fields $ DESC fs).
             fold (list_to_value (DESC fs) (ValList (DESC (Fields $ DESC fs)) (VALUE vs))); simpl.
             rewrite <- IHHsc. by apply SC_SCO in Hsc.
          -- fold (Vals (VALUE vs)); fold (ValList (<[k:=f]> (DESC fs)) (VALUE vs)).
             rewrite Desc_insert_unfold. rewrite Desc_insert_fold, ValList_drop_ok by assumption.
             fold (Fields $ DESC fs).
             fold (list_to_value (DESC fs) (ValList (DESC (Fields $ DESC fs)) (VALUE vs))); simpl.
             rewrite <- IHHsc. apply SC_SCO in Hsc. by apply CompatRefl.
          -- fold (Vals (VALUE vs)); fold (ValList (<[k:=f]> (DESC fs)) (VALUE vs)).
             rewrite Desc_insert_unfold. rewrite Desc_insert_fold, ValList_drop_ok by assumption.
             fold (Fields $ DESC fs).
             fold (list_to_value (DESC fs) (ValList (DESC (Fields $ DESC fs)) (VALUE vs))); simpl.
             rewrite <- IHHsc. by rewrite Value_lookup_unfold.
        * unfold Merge. destruct f; destruct val; unfold field_val_type_match; (contradiction || reflexivity).
      + unfold ValList_filter_p; simpl.
        rewrite lookup_insert_eq.
        destruct val; try trivial.
        unfold field_val_type_match in Hty.
        destruct f; contradiction.
  Qed.

  Lemma Value_wf_weaken : forall v d k, v !! k = None -> Value_wf d v <-> Value_wf (delete k d) v.
  Proof.
    intros v. value_unfold.
    induction vs as [|k val vs' Hno Hfst] using map_first_key_ind.
    - intros d k _. desc_unfold. by rewrite !map_fold_empty.
    - intros d k' Hno'. desc_unfold.
      split.
      + rewrite !map_fold_insert_first_key by assumption.
        destruct val; unfold Val_wf_fold; rewrite ?Val_wf_fold_eq, ?Value_wf_eq.
        * destruct (k' == k).
          -- by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
          -- rewrite lookup_delete_ne by assumption.
             destruct (fs !! k).
             ++ destruct f; try done.
                intros (Hwf & Hkey & Hwf_nest).
                split_and!; try (assumption || lia).
                rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
             ++ rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
        * destruct (k' == k).
          -- by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
          -- rewrite lookup_delete_ne by assumption.
             destruct (fs !! k).
             ++ destruct f; try done.
                intros (Hkey & Hwf_nest).
                split_and!; try (assumption || lia).
                rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
             ++ rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
        * destruct (k' == k).
          -- by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
          -- rewrite lookup_delete_ne by assumption.
             destruct (fs !! k).
             ++ destruct f; try done.
                intros (Hwf_nest & Hkey & Hwf).
                split_and!; try (assumption || lia).
                rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
             ++ rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
        * destruct (k' == k).
          -- by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
          -- rewrite lookup_delete_ne by assumption.
             destruct (fs !! k).
             ++ destruct f; done.
             ++ rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
                specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
                by rewrite <- IHvs.
      + rewrite !map_fold_insert_first_key by assumption.
        destruct val; unfold Val_wf_fold; rewrite ?Val_wf_fold_eq, ?Value_wf_eq; destruct (k' == k).
        * by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
        * rewrite lookup_delete_ne by assumption.
          destruct (fs !! k).
          -- destruct f; try done.
             intros (Hwf & Hkey & Hwf_nest).
             split_and!; try (assumption || lia).
             rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
          -- rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
        * by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
        * rewrite lookup_delete_ne by assumption.
          destruct (fs !! k).
          -- destruct f; try done.
             intros (Hkey & Hwf_nest).
             split_and!; try (assumption || lia).
             rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
          -- rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
        * by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
        * rewrite lookup_delete_ne by assumption.
          destruct (fs !! k).
          -- destruct f; try done.
             intros (Hwf_nest & Hkey & Hwf).
             split_and!; try (assumption || lia).
             rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
          -- rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
        * by rewrite Value_lookup_unfold, e, lookup_insert_eq in Hno'.
        * rewrite lookup_delete_ne by assumption.
          destruct (fs !! k).
          -- destruct f; done.
          -- rewrite Value_lookup_unfold, lookup_insert_ne, Value_lookup_fold in Hno' by done.
             specialize (IHvs (DESC fs) k' Hno'); simpl in IHvs.
             by rewrite IHvs.
  Qed.

  Lemma WillEncode_weaken : forall kv d k v,
    kv ∈ ValList (delete k d) v -> WillEncode d kv <-> WillEncode (delete k d) kv.
  Proof.
    intros [k val] d k' v Hin.
    split.
    - unfold WillEncode; simpl. intros (f & Hsome & Hfold).
      map_unfold. unfold ValList in Hin. simpl in Hin.
      apply list_elem_of_filter in Hin as [Hfil Hin].
      unfold ValList_filter_p in Hfil; simpl in *.
      destruct (k' == k).
      + by rewrite e, lookup_delete_eq in Hfil.
      + rewrite lookup_delete_ne, Hsome in Hfil by assumption.
        exists f. rewrite lookup_delete_ne by assumption.
        split; first exact Hsome.
        destruct val; unfold Val_wf_fold in *;
          rewrite ?Val_wf_fold_eq, ?Value_wf_eq, lookup_delete_ne, Hsome in * by assumption;
                                                                   destruct f; done.
    - unfold WillEncode; simpl. intros (f & Hsome & Hfold).
      map_unfold. unfold ValList in Hin; simpl in Hin.
      apply list_elem_of_filter in Hin as [Hfil Hin].
      unfold ValList_filter_p in Hfil; simpl in *.
      destruct (k' == k).
      + by rewrite e, lookup_delete_eq in Hfil.
      + rewrite Hsome in Hfil by assumption.
        exists f. rewrite lookup_delete_ne in Hsome by assumption.
        split; first exact Hsome.
        destruct val; unfold Val_wf_fold in *;
          rewrite ?Val_wf_fold_eq, ?Value_wf_eq, lookup_delete_ne, Hsome in * by assumption;
                                                                   destruct f; done.
  Qed.
  
  Lemma ParseOk_wf : forall v d, 
    (* FIXME: ⟨ v ∷ d ⟩ is likely optional, replace filter_cons_True with filter_cons... *)
    ⟨ v ∷ d ⟩ -> Value_wf d v -> S.Rep_wf (WillEncode d) (ValList d v).
  Proof.
    intros v. value_unfold.
    induction vs as [|k val vs' Hno Hfst] using map_first_key_ind; first done.
    intros d Hsc. desc_unfold.
    pose proof (SC_delete_key _ _ k Hsc) as Hdel. 
    apply SC_implies_properties_typed in Hsc as (Hvd & Hdv & Hmissing & Hnest).
    specialize (Hvd k val) as Hval_in_d.
    rewrite Value_lookup_unfold in Hval_in_d.
    rewrite lookup_insert_eq in Hval_in_d.
    specialize (Hval_in_d eq_refl).
    destruct Hval_in_d as (f & Hd_in & Hty).
    rewrite map_fold_insert_first_key by assumption.
    unfold ValList; simpl.
    rewrite map_to_list_insert_first_key by assumption.
    rewrite filter_cons_True.
    - fold (Vals (VALUE vs')).
      fold (ValList (DESC fs) (VALUE vs')); simpl.
      rewrite Desc_lookup_unfold in Hd_in.
      destruct val; unfold Val_wf_fold;
        rewrite ?Val_wf_fold_eq, ?Value_wf_eq, Hd_in;
                                               destruct f; try done.
      + intros (Hfold & Hkey & Hval_wf). 
        split.
        * unfold WillEncode; simpl. exists (F_MSG d).
          rewrite Hd_in. split_and!; (done || lia).
        * rewrite ValList_drop_ok' with (k := k) by assumption.
          rewrite S.Rep_wf_iff_local with (wf2 := WillEncode (delete k (DESC fs))).
          -- apply IHvs.
             ++ by rewrite Value_delete_unfold, delete_insert_id in Hdel by assumption.
             ++ rewrite Desc_delete_unfold.
                change _ with (Value_wf (DESC $ delete k fs) (VALUE vs')).
                change _ with (Value_wf (DESC fs) (VALUE vs')) in Hfold.
                rewrite Value_wf_weaken with (k := k) in Hfold; done.
          -- intros kv Hin. by apply WillEncode_weaken with (v := VALUE vs').  
      + intros (Hkey & Hfold). 
        split.
        * unfold WillEncode; simpl. exists F_BOOL.
          rewrite Hd_in. split_and!; (done || lia).
        * rewrite ValList_drop_ok' with (k := k) by assumption.
          rewrite S.Rep_wf_iff_local with (wf2 := WillEncode (delete k (DESC fs))).
          -- apply IHvs.
             ++ by rewrite Value_delete_unfold, delete_insert_id in Hdel by assumption.
             ++ rewrite Desc_delete_unfold.
                change _ with (Value_wf (DESC $ delete k fs) (VALUE vs')).
                change _ with (Value_wf (DESC fs) (VALUE vs')) in Hfold.
                rewrite Value_wf_weaken with (k := k) in Hfold; done.
          -- intros kv Hin. by apply WillEncode_weaken with (v := VALUE vs').  
      + intros (Hfold & Hkey & Hwf). 
        split.
        * unfold WillEncode; simpl. exists F_INT.
          rewrite Hd_in. split_and!; (done || lia).
        * rewrite ValList_drop_ok' with (k := k) by assumption.
          rewrite S.Rep_wf_iff_local with (wf2 := WillEncode (delete k (DESC fs))).
          -- apply IHvs.
             ++ by rewrite Value_delete_unfold, delete_insert_id in Hdel by assumption.
             ++ rewrite Desc_delete_unfold.
                change _ with (Value_wf (DESC $ delete k fs) (VALUE vs')).
                change _ with (Value_wf (DESC fs) (VALUE vs')) in Hfold.
                rewrite Value_wf_weaken with (k := k) in Hfold; done.
          -- intros kv Hin. by apply WillEncode_weaken with (v := VALUE vs').  
    - unfold ValList_filter_p; simpl.
      desc_unfold. rewrite Hd_in.
      specialize (Hmissing k).
      rewrite Value_lookup_unfold in Hmissing.
      rewrite lookup_insert_eq in Hmissing.
      destruct val; done.
  Qed.

  Definition ParseOk_Value_P (v : Value) :=
    forall d, ⟨ v ∷ d ⟩ -> LimitParseOkCompat'' Compatible ParseValue SerialValue d d v.

  Definition ParseOk_Val_P (v : Val) :=
    forall d k enc,
    Val_wf d (k, v) ->
    SerialVal SerialValue d (k, v) = S.mkSuccess enc.

  Theorem InterParseOk : forall v d, ⟨ v ∷ d ⟩ -> LimitParseOkCompat'' Compatible ParseValue SerialValue d d v.
  Proof.
    intros v d Hsc.
    apply LimitRecursiveStateCompatCorrect with
      (valid_state := fun d v => ⟨ v ∷ d ⟩)
      (linked_state := fun d1 d2 => d1 = d2); try done.
    intros d' d2 x enc Hwf Hsc__n Hdeq IH. subst d2.
    intros Hser; exists (list_to_value d' (ValList d' x)); revert Hser.
    unfold SerialValue', ParseValue' at 1.
    apply LimitMapCompatFullCorrect.
    + apply (FullDescriptor_RoundTrip _ _ Hsc__n).
    + intros Hwf_vallist Hser. fold SerialValue' in Hser.
      apply @RepCorrectWeakFull with (enc := enc) (bound := Length enc)
      (ser__x := (SerialVal
         (S.recur_step_st SerialValue' ValueDepth x
            (λ (st__n : Desc) (x__n : Value) (_ : (ValueDepth x__n < ValueDepth x)%nat),
               S.recur_st SerialValue' ValueDepth st__n x__n))
         d')) (wfx := WillEncode d').
      * vm_compute. exists "Bind left failed"%string.
        exists (Some (mkData "Map underlying failed" []
                   (Some (mkData "No more data to parse" [] None)))).
        reflexivity.
      * intros [z val] enc__n Hwf__val. clear Hser.
        fold (SerialValue'). unfold S.recur_step_st. 
        unfold SerialVal. desc_unfold. unfold WillEncode in Hwf.
        destruct Hwf__val as (f & Hin & Hval_wf). simpl in Hin. rewrite Hin.
        destruct f.
        -- destruct val; simpl in *; try done.
           ++ rewrite Hin in Hval_wf. intros Hser.
              apply SerialConcatInversion in Hser.
              destruct Hser as ( enc__t & enc__b & Ht_ok & Hb_ok & Henc ).
              rewrite Henc, App_Length. apply UnsignedLength in Ht_ok. 
              lia.
           ++ rewrite Hin in Hval_wf. contradiction.
        -- destruct val; simpl in *; try done.
           ++ rewrite Hin in Hval_wf. intros Hser.
              apply SerialConcatInversion in Hser.
              destruct Hser as ( enc__t & enc__b & Ht_ok & Hb_ok & Henc ).
              rewrite Henc, App_Length. apply UnsignedLength in Ht_ok. 
              lia.
           ++ rewrite Hin in Hval_wf. contradiction.
        -- destruct val; simpl in *; try done.
           ++ rewrite Hin in Hval_wf. intros Hser.
              apply SerialConcatInversion in Hser.
              destruct Hser as ( enc__t & enc__b & Ht_ok & Hb_ok & Henc ).
              rewrite Henc, App_Length. apply UnsignedLength in Ht_ok. 
              lia.
           ++ rewrite Hin in Hval_wf. contradiction.
      * clear v d Hsc Hser. intros [z v] enc__elem Hin Hser Hbound rest Hwf__n _. revert Hser.
        unfold SerialVal at 1. unfold ParseVal at 1.
        destruct Hwf__n as (f & Hin__d & Hval_wf); simpl in *. rewrite Hin__d.
        destruct f.
        -- destruct v; fold (SerialValue'); try done.
           ++ unfold S.Map, S.Opt.
              apply DepConcatCorrect_internal.
              ** clear; intros. by apply UnsignedNonEmpty with (x := l).
              ** apply UnsignedParseOk.
              ** intros enc__nested Hnest_bound rest__nested Hwf_nested Hser.
                 rewrite Hin__d. unfold P.Map at 1.
                 unfold S.PartMap in Hser.
                 unfold S.recur_step_st in Hser.
                 unfold P.recur_step_st.
                 apply SerialLen'Inversion in Hser as (enc__len & enc__pay & Hlen_ok & Hpay_ok & Henc).
                 destruct (decide (_ < ValueDepth x)%nat) as [Hval_depth |] eqn:Hdepth in Hpay_ok;
                   last (
                       unfold S.RecursiveProgressError in Hpay_ok;
                       destruct (ValueDepth _ == ValueDepth _) in Hpay_ok; discriminate
                     ).
                 unfold P.Len, P.Bind. rewrite Henc, ?App_assoc.
                 apply (NatStrictParseOk _ _ (App enc__pay rest__nested)) in Hlen_ok.
                 --- rewrite Hlen_ok. unfold P.Limit. rewrite Slice_App.
                     rewrite Henc, App_Length in Hnest_bound.
                     destruct (decide (Length enc__pay < Length enc)%nat) as [Hpay_depth |]; last lia.
                     unfold Val_wf_fold in Hval_wf;
                       rewrite Hin__d, Value_wf_eq in Hval_wf.
                     destruct Hval_wf as (_ & Hkey & Hval_wf). 
                     assert (⟨ v ∷ d ⟩) as Hsc_nest.
                     {
                       apply SC_implies_nested_correct in Hsc__n.
                       apply ValList_elem_of in Hin.
                       rewrite map_Forall_lookup in Hsc__n.
                       replace (x !! z) with (Vals x !! z) in Hin by by value_unfold.
                       specialize (Hsc__n z (V_MSG v) Hin) as HnestedCorrect.
                       unfold NestedCorrect in HnestedCorrect.
                       by rewrite Hin__d in HnestedCorrect.
                     }
                     specialize (IH enc__pay d d v Hpay_depth Hval_depth Hval_wf Hsc_nest eq_refl Hpay_ok).
                     destruct IH as (v' & Hparse_ok & Hcompat).
                     apply CompatibleEqual in Hcompat; last trivial. subst v'.
                     by rewrite Hparse_ok, App_nil_l, Drop_App.
                 --- unfold S.PartMap_wf, S.Len'_wf, S.recur_step_st in Hwf_nested.
                     rewrite Hdepth, Hpay_ok, Hlen_ok in Hwf_nested. lia.
              ** (* Have to show that encoding of nested message is small enough to be tagged correctly *)
                unfold S.Concat_wf, S.PartMap_wf.
                unfold Val_wf_fold in Hval_wf; rewrite Hin__d, Value_wf_eq in Hval_wf.
                destruct Hval_wf as (_ & Hkey_wf & Hnested_val_wf).
                split; first exact Hkey_wf.
                unfold S.Len'_wf.
                destruct (S.recur_step_st _ _ _ _ _ _) eqn:Hser; last trivial.
                destruct (SerialNatStrict _) eqn:Htag; last trivial.
                split; last exact Hnested_val_wf. rewrite result0 in Htag.
                by apply NatStrictStrict in Htag.
           ++ unfold Val_wf, Val_wf_fold in Hval_wf.
              rewrite Hin__d in Hval_wf. contradiction.
        -- destruct v; fold (SerialValue'); try done.
           ++ unfold S.Map, S.Opt.
              apply DepConcatCorrect; first apply UnsignedParseOk.
              ** intros enc__pay rest__pay Hwf_pay Hser.
                 rewrite Hin__d. unfold P.Map.
                 unfold S.PartMap in Hser.
                 apply (BoolParseOk _ _ rest__pay) in Hser.
                 --- by rewrite Hser.
                 --- by unfold S.PartMap_wf in Hwf_pay.
              ** unfold S.Concat_wf, S.PartMap_wf, S.Trivial_wf.
                 unfold Val_wf_fold in Hval_wf.
                 rewrite Hin__d in Hval_wf. destruct Hval_wf as [Hval_wf _].
                 lia.
           ++ unfold Val_wf, Val_wf_fold in Hval_wf.
              rewrite Hin__d in Hval_wf. contradiction.
        -- destruct v; fold (SerialValue'); try done.
           ++ unfold S.Map, S.Opt.
              apply DepConcatCorrect; first apply UnsignedParseOk.
              ** intros enc__pay rest__pay Hwf_pay Hser.
                 rewrite Hin__d. unfold P.Map.
                 unfold S.PartMap in Hser.
                 apply (Z32ParseOk _ _ rest__pay) in Hser.
                 --- by rewrite Hser.
                 --- unfold SerialZ_wf, S.PartMap_wf in *. lia.
              ** unfold S.Concat_wf, S.PartMap_wf, SerialZ_wf.
                 unfold Val_wf_fold in Hval_wf.
                 rewrite Hin__d in Hval_wf. destruct Hval_wf as [_ Hval_wf].
                 lia.
           ++ unfold Val_wf, Val_wf_fold in Hval_wf.
              rewrite Hin__d in Hval_wf. contradiction.
      * apply ParseOk_wf; assumption.
      * exact Hser.
      * lia.
    + unfold S.Map_wf.
      apply ParseOk_wf; assumption.
  Qed.

End Theorems.
