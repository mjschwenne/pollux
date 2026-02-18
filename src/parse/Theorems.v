From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Failure.
From Pollux.parse Require Import Parser.
From Pollux.parse Require Import Serializer.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Theorems (InputModule : AbstractInput).
  Module F := Failures(InputModule).
  Module P := Parsers(InputModule).
  Module S := Serializers(InputModule).
  Import InputModule.

  Section Theorems.
    Context `{EqDecision Input}.

  Definition Output := Input.
  Definition Parser (X : Type) := P.Parser X.
  Definition Serializer (X : Type) (wf : X -> Prop) := S.Serializer X wf.

  Definition ParseOk''' {X : Type} {wf : X -> Prop}
    (par : Parser X) (ser : Serializer X wf) (x : X) (enc rest : Input) :=
    wf x -> ser x = S.Success enc -> par (App enc rest) = P.Success x rest.

  Definition ParseOk'' {X : Type} {wf : X -> Prop}
    (par : Parser X) (ser : Serializer X wf) (x : X) (enc : Input) :=
    forall (rest : Input), ParseOk''' par ser x enc rest.

  Definition ParseOk' {X : Type} {wf : X -> Prop} (par : Parser X) (ser : Serializer X wf) (x : X) :=
    forall (enc : Input), ParseOk'' par ser x enc.

  Definition ParseOk {X : Type} {wf : X -> Prop} (par : Parser X) (ser : Serializer X wf) :=
    forall (x : X), ParseOk' par ser x.

  Lemma SucceedCorrect {X : Type} (x : X) :
    ParseOk' (P.SucceedWith x) S.SucceedWith x.
  Proof using Type.
    intros enc rest wf_ok. 
    unfold S.SucceedWith.
    intros Hser_ok. inversion Hser_ok as [Henc].
    unfold P.SucceedWith.
    rewrite App_nil_l.
    reflexivity.
  Qed.

  (* While we couldn't do this for any type (see SucceedCorrect above), we CAN do it with unit
       since we know statically that there is only one member of type unit, (). *)
  Lemma EpsilonCorrect : ParseOk P.Epsilon S.Epsilon.
  Proof using Type.
    intros x enc rest Hwf Hser_ok.
    inversion Hser_ok as [Hdefault].
    subst.
    unfold P.Epsilon, P.SucceedWith.
    rewrite App_nil_l.
    destruct x.
    reflexivity.
  Qed.

  Lemma BindCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : R -> S.Serializer L wfl)
    (rp : L -> Parser R) (rs : S.Serializer R wfr) (tag : R -> L) :
    forall r, ParseOk lp (ls r) -> ParseOk (rp (tag r)) rs ->
         ParseOk' (P.Bind lp rp) (S.Bind tag ls rs) r.
  Proof using Type.
    intros x Hleft_ok Hright_ok enc rest wf_ok.
    unfold S.Bind.
    destruct (ls x (tag x)) as [l_enc|] eqn:Hleft; last discriminate.
    destruct (rs x) as [r_enc|] eqn:Hright; last discriminate.
    intro Hser_ok. inversion Hser_ok as [Henc].
    rewrite App_assoc.
    unfold P.Bind.
    destruct wf_ok as [wfl_ok wfr_ok].
    pose proof Hleft_ok (tag x) l_enc (App r_enc rest) wfl_ok Hleft as Hl_ret.
    rewrite Hl_ret.
    pose proof Hright_ok x r_enc rest wfr_ok Hright as Hr_ret.
    assumption.
  Qed.

  Definition BindSucceedsRightOk {R L : Type} {wfr : R -> Prop}
    (rp : L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) : Prop := 
    forall (r : R) (r_enc rest : Input), ParseOk''' (rp (tag r) (App r_enc rest)) rs r r_enc rest.

  Definition BindSucceedsLeftOk {R L : Type} {wfl : L -> Prop}
    (lp : Parser L) (ls : R -> Output -> Serializer L wfl) (tag : R -> L) : Prop :=
    forall (r : R) (l_enc r_enc rest : Input), ParseOk''' lp (ls r r_enc) (tag r) l_enc (App r_enc rest).

  Lemma BindSucceedsCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : R -> Output -> S.Serializer L wfl)
    (rp : L -> Input -> Parser R) (rs : S.Serializer R wfr) (tag : R -> L) :
    BindSucceedsRightOk rp rs tag -> BindSucceedsLeftOk lp ls tag ->
    ParseOk (P.BindSucceeds lp rp) (S.BindSucceeds tag ls rs).
  Proof using Type.
    intros Hright_ok Hleft_ok x enc rest wf_ok.
    unfold S.BindSucceeds.
    destruct (rs x) as [r_enc|] eqn:Hright; last discriminate.
    destruct (ls x r_enc (tag x)) as [l_enc|] eqn:Hleft; last discriminate.
    intros Hser_ok. inversion Hser_ok as [Henc].
    destruct wf_ok as [wfl_ok wfr_ok].
    rewrite App_assoc.
    unfold P.BindSucceeds.
    pose proof Hleft_ok x l_enc r_enc rest as Hlp.
    pose proof wfl_ok as wfl_ok'.
    apply Hlp in wfl_ok' as _, Hleft as Hl_ret; try assumption.
    rewrite Hl_ret.
    pose proof Hright_ok x r_enc rest as Hrp.
    pose proof wfr_ok as wfr_ok'.
    apply Hrp in wfr_ok' as _, Hright as Hr_ret; try assumption.
  Qed.

  Definition BindResultLeftOk {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : S.Result -> Output -> Serializer L wfl)
    (rs : Serializer R wfr) (tag : R -> L): Prop :=
    forall (r : R), ParseOk' lp (ls (rs r) (S.Out $ rs r)) (tag r).

  Definition BindResultRightOk {L R : Type} {wfr : R -> Prop}
    (rp : P.Result L -> Input -> Parser R) (rs : Serializer R wfr)
    (lp : Parser L) (tag : R -> L) : Prop :=
    forall (r : R) (l_enc r_enc rest: Input),
    let enc := (App (App l_enc r_enc) rest) in
    ParseOk''' (rp (lp enc) enc) rs r r_enc rest.

  Lemma BindResultCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : S.Result -> Output -> S.Serializer L wfl)
    (rp : P.Result L -> Input -> Parser R) (rs : S.Serializer R wfr) (tag : R -> L) :
    BindResultLeftOk lp ls rs tag -> BindResultRightOk rp rs lp tag ->
    ParseOk (P.BindResult lp rp) (S.BindResult tag ls rs).
  Proof using Type.
    unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
    intros Hleft_ok Hright_ok x enc rest wf_ok.
    unfold S.BindResult.
    destruct (rs x) as [r_enc|] eqn:Hright.
    - simpl. symmetry in Hright.
      intro Hls. unfold S.BindResult_wf in wf_ok.
      destruct wf_ok as [wfl_ok wfr_ok].
      pose proof Hright as Hright'.
      pose proof Hleft_ok x enc rest as Hlp. 
      rewrite <- Hright in Hlp. simpl in Hlp.
      pose proof wfl_ok as wfl_ok'.
      apply Hlp in wfl_ok' as _, Hls as Hl_ret; try assumption.
      unfold P.BindResult.
      rewrite Hl_ret.

      unfold BindResultRightOk, ParseOk', ParseOk'', ParseOk''' in Hright_ok.
      pose proof Hright_ok x enc r_enc rest as Hr.
      pose proof wfr_ok as wfr_ok'.
      symmetry in Hright'.
      apply Hr in wfr_ok' as _, Hright' as Hr_ret; try assumption.
      (* rewrite Hl_ret in Hr_ret. *)
  Abort.

  Lemma SerialConcatInversion {A B : Type} {wf__a : A -> Prop} {wf__b : B -> Prop}
    (ser__a : S.Serializer A wf__a) (ser__b : S.Serializer B wf__b) : 
    forall (a : A) (b : B) (enc : Output),
    S.Concat ser__a ser__b (a, b) = S.Success enc <->
                                  exists (enc__a enc__b : Output),
                                    ser__a a = S.Success enc__a /\
                                    ser__b b = S.Success enc__b /\
                                    enc = App enc__a enc__b.
  Proof using Type.
    intros. split.
    - unfold S.Concat.
      destruct (ser__a a) as [out__a |] eqn:Ha; last discriminate.
      destruct (ser__b b) as [out__b |] eqn:Hb; last discriminate.
      intro H; inversion H as [Henc]; clear H.
      exists out__a, out__b. repeat (split; first reflexivity); reflexivity.
    - intros (out__a & out__b & Ha & Hb & Henc). unfold S.Concat.
      rewrite Ha, Hb. congruence.
  Qed.

  Theorem ConcatCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : S.Serializer L wfl)
    (rp : Parser R) (rs : S.Serializer R wfr) :
    ParseOk lp ls -> ParseOk rp rs -> ParseOk (P.Concat lp rp) (S.Concat ls rs).
  Proof using Type.
    intros Hleft_ok Hright_ok.
    intros [l r] enc rest [Hl_wf Hr_wf] Hconcat.
    apply SerialConcatInversion in Hconcat.
    destruct Hconcat as (enc__l & enc__r & Hl & Hr & Henc).
    subst. rewrite App_assoc.
    apply (Hleft_ok _ _ (App enc__r rest)) in Hl; last assumption.
    apply (Hright_ok _ _ rest) in Hr; last assumption.
    unfold P.Concat.
    rewrite Hl, Hr.
    reflexivity.
  Qed.

  Lemma BindCorrect' {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
    (lp : Parser L) (ls : S.Serializer L wfl)
    (rp : L -> Parser R) (rs : S.Serializer R wfr) (tag : R -> L) :
    forall r, ParseOk lp ls -> ParseOk' (rp (tag r)) rs r -> ParseOk' (P.Bind lp rp) (S.Bind' tag ls rs) r.
  Proof using Type.
    intros r Hleft_ok Hright_ok enc rest [wfl_ok wfr_ok] Hbind.
    apply SerialConcatInversion in Hbind.
    destruct Hbind as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
    rewrite Henc. rewrite App_assoc.
    unfold P.Bind.
    apply (Hleft_ok _ _ (App enc__r rest)) in Hl_ok; last assumption.
    rewrite Hl_ok.
    apply (Hright_ok _ rest) in Hr_ok; assumption.
  Qed.

  (* Relax the rest requirement, since the Limit parser will ensure rest = [] *)
  Definition LimitParseOk {X : Type} {wf : X -> Prop} (ser : Serializer X wf) (par : Parser X) := 
    forall x enc,
    wf x -> ser x = S.Success enc -> par enc = P.Success x Input_default.

  Definition LenOk {X : Type} {wf : X -> Prop} (ser : Serializer X wf) (len : X -> nat) (x : X) :=
    forall enc, ser x = S.Success enc -> len x = Length enc.

  Lemma LimitCorrect {X : Type} {wf : X -> Prop} (len : X -> nat)
    (underlying__ser : S.Serializer X wf) (underlying__par : Parser X) (x : X) :
    LimitParseOk underlying__ser underlying__par ->
    LenOk underlying__ser len x ->
    ParseOk' (P.Limit underlying__par (len x)) (S.Limit underlying__ser len) x.
  Proof using Type.
    intros Hlim_ok Hlen_ok enc rest Hwf.
    unfold S.Limit, P.Limit.
    intros Hser.
    unfold LenOk in Hlen_ok.
    specialize (Hlen_ok enc Hser).
    rewrite Hlen_ok.
    rewrite Slice_App.
    specialize (Hlim_ok x enc Hwf Hser).
    rewrite Hlim_ok.
    rewrite Drop_App, App_nil_l.
    reflexivity.
  Qed.

  Lemma LenCorrect {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop}
    (ser__len : S.Serializer nat wfn) (par__len : Parser nat) (len : X -> nat)
    (ser__x : S.Serializer X wfx) (par__x : Parser X) (x : X) :
    ParseOk par__len ser__len ->
    LimitParseOk ser__x par__x ->
    LenOk ser__x len x ->
    ParseOk' (P.Len par__len par__x) (S.Len len ser__len ser__x) x.
  Proof using Type.
    intros Hnat_ok Hlim_ok Hlen_ok.
    unfold P.Len, S.Len.
    apply BindCorrect'; first assumption.
    apply LimitCorrect; assumption.
  Qed.

  Definition LimitParseOkWeak {X : Type} {wf : X -> Prop} (ser : Serializer X wf) (par : Parser X) (x : X) := 
    forall enc, wf x -> ser x = S.Success enc -> par enc = P.Success x Input_default.

  Lemma LenCorrect'Weakened {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop}
    (ser__len : S.Serializer nat wfn) (par__len : Parser nat)
    (ser__x : S.Serializer X wfx) (par__x : Parser X) (x : X) :
    ParseOk par__len ser__len ->
    LimitParseOkWeak ser__x par__x x ->
    ParseOk' (P.Len par__len par__x) (S.Len' ser__len ser__x) x.
  Proof using Type.
    intros Hnat_ok Hlim_ok enc' rest Hwf.
    unfold P.Len, S.Len'.
    destruct (ser__x x) as [enc__x |] eqn:Hser__x; last discriminate.
    destruct (ser__len (Length enc__x)) as [enc__len |] eqn:Hser__len; last discriminate.
    unfold S.Len'_wf in Hwf.
    rewrite Hser__x in Hwf.
    rewrite Hser__len in Hwf.
    destruct Hwf as [Hwf__len Hwf__x].
    intros Henc. inversion Henc as [Henc__x].
    unfold P.Bind.
    rewrite App_assoc.
    specialize (Hnat_ok (Length enc__x) enc__len (App enc__x rest) Hwf__len Hser__len); rewrite Hnat_ok.
    unfold P.Limit.
    rewrite Slice_App.
    specialize (Hlim_ok enc__x Hwf__x Hser__x); rewrite Hlim_ok.
    rewrite App_nil_l, Drop_App.
    reflexivity.
  Qed.
  
  Lemma LenCorrect' {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop}
    (ser__len : S.Serializer nat wfn) (par__len : Parser nat)
    (ser__x : S.Serializer X wfx) (par__x : Parser X) :
    ParseOk par__len ser__len ->
    LimitParseOk ser__x par__x ->
    ParseOk (P.Len par__len par__x) (S.Len' ser__len ser__x).
  Proof using Type.
    intros Hnat_ok Hlim_ok x enc rest Hwf.
    unfold P.Len, S.Len'.
    destruct (ser__x x) as [enc__x |] eqn:Hser__x; last discriminate.
    destruct (ser__len (Length enc__x)) as [enc__len |] eqn:Hser__len; last discriminate.
    unfold S.Len'_wf in Hwf.
    rewrite Hser__x in Hwf.
    rewrite Hser__len in Hwf.
    destruct Hwf as [Hwf__len Hwf__x].
    intros H; inversion H as [Henc]; clear H.
    unfold P.Bind.
    rewrite App_assoc.
    specialize (Hnat_ok (Length enc__x) enc__len (App enc__x rest) Hwf__len Hser__len); rewrite Hnat_ok.
    unfold P.Limit.
    rewrite Slice_App.
    specialize (Hlim_ok x enc__x Hwf__x Hser__x); rewrite Hlim_ok.
    rewrite App_nil_l, Drop_App.
    reflexivity.
  Qed.

  Lemma SerialLen'Inversion {X : Type} {wfn : nat -> Prop} {wfx : X -> Prop}
    (ser__n : S.Serializer nat wfn) (ser__x : S.Serializer X wfx) :
    forall (x : X) (enc : Output),
    S.Len' ser__n ser__x x = S.Success enc <->
                           exists (enc__n enc__x : Output),
                             ser__n (Length enc__x) = S.Success enc__n /\
                             ser__x x = S.Success enc__x /\
                             enc = App enc__n enc__x.
  Proof using Type.
    intros. split.
    - unfold S.Len'.
      destruct (ser__x x) as [out__x |] eqn:Hx; last discriminate.
      destruct (ser__n (Length out__x)) as [out__n |] eqn:Hn; last discriminate.
      intro H; inversion H as [Henc]; clear H.
      exists out__n, out__x. repeat (split; done).
    - intros (out__n & out__x & Hn & Hx & Henc). unfold S.Len'.
      rewrite Hx, Hn, Henc. reflexivity.
  Qed.

  Lemma par_rep'_unfold {X : Type} (underlying : Parser X) (inp : Input) :
    P.rep' underlying inp =
        match underlying inp with
        | P.Success x rem => if decide (Length rem < Length inp) then
                            match P.rep' underlying rem with
                            | P.Success xs rest => P.Success (x :: xs) rest
                            | P.Failure P.Failure.Recoverable data => P.Success [x] rem
                            | P.Failure P.Failure.Fatal data => P.Failure P.Failure.Fatal data
                            end
                          else
                            P.Failure P.Failure.Fatal $ P.Failure.mkData
                              "Parser.Rep underlying increased input length" rem None
        | P.Failure P.Failure.Recoverable (P.Failure.mkData _ rem _) => P.Success [] rem
        | P.Failure P.Failure.Fatal data => P.Failure P.Failure.Fatal data
        end.
  Proof using Type.
    unfold P.rep'. unfold P.rep'_func.
    rewrite WfExtensionality.fix_sub_eq_ext; program_simpl.
    destruct (underlying inp); program_simpl.
    - destruct (decide (Length remaining < Length inp)); last reflexivity.
      destruct (Fix_sub _); first reflexivity.
      destruct level; reflexivity.
    - destruct level; first reflexivity.
      destruct data; reflexivity.
  Qed.

  Lemma par_rep_fold'_unfold {A B : Type} (underlying : Parser B) (combine : A -> B -> A)
    (acc : A) (inp : Input) :
    P.rep_fold' underlying combine acc inp =
      match underlying inp with
      | P.Success ret rem => if decide (Length rem < Length inp) then
                            P.rep_fold' underlying combine (combine acc ret) rem
                          else
                            P.Success acc inp
      | P.Failure lvl data as f => if P.NeedsAlternative f inp then
                                  P.Success acc inp
                                else
                                  @P.Propagate A _ (P.Failure lvl data) I
      end.
  Proof using Type.
    unfold P.rep_fold', P.rep_fold'_func.
    rewrite WfExtensionality.fix_sub_eq_ext; program_simpl.
    destruct (underlying inp); last reflexivity. f_equal.
  Qed.

  Lemma ser_rep'_unfold {X : Type} {wfx : X -> Prop}
    (underlying : S.Serializer X wfx) (xs : list X):
    S.rep' underlying xs = 
    match xs with
    | [] => S.Success S.Output_default
    | x :: xs' => match underlying x, S.rep' underlying xs' with
                 | S.Success x_enc, S.Success rest_enc => S.Success $ App x_enc rest_enc
                 | S.Failure lvl data as f, S.Success rest_enc => f
                 | S.Success x_enc, S.Failure lvl data as f => f
                 | S.Failure lvl__x data__x, S.Failure lvl__r data__r =>
                     S.Failure S.Failure.Recoverable $ S.Failure.Concat data__x data__r
                 end
    end.
  Proof using Type.
    destruct xs; reflexivity.
  Qed.
  
  Lemma SerialRepInversion_First {X : Type} {wfx : X -> Prop} (ser__x : S.Serializer X wfx) :
    forall (x : X) (xs : list X) (enc : Output),
      S.Rep ser__x (x :: xs) = S.Success enc <-> exists enc__x enc__rest,
          ser__x x = S.Success enc__x /\
          S.Rep ser__x xs = S.Success enc__rest /\
          enc = (App enc__x enc__rest). 
  Proof using Type.
    intros x xs enc. split.
    - unfold S.Rep. rewrite ser_rep'_unfold.
      destruct (ser__x x) as [out__x |] eqn:Hser__x.
      * destruct (S.rep' ser__x xs); last discriminate.
        intro Hser. inversion Hser as [Henc].
        exists out__x, out. done.
      * destruct (S.rep' ser__x xs); last discriminate.
        discriminate.
    - intros (enc__x & enc__rest & Hser__x & Hser__rest & Henc).
      unfold S.Rep in Hser__rest.
      rewrite ser_rep'_unfold, Hser__x, Hser__rest, Henc; reflexivity.
  Qed.

  Lemma SerialRepInversion {X : Type} {wfx : X -> Prop} (ser__x : S.Serializer X wfx) :
    forall (xs : list X),
      (exists enc, S.Rep ser__x xs = S.Success enc) <-> forall x, x ∈ xs -> exists enc__x, ser__x x = S.Success enc__x.
  Proof using Type.
    (* This proof written almost completely by Gemini 3 Pro... *)
    intros xs.
    induction xs as [|y ys IH].
    - split.
      + intros [enc Hser] x Hx. apply not_elem_of_nil in Hx. contradiction.
      + intros H. exists S.Output_default. rewrite ser_rep'_unfold. reflexivity.
    - split.
      + intros [enc Hser] x Hx.
        rewrite SerialRepInversion_First in Hser.
        destruct Hser as (enc__y & enc__rest & Hy_ok & Hrest_ok & Henc).
        rewrite elem_of_cons in Hx. destruct Hx as [Heq|Hin].
        * subst. exists enc__y. assumption.
        * apply (proj1 IH).
          -- exists enc__rest. assumption.
          -- assumption.
      + intros H.
        assert (exists enc__y, ser__x y = S.Success enc__y) as [enc__y Henc__y].
        { destruct (H y) as [ex Hex].
          - apply list_elem_of_here.
          - exists ex. assumption. }
        assert (exists enc__rest, S.Rep ser__x ys = S.Success enc__rest) as [enc__rest Henc__rest].
        { apply (proj2 IH). intros z Hz. destruct (H z) as [ez Hez].
          - simpl; right; assumption.
          - exists ez. assumption. }
        exists (App enc__y enc__rest).
        rewrite SerialRepInversion_First.
        exists enc__y, enc__rest.
        repeat split; assumption.
  Qed.


  Lemma SerialRepSubst {X : Type} {wfx : X -> Prop} (ser1 ser2 : S.Serializer X wfx) :
    forall xs, (forall x, x ∈ xs -> ser1 x = ser2 x) -> S.Rep ser1 xs = S.Rep ser2 xs.
  Proof using Type.
    intros xs Heq.
    induction xs.
    - reflexivity.
    - unfold S.Rep.
      rewrite ser_rep'_unfold.
      rewrite Heq by apply list_elem_of_here.
      rewrite (ser_rep'_unfold ser2).
      destruct (ser2 a).
      + unfold S.Rep in IHxs; rewrite IHxs; first reflexivity.
        intros x Helem.
        apply list_elem_of_further with (y := a) in Helem.
        apply Heq. assumption.
      + unfold S.Rep in IHxs; rewrite IHxs; first reflexivity.
        intros x Helem.
        apply list_elem_of_further with (y := a) in Helem.
        apply Heq. assumption.
  Qed.

  Lemma RepCorrect {X : Type} {wfx : X -> Prop} (ser__x : S.Serializer X wfx) (par__x : Parser X) :
    (* TODO: Split this into a typeclass. Make one for consuming parsers too. *)
    (exists msg, par__x Input_default = P.Failure P.Failure.Recoverable $ P.Failure.mkData msg Input_default None) ->
    (forall x enc, ser__x x = S.Success enc -> Length enc > 0) ->
    ParseOk par__x ser__x ->
    LimitParseOk (S.Rep ser__x) (P.Rep par__x).
  Proof using Type.
    intros HparEmp Hpro HpOk xs.
    induction xs as [| y ys].
    - intros enc Hwf Hser. simpl in Hser.
      inversion Hser as [Henc].
      rewrite (@par_rep'_unfold X).
      unfold S.Output_default;
      rewrite Length_default.
      destruct HparEmp as [emp_msg HparEmp].
      rewrite HparEmp.
      reflexivity.
    - intros enc Hwf. destruct Hwf as [Hwf__y Hwf__rest].
      unfold S.Rep, P.Rep.
      intros Hser. rewrite SerialRepInversion_First in Hser.
      destruct Hser as (enc__y & enc__rest & Hser__y & Hser__rest & Henc).
      rewrite (@par_rep'_unfold X), Henc, App_Length.
      specialize (HpOk y enc__y enc__rest Hwf__y Hser__y) as Hok__y.
      rewrite Hok__y.
      pose proof (Hpro y enc__y Hser__y) as Hpro__y.
      destruct (decide (Length _ < _)); last lia.
      specialize (IHys enc__rest Hwf__rest Hser__rest); unfold P.Rep in IHys.
      rewrite IHys. reflexivity.
  Qed.

  Lemma par_recur_unfold {X : Type} (underlying : Parser X -> Parser X) (inp : Input) :
    P.recur underlying inp =
    underlying (fun rem => match decide (Length rem < Length inp) with
                        | left _ => P.recur underlying rem
                        | right _ => P.RecursiveProgressError "Parser.Recursive" inp rem
                        end) inp.
  Proof using Type.
    unfold P.recur at 1. unfold P.recur_func.
    rewrite WfExtensionality.fix_sub_eq_ext.
    f_equal.
  Qed.
  
  Lemma ser_recur_unfold {X : Type} {wfx : X -> Prop} (underlying : S.Serializer X wfx -> S.Serializer X wfx)
    (depth : X -> nat) (x : X) :
    S.recur underlying depth x =
    underlying (fun x__n => match decide (depth x__n < depth x) with
                       | left _ => S.recur underlying depth x__n
                       | right _ => S.RecursiveProgressError "Serial.Recursive" depth x x__n
                       end) x.
  Proof using Type.
    unfold S.recur at 1. unfold S.recur_func.
    rewrite WfExtensionality.fix_sub_eq_ext.
    f_equal. 
  Qed.

  Theorem RecursiveCorrect {X : Type} {wf : X -> Prop}
    (par_underlying : Parser X -> Parser X)
    (ser_underlying : S.Serializer X wf -> S.Serializer X wf)
    (depth : X -> nat) :
    (forall (x : X) (enc rest : Input),
       wf x ->
       (forall (inp__n : Input) (x__n : X),
          Length inp__n < Length (App enc rest) ->
          depth x__n < depth x ->
          wf x__n ->
          forall rest__n,
          S.recur ser_underlying depth x__n = S.Success inp__n ->
          P.recur par_underlying (App inp__n rest__n) = P.Success x__n rest__n) ->
       ser_underlying (S.recur_step ser_underlying depth x
                         (fun x__n _ => S.recur ser_underlying depth x__n)) x = S.Success enc ->
       par_underlying (P.recur_step par_underlying (App enc rest)
                         (fun inp__n _ => P.recur par_underlying inp__n)) (App enc rest) =
       P.Success x rest) ->
    ParseOk (P.Recursive par_underlying) (S.Recursive ser_underlying depth).
  Proof using Type.
    intros H_underlying_ok.
    unfold ParseOk, ParseOk', ParseOk'', ParseOk''', P.Recursive, S.Recursive.
    intros x enc rest Hwf Hser.
    
    (* The proof proceeds by well-founded induction on depth x *)
    remember (depth x) as d eqn:Heq.
    revert x enc rest Hwf Hser Heq.
    induction d as [d IH] using lt_wf_ind.
    intros x enc rest Hwf Hser Heq.
    
    rewrite par_recur_unfold.
    rewrite ser_recur_unfold in Hser.
    
    unfold P.recur_step in H_underlying_ok.
    eapply H_underlying_ok; eauto.
    
    intros inp__n r__n Hlen__n Hdepth__n Hwf__n rest__n Hser__n.
    
    eapply IH.
    - subst d. exact Hdepth__n.
    - exact Hwf__n.
    - exact Hser__n.
    - reflexivity.
  Qed.

  Lemma par_recur_st_unfold {X S : Type}
    (underlying : (S -> Parser X) -> (S -> Parser X))
    (st : S)
    (inp : Input) :
    P.recur_st underlying st inp =
    underlying (fun st__n rem => if decide (Length rem < Length inp) then
                              P.recur_st underlying st__n rem
                            else
                              P.RecursiveProgressError "Parser.RecursiveState" inp rem
      ) st inp.
  Proof using Type.
    unfold P.recur_st at 1. unfold P.recur_st_func.
    rewrite WfExtensionality.fix_sub_eq_ext.
    f_equal.
  Qed.

  Lemma ser_recur_st_unfold {X S : Type} {wfx : X -> Prop}
    (underlying : (S -> S.Serializer X wfx) -> S -> S.Serializer X wfx)
    (depth : X -> nat) (st : S) (x : X) :
    S.recur_st underlying depth st x =
    underlying (fun st__n x__n => if decide (depth x__n < depth x) then
                             S.recur_st underlying depth st__n x__n
                           else
                             S.RecursiveProgressError "Serial.RecursiveState" depth x x__n
      ) st x.
  Proof using Type.
    unfold S.recur_st at 1. unfold S.recur_st_func.
    rewrite WfExtensionality.fix_sub_eq_ext.
    f_equal. 
  Qed.

  Theorem RecursiveStateCorrect {X S : Type} {wf : X -> Prop}
    (par_underlying : (S -> Parser X) -> S -> Parser X)
    (ser_underlying : (S -> S.Serializer X wf) -> S -> S.Serializer X wf)
    (valid_state : S -> X -> Prop)
    (depth : X -> nat)
    (st : S)
    (x : X) :
    (forall (st : S) (x : X) (enc rest : Input),
       wf x -> valid_state st x ->
       (forall (inp__n : Input) (st__n : S) (x__n : X),
          Length inp__n < Length (App enc rest) ->
          depth x__n < depth x ->
          wf x__n ->
          valid_state st__n x__n ->
          forall rest__n,
          S.recur_st ser_underlying depth st__n x__n = S.Success inp__n ->
          P.recur_st par_underlying st__n (App inp__n rest__n) = P.Success x__n rest__n) ->
       ser_underlying (S.recur_step_st ser_underlying depth x
                         (fun st__n x__n _ => S.recur_st ser_underlying depth st__n x__n)) st x = S.Success enc ->
       par_underlying (P.recur_step_st par_underlying (App enc rest)
                         (fun st__n inp__n _ => P.recur_st par_underlying st__n inp__n)) st (App enc rest) =
       P.Success x rest) ->
    valid_state st x ->
    ParseOk' (P.RecursiveState par_underlying st)
      (S.RecursiveState ser_underlying depth st) x.
  Proof using Type.
    unfold ParseOk, ParseOk', ParseOk'', ParseOk''', P.RecursiveState, S.RecursiveState.
    intros H_underlying_ok Hstate_valid enc rest Hwf Hser.
    
    (* The proof proceeds by well-founded induction on depth x *)
    remember (depth x) as d eqn:Heq.
    revert st x Hstate_valid enc rest Hwf Hser Heq.
    induction d as [d IH] using lt_wf_ind.
    intros st x Hstate enc rest Hwf Hser Heq.
    
    rewrite par_recur_st_unfold.
    rewrite ser_recur_st_unfold in Hser.
    
    unfold P.recur_step_st in H_underlying_ok.
    eapply H_underlying_ok; eauto.
    
    intros inp__n st__n r__n Hlen__n Hdepth__n Hwf__n Hstate__n rest__n Hser__n.
    
    eapply IH.
    - subst d. exact Hdepth__n.
    - exact Hstate__n.
    - exact Hwf__n.
    - exact Hser__n.
    - reflexivity.
  Qed.
  End Theorems.
End Theorems.
