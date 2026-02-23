From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.
From Corelib Require Import Morphisms.

Module Result (InputModule : AbstractInput).
  Section Failure.
    Import InputModule.

    Context `{EqDecision Input}.

    Inductive Level :=
    | Fatal
    | Recoverable.

    Global Instance Level_dec : forall (x y : Level), Decision (x = y).
    Proof using Type.
      intros x y.
      destruct x, y; ((left; reflexivity) || (right; discriminate)).
    Qed.

    Global Instance Level_eqdec : EqDecision Level.
    Proof.
      unfold EqDecision.
      apply Level_dec.
    Defined.

    (* Record information about when a parse / serialize fails *)
    (* I'll use the failure data for the serializers too, but interpret "remaining" as "output". *)
    Inductive Data :=
    | mkData (msg : string) (remaining : Input) (next : option Data).

    Definition getMsg (data : Data) : string :=
      match data with
      | mkData msg _ _ => msg
      end.

    Definition getRemaining (data : Data) : Input :=
      match data with
      | mkData _ remaining _ => remaining
      end.

    Definition getNext (data : Data) : option Data :=
      match data with
      | mkData _ _ next => next
      end.

    Definition maxLevel (l1 l2 : Level) : Level :=
      match l1, l2 with
      | Recoverable, Recoverable => Recoverable
      | Recoverable, Fatal => Fatal
      | Fatal, Recoverable => Fatal
      | Fatal, Fatal => Fatal
      end.

    (* Add more failure data to the end of the current chain of failures *)
    Fixpoint ConcatData (self other : Data) : Data :=
      match self with
      | mkData msg remaining next =>
          match next with
          | None => mkData msg remaining (Some other)
          | Some next_val => mkData msg remaining (Some (ConcatData next_val other))
          end
      end.

  End Failure.

  Section Result.
    Import InputModule.

    Context `{EqDecision Input}.

    Inductive Result {X : Type} :=
    | Success (result : X) (enc : Input)
    | Failure (lvl : Level) (data : Data).
    Arguments Result X : clear implicits.

    (* NOTE: Use parser / serializer specific aliases for purposeful enc meaning *)
    Definition getEnc {X : Type} (r : Result X) : Input :=
      match r with
      | Success _ rem
      | Failure _ (mkData _ rem _) => rem
      end.

    Definition IsFailure {X : Type} (r : Result X) : bool :=
      match r with
      | Failure _ _ => true
      | _ => false
      end.
    
    Definition IsFatalFailure {X : Type} (r : Result X) : bool :=
      match r with
      | Failure Fatal _ => true
      | _ => false
      end.
    
    Definition IsFailureProp {X : Type} (r : Result X) : Prop :=
      match r with
      | Failure _ _ => True
      | _ => False
      end.
    
    (* This function basically lets us change the parameterized type of a parse failure. This is useful
     if we imagine that parsing a number depends are first parsing a list of digits. If we fail to
     parse the list of digits, we want to propagate that error up as the result of paring the number
     but can't (directly) do this since the type of the failure is wrong. This function constructs
     the same parse failure but with the correct type. It takes a proof term as input since this
     only makes sense for failures. Successes with have something of type R in them, which we can't
     convert to a U. *)
    Definition Propagate {A B : Type} (pr : Result A) (pf : IsFailureProp pr) :
      Result B.
    Proof.
      destruct pr.
      - destruct pf.
      - apply Failure; assumption.
    Defined.

    Definition IsSuccess {X : Type} (r : Result X) : bool :=
      match r with
      | Success _ _ => true
      | Failure _ _ => false
      end.
    
    Definition IsSuccessProp {X : Type} (r : Result X) : Prop :=
      match r with
      | Success _ _ => True
      | Failure _ _ => False
      end.

    (* Similarly to PropagateFailure, this function only works on a ParseSuccess and lets us unwrap it.
     Honestly, both of these could be done inline whenever needed, but I like learning more about how
     to handle these in Rocq. I don't know what extraction would do to these. *)
    Definition Extract {X : Type} (pr : Result X) (pf : IsSuccessProp pr) : X * Input. 
    Proof.
      destruct pr.
      - split; assumption.
      - destruct pf.
    Defined.

    Definition ResultMap {X Y : Type} (r : Result X) (f : X -> Y) : Result Y :=
      match r with
      | Success result remaining => Success (f result) remaining
      | Failure lvl data => Failure lvl data
      end.

    Definition MapRecoverableError {X : Type} (r : Result X) (f : Data -> Data) :
      Result X :=
      match r with
      | Failure Recoverable data => Failure Recoverable (f data)
      | _ => r
      end.

    (* Only useful for parsers which support backtracking. If we encounter a
       recoverable error which didn't consume input, then we can backtrack safely. *)
    (* WARN: I hope this doesn't complicate the notion of failure equivalence... *)
    Definition NeedsAlternative {X : Type} (r : Result X) (input : Input) : bool :=
      match r with
      | Failure Recoverable (mkData _ rem _) => if rem == input then true else false
      | _ => false
      end.

  End Result.
  Arguments Result X : clear implicits.

  Section ResultEquivalence.
    Import InputModule.

    Context {X : Type}.
    Context `{EqDecision X}.
    Context `{EqDecision Input}.

    Definition result_equivb (ret1 ret2 : Result X) : bool :=
      match ret1, ret2 with
      | Success r1 rem1, Success r2 rem2 => if r1 == r2 then
                                             if rem1 == rem2 then true else false
                                           else
                                             false
      | Success _ _, Failure _ _
      | Failure _ _, Success _ _ => false
      | Failure lvl1 _, Failure lvl2 _ => if lvl1 == lvl2 then true else false
      end.

    Definition result_equiv : relation (Result X) :=
      fun ret1 ret2 => match ret1, ret2 with
                    | Success r1 rem1, Success r2 rem2 => r1 = r2 /\ rem1 = rem2
                    | Success _ _, Failure _ _
                    | Failure _ _, Success _ _ => False
                    | Failure lvl1 _, Failure lvl2 _ => lvl1 = lvl2
                    end.
    Infix "≡ᵣ" := result_equiv (at level 70):type_scope.

    Theorem ResultEquivSuccess : forall r1 r2 x1 x2 enc1 enc2,
      r1 ≡ᵣ r2 -> r1 = Success x1 enc1 -> r2 = Success x2 enc2 ->
      x1 = x2 /\ enc1 = enc2.
    Proof using Type.
      intros r1 r2 x1 x2 enc1 enc2 Hequiv Hsucc1 Hsucc2.
      subst. unfold result_equiv in Hequiv.
      assumption.
    Qed.

    Theorem ResultEquivSuccessApp : forall x enc enc1 enc2,
      Success x enc1 ≡ᵣ Success x enc2 ->
      Success x (App enc enc1) ≡ᵣ Success x (App enc enc2).
    Proof using Type.
      unfold result_equiv.
      intros x enc enc1 enc2 [_ Henc].
      subst. split; reflexivity.
    Qed.

    Lemma result_equiv_refl : Reflexive result_equiv.
    Proof using Type.
      intros r. destruct r; done.
    Qed.

    Lemma result_equiv_sym : Symmetric result_equiv.
    Proof using Type.
      intros r1 r2 H.
      destruct r1 as [x1 enc1 | lvl1 data1], r2 as [x2 enc2 | lvl2 data2].
      - destruct H as [Hx Henc]. done.
      - unfold result_equiv in H. contradiction.
      - unfold result_equiv in H. contradiction.
      - unfold result_equiv in H. done.
    Qed.

    Lemma result_equiv_trans : Transitive result_equiv.
    Proof using Type.
      intros r1 r2 r3 H H'.
      destruct r1 as [x1 enc1 | lvl1 data1],
                 r2 as [x2 enc2 | lvl2 data2],
                   r3 as [x3 enc3 | lvl3 data3];
                   unfold result_equiv in *; try contradiction.
      - destruct H as [Hx12 Henc12], H' as [Hx23 Henc23]; subst. easy.
      - congruence.
    Qed.

    Instance result_equiv_Equiv : Equivalence result_equiv.
    Proof using Type.
      split; [
          apply result_equiv_refl |
          apply result_equiv_sym |
          apply result_equiv_trans
        ].
    Qed.

  End ResultEquivalence.
  Infix "≡ᵣ" := result_equiv (at level 70):type_scope.
End Result.
