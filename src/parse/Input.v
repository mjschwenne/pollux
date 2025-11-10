From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.

(* Define abstract types and their properties *)
Module Type AbstractInput.
  Parameter Input : Type.
  Parameter Input_default : Input.
  Parameter C : Type.
  Parameter C_default : C.

  (* AbstractInput must support equality *)
  Parameter Input_eq : EqDecision Input.
  Parameter C_eq : EqDecision C.

  (* AbstractInput must support length *)
  Parameter Length : Input -> nat.

  (* AbstractInput must support viewing as a sequence *)
  Parameter View : Input -> list C.
  Axiom View_length : forall self, length (View self) = Length self.

  (* AbstractInput must support conversion to a sequence *)
  Parameter ToInput : list C -> Input.
  Axiom ToInput_correct : forall r, View (ToInput r) = r.

  (* AbstractInput must support indexing *)
  Parameter CharAt : Input -> nat -> C.
  Axiom CharAt_correct :
    forall self i, 0 <= i < Length self ->
    CharAt self i = nth i (View self) C_default.

  Parameter App : Input -> Input -> Input.
  Axiom App_correct :
    forall self other, App self other = ToInput $ (View self) ++ (View other).
  Axiom App_nil_l :
    forall self, App Input_default self = self.
  Axiom App_assoc :
    forall i1 i2 i3, App (App i1 i2) i3 = App i1 (App i2 i3).

  (* AbstractInput must support dropping elements *)
  Parameter Drop : Input -> nat -> Input.
  Axiom Drop_correct :
    forall self start, 0 <= start <= Length self ->
    View (Drop self start) = drop start (View self).
  Axiom Drop_zero : forall self, Drop self 0 = self.

  (* AbstractInput must support slicing *)
  Parameter Slice : Input -> nat -> nat -> Input.
  Axiom Slice_correct :
    forall self start end',
    0 <= start /\ start <= end' /\ end' <= Length self ->
    View (Slice self start end') = Util.sublist start end' (View self).

  (* For the Lemma about Drop, just use drop_drop *)
  Axiom DropDrop :
    forall self a b,
    0 <= a <= Length self -> 0 <= b <= Length self - a -> Drop self (a + b) = Drop (Drop self a) b.
End AbstractInput.

Module ByteInput <: AbstractInput.
  Definition C := byte.
  Definition C_default := (W8 0).
  Definition Input := list C.
  Definition Input_default : Input := [].

  Definition C_eq := w8_eq_dec.
  Definition Input_eq := @list_eq_dec C C_eq.

  Definition ToInput (r : list C) := r.
  Definition View (self : Input) := self.
  Definition Length (self : Input) := length self.
  Definition CharAt (self : Input) (i : nat) := nth i self C_default.
  Definition App (self : Input) (other : Input) := self ++ other.
  Definition Drop (self : Input) (start : nat) := drop start self.
  Definition Slice (self : Input) (start last : nat) := Util.sublist start last self.

  Theorem View_length : forall self, length (View self) = Length self.
  Proof. reflexivity. Qed.

  Theorem ToInput_correct : forall r, View (ToInput r) = r.
  Proof. reflexivity. Qed.

  Theorem CharAt_correct : forall self i, 0 <= i < length self ->
                                     CharAt self i = nth i (View self) C_default.
  Proof. reflexivity. Qed.

  Theorem App_correct : forall self other, App self other = ToInput $ (View self) ++ (View other).
  Proof. reflexivity. Qed.

  Theorem App_nil_l : forall self, App Input_default self = self.
  Proof. intros. unfold App. rewrite app_nil_l. reflexivity. Qed.

  Theorem App_assoc : forall i1 i2 i3, App (App i1 i2) i3 = App i1 (App i2 i3).
  Proof. intros. unfold App. rewrite <- app_assoc. reflexivity. Qed.

  Theorem Drop_correct : forall self start, 0 <= start <= Length self ->
                                       View (Drop self start) = drop start (View self).
  Proof. reflexivity. Qed.

  Theorem Slice_correct : forall self start end',
    0 <= start /\ start <= end' /\ end' <= Length self ->
    View (Slice self start end') = Util.sublist start end' (View self).
  Proof. reflexivity. Qed.

  Theorem Drop_zero : forall self, Drop self 0 = self.
  Proof. intros. unfold Drop. apply drop_0. Qed.

  Theorem DropDrop : 
    forall self a b,
    0 <= a <= Length self -> 0 <= b <= Length self - a -> Drop self (a + b) = Drop (Drop self a) b.
  Proof.
    intros.
    unfold Drop.
    symmetry.
    apply drop_drop.
  Qed.

End ByteInput.
