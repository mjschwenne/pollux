From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Result.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Serializers (InputModule : AbstractInput).
  Module R := Result(InputModule).
  Import R.
  Import InputModule.

  (* Use Output type for serializers, just to help keep the terminology intuitive. *)
  (* Since results have an result for use in parsers, we'll always use unit for the Serializers *)
  Definition Output := Input.
  Definition Output_default := Input_default.
  Definition mkSuccess enc := Success () enc.
  Lemma mkSuccess_eq : forall enc, R.Success () enc = mkSuccess enc.
  Proof. intros. reflexivity. Qed.
  Definition Out := @getEnc unit.
  Definition Result := @Result unit.

  Section Def.
    Definition Serializer (X : Type) (wf : X -> Prop) := X -> Result. 

    Definition Trivial_wf {X : Type} : X -> Prop := fun _ => True.
  End Def.

  Section Combinators.

    Definition SucceedWith {X : Type} : Serializer X Trivial_wf :=
      fun inp => mkSuccess Output_default.

    Definition Epsilon : (Serializer unit Trivial_wf) := SucceedWith.
    
    Definition FailWith {X : Type} (message : string) (level : Level) :
      Serializer X Trivial_wf :=
      fun inp => Failure level $ mkData message Output_default None.

    Definition ResultWith {X : Type} (result : Result) : Serializer X Trivial_wf :=
      fun inp => result.
    Instance ResultWith_Proper (X : Type) :
      forall x, Proper (result_equiv ==> result_equiv) (@flip Result X Result ResultWith x).
    Proof.
      intros x r1 r2 Hequiv.
      unfold flip, ResultWith.
      assumption.
    Qed.

    Definition Blob : Serializer Output Trivial_wf :=
      fun b => mkSuccess b.

    Definition Concat_wf {L R : Type} (wfl : L -> Prop) (wfr : R -> Prop) : (L * R) -> Prop :=
      fun lr => let (l, r) := lr in wfl l /\ wfr r.

    Definition Concat {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (left : Serializer L wfl) (right : Serializer R wfr) : Serializer (L * R) (Concat_wf wfl wfr) :=
      fun inp =>
        let (l, r) := inp in 
        match left l, right r with
        | Success _ l_enc, Success _ r_enc => mkSuccess (App l_enc r_enc)
        | Failure level data, Success _ r_enc =>
            Failure level $
              mkData "Conat left failed, right succeeded" r_enc
              (Some data)
        | Success _ l_enc, Failure level data =>
            Failure level $
              mkData "Concat right failed, left succeeded" l_enc
              (Some data)
        | Failure l_lvl l_data, Failure r_lvl r_data =>
            Failure (maxLevel l_lvl r_lvl) $
              mkData "Concat both failed"
              Output_default
              (Some $ ConcatData l_data r_data)
        end.

    Definition Bind'_wf {L R : Type} (wfl : L -> Prop) (wfr : R -> Prop) (tag : R -> L) : R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    Definition Bind' {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : Serializer L wfl) (right : Serializer R wfr) :
      Serializer R $ Bind'_wf wfl wfr tag :=
      fun r => Concat left right (tag r, r).

    Definition Bind_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : R -> Serializer L wfl) (right : Serializer R wfr) : R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    Definition Bind {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop} 
      (tag : R -> L) (left : forall r, Serializer L (fun l => l = tag r /\ wfl l)) (right : Serializer R wfr) :
      Serializer R (@Bind_wf L R wfl wfr tag left right) := 
      fun r =>
        match left r (tag r) with
        | Success _ l_enc => match right r with
                            | Success _ r_enc => mkSuccess (App l_enc r_enc)
                            | Failure lvl data => Failure lvl $
                                                   mkData
                                                   "Bind serializing body failed"
                                                   l_enc
                                                   (Some data)
                            end
        | Failure lvl data => Failure lvl $
                               mkData
                               "Bind serializing tag failed"
                               Output_default
                               (Some data)
        end.

    Definition BindSucceeds_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : R -> Output -> Serializer L wfl) (right : Serializer R wfr) : R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    (* This is tricky since technically Parse.BindSucceeds isn't limited to only
    inspecting the encoding of the right serializer (could use things like the
    lookahead parser) so the correctness theorem will have to ensure that both
    get the same encoding. *)
    Definition BindSucceeds {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}  
      (tag : R -> L) (left : R -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (BindSucceeds_wf tag left right) := 
      fun r =>
        match right r with
        | Success _ r_enc => match left r r_enc (tag r) with
                            | Success _ l_enc => mkSuccess (App l_enc r_enc)
                            | Failure lvl data => Failure lvl $
                                                   mkData
                                                   "BindSucceeds serializing tag failed"
                                                   r_enc
                                                   (Some data)
                            end
        | Failure lvl data => Failure lvl $
                               mkData
                               "BindSucceeds serializing body failed"
                               Output_default
                               (Some data)
        end.

    Definition BindResult_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : Result -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    Definition BindResult {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : Result -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (BindResult_wf tag left right) :=
      fun r =>
        let r_ret := right r in
        left r_ret (Out r_ret) (tag r).

    (* This formulation is only useful for the proof. *)
    Definition Limit {X : Type} {wf : X -> Prop} (underlying : Serializer X wf) (len : X -> nat) :
      Serializer X wf := underlying.

    Definition Len_wf {X : Type} (wfx : X -> Prop) (wfn : nat -> Prop) (len : X -> nat) : X -> Prop :=
      fun x => wfn (len x) /\ wfx x.

    Definition Len {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop} (len : X -> nat)
      (ser__len : Serializer nat wfn) (underlying : Serializer X wfx) :
      Serializer X $ Len_wf wfx wfn len :=
      Bind' len ser__len $ Limit underlying len.

    Definition Len'_wf {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop}
      (ser__len : Serializer nat wfn) (ser__x : Serializer X wfx) : X -> Prop :=
      fun x => match ser__x x with
            | Success _ enc__x => match ser__len (Length enc__x) with
                               | Success _ enc__len => wfn (Length enc__x) /\ wfx x
                               | Failure _ _ => True
                               end
            | Failure _ _ => True
            end.
    
    Definition Len' {X : Type} {wfx : X -> Prop} {wfn : nat -> Prop}
      (ser__len : Serializer nat wfn) (underlying : Serializer X wfx) :
      Serializer X $ Len'_wf ser__len underlying :=
      fun x => match underlying x with
            | Success _ enc => match ser__len (Length enc) with
                              | Success _ len_enc => mkSuccess (App len_enc enc)
                              | Failure lvl data => Failure lvl $
                                                     mkData
                                                     "Len' serializing tag failed"
                                                     enc
                                                     (Some data)
                              end
            | Failure lvl data => Failure lvl $
                                   mkData
                                   "Len' serializing body failed"
                                   Output_default
                                   (Some data)
            end.

    Definition Map_wf {A B : Type} (wf : B -> Prop) (f : A -> B) : A -> Prop :=
      fun a => wf (f a).
    
    Definition Map {A B : Type} {wf : B -> Prop} (underlying : Serializer B wf) (f : A -> B) :
      Serializer A $ Map_wf wf f := 
      fun a => underlying (f a).

    Fixpoint Rep_wf {X : Type} (wf : X -> Prop) (ls : list X) : Prop :=
      match ls with
      | [] => True
      | x :: ls' => wf x /\ Rep_wf wf ls'
      end.

    Fixpoint rep' {X : Type} {wfx : X -> Prop}
      (underlying : Serializer X wfx) (xs : list X) : Result :=
      match xs with
      | [] => mkSuccess Output_default
      | x :: xs' => match underlying x, rep' underlying xs' with
                   | Success _ x_enc, Success _ rest_enc => mkSuccess $ App x_enc rest_enc
                   | Failure lvl data as f, Success _ rest_enc => f
                   | Success _ x_enc, Failure lvl data as f => f
                   | Failure lvl__x data__x, Failure lvl__r data__r =>
                       Failure (maxLevel lvl__x lvl__r) $ ConcatData data__x data__r
                   end
      end.

    Definition Rep {X : Type} {wfx : X -> Prop}
      (underlying : Serializer X wfx) : Serializer (list X) (Rep_wf wfx) :=
      fun xs => rep' underlying xs.

    Definition RecursiveProgressError {X : Type} (name : string) (depth : X -> nat) (x x__n : X) : Result :=
      if depth x__n == depth x then
        Failure Recoverable (mkData
                               (name ++ " no progress in recursive serializer")
                               Output_default None)
      else
        Failure Fatal (mkData
                         (name ++ " fixpoint called with deeper value to serialize")
                         Output_default None).

    Definition recur_step {X : Type} {wfx : X -> Prop}
      (underlying : Serializer X wfx -> Serializer X wfx)
      (depth : X -> nat)
      (x : X)
      (rec_call : forall x__n : X, depth x__n < depth x -> Result)
      (x__n : X) : Result :=
      match decide (depth x__n < depth x) with
      | left pf => rec_call x__n pf
      | right _ => RecursiveProgressError "Serial.Recursive" depth x x__n
      end.

    Program Fixpoint recur {X : Type} {wfx : X -> Prop} 
      (underlying : Serializer X wfx -> Serializer X wfx)
      (depth : X -> nat) (x : X) {measure (depth x)} : Result :=
      underlying (recur_step underlying depth x
                    (fun x__n _ => recur underlying depth x__n)) x.

    Definition Recursive {X : Type} {wfx : X -> Prop} (underlying : Serializer X wfx -> Serializer X wfx) depth :
      Serializer X wfx := recur underlying depth.

    Definition recur_step_st {X S : Type} {wfx : X -> Prop}
      (underlying : (S -> Serializer X wfx) -> S -> Serializer X wfx)
      (depth : X -> nat)
      (x : X)
      (rec_call : forall (st : S) (x__n : X), depth x__n < depth x -> Result)
      (st : S)
      (x__n : X) : Result :=
      match decide (depth x__n < depth x) with
      | left pf => rec_call st x__n pf
      | right _ => RecursiveProgressError "Serial.RecursiveState" depth x x__n
      end.

    Program Fixpoint recur_st {X S : Type} {wfx : X -> Prop} 
      (underlying : (S -> Serializer X wfx) -> S -> Serializer X wfx)
      (depth : X -> nat) (st : S) (x : X) {measure (depth x)} : Result :=
      underlying (recur_step_st underlying depth x
                    (fun st__n x__n _ => recur_st underlying depth st__n x__n)) st x.

    Definition RecursiveState {X S : Type} {wfx : X -> Prop}
      (underlying : (S -> Serializer X wfx) -> S -> Serializer X wfx) depth st :
      Serializer X wfx := recur_st underlying depth st.

  End Combinators.
End Serializers.
