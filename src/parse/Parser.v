From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.
From Equations Require Import Equations.

Module Parsers (InputModule : AbstractInput).
  Section Parsers.
    Import InputModule.

    Context `{EqDecision Input}.

    Inductive FailureLevel :=
    | Fatal
    | Recoverable.

    (* Record information about when a parse / serialize fails *)
    Inductive FailureData :=
    | mkFailureData (msg : string) (remaining : Input) (next : option FailureData).

    Definition getFailureMsg (data : FailureData) : string :=
      match data with
      | mkFailureData msg _ _ => msg
      end.

    Definition getFailureRemaining (data : FailureData) : Input :=
      match data with
      | mkFailureData _ remaining _ => remaining
      end.

    Definition getFailureNext (data : FailureData) : option FailureData :=
      match data with
      | mkFailureData _ _ next => next
      end.

    (* Add more failure data to the end of the current chain of failures *)
    Fixpoint ConcatFailure (self other : FailureData) : FailureData :=
      match self with
      | mkFailureData msg remaining next =>
          match next with
          | None => mkFailureData msg remaining (Some other)
          | Some next_val => mkFailureData msg remaining (Some (ConcatFailure next_val other))
          end
      end.

    (** I'll use the failure for the serializers too, but interpret "remaining" as "output". *)
    
    Inductive ParseResult {R : Type} :=
    | ParseSuccess (result : R) (remaining : Input)
    | ParseFailure (level : FailureLevel) (data : FailureData).
    
    Arguments ParseResult R : clear implicits.

    (**
     FUNCTIONS ON PARSE RESULTS
     *)

    (* If Remaining is the same as the input, then parser is "uncommitted",
     so combinators like Or or ZeroOrMore can try alternatives. *)
    Definition Remaining {R : Type} (pr : ParseResult R) : Input :=
      match pr with
      | ParseSuccess _ rem
      | ParseFailure _ (mkFailureData _ rem _) => rem
      end.
    
    Definition IsFailure {R : Type} (pr : ParseResult R) : bool :=
      match pr with
      | ParseFailure _ _ => true
      | _ => false
      end.

    Definition IsFatalFailure {R : Type} (pr : ParseResult R) : bool :=
      match pr with
      | ParseFailure Fatal _ => true
      | _ => false
      end.

    Definition IsFailureProp {R : Type} (pr : ParseResult R) : Prop :=
      match pr with
      | ParseSuccess _ _ => False
      | ParseFailure _ _ => True
      end.

    (* This function basically lets us change the parameterized type of a parse failure. This is useful
     if we imagine that parsing a number depends are first parsing a list of digits. If we fail to
     parse the list of digits, we want to propagate that error up as the result of paring the number
     but can't (directly) do this since the type of the failure is wrong. This function constructs
     the same parse failure but with the correct type. It takes a proof term as input since this
     only makes sense for failures. Successes with have something of type R in them, which we can't
     convert to a U. *)
    Definition PropagateFailure {R : Type} {U : Type} (pr : ParseResult R) (pf : IsFailureProp pr) :
      ParseResult U.
    Proof.
      destruct pr.
      - destruct pf.
      - apply ParseFailure; assumption.
    Defined.

    Definition IsSuccessProp {R : Type} (pr : ParseResult R) : Prop :=
      match pr with
      | ParseSuccess _ _ => True
      | ParseFailure _ _ => False
      end.

    (* Similarly to PropagateFailure, this function only works on a ParseSuccess and lets us unwrap it.
     Honestly, both of these could be done inline whenever needed, but I like learning more about how
     to handle these in Rocq. I don't know what extraction would do to these. *)
    Definition Extract {R : Type} (pr : ParseResult R) (pf : IsSuccessProp pr) : R * Input. 
    Proof.
      destruct pr.
      - split; assumption.
      - destruct pf.
    Defined.

    Definition ResultMap {R : Type} {R' : Type} (pr : ParseResult R) (f : R -> R') : ParseResult R' :=
      match pr with
      | ParseSuccess result remaining => ParseSuccess (f result) remaining
      | ParseFailure lvl data => ParseFailure lvl data
      end.

    Definition MapRecoverableError {R : Type} (pr : ParseResult R) (f : FailureData -> FailureData) :
      ParseResult R :=
      match pr with
      | ParseFailure Recoverable data => ParseFailure Recoverable (f data)
      | _ => pr
      end.

    Definition NeedsAlternative {R : Type} (pr : ParseResult R) (input : Input) : bool :=
      match pr with
      | ParseFailure Recoverable (mkFailureData _ rem _) => if rem == input then true else false
      | _ => false
      end.

    (** SERIALIZER RESULTS *)

    (* Use Output type for serializers *)
    Definition Output := Input.

    Inductive SerializeResult :=
    | SerialSuccess (out : Output)
    | SerialFailure (level : FailureLevel) (data : FailureData).

    (** FUNCTIONS ON SERIALIZER RESULTS *)

    Definition Out (sr : SerializeResult) : Output := 
      match sr with
      | SerialSuccess out
      | SerialFailure _ (mkFailureData _ out _) => out
      end.

    Definition IsSerialFailure (sr : SerializeResult) : bool :=
      match sr with
      | SerialFailure _ _ => true
      | _ => false
      end.
    
    Definition IsSerialFatalFailure (sr : SerializeResult) : bool :=
      match sr with
      | SerialFailure Fatal _ => true
      | _ => false
      end.

    Definition IsSerialFailureProp (sr : SerializeResult) : Prop :=
      match sr with
      | SerialSuccess _ => False
      | SerialFailure _ _ => True
      end.
    
    (* PropagateSerialFailure function not needed since SerializeResults are parameterized. *)

    Definition IsSerialSuccessProp (sr : SerializeResult) : Prop :=
      match sr with
      | SerialSuccess _ => True
      | SerialFailure _ _ => False
      end.

    (**
     Parser Definition

     This are missing Dafny variance specifiers. I don't know how big of a problem this will be
     *)

    (* A parser is a total function from a position to a parse result *)
    Definition Parser R : Type := Input -> ParseResult R.

    (* A parser selector is a function that, given a name that exists,
     returns a parser associated to this name *)
    Definition ParserSelector R : Type := string -> ParseResult R.

    (** Serializer Definition *)

    Definition Serializer (R : Type) (wf : R -> Prop) := R -> SerializeResult. 

    (**
     Misc Utilities and Definitions
     *)
    Definition IsRemaining (input remaining : Input) : Prop :=
      Length remaining <= Length input /\ Drop input (Length input - Length remaining) = remaining.

    Lemma IsRemainingTrans (input remaining1 remaining2 : Input) :
      IsRemaining input remaining1 -> IsRemaining remaining1 remaining2 -> IsRemaining input remaining2.
    Proof using Type.
      intros [H1_len H1_drop] [H2_len H2_drop].
      unfold IsRemaining.
      split.
      - apply Nat.le_trans with (Length remaining1); assumption.
      - rewrite <- H2_drop at 2. 
        rewrite <- H1_drop at 1.
        rewrite <- DropDrop.
        * rewrite Nat.add_sub_assoc; last assumption.
          rewrite Nat.sub_add; last assumption.
          reflexivity.
        * lia.
        * lia.
    Qed.

    (** TOP LEVEL CORRECTNESS DEFINITION *)
    Definition ParseOk''' {R : Type} {wf : R -> Prop}
      (par : Parser R) (ser : Serializer R wf) (x : R) (enc rest : Input) :=
      wf x -> ser x = SerialSuccess enc -> par (App enc rest) = ParseSuccess x rest.

    Definition ParseOk'' {R : Type} {wf : R -> Prop}
      (par : Parser R) (ser : Serializer R wf) (x : R) (enc : Input) :=
      forall (rest : Input), ParseOk''' par ser x enc rest.

    Definition ParseOk' {R : Type} {wf : R -> Prop} (par : Parser R) (ser : Serializer R wf) (x : R) :=
      forall (enc : Input), ParseOk'' par ser x enc.

    Definition ParseOk {R : Type} {wf : R -> Prop} (par : Parser R) (ser : Serializer R wf) :=
      forall (x : R), ParseOk' par ser x.

    (**
     COMBINATORS
     *)

    (* This parser does not consume any input and returns the given value *)
    Definition ParseSucceedWith {R : Type} (result : R) : Parser R :=
      (fun inp => ParseSuccess result inp).

    Definition serial_trivial_wf {R : Type} : R -> Prop := fun _ => True.

    Definition SerialSucceedWith {R : Type} : Serializer R serial_trivial_wf :=
      (fun inp => SerialSuccess Input_default).

    Lemma SucceedCorrect {R : Type} (r : R) :
      ParseOk' (ParseSucceedWith r) SerialSucceedWith r.
    Proof using Type.
      intros enc rest wf_ok. 
      unfold SerialSucceedWith.
      intros Hser_ok. inversion Hser_ok as [Henc].
      unfold ParseSucceedWith.
      rewrite App_nil_l.
      reflexivity.
    Qed.

    (* A parser that always succeeds, consumes nothing and returns () *)
    Definition ParseEpsilon : (Parser unit) := ParseSucceedWith tt.

    Definition SerialEpsilon : (Serializer unit serial_trivial_wf) := SerialSucceedWith.

    (* While we couldn't do this for any type (see SucceedCorrect above), we CAN do it with unit
       since we know statically that there is only one member of type unit, (). *)
    Lemma EpsilonCorrect : ParseOk ParseEpsilon SerialEpsilon.
    Proof using Type.
      intros x enc rest Hwf Hser_ok.
      inversion Hser_ok as [Hdefault].
      subst.
      unfold ParseEpsilon.
      unfold ParseSucceedWith.
      rewrite App_nil_l.
      destruct x.
      reflexivity.
    Qed.

    (* A parser that does not consume any input and returns the given failure *)
    Definition ParseFailWith {R : Type} (message : string) (level : FailureLevel) : Parser R :=
      fun inp => ParseFailure level $ mkFailureData message inp None.

    Definition SerialFailWith {R : Type} (message : string) (level : FailureLevel) :
      Serializer R serial_trivial_wf :=
        fun inp => SerialFailure level $ mkFailureData message Input_default None.

    (* WARN I don't think a connecting lemma here is possible. *)

    (* A parser that always returns the given result *)
    Definition ParseResultWith {R : Type} (result : ParseResult R) : Parser R :=
      fun inp => result.

    Definition SerialResultWith {R : Type} (result : SerializeResult) : Serializer R serial_trivial_wf :=
      fun inp => result.

    (* WARN I don't think a connecting lemma here is possible. *)

    (* A parser that fails if the string has not been entirely consumed *)
    Definition ParseEndOfInput : Parser unit :=
      fun inp => if Length inp == 0 then
                ParseSuccess () inp
              else
                ParseFailure Recoverable
                  (mkFailureData "expected end of input" inp None).

    (* WARN I also don't there is a corresponding serializer combinator here. *)

    Definition SerialBlob : Serializer Output serial_trivial_wf :=
      fun b => SerialSuccess b.

    (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result and the remaining sequence to the right parser generator. *)
    Definition ParseBind {L R : Type} (left : Parser L) (right : L -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | ParseSuccess leftResult remaining => right leftResult remaining
        | ParseFailure level data => ParseFailure level data
        end.

    Definition Bind_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : R -> Serializer L wfl) (right : Serializer R wfr) : R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    Definition SerialBind {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop} 
      (tag : R -> L) (left : forall r, Serializer L (fun l => l = tag r /\ wfl l)) (right : Serializer R wfr) :
      Serializer R (@Bind_wf L R wfl wfr tag left right) := 
      fun r =>
        match left r (tag r) with
        | SerialSuccess l_enc => match right r with
                                | SerialSuccess r_enc => SerialSuccess (App l_enc r_enc)
                                | SerialFailure lvl data as f => f
                                end
        | SerialFailure lvl data as f => f
        end.

    Lemma BindCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : R -> Serializer L wfl)
      (rp : L -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      forall r, ParseOk lp (ls r) -> ParseOk (rp (tag r)) rs ->
      ParseOk' (ParseBind lp rp) (SerialBind tag ls rs) r.
    Proof using Type.
      intros x Hleft_ok Hright_ok enc rest wf_ok.
      unfold SerialBind.
      destruct (ls x (tag x)) as [l_enc|] eqn:Hleft; last discriminate.
      destruct (rs x) as [r_enc|] eqn:Hright; last discriminate.
      intro Hser_ok. inversion Hser_ok as [Henc].
      rewrite App_assoc.
      unfold ParseBind.
      destruct wf_ok as [wfl_ok wfr_ok].
      pose proof Hleft_ok (tag x) l_enc (App r_enc rest) wfl_ok Hleft as Hl_ret.
      rewrite Hl_ret.
      pose proof Hright_ok x r_enc rest wfr_ok Hright as Hr_ret.
      assumption.
    Qed.

    (* A parser that fails if the left parser fails. If the left parser
     succeeds, provides its result to the right parser generator and returns its
     result applied to the remaining input *)
    Definition ParseBindSucceeds {L R : Type} (left : Parser L) (right : L -> Input -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | ParseSuccess leftResult remaining => right leftResult remaining remaining
        | ParseFailure level data => ParseFailure level data
        end.

    Definition BindSucceeds_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : R -> Output -> Serializer L wfl) (right : Serializer R wfr) : R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    (* This is tricky since technically ParseBindSucceeds isn't limited to only
    inspecting the encoding of the right serializer (could use things like the
    lookahead parser) so the correctness theorem will have to ensure that both
    get the same encoding. *)
    Definition SerialBindSucceeds {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}  
      (tag : R -> L) (left : R -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (BindSucceeds_wf tag left right) := 
      fun r =>
        match right r with
        | SerialSuccess r_enc => match left r r_enc (tag r) with
                                | SerialSuccess l_enc => SerialSuccess (App l_enc r_enc)
                                | SerialFailure lvl data as f => f
                                end
        | SerialFailure lvl data as f => f
        end.

    Definition BindSucceedsRightOk {R L : Type} {wfr : R -> Prop}
      (rp : L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) : Prop := 
      forall (r : R) (r_enc rest : Input), ParseOk''' (rp (tag r) (App r_enc rest)) rs r r_enc rest.

    Definition BindSucceedsLeftOk {R L : Type} {wfl : L -> Prop}
      (lp : Parser L) (ls : R -> Output -> Serializer L wfl) (tag : R -> L) : Prop :=
      forall (r : R) (l_enc r_enc rest : Input), ParseOk''' lp (ls r r_enc) (tag r) l_enc (App r_enc rest).

    Lemma BindSucceedsCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : R -> Output -> Serializer L wfl)
      (rp : L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      BindSucceedsRightOk rp rs tag -> BindSucceedsLeftOk lp ls tag ->
      ParseOk (ParseBindSucceeds lp rp) (SerialBindSucceeds tag ls rs).
    Proof using Type.
      intros Hright_ok Hleft_ok x enc rest wf_ok.
      unfold SerialBindSucceeds.
      destruct (rs x) as [r_enc|] eqn:Hright; last discriminate.
      destruct (ls x r_enc (tag x)) as [l_enc|] eqn:Hleft; last discriminate.
      intros Hser_ok. inversion Hser_ok as [Henc].
      destruct wf_ok as [wfl_ok wfr_ok].
      rewrite App_assoc.
      unfold ParseBindSucceeds.
      pose proof Hleft_ok x l_enc r_enc rest as Hlp.
      pose proof wfl_ok as wfl_ok'.
      apply Hlp in wfl_ok' as _, Hleft as Hl_ret; try assumption.
      rewrite Hl_ret.
      pose proof Hright_ok x r_enc rest as Hrp.
      pose proof wfr_ok as wfr_ok'.
      apply Hrp in wfr_ok' as _, Hright as Hr_ret; try assumption.
    Qed.

    (* Given a left parser and a parser generator based on the output of the left parser,
     returns the result of the right parser applied on the original input. *)
    Definition ParseBindResult {L R : Type} (left : Parser L) (right : ParseResult L -> Input -> Parser R) :
      Parser R :=
      fun inp =>
        right (left inp) inp inp.

    Definition BindResult_wf {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : SerializeResult -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      R -> Prop :=
      fun r => wfl (tag r) /\ wfr r.

    Definition SerialBindResult {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : SerializeResult -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (BindResult_wf tag left right) :=
      fun r =>
        let r_ret := right r in
        left r_ret (Out r_ret) (tag r).

    Definition BindResultLeftOk {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : SerializeResult -> Output -> Serializer L wfl)
      (rs : Serializer R wfr) (tag : R -> L): Prop :=
      forall (r : R), ParseOk' lp (ls (rs r) (Out $ rs r)) (tag r).

    Definition BindResultRightOk {L R : Type} {wfr : R -> Prop}
      (rp : ParseResult L -> Input -> Parser R) (rs : Serializer R wfr)
      (lp : Parser L) (tag : R -> L) : Prop :=
      forall (r : R) (l_enc r_enc rest: Input),
      let enc := (App (App l_enc r_enc) rest) in
      ParseOk''' (rp (lp enc) enc) rs r r_enc rest.

    Lemma BindResultCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : SerializeResult -> Output -> Serializer L wfl)
      (rp : ParseResult L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      BindResultLeftOk lp ls rs tag -> BindResultRightOk rp rs lp tag ->
      ParseOk (ParseBindResult lp rp) (SerialBindResult tag ls rs).
    Proof using Type.
      unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
      intros Hleft_ok Hright_ok x enc rest wf_ok.
      unfold SerialBindResult.
      destruct (rs x) as [r_enc|] eqn:Hright.
      - simpl. symmetry in Hright.
        intro Hls. unfold BindResult_wf in wf_ok.
        destruct wf_ok as [wfl_ok wfr_ok].
        pose proof Hright as Hright'.
        pose proof Hleft_ok x enc rest as Hlp. 
        rewrite <- Hright in Hlp. simpl in Hlp.
        pose proof wfl_ok as wfl_ok'.
        apply Hlp in wfl_ok' as _, Hls as Hl_ret; try assumption.
        unfold ParseBindResult.
        rewrite Hl_ret.

        unfold BindResultRightOk, ParseOk', ParseOk'', ParseOk''' in Hright_ok.
        pose proof Hright_ok x enc r_enc rest as Hr.
        pose proof wfr_ok as wfr_ok'.
        symmetry in Hright'.
        apply Hr in wfr_ok' as _, Hright' as Hr_ret; try assumption.
        (* rewrite Hl_ret in Hr_ret. *)
    Abort.

    (* Apply two parser consecutively. If both succeed, return the pair of both results *)
    Definition ParseConcat {L R : Type} (left : Parser L) (right : Parser R) : Parser (L * R) :=
      fun inp =>
        match left inp with
        | ParseSuccess ll lrem => match right lrem with
                                 | ParseSuccess rr rrem => ParseSuccess (ll, rr) rrem
                                 | ParseFailure lvl data as p => PropagateFailure p I
                                 end
        | ParseFailure lvl data as p => PropagateFailure p I
        end.

    Definition Concat_wf {L R : Type} (wfl : L -> Prop) (wfr : R -> Prop) : (L * R) -> Prop :=
      fun lr => let (l, r) := lr in wfl l /\ wfr r.

    Definition SerialConcat {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (left : Serializer L wfl) (right : Serializer R wfr) : Serializer (L * R) (Concat_wf wfl wfr) :=
      fun inp =>
        let (l, r) := inp in 
        match left l, right r with
        | SerialSuccess l_enc, SerialSuccess r_enc => SerialSuccess (App l_enc r_enc)
        | SerialFailure level data, _
        | _, SerialFailure level data => SerialFailure level data
        end.

    Lemma SerialConcatInversion : forall {A B : Type} {wf__a : A -> Prop} {wf__b : B -> Prop}
                                      (ser__a : Serializer A wf__a) (ser__b : Serializer B wf__b)
                                      (a : A) (b : B) (enc : Output),
      SerialConcat ser__a ser__b (a, b) = SerialSuccess enc <->
                                        exists (enc__a enc__b : Output),
                                          ser__a a = SerialSuccess enc__a /\
                                          ser__b b = SerialSuccess enc__b /\
                                          enc = App enc__a enc__b.
    Proof using Type.
      intros. split.
      - unfold SerialConcat.
        destruct (ser__a a) as [out__a |] eqn:Ha; last discriminate.
        destruct (ser__b b) as [out__b |] eqn:Hb; last discriminate.
        intro H. inversion H as [Henc]. clear H.
        exists out__a, out__b. repeat (split; first reflexivity); reflexivity.
      - intros (out__a & out__b & Ha & Hb & Henc). unfold SerialConcat.
        rewrite Ha. rewrite Hb.
        subst. reflexivity.
    Qed.

    Theorem ConcatCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : Serializer L wfl)
      (rp : Parser R) (rs : Serializer R wfr) :
      ParseOk lp ls -> ParseOk rp rs -> ParseOk (ParseConcat lp rp) (SerialConcat ls rs).
    Proof using Type.
      intros Hleft_ok Hright_ok.
      intros [l r] enc rest [Hl_wf Hr_wf] Hconcat.
      apply SerialConcatInversion in Hconcat.
      destruct Hconcat as (enc__l & enc__r & Hl & Hr & Henc).
      subst. rewrite App_assoc.
      apply (Hleft_ok _ _ (App enc__r rest)) in Hl; last assumption.
      apply (Hright_ok _ _ rest) in Hr; last assumption.
      unfold ParseConcat.
      rewrite Hl. rewrite Hr.
      reflexivity.
    Qed.

    (* Apply two consecutive parsers consecutively. If both succeed, apply the mapper to the results
     and return it *)
    Definition ConcatMap {L R T : Type} (left : Parser L) (right : Parser R) (mapper : L -> R -> T) : Parser T :=
      fun inp =>
        match left inp with
        | ParseSuccess ll lrem => match right lrem with
                                 | ParseSuccess rr rrem => ParseSuccess (mapper ll rr) rrem
                                 | ParseFailure lvl data as p => PropagateFailure p I
                                 end
        | ParseFailure lvl data as p => PropagateFailure p I
        end.

    (* Return only the result of the right parser if the two parsers match *)
    Definition ConcatKeepRight {L R : Type} (left : Parser L) (right : Parser R) : Parser R :=
      ConcatMap left right (fun l r => r).
    
    (* Return only the result of the left parser if the two parsers match *)
    Definition ConcatKeepLeft {L R : Type} (left : Parser L) (right : Parser R) : Parser L :=
      ConcatMap left right (fun l r => l).
    
    Definition SerialBind' {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (tag : R -> L) (left : Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (fun r => wfl (tag r) /\ wfr r) :=
      fun r => SerialConcat left right (tag r, r).

    Lemma BindCorrect' {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : Serializer L wfl)
      (rp : L -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      forall r, ParseOk lp ls -> ParseOk' (rp (tag r)) rs r -> ParseOk' (ParseBind lp rp) (SerialBind' tag ls rs) r.
    Proof using Type.
      intros r Hleft_ok Hright_ok enc rest [wfl_ok wfr_ok] Hbind.
      apply SerialConcatInversion in Hbind.
      destruct Hbind as (enc__l & enc__r & Hl_ok & Hr_ok & Henc).
      rewrite Henc. rewrite App_assoc.
      unfold ParseBind.
      apply (Hleft_ok _ _ (App enc__r rest)) in Hl_ok; last assumption.
      rewrite Hl_ok.
      apply (Hright_ok _ rest) in Hr_ok; assumption.
    Qed.

    (* Limit the underlying parser to only access the first N tokens in the input. *)
    Definition ParseLimit {R : Type} (underlying : Parser R) (n : nat) : Parser R :=
      fun inp => match underlying (Slice inp 0 n) with
              | ParseSuccess r rem => ParseSuccess r (App rem (Drop inp n))
              | ParseFailure lvl data as f => f
              end.

    (* This formulation is only useful for the proof. *)
    Definition SerialLimit {R : Type} {wfr : R -> Prop} (underlying : Serializer R wfr) (len : R -> nat) :
      Serializer R wfr := underlying.

    Definition ParseLen {R : Type} (len : Parser nat) (underlying : Parser R) : Parser R :=
      ParseBind len (fun l => ParseLimit underlying l).

    Definition SerialLen {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop} (len : R -> nat)
      (ser_len : Serializer nat wfn) (underlying : Serializer R wfr) : Serializer R (fun r => wfn (len r) /\ wfr r) :=
      SerialBind' (len) ser_len (SerialLimit underlying len).

    Definition SerialLen'_wf {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop}
      (s__len : Serializer nat wfn) (s__r : Serializer R wfr) : R -> Prop :=
      fun r => match s__r r with
            | SerialSuccess enc__r => match s__len (Length enc__r) with
                                  | SerialSuccess enc__len => wfn (Length enc__r) /\ wfr r
                                  | SerialFailure _ _ => True
                                  end
            | SerialFailure _ _ => True
            end.
    
    Definition SerialLen' {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop}
      (ser_len : Serializer nat wfn) (underlying : Serializer R wfr) :
      Serializer R $ SerialLen'_wf ser_len underlying :=
      fun r => match underlying r with
            | SerialSuccess enc => match ser_len (Length enc) with
                                  | SerialSuccess len_enc => SerialSuccess (App len_enc enc)
                                  | SerialFailure lvl data as f => f
                                  end
            | SerialFailure lvl data as f => f
            end.

    (* Relax the rest requirement, since the Limit parser will ensure rest = [] *)
    Definition LimitParseOk {R : Type} {wf : R -> Prop} (ser : Serializer R wf) (par : Parser R) := 
      forall x enc,
      wf x -> ser x = SerialSuccess enc -> par enc = ParseSuccess x Input_default.

    Definition LenOk {R : Type} {wf : R -> Prop} (ser : Serializer R wf) (len : R -> nat) (r : R) :=
      forall enc, ser r = SerialSuccess enc -> len r = Length enc.

    Lemma LimitCorrect {R : Type} {wf : R -> Prop} (len : R -> nat)
      (underlying__ser : Serializer R wf) (underlying__par : Parser R) (r : R) :
      LimitParseOk underlying__ser underlying__par ->
      LenOk underlying__ser len r ->
      ParseOk' (ParseLimit underlying__par (len r)) (SerialLimit underlying__ser len) r.
    Proof using Type.
      intros Hlim_ok Hlen_ok.
      intros enc rest Hwf.
      unfold SerialLimit, ParseLimit.
      intros Hser.
      unfold LenOk in Hlen_ok.
      specialize (Hlen_ok enc Hser).
      rewrite Hlen_ok.
      rewrite Slice_App.
      specialize (Hlim_ok r enc Hwf Hser).
      rewrite Hlim_ok.
      rewrite Drop_App, App_nil_l.
      reflexivity.
    Qed.

    Lemma LenCorrect {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop}
      (ser__len : Serializer nat wfn) (par__len : Parser nat) (len : R -> nat)
      (ser__r : Serializer R wfr) (par__r : Parser R) (r : R) :
      ParseOk par__len ser__len ->
      LimitParseOk ser__r par__r ->
      LenOk ser__r len r ->
      ParseOk' (ParseLen par__len par__r) (SerialLen len ser__len ser__r) r.
    Proof using Type.
      intros Hnat_ok Hlim_ok Hlen_ok.
      unfold ParseLen, SerialLen.
      apply BindCorrect'; first assumption.
      apply LimitCorrect; assumption.
    Qed.

    Definition LimitParseOkWeak {R : Type} {wf : R -> Prop} (ser : Serializer R wf) (par : Parser R)
      (x : R) := 
      forall enc,
      wf x -> ser x = SerialSuccess enc -> par enc = ParseSuccess x Input_default.

    Lemma LenCorrect'Weakened {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop}
      (ser__len : Serializer nat wfn) (par__len : Parser nat)
      (ser__r : Serializer R wfr) (par__r : Parser R) (r : R) :
      ParseOk par__len ser__len ->
      LimitParseOkWeak ser__r par__r r ->
      ParseOk' (ParseLen par__len par__r) (SerialLen' ser__len ser__r) r.
    Proof using Type.
      intros Hnat_ok Hlim_ok.
      intros enc' rest Hwf.
      unfold ParseLen, SerialLen', ParseOk'''.
      destruct (ser__r r) as [enc__r |] eqn:Hser__r; last discriminate.
      destruct (ser__len (Length enc__r)) as [enc__len |] eqn:Hser__len; last discriminate.
      unfold SerialLen'_wf in Hwf.
      rewrite Hser__r in Hwf.
      rewrite Hser__len in Hwf.
      destruct Hwf as [Hwf__len Hwf__r].
      intros Henc. inversion Henc as [Henc__r].
      unfold ParseBind.
      rewrite App_assoc.
      specialize (Hnat_ok (Length enc__r) enc__len (App enc__r rest) Hwf__len Hser__len); rewrite Hnat_ok.
      unfold ParseLimit.
      rewrite Slice_App.
      specialize (Hlim_ok enc__r Hwf__r Hser__r); rewrite Hlim_ok.
      rewrite App_nil_l, Drop_App.
      reflexivity.
    Qed.
      
    Lemma LenCorrect' {R : Type} {wfr : R -> Prop} {wfn : nat -> Prop}
      (ser__len : Serializer nat wfn) (par__len : Parser nat)
      (ser__r : Serializer R wfr) (par__r : Parser R) :
      ParseOk par__len ser__len ->
      LimitParseOk ser__r par__r ->
      ParseOk (ParseLen par__len par__r) (SerialLen' ser__len ser__r).
    Proof using Type.
      intros Hnat_ok Hlim_ok.
      intros r enc rest Hwf.
      unfold ParseLen, SerialLen'.
      destruct (ser__r r) as [enc__r |] eqn:Hser__r; last discriminate.
      destruct (ser__len (Length enc__r)) as [enc__len |] eqn:Hser__len; last discriminate.
      unfold SerialLen'_wf in Hwf.
      rewrite Hser__r in Hwf.
      rewrite Hser__len in Hwf.
      destruct Hwf as [Hwf__len Hwf__r].
      intros Henc. inversion Henc.
      unfold ParseBind.
      rewrite App_assoc.
      specialize (Hnat_ok (Length enc__r) enc__len (App enc__r rest) Hwf__len Hser__len); rewrite Hnat_ok.
      unfold ParseLimit.
      rewrite Slice_App.
      specialize (Hlim_ok r enc__r Hwf__r Hser__r); rewrite Hlim_ok.
      rewrite App_nil_l, Drop_App.
      reflexivity.
    Qed.

    Lemma SerialLen'Inversion : forall {A : Type} {wfn : nat -> Prop} {wf__a : A -> Prop}
                                      (ser__n : Serializer nat wfn) (ser__a : Serializer A wf__a)
                                      (a : A) (enc : Output),
      SerialLen' ser__n ser__a a = SerialSuccess enc <->
                                 exists (enc__n enc__a : Output),
                                   ser__n (Length enc__a) = SerialSuccess enc__n /\
                                   ser__a a = SerialSuccess enc__a /\
                                   enc = App enc__n enc__a.
    Proof using Type.
      intros. split.
      - unfold SerialLen'.
        destruct (ser__a a) as [out__a |] eqn:Ha; last discriminate.
        destruct (ser__n (Length out__a)) as [out__n |] eqn:Hn; last discriminate.
        intro H; inversion H as [Henc]; clear H.
        exists out__n, out__a. repeat (split; done).
      - intros (out__n & out__a & Hn & Ha & Henc). unfold SerialLen'.
        rewrite Ha, Hn, Henc. reflexivity.
    Qed.

    (* A parser combinator that makes it possible to transform the result of a parser in another one. *)
    Definition ParseMap {R U : Type} (underlying : Parser R) (f : R -> U) : Parser U :=
      fun inp =>
        match underlying inp with
        | ParseSuccess leftResult remaining => ParseSuccess (f leftResult) remaining
        | ParseFailure level data => ParseFailure level data
        end.

    Definition SerialMap {R U : Type} {wf : U -> Prop} (underlying : Serializer U wf) (f : R -> U) :
      Serializer R (fun r => wf (f r)) := 
      fun r => underlying (f r).

    (* Returns a parser that succeeds if the underlying parser fails and vice-versa.
     The result does not consume any input. *)
    Definition Not {R : Type} (underlying : Parser R) : Parser unit :=
      fun inp =>
        match underlying inp with
        | ParseFailure level data as result =>
            if IsFatalFailure result then
              PropagateFailure result I
            else
              ParseSuccess () inp
        | ParseSuccess _ _ => ParseFailure Recoverable (mkFailureData "not failed" inp None)
        end.

    (* Make the two parsers parse the same string and, if both succeed, return a pair of the
     two results, with the remaining of the right parser.

     If one parser fails, return that parse failure. If both fail, return the left failure
     *)
    Definition ParseAnd {L R : Type} (left : Parser L) (right : Parser R) : Parser (L * R) :=
      fun inp =>
        match left inp, right inp with
        | ParseSuccess l _, ParseSuccess r rr => ParseSuccess (l, r) rr
        | ParseFailure level data, _
        | _, ParseFailure level data => ParseFailure level data
        end.

    Definition Or {R : Type} (left : Parser R) (right : Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | ParseSuccess r rem as p => p
        | ParseFailure _ data as p =>
            if negb $ NeedsAlternative p inp then
              p
            else 
              let p2 := right inp in
              if negb $ NeedsAlternative p2 inp then
                p2
              else
                MapRecoverableError p2 (fun dataRight => ConcatFailure data dataRight)
        end.

    (* Like Or, but takes as many parsers as needed *)
    Fixpoint OrSeq {R : Type} (alternatives : list (Parser R)) : Parser R :=
      match alternatives with
      | [] => ParseFailWith "no alternatives" Recoverable
      | alt :: [] => alt
      | alt :: alts => Or alt (OrSeq alts)
      end.

    (* If the underlying parser succeeds, return it's result without committing the input.
     If the underlying parser fails,
     - with a fatal failure, return it as-is
     - with a recoverable failure, return it without committing the input *)
    Definition Lookahead {R : Type} (underlying : Parser R) : Parser R :=
      fun inp =>
        match underlying inp with
        | ParseSuccess r rem => ParseSuccess r inp
        | ParseFailure Fatal data as p => p
        | ParseFailure Recoverable data => ParseFailure Recoverable (mkFailureData (getFailureMsg data) inp None)
        end.

    (* (Opt a) evaluates `a` on the input, and then
     - If `a` succeeds, return the result unchanged
     - If `a` fails, and the failure is not fatal, propagate the same failure without consuming input.

     (Opt a) is useful when there are alternatives to parse and `a` parsed partially and we're OK with
     backtracking to try something else. *)
    Definition Opt {R : Type} (underlying : Parser R) : Parser R :=
      fun inp =>
        match underlying inp with
        | ParseSuccess r rem as p => p
        | ParseFailure Fatal data as p => p
        | ParseFailure Recoverable data => ParseFailure Recoverable (mkFailureData (getFailureMsg data) inp None)
        end.
    
    (* If the condition parser fails, returns a non-committing failure.
     Suitable to use in Or parsers. *)
    Definition If {L R : Type} (condition : Parser L) (succeed : Parser R) : Parser R :=
      ParseBind (Lookahead condition) (fun _ => succeed).
    
    (* (Maybe a) evaluates `a` on the input, and then
     - If `a` succeeds, wraps the result in Some
     - If `a` fails, and the failure is not fatal and did not consume input, succeeds with None.
       If the error is fatal or did consume input, fails with the same failure. *)
    Definition Maybe {R : Type} (underlying : Parser R) : Parser (option R) :=
      fun inp =>
        match underlying inp with
        | ParseSuccess rr rem => ParseSuccess (Some rr) rem
        | ParseFailure Fatal data as pr => PropagateFailure pr I
        | ParseFailure Recoverable data as pr => if negb $ NeedsAlternative pr inp then
                                                  PropagateFailure pr I
                                                else
                                                  ParseSuccess None inp
        end.

    (* TODO debug parser? Might just need to be in OCaml since Rocq I/O functions seem funky *)

    Definition rep'_memory {A : Type} (underlying : Parser A) (inp : Input) : (ParseResult A * bool) :=
      match underlying inp with
      | ParseSuccess ret rem as p => if Nat.ltb (Length rem) (Length inp) then
                                      (p, true)
                                    else
                                      (p, false)
      | ParseFailure lvl data as p => (p, true)
      end.

    Lemma rep'_memory_len {A : Type} (underlying : Parser A) (inp : Input) :
      forall ret rem,
      rep'_memory underlying inp = (ParseSuccess ret rem, true) -> Length rem < Length inp.
    Proof using Type.
      intros ret rem.
      unfold rep'_memory.
      destruct (underlying inp) eqn:Hp.
      - destruct (Length remaining <? Length inp) eqn:Hn.
        * destruct (Nat.ltb_spec (Length remaining) (Length inp)) in Hn.
        + intros Hinv. inversion Hinv. subst. assumption.
        + discriminate.
          * intros Hinv. inversion Hinv.
      - intros Hinv. inversion Hinv.
    Qed.

    (* The primitive repetition combinator which applies the underlying parser over the input
     until a recoverable failure happens and returns the accumulated results *)
    (* Defined below, Rep' is the repetition primitive in the parser combinators for Dafny.
     In this version, we use well-founded recursion to ensure it terminates.
     In order to the equations plugin to record the decision of the if statement, I'm using
     decide here, which enables near automatic handling of this fact.

     However, this leads to warnings:

     Warning:
     The decreasing recursive call obligation Rep'_obligation_2 could not be defined as a hint:
     Rep'_obligation_2 cannot be used as a hint. [wf-obligation-cannot-be-used,equations,default]
     Warning:
     The decreasing recursive call obligation Rep'_obligation_3 could not be defined as a hint:
     Rep'_obligation_3 cannot be used as a hint. [wf-obligation-cannot-be-used,equations,default]

     I tried to rewrite this to not use `decide`, which resulted in rep'_memory above. The idea
     there was that since I can use `inspect` and the eqn:H notation to record facts for obligation proofs,
     the helper function would let me inject the fact that Nat.ltb (Length rem) (Length inp) is true into
     the obligation context, which I could then solve easily. Unfortunately, this led to the same warnings
     being issued, so for the moment I've reverted to the self-contained version using decide.
     *)
    Equations? rep' {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A)
      (inp : Input) : ParseResult A by wf (Length inp) lt :=
      rep' underlying combine acc inp with underlying inp => {
        | ParseSuccess ret rem => if decide (Length rem < Length inp) then
                                   rep' underlying combine (combine acc ret) rem
                                 else
                                   ParseSuccess acc inp
        | ParseFailure lvl data => if NeedsAlternative (ParseFailure lvl data) inp then
                                    ParseSuccess acc inp
                                  else
                                    PropagateFailure (ParseFailure lvl data) I
        }.
    Proof.
      all: try done.
    Qed.

    (* Proof for the memory version *)
    (*   apply rep'_memory_len in H. *)
    (*   assumption. *)
    (* Qed. *)

    (* Repeats the underlying parser until the first failure that accepts alternatives, combining results
     into an accumulator and return the final accumulated result. *)
    Definition Rep {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A) :
      Parser A :=
      fun inp => rep' underlying combine acc inp.

    (* Repeats the underlying parser N times, combining results into an accumulator and returning the
       final accumulated result. *)
    Fixpoint RepN {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (n : nat) (acc : A) : Parser A :=
      fun inp => match n with
              | O => ParseSuccess acc inp
              | S m => match underlying inp with
                      | ParseSuccess b rem => RepN underlying combine m (combine acc b) rem
                      | ParseFailure lvl data => ParseFailure lvl data
                      end
              end.

    (* Repeats the underlying parser interleaved with a separator. Returns a sequence of results *)
    (* WARN: Unfortunately, without arrays or sequences with constant time accesses accumulating the list
       is an O(n^2) operation *)
    Definition RepSep {A B : Type} (underlying : Parser A) (separator : Parser B) :
      Parser (list A) :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep (ConcatKeepRight separator underlying)
                          (fun (acc : list A) (a : A) => acc ++ [a])
                          [ret]
           | None => ParseSucceedWith []
           end).

    (* Repeats the underlying parser interleaved with a separator exactly N time.
       Returns a sequence of results *)
    (* WARN: Unfortunately, without arrays or sequences with constant time accesses accumulating the list
       is an O(n^2) operation *)
    Definition RepSepN {A B : Type} (underlying : Parser A) (separator : Parser B) (n : nat) : Parser (list A) :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN (ConcatKeepRight separator underlying)
                          (fun (acc : list A) (a : A) => acc ++ [a])
                          (pred n) [ret]
           | None => ParseSucceedWith []
        end).

    (* Repeats the underlying parser, merging intermediate results. Returns the final merged result. *)
    Definition RepMerge {A : Type} (underlying : Parser A) (merger : A -> A -> A) : Parser A :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep underlying merger ret
           | None => ParseFailWith "No first element in RepMerge" Recoverable
           end).

    (* Repeats the underlying parser, merging intermediate results exactly N time.
       Returns the final merged result. *)
    Definition RepMergeN {A : Type} (underlying : Parser A) (merger : A -> A -> A) (n : nat) : Parser A :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN underlying merger (pred n) ret
           | None => ParseFailWith "No first element in RepMergeN" Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results.
     Returns the final merged result. *)
    Definition RepSepMerge {A B : Type} (underlying : Parser A) (separator : Parser B)
      (merger : A -> A -> A) : Parser A :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep (ConcatKeepRight separator underlying) merger ret
           | None => ParseFailWith "No first element in RepSepMerge" Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results,
       exactly N times. Returns the final merged result. *)
    Definition RepSepMergeN {A B : Type} (underlying : Parser A) (separator : Parser B)
      (merger : A -> A -> A) (n : nat) : Parser A :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN (ConcatKeepRight separator underlying) merger (pred n) ret
           | None => ParseFailWith "No first element in RepSepMergeN" Recoverable
           end).

    (* Repeated the underlying parser until the first failure that accepts alternatives, and returns the
       underlying sequence. *)
    Definition ZeroOrMore {R : Type} (underlying : Parser R) : Parser (list R) :=
      Rep underlying (fun (acc : list R) (r : R) => acc ++ [r]) [].

    (* Like ZeroOrMore but will return a failure if there is not at least one match. *)
    Definition OneOrMore {R : Type} (underlying : Parser R) : Parser (list R) :=
      ParseBind underlying
        (fun r =>
           Rep underlying (fun (acc : list R) (r : R) => acc ++ [r]) [r]).

    Definition SeqN {R : Type} (underlying : Parser R) (n : nat) : Parser (list R) :=
      RepN underlying (fun (acc : list R) (r : R) => acc ++ [r]) n [].

    Fixpoint SerialRepWf {A : Type} (wfa : A -> Prop) (ls : list A) : Prop :=
      match ls with
      | [] => True
      | a :: [] => wfa a
      | a :: ls => wfa a /\ SerialRepWf wfa ls
      end.

    Fixpoint sep_rep' {A : Type} {wfa : A -> Prop}
      (underlying : Serializer A wfa) (acc : Output) : Serializer (list A) (SerialRepWf wfa) :=
      fun ls =>
        match ls with
        | [] => SerialSuccess acc
        | a :: ls' => match underlying a with
                     | SerialSuccess a_enc => sep_rep' underlying (App acc a_enc) ls'
                     | SerialFailure lvl data as f => f
                     end
        end.

    Definition SerialRep {A : Type} {wfa : A -> Prop}
      (underlying : Serializer A wfa) : Serializer (list A) (SerialRepWf wfa) :=
      fun a => sep_rep' underlying Input_default a.

    Definition RecursiveProgressError {R : Type} (name : string) (inp : Input) (remaining : Input) :
      ParseResult R :=
      if Length remaining == Length inp then
        ParseFailure Recoverable (mkFailureData (name ++ " no progress in recursive parser") remaining None)
      else
        ParseFailure Fatal (mkFailureData
                              (name ++ " fixpoint called with an increasing remaining sequence")
                              remaining None).

    Definition par_recur_step {R : Type}
      (underlying : Parser R -> Parser R)
      (inp : Input)
      (rec_call : forall inp__next : Input, Length inp__next < Length inp -> ParseResult R)
      (inp__next : Input) : ParseResult R :=
      match decide (Length inp__next < Length inp) with
      | left pf => rec_call inp__next pf
      | right _ => RecursiveProgressError "Parser.Recursive" inp inp__next
      end.

    Program Fixpoint par_recur {R : Type} (underlying : Parser R -> Parser R) (inp : Input)
      {measure (Length inp)} : ParseResult R :=
      underlying (par_recur_step underlying inp (fun inp__next _ => par_recur underlying inp__next)) inp.
    Next Obligation.
      apply measure_wf.
      apply lt_wf.
    Defined.

    (* Given a function that requires a parser to return a parser, provide the result
       of this parser to that function itself.

       Careful: This function is not tail-recursive.*)
    Definition ParseRecursive {R : Type} (underlying : Parser R -> Parser R) : Parser R :=
      par_recur underlying.

    Lemma par_recur_unfold {R : Type} (underlying : Parser R -> Parser R) (inp : Input) :
      par_recur underlying inp =
      underlying (fun rem => match decide ((Length rem) < (Length inp)) with
                          | left _ => par_recur underlying rem
                          | right _ => RecursiveProgressError "Parser.Recursive" inp rem
                          end) inp.
    Proof using Type.
      unfold par_recur at 1. unfold par_recur_func.
      rewrite WfExtensionality.fix_sub_eq_ext.
      f_equal.
    Qed.
      
    Definition SerialRecursiveProgressError {R : Type} (name : string) (depth : R -> nat) (r: R) (r__next : R) :
      SerializeResult :=
      if depth r__next == depth r then
        SerialFailure Recoverable (mkFailureData (name ++ " no progress in recursive serializer")
                                     Input_default None)
      else
        SerialFailure Fatal (mkFailureData (name ++ " fixpoint called with deeper value to serialize")
                               Input_default None).

    Definition ser_recur_step {R : Type} {wfo : R -> Prop}
      (underlying : Serializer R wfo -> Serializer R wfo)
      (depth : R -> nat)
      (r : R)
      (rec_call : forall r__next : R, depth r__next < depth r -> SerializeResult)
      (r__next : R) : SerializeResult :=
      match decide (depth r__next < depth r) with
      | left pf => rec_call r__next pf
      | right _ => SerialRecursiveProgressError "Serial.Recursive" depth r r__next
      end.

    Program Fixpoint ser_recur {R : Type} {wfo : R -> Prop} 
      (underlying : Serializer R wfo -> Serializer R wfo)
      (depth : R -> nat) (r : R) {measure (depth r)} : SerializeResult :=
      underlying (ser_recur_step underlying depth r 
                    (fun r__next _ => ser_recur underlying depth r__next)) r.
    Next Obligation.
      apply measure_wf.
      apply lt_wf.
    Defined.

    Definition SerialRecursive {R : Type} {wf : R -> Prop} (underlying : Serializer R wf -> Serializer R wf) depth :
      Serializer R wf := ser_recur underlying depth.

    Lemma ser_recur_unfold {R : Type} {wfo : R -> Prop} (underlying : Serializer R wfo -> Serializer R wfo)
      (depth : R -> nat) (r : R) :
      ser_recur underlying depth r =
      underlying (fun r__next => match decide (depth r__next < depth r) with
                            | left _ => ser_recur underlying depth r__next
                            | right _ => SerialRecursiveProgressError "Serial.Recursive" depth r r__next
                            end) r.
    Proof using Type.
      unfold ser_recur at 1. unfold ser_recur_func.
      rewrite WfExtensionality.fix_sub_eq_ext.
      f_equal. 
    Qed.


    Theorem RecursiveCorrect {R : Type} {wf : R -> Prop}
      (par_underlying : Parser R -> Parser R)
      (ser_underlying : Serializer R wf -> Serializer R wf)
      (depth : R -> nat)
      (H_underlying_ok : forall (r : R) (enc rest : Input),
         wf r ->
         (forall (inp__next : Input) (r__next : R),
            Length inp__next < Length (App enc rest) ->
            depth r__next < depth r ->
            wf r__next ->
            forall rest__next,
            ser_recur ser_underlying depth r__next = SerialSuccess inp__next ->
            par_recur par_underlying (App inp__next rest__next) = ParseSuccess r__next rest__next) ->
         ser_underlying (ser_recur_step ser_underlying depth r 
                           (fun r__next _ => ser_recur ser_underlying depth r__next)) r = SerialSuccess enc ->
         par_underlying (par_recur_step par_underlying (App enc rest)
                           (fun inp__next _ => par_recur par_underlying inp__next)) (App enc rest) = ParseSuccess r rest) :
      ParseOk (ParseRecursive par_underlying) (SerialRecursive ser_underlying depth).
    Proof using Type.
      unfold ParseOk, ParseOk', ParseOk'', ParseOk''', ParseRecursive, SerialRecursive.
      intros x enc rest Hwf Hser.
      
      (* The proof proceeds by well-founded induction on depth x *)
      remember (depth x) as d eqn:Heq.
      revert x enc rest Hwf Hser Heq.
      induction d as [d IH] using lt_wf_ind.
      intros x enc rest Hwf Hser Heq.
      
      rewrite par_recur_unfold.
      rewrite ser_recur_unfold in Hser.
      
      unfold par_recur_step in H_underlying_ok.
      eapply H_underlying_ok; eauto.
      
      intros inp__next r__next Hlen Hdepth Hwf__next rest__next Hser__next.
      
      eapply IH.
      - subst d. exact Hdepth.
      - exact Hwf__next.
      - exact Hser__next.
      - reflexivity.
    Qed.

    Definition par_recur_step_st {R S : Type}
      (underlying : (S -> Parser R) -> (S -> Parser R))
      (inp : Input)
      (rec_call : forall (st : S) (inp__next : Input), Length inp__next < Length inp ->
                                                ParseResult R)
      (st : S)
      (inp__next : Input) : ParseResult R :=
      match decide (Length inp__next < Length inp) with
      | left pf => rec_call st inp__next pf
      | right _ => RecursiveProgressError "Parser.RecursiveState" inp inp__next
      end.

    Program Fixpoint par_recur_st {R S : Type}
      (underlying : (S -> Parser R) -> (S -> Parser R))
      (st : S) (inp : Input) {measure (Length inp)} : ParseResult R :=
      underlying (par_recur_step_st underlying inp
                    (fun st__n inp__next _ => par_recur_st underlying st__n inp__next)) st inp.
    Next Obligation.
      apply measure_wf.
      apply lt_wf.
    Defined.

    Definition ParseRecusriveState {R S : Type}
      (underlying : (S -> Parser R) -> (S -> Parser R)) (st : S) : Parser R :=
      par_recur_st underlying st.
      
    Lemma par_recur_st_unfold {R S : Type}
      (underlying : (S -> Parser R) -> (S -> Parser R))
      (st : S)
      (inp : Input) :
      par_recur_st underlying st inp =
      underlying (fun st__n rem => if decide ((Length rem) < (Length inp)) then
                                par_recur_st underlying st__n rem
                              else
                                RecursiveProgressError "Parser.RecursiveState" inp rem
        ) st inp.
    Proof using Type.
      unfold par_recur_st at 1. unfold par_recur_st_func.
      rewrite WfExtensionality.fix_sub_eq_ext.
      f_equal.
    Qed.
    
    Definition ser_recur_step_st {R S : Type} {wfo : R -> Prop}
      (underlying : (S -> Serializer R wfo) -> S -> Serializer R wfo)
      (depth : R -> nat)
      (r : R)
      (rec_call : forall (st : S) (r__next : R), depth r__next < depth r -> SerializeResult)
      (st : S)
      (r__next : R) : SerializeResult :=
      match decide (depth r__next < depth r) with
      | left pf => rec_call st r__next pf
      | right _ => SerialRecursiveProgressError "Serial.RecursiveState" depth r r__next
      end.

    Program Fixpoint ser_recur_st {R S : Type} {wfo : R -> Prop} 
      (underlying : (S -> Serializer R wfo) -> S -> Serializer R wfo)
      (depth : R -> nat) (st : S) (r : R) {measure (depth r)} : SerializeResult :=
      underlying (ser_recur_step_st underlying depth r 
                    (fun st__n r__next _ => ser_recur_st underlying depth st__n r__next)) st r.
    Next Obligation.
      apply measure_wf.
      apply lt_wf.
    Defined.

    Definition SerialRecursiveState {R S : Type} {wf : R -> Prop}
      (underlying : (S -> Serializer R wf) -> S -> Serializer R wf) depth st :
      Serializer R wf := ser_recur_st underlying depth st.

    Lemma ser_recur_st_unfold {R S : Type} {wfo : R -> Prop}
      (underlying : (S -> Serializer R wfo) -> S -> Serializer R wfo)
      (depth : R -> nat) (st : S) (r : R) :
      ser_recur_st underlying depth st r =
      underlying (fun st__n r__next => match decide (depth r__next < depth r) with
                                | left _ => ser_recur_st underlying depth st__n r__next
                                | right _ => SerialRecursiveProgressError
                                              "Serial.RecursiveState" depth r r__next
                            end) st r.
    Proof using Type.
      unfold ser_recur_st at 1. unfold ser_recur_st_func.
      rewrite WfExtensionality.fix_sub_eq_ext.
      f_equal. 
    Qed.
  End Parsers.
End Parsers.
