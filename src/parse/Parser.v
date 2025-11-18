From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.

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
    Definition Parser {R : Type} := Input -> ParseResult R.
    Arguments Parser R : clear implicits.

    (* A parser selector is a function that, given a name that exists,
     returns a parser associated to this name *)
    Definition ParserSelector {R : Type} := string -> ParseResult R.
    Arguments ParserSelector R : clear implicits.

    (** Serializer Definition *)

    Definition Serializer {R : Type} {wf : R -> Output -> Prop} := R -> SerializeResult. 
    Arguments Serializer R : clear implicits.

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
    Definition ParseOk''' {R : Type} {wf : R -> Output -> Prop}
      (par : Parser R) (ser : Serializer R wf) (x : R) (enc rest : Input) :=
      wf x enc -> ser x = SerialSuccess enc -> par (App enc rest) = ParseSuccess x rest.

    Definition ParseOk'' {R : Type} {wf : R -> Output -> Prop}
      (par : Parser R) (ser : Serializer R wf) (x : R) (enc : Input) :=
      forall (rest : Input), ParseOk''' par ser x enc rest.

    Definition ParseOk' {R : Type} {wf : R -> Output -> Prop} (par : Parser R) (ser : Serializer R wf) (x : R) :=
      forall (enc : Input), ParseOk'' par ser x enc.

    Definition ParseOk {R : Type} {wf : R -> Output -> Prop} (par : Parser R) (ser : Serializer R wf) :=
      forall (x : R), ParseOk' par ser x.

    (**
     COMBINATORS
     *)

    (* This parser does not consume any input and returns the given value *)
    Definition ParseSucceedWith {R : Type} (result : R) : Parser R :=
      (fun inp => ParseSuccess result inp).

    Definition serial_trivial_wf {R : Type} : R -> Output -> Prop := fun _ _ => True.

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

    (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result and the remaining sequence to the right parser generator. *)
    Definition ParseBind {L R : Type} (left : Parser L) (right : L -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | ParseSuccess leftResult remaining => right leftResult remaining
        | ParseFailure level data => ParseFailure level data
        end.

    Definition Bind_wf {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
      (tag : R -> L) (left : R -> Serializer L wfl) (right : Serializer R wfr) : R -> Output -> Prop :=
      fun r enc => forall l_enc r_enc,
        left r (tag r) = SerialSuccess l_enc -> right r = SerialSuccess r_enc ->
        wfl (tag r) l_enc /\ wfr r r_enc /\ enc = (App l_enc r_enc).

    Definition SerialBind {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
      (tag : R -> L) (left : R -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (Bind_wf tag left right) := 
      fun r =>
        match left r (tag r) with
        | SerialSuccess l_enc => match right r with
                                | SerialSuccess r_enc => SerialSuccess (App l_enc r_enc)
                                | SerialFailure lvl data as f => f
                                end
        | SerialFailure lvl data as f => f
        end.

    Lemma BindCorrect {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
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
      pose proof (wf_ok l_enc r_enc Hleft Hright) as (wfl_ok & wfr_ok & _).
      pose proof Hleft_ok (tag x) l_enc (App r_enc rest) wfl_ok Hleft as Hl_ret.
      rewrite Hl_ret.
      pose proof Hright_ok x r_enc rest wfr_ok Hright as Hr_ret.
      assumption.
    Qed.

    (* Lemma BindCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop} *)
    (*   (lp : Parser L) (ls : R -> Serializer L wfl) *)
    (*   (rp : L -> Parser R) (rs : Serializer R wfr) (tag : R -> L) : *)
    (*   forall (r : R), ParseOk lp (ls r) -> ParseOk (rp (tag r)) rs -> *)
    (*              ParseOk' (ParseBind lp rp) (SerialBind tag ls rs) r. *)
    (* Proof using Type. *)
    (*   intros x Hleft_ok Hright_ok enc rest [wfl_ok wfr_ok]. *)
    (*   unfold SerialBind. *)
    (*   destruct (ls x (tag x)) as [l_enc|] eqn:Hleft; last discriminate. *)
    (*   destruct (rs x) as [r_enc|] eqn:Hright; last discriminate. *)
    (*   intro Hser_ok. inversion Hser_ok as [Henc]. *)
    (*   rewrite App_assoc. *)
    (*   unfold ParseBind. *)
    (*   pose proof Hleft_ok (tag x) l_enc (App r_enc rest) as Hlp. *)
    (*   apply Hlp in wfl_ok as Hl_tmp. apply Hl_tmp in Hleft as Hl_ret. *)
    (*   rewrite Hl_ret. *)
    (*   pose proof Hright_ok x r_enc rest as Hrp. *)
    (*   apply Hrp in wfr_ok as Hr_tmp. apply Hr_tmp in Hright as Hr_ret. *)
    (*   assumption. *)
    (* Qed. *)

    (* A parser that fails if the left parser fails. If the left parser
     succeeds, provides its result to the right parser generator and returns its
     result applied to the remaining input *)
    Definition ParseBindSucceeds {L R : Type} (left : Parser L) (right : L -> Input -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | ParseSuccess leftResult remaining => right leftResult remaining remaining
        | ParseFailure level data => ParseFailure level data
        end.

    Definition BindSucceeds_wf {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
      (tag : R -> L) (left : R -> Output -> Serializer L wfl) (right : Serializer R wfr) : R -> Output -> Prop :=
      fun r enc => forall l_enc r_enc,
        left r r_enc (tag r) = SerialSuccess l_enc -> right r = SerialSuccess r_enc ->
        wfl (tag r) l_enc /\ wfr r r_enc /\ enc = (App l_enc r_enc).

    (* This is tricky since technically ParseBindSucceeds isn't limited to only
    inspecting the encoding of the right serializer (could use things like the
    lookahead parser) so the correctness theorem will have to ensure that both
    get the same encoding. *)
    Definition SerialBindSucceeds {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}  
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

    Lemma BindSucceedsCorrect {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
      (lp : Parser L) (ls : R -> Output -> Serializer L wfl)
      (rp : L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      forall (r : R) (rest : Input),
      ParseOk' (rp (tag r) (App (Out $ rs r) rest)) rs r -> ParseOk' lp (ls r (Out $ rs r)) (tag r) ->
      ParseOk (ParseBindSucceeds lp rp) (SerialBindSucceeds tag ls rs).
    Proof using Type.
      intros x rest Hright_ok Hleft_ok [wfl_ok wfr_ok].
      unfold SerialBindSucceeds.
      destruct (rs x) as [r_enc|] eqn:Hright; last discriminate.
      destruct (ls x r_enc (tag x)) as [l_enc|] eqn:Hleft; last discriminate.
      intros Hser_ok. inversion Hser_ok as [Henc].
      simpl. rewrite App_assoc.
      unfold ParseBindSucceeds.
      pose proof Hleft_ok l_enc (App r_enc rest) as Hlp.
      pose proof wfl_ok as wfl_ok'.
      apply Hlp in wfl_ok' as _, Hleft as Hl_ret; last assumption.
      rewrite Hl_ret.
      pose proof Hright_ok r_enc rest as Hrp.
      pose proof wfr_ok as wfr_ok'.
      apply Hrp in wfr_ok as _, Hright as Hr_ret; last assumption.
      assumption.
    Qed.

    (* Given a left parser and a parser generator based on the output of the left parser,
     returns the result of the right parser applied on the original input. *)
    Definition ParseBindResult {L R : Type} (left : Parser L) (right : ParseResult L -> Input -> Parser R) :
      Parser R :=
      fun inp =>
        right (left inp) inp inp.

    Definition SerialBindResult {L R : Type} {wfl : L -> Output -> Prop} {wfr : R -> Output -> Prop}
      (tag : R -> L) (left : SerializeResult -> Output -> Serializer L wfl) (right : Serializer R wfr) :
      Serializer R (Bind_wf wfl wfr tag) :=
      fun r =>
        let r_ret := right r in
        left r_ret (Out r_ret) (tag r).

    Lemma BindResultCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : SerializeResult -> Output -> Serializer L wfl)
      (rp : ParseResult L -> Input -> Parser R) (rs : Serializer R wfr) (tag : R -> L) :
      forall (r : R) (l_enc rest : Input),
      ParseOk' (rp (lp (App l_enc (Out $ rs r))) (App l_enc (Out $ rs r))) rs r -> ParseOk' lp (ls (rs r) (Out $ rs r)) (tag r) ->
      ParseOk''' (ParseBindResult lp rp) (SerialBindResult tag ls rs) r (App l_enc (Out $ rs r)) rest.
    Proof using Type.
      intros x l_enc Hright_ok Hleft_ok enc rest [wfl_ok wfr_ok].
      unfold SerialBindResult.
      destruct (rs x) as [r_enc'|] eqn:Hright.
      - simpl. destruct (ls (SerialSuccess r_enc') r_enc' (tag x)) as [l_enc'|] eqn:Hleft;
          last discriminate.
        intro Hser_ok. inversion Hser_ok as [Henc]. subst.
        unfold ParseBindResult. 
        pose proof Hleft_ok enc rest as Hlp. simpl in Hlp.
        pose proof wfl_ok as wfl_ok'.
        apply Hlp in wfl_ok' as _, Hleft as Hl_ret; last assumption.
        pose proof Hright_ok enc rest as Hrp. simpl in Hrp.
        unfold ParseOk'', ParseOk''' in Hrp.
        unfold ParseOk', ParseOk'', ParseOk''' in Hright_ok.

    (* A parser combinator that makes it possible to transform the result of a parser in another one. *)
    Definition Map {R U : Type} (underlying : Parser R) (f : R -> U) : Parser U :=
      fun inp =>
        match underlying inp with
        | ParseSuccess leftResult remaining => ParseSuccess (f leftResult) remaining
        | ParseFailure level data => ParseFailure level data
        end.

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

    Lemma ConcatCorrect {L R : Type} {wfl : L -> Prop} {wfr : R -> Prop}
      (lp : Parser L) (ls : Serializer L wfl)
      (rp : Parser R) (rs : Serializer R wfr) :
      ParseOk lp ls -> ParseOk rp rs -> ParseOk (ParseConcat lp rp) (SerialConcat ls rs).
    Proof using Type.
      unfold ParseOk.
      intros Hleft_ok Hright_ok.
      intros [l r] enc rest [Hl_wf Hr_wf].
      unfold SerialConcat.
      destruct (ls l) as [l_enc|] eqn:Hleft; last discriminate.
      destruct (rs r) as [r_enc|] eqn:Hright; last discriminate.
      intros Hser_ok. inversion Hser_ok as [Henc].
      unfold ParseConcat. simpl. 
      rewrite App_assoc.
      pose proof Hleft_ok l l_enc (App r_enc rest) as Hlp.
      rewrite Hleft in Hlp.
      simpl in Hlp.
      apply Hlp in Hl_wf as Hl_ret; last reflexivity.
      rewrite Hl_ret.
      pose proof Hright_ok r r_enc rest as Hrp.
      rewrite Hright in Hrp.
      simpl in Hrp.
      apply Hrp in Hr_wf as Hr_ret; last reflexivity.
      rewrite Hr_ret.
      reflexivity.
    Qed.

    (* Return only the result of the right parser if the two parsers match *)
    Definition ConcatKeepRight {L R : Type} (left : Parser L) (right : Parser R) : Parser R :=
      ConcatMap left right (fun l r => r).
    
    (* Return only the result of the left parser if the two parsers match *)
    Definition ConcatKeepLeft {L R : Type} (left : Parser L) (right : Parser R) : Parser L :=
      ConcatMap left right (fun l r => l).
    
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

    (* Repeats the underlying parser, merging intermediate results. Returns the final merged result. *)
    Definition RepMerge {A : Type} (underlying : Parser A) (merger : A -> A -> A) : Parser A :=
      ParseBind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep underlying merger ret
           | None => ParseFailWith "No first element in RepMerge" Recoverable
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

    (* Repeated the underlying parser until the first failure that accepts alternatives, and returns the
       underlying sequence. *)
    Definition ZeroOrMore {R : Type} (underlying : Parser R) : Parser (list R) :=
      Rep underlying (fun (acc : list R) (r : R) => acc ++ [r]) [].

    (* Like ZeroOrMore but will return a failure if there is not at least one match. *)
    Definition OneOrMore {R : Type} (underlying : Parser R) : Parser (list R) :=
      ParseBind underlying
        (fun r =>
           Rep underlying (fun (acc : list R) (r : R) => acc ++ [r]) [r]).

    Definition RecursiveProgressError {R : Type} (name : string) (inp : Input) (remaining : Input) :
      ParseResult R :=
      if Length remaining == Length inp then
        ParseFailure Recoverable (mkFailureData (name ++ " no progress in recursive parser") remaining None)
      else
        ParseFailure Fatal (mkFailureData
                              (name ++ " fixpoint called with an increasing remaining sequence")
                              remaining None).

    Equations recursive' {R : Type} (underlying : Parser R -> Parser R) (inp : Input) :
      ParseResult R by wf (Length inp) :=
      recursive' underlying inp := (underlying callback) inp
    where callback : (Input -> ParseResult R) :=
      callback := fun rem => if decide ((Length rem) < (Length inp)) then
                            recursive' underlying rem
                          else
                            RecursiveProgressError "Parser.Recursive" inp rem.

  (* So this function /should/ be defined like this:

    Equations? recursive {R : Type} (underlying : Parser R -> Parser R) (inp : Input) :
      ParseResult R by wf (Length inp) :=
      recursive underlying inp := (underlying callback) inp
    where callback : (Input -> ParseResult R) :=
      callback rem with inspect (Nat.ltb (Length rem) (Length inp)) := {
      | true eqn:H => recursive underlying rem
      | false eqn:H => RecursiveProgressError "Parser.Recursive" inp rem
      }.
    Proof.
      destruct (Nat.ltb_spec (Length rem) (Length inp)) in H.
      - assumption.
      - discriminate.
    Qed.

    But equations chokes on the partial application of callback in the recursive' definition.
    Instead, we can define the where clause function to be a lambda (no partial application)
    and use the same decide trick to force it to pick up on the Length rem < Length inp requirement.

    https://github.com/mattam82/Coq-Equations/issues/623
   *)

    (* Given a function that requires a parser to return a parser, provide the result
       of this parser to that function itself.

       Careful: This function is not tail-recursive.*)
    Definition Recursive {R : Type} (underlying : Parser R -> Parser R) : Parser R :=
      fun inp => recursive' underlying inp.
      
  (* Skipped the tail-recursive version of Recursive and RecursiveMap since I'm not sure they're useful
     and they will be a lot of work.

     If performance on large files becomes an issue, RecursiveNoStack could be a performance improvement.

     The description for RecursiveMap is this:

     "Given a map of name := recursive definitions, provide the result of this parser to the
      recursive definitions and set 'fun' as the initial parser. Careful: This function is not
      tail-recursive and will consume stack"

     I'm not actually sure how or why this would be useful.
   *)

  End Parsers.
End Parsers.

Module test.

  Module ConcreteParsers := Parsers(ByteInput).
  Import ConcreteParsers.

  Compute IsFatalFailure (ParseFailure Recoverable (mkFailureData "" [] None)).
  Compute let pr := ParseFailure Recoverable (mkFailureData "" [] None) in
            PropagateFailure pr I : @ParseResult bool.
  Compute let pr := ParseSuccess 10 [] in
            Extract pr I.


End test.
