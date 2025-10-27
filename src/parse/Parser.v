From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.

From Equations Require Import Equations.

Module Parsers (InputModule : AbstractInput).
  Import InputModule.

  Inductive FailureLevel :=
  | Fatal
  | Recoverable.

  (* Record information about when a parse fails *)
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
  Fixpoint Concat (self other : FailureData) : FailureData :=
    match self with
    | mkFailureData msg remaining next =>
        match next with
        | None => mkFailureData msg remaining (Some other)
        | Some next_val => mkFailureData msg remaining (Some (Concat next_val other))
        end
    end.
  
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

  (* Similarly to PropagateFailure, this function only works on a ParseSuccess and lets us unwrap it.
     Honestly, both of these could be done inline whenever needed, but I like learning more about how
     to handle these in Rocq. I don't know what extraction would do to these. *)
  Definition IsSuccessProp {R : Type} (pr : ParseResult R) : Prop :=
    match pr with
    | ParseSuccess _ _ => True
    | ParseFailure _ _ => False
    end.

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

  Definition NeedsAlternative {R : Type} `{EqDecision Input} (pr : ParseResult R) (input : Input) : bool :=
    match pr with
    | ParseFailure Recoverable (mkFailureData _ rem _) => if rem == input then true else false
    | _ => false
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

  (**
     Misc Utilities and Definitions
   *)
  Definition IsRemaining (input remaining : Input) : Prop :=
    Length remaining <= Length input /\ Drop input (Length input - Length remaining) = remaining.

  Lemma IsRemainingTrans (input remaining1 remaining2 : Input) :
    IsRemaining input remaining1 -> IsRemaining remaining1 remaining2 -> IsRemaining input remaining2.
  Proof.
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

  (**
     COMBINATORS
  *)
  (* This parser does not consume any input and returns the given value *)
  Definition SucceedWith {R : Type} (result : R) : Parser R :=
    (fun inp => ParseSuccess result inp).

  (* A parser that always succeeds, consumes nothing and returns () *)
  Definition Epsilon : (Parser unit) := SucceedWith ().

  (* A parser that does not consume any input and returns the given failure *)
  Definition FailWith {R : Type} (message : string) (level : FailureLevel) : Parser R :=
    (fun inp => ParseFailure level $ mkFailureData message inp None).

  (* A parser that always returns the given result *)
  Definition ResultWith {R : Type} (result : ParseResult R) : Parser R :=
    (fun inp => result).

  (* A parser that fails if the string has not been entirely consumed *)
  Definition EndOfString : Parser unit :=
    (fun inp => if Length inp == 0 then
               ParseSuccess () inp
             else
               ParseFailure Recoverable
                 (mkFailureData "expected end of string" inp None)).

  (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result and the remaining sequence to the right parser generator. *)
  Definition Bind {L R : Type} (left : Parser L) (right : L -> Parser R) : Parser R :=
    fun inp =>
      match left inp with
      | ParseSuccess leftResult remaining => right leftResult remaining
      | ParseFailure level data => ParseFailure level data
      end.

  (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result to the right parser generator and returns its result applied to the remaining input *)
  Definition BindSucceeds {L R : Type} (left : Parser L) (right : L -> Input -> Parser R) : Parser R :=
    fun inp =>
      match left inp with
      | ParseSuccess leftResult remaining => right leftResult remaining remaining
      | ParseFailure level data => ParseFailure level data
      end.

  (* Given a left parser and a parser generator based on the output of the left parser,
     returns the result of the right parser applied on the original input. *)
  Definition BindResult {L R : Type} (left : Parser L) (right : ParseResult L -> Input -> Parser R) : Parser R :=
    fun inp =>
      right (left inp) inp inp.

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
  Definition And {L R : Type} (left : Parser L) (right : Parser R) : Parser (L * R) :=
    fun inp =>
      match left inp, right inp with
      | ParseSuccess l _, ParseSuccess r rr => ParseSuccess (l, r) rr
      | ParseFailure level data, _
      | _, ParseFailure level data => ParseFailure level data
      end.

  Definition Or {R : Type} `{EqDecision Input} (left : Parser R) (right : Parser R) : Parser R :=
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
              MapRecoverableError p2 (fun dataRight => Concat data dataRight)
      end.

  (* Like Or, but takes as many parsers as needed *)
  Fixpoint OrSeq {R : Type} `{EqDecision Input} (alternatives : list (Parser R)) : Parser R :=
    match alternatives with
    | [] => FailWith "no alternatives" Recoverable
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
    Bind (Lookahead condition) (fun _ => succeed).
  
  (* (Maybe a) evaluates `a` on the input, and then
     - If `a` succeeds, wraps the result in Some
     - If `a` fails, and the failure is not fatal and did not consume input, succeeds with None.
       If the error is fatal or did consume input, fails with the same failure. *)
  Definition Maybe {R : Type} `{EqDecision Input} (underlying : Parser R) : Parser (option R) :=
    fun inp =>
      match underlying inp with
      | ParseSuccess rr rem => ParseSuccess (Some rr) rem
      | ParseFailure Fatal data as pr => PropagateFailure pr I
      | ParseFailure Recoverable data as pr => if negb $ NeedsAlternative pr inp then
                                                PropagateFailure pr I
                                              else
                                                ParseSuccess None inp
      end.
  
End Parsers.

Module test.

  Module ConcreteParsers := Parsers(ByteInput).
  Import ConcreteParsers.

  Compute IsFatalFailure (ParseFailure Recoverable (mkFailureData "" [] None)).
  Compute let pr := ParseFailure Recoverable (mkFailureData "" [] None) in
            PropagateFailure pr I : ParseResult bool.
  Compute let pr := ParseSuccess 10 [] in
            Extract pr I.

End test.
