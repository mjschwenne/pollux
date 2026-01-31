From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Failure.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Parsers (InputModule : AbstractInput).
  Module Failure := Failures(InputModule).
  Import InputModule.

  Section Results.
    Context `{EqDecision Input}.

    Inductive Result {X : Type} :=
    | Success (result : X) (remaining : Input)
    | Failure (level : Failure.Level) (data : Failure.Data).
    Arguments Result X : clear implicits.

    (** FUNCTIONS ON PARSE RESULTS *)

    (* If Remaining is the same as the input, then parser is "uncommitted",
     so combinators like Or or ZeroOrMore can try alternatives. *)
    Definition Remaining {X : Type} (pr : Result X) : Input :=
      match pr with
      | Success _ rem
      | Failure _ (Failure.mkData _ rem _) => rem
      end.
    
    Definition IsFailure {X : Type} (pr : Result X) : bool :=
      match pr with
      | Failure _ _ => true
      | _ => false
      end.

    Definition IsFatalFailure {X : Type} (pr : Result X) : bool :=
      match pr with
      | Failure Failure.Fatal _ => true
      | _ => false
      end.

    Definition IsFailureProp {X : Type} (pr : Result X) : Prop :=
      match pr with
      | Success _ _ => False
      | Failure _ _ => True
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

    Definition IsSuccessProp {X : Type} (pr : Result X) : Prop :=
      match pr with
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

    Definition ResultMap {X Y : Type} (pr : Result X) (f : X -> Y) : Result Y :=
      match pr with
      | Success result remaining => Success (f result) remaining
      | Failure lvl data => Failure lvl data
      end.

    Definition MapRecoverableError {X : Type} (pr : Result X) (f : Failure.Data -> Failure.Data) :
      Result X :=
      match pr with
      | Failure Failure.Recoverable data => Failure Failure.Recoverable (f data)
      | _ => pr
      end.

    Definition NeedsAlternative {X : Type} (pr : Result X) (input : Input) : bool :=
      match pr with
      | Failure Failure.Recoverable (Failure.mkData _ rem _) => if rem == input then true else false
      | _ => false
      end.

    End Results.
    Arguments Result X : clear implicits.

    Section Def.
      (** Parser Definition *)

      (* A parser is a total function from a position to a parse result *)
      Definition Parser (X : Type) := Input -> Result X.

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

    End Def.

    Section Combinators.
      Context `{EqDecision Input}.

      (* This parser does not consume any input and returns the given value *)
      Definition SucceedWith {X : Type} (result : X) : Parser X :=
        fun inp => Success result inp.

      (* A parser that always succeeds, consumes nothing and returns () *)
      Definition Epsilon : (Parser unit) := SucceedWith tt.

      (* A parser that does not consume any input and returns the given failure *)
      Definition FailWith {X : Type} (message : string) (level : Failure.Level) : Parser X :=
        fun inp => Failure level $ Failure.mkData message inp None.

      (* A parser that always returns the given result *)
      Definition ResultWith {X : Type} (result : Result X) : Parser X :=
        fun inp => result.

    (* A parser that fails if the string has not been entirely consumed *)
      Definition EndOfInput : Parser unit :=
        fun inp => if Length inp == 0 then
                  Success () inp
                else
                  Failure Failure.Recoverable
                    (Failure.mkData "expected end of input" inp None).

    (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result and the remaining sequence to the right parser generator. *)
    Definition Bind {L R : Type} (left : Parser L) (right : L -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | Success leftResult remaining => right leftResult remaining
        | Failure level data => Failure level data
        end.

    (* A parser that fails if the left parser fails. If the left parser
     succeeds, provides its result to the right parser generator and returns its
     result applied to the remaining input *)
    Definition BindSucceeds {L R : Type} (left : Parser L) (right : L -> Input -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | Success leftResult remaining => right leftResult remaining remaining
        | Failure level data => Failure level data
        end.

    (* Given a left parser and a parser generator based on the output of the left parser,
     returns the result of the right parser applied on the original input. *)
    Definition BindResult {L R : Type} (left : Parser L) (right : Result L -> Input -> Parser R) :
      Parser R :=
      fun inp =>
        right (left inp) inp inp.

    (* Apply two parser consecutively. If both succeed, return the pair of both results *)
    Definition Concat {L R : Type} (left : Parser L) (right : Parser R) : Parser (L * R) :=
      fun inp =>
        match left inp with
        | Success ll lrem => match right lrem with
                                 | Success rr rrem => Success (ll, rr) rrem
                                 | Failure lvl data as p => Propagate p I
                                 end
        | Failure lvl data as p => Propagate p I
        end.

    (* Apply two consecutive parsers consecutively. If both succeed, apply the mapper to the results
     and return it *)
    Definition ConcatMap {L R T : Type} (left : Parser L) (right : Parser R) (mapper : L -> R -> T) : Parser T :=
      fun inp =>
        match left inp with
        | Success ll lrem => match right lrem with
                            | Success rr rrem => Success (mapper ll rr) rrem
                            | Failure lvl data as p => Propagate p I
                            end
        | Failure lvl data as p => Propagate p I
        end.

    (* Return only the result of the right parser if the two parsers match *)
    Definition ConcatKeepRight {L R : Type} (left : Parser L) (right : Parser R) : Parser R :=
      ConcatMap left right (fun l r => r).
    
    (* Return only the result of the left parser if the two parsers match *)
    Definition ConcatKeepLeft {L R : Type} (left : Parser L) (right : Parser R) : Parser L :=
      ConcatMap left right (fun l r => l).
    
    (* Limit the underlying parser to only access the first N tokens in the input. *)
    Definition Limit {X : Type} (underlying : Parser X) (n : nat) : Parser X :=
      fun inp => match underlying (Slice inp 0 n) with
              | Success r rem => Success r (App rem (Drop inp n))
              | Failure lvl data as f => f
              end.

    Definition Len {X : Type} (len : Parser nat) (underlying : Parser X) : Parser X :=
      Bind len (fun l => Limit underlying l).

    (* A parser combinator that makes it possible to transform the result of a parser in another one. *)
    Definition Map {A B : Type} (underlying : Parser A) (f : A -> B) : Parser B :=
      fun inp =>
        match underlying inp with
        | Success result remaining => Success (f result) remaining
        | Failure level data => Failure level data
        end.

    (* Returns a parser that succeeds if the underlying parser fails and vice-versa.
     The result does not consume any input. *)
    Definition Not {X : Type} (underlying : Parser X) : Parser unit :=
      fun inp =>
        match underlying inp with
        | Failure level data as result =>
            if IsFatalFailure result then
              Propagate result I
            else
              Success () inp
        | Success _ _ => Failure Failure.Recoverable (Failure.mkData "Not failed" inp None)
        end.

    (* Make the two parsers parse the same string and, if both succeed, return a pair of the
     two results, with the remaining of the right parser.

     If one parser fails, return that parse failure. If both fail, return the left failure
     *)
    Definition And {A B : Type} (left : Parser A) (right : Parser B) : Parser (A * B) :=
      fun inp =>
        match left inp, right inp with
        | Success a _, Success b rr => Success (a, b) rr
        | Failure level data, _
        | _, Failure level data => Failure level data
        end.

    Definition Or {X : Type} (left right : Parser X) : Parser X :=
      fun inp =>
        match left inp with
        | Success r rem as p => p
        | Failure _ data as p =>
            if negb $ NeedsAlternative p inp then
              p
            else 
              let p2 := right inp in
              if negb $ NeedsAlternative p2 inp then
                p2
              else
                MapRecoverableError p2 (fun dataRight => Failure.Concat data dataRight)
        end.

    (* Like Or, but takes as many parsers as needed *)
    Fixpoint OrSeq {X : Type} (alternatives : list (Parser X)) : Parser X :=
      match alternatives with
      | [] => FailWith "no alternatives" Failure.Recoverable
      | alt :: [] => alt
      | alt :: alts => Or alt (OrSeq alts)
      end.

    (* If the underlying parser succeeds, return it's result without committing the input.
     If the underlying parser fails,
     - with a fatal failure, return it as-is
     - with a recoverable failure, return it without committing the input *)
    Definition Lookahead {X : Type} (underlying : Parser X) : Parser X :=
      fun inp =>
        match underlying inp with
        | Success r rem => Success r inp
        | Failure Failure.Fatal data as p => p
        | Failure Failure.Recoverable data =>
            Failure Failure.Recoverable (Failure.mkData (Failure.getMsg data) inp None)
        end.

    (* (Opt a) evaluates `a` on the input, and then
     - If `a` succeeds, return the result unchanged
     - If `a` fails, and the failure is not fatal, propagate the same failure without consuming input.

     (Opt a) is useful when there are alternatives to parse and `a` parsed partially and we're OK with
     backtracking to try something else. *)
    Definition Opt {X : Type} (underlying : Parser X) : Parser X :=
      fun inp =>
        match underlying inp with
        | Success r rem as p => p
        | Failure Failure.Fatal data as p => p
        | Failure Failure.Recoverable data =>
            Failure Failure.Recoverable (Failure.mkData (Failure.getMsg data) inp None)
        end.
    
    (* If the condition parser fails, returns a non-committing failure.
     Suitable to use in Or parsers. *)
    Definition If {A B : Type} (condition : Parser A) (succeed : Parser B) : Parser B :=
      Bind (Lookahead condition) (fun _ => succeed).
    
    (* (Maybe a) evaluates `a` on the input, and then
     - If `a` succeeds, wraps the result in Some
     - If `a` fails, and the failure is not fatal and did not consume input, succeeds with None.
       If the error is fatal or did consume input, fails with the same failure. *)
    Definition Maybe {X : Type} (underlying : Parser X) : Parser (option X) :=
      fun inp =>
        match underlying inp with
        | Success rr rem => Success (Some rr) rem
        | Failure Failure.Fatal data as pr => Propagate pr I
        | Failure Failure.Recoverable data as pr => if negb $ NeedsAlternative pr inp then
                                                     Propagate pr I
                                                   else
                                                     Success None inp
        end.

    Program Fixpoint rep' {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A) (inp : Input)
      {measure (Length inp)} : Result A :=
      match underlying inp with
      | Success ret rem => if decide (Length rem < Length inp) then
                            rep' underlying combine (combine acc ret) rem
                          else
                            Success acc inp
      | Failure lvl data as f => if NeedsAlternative f inp then
                                  Success acc inp
                                else
                                  @Propagate A _ (Failure lvl data) I
      end.
                             
    (* Repeats the underlying parser until the first failure that accepts alternatives, combining results
     into an accumulator and return the final accumulated result. *)
    Definition Rep {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A) :
      Parser A :=
      fun inp => rep' underlying combine acc inp.

    (* Repeats the underlying parser N times, combining results into an accumulator and returning the
       final accumulated result. *)
    Fixpoint RepN {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (n : nat) (acc : A) : Parser A :=
      fun inp => match n with
              | O => Success acc inp
              | S m => match underlying inp with
                      | Success b rem => RepN underlying combine m (combine acc b) rem
                      | Failure lvl data => Failure lvl data
                      end
              end.

    (* Repeats the underlying parser interleaved with a separator. Returns a sequence of results *)
    (* WARN: Unfortunately, without arrays or sequences with constant time accesses accumulating the list
       is an O(n^2) operation *)
    Definition RepSep {A B : Type} (underlying : Parser A) (separator : Parser B) : Parser (list A) :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep (ConcatKeepRight separator underlying)
                          (fun (acc : list A) (a : A) => acc ++ [a])
                          [ret]
           | None => SucceedWith []
           end).

    (* Repeats the underlying parser interleaved with a separator exactly N time.
       Returns a sequence of results *)
    (* WARN: Unfortunately, without arrays or sequences with constant time accesses accumulating the list
       is an O(n^2) operation *)
    Definition RepSepN {A B : Type} (underlying : Parser A) (separator : Parser B) (n : nat) : Parser (list A) :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN (ConcatKeepRight separator underlying)
                          (fun (acc : list A) (a : A) => acc ++ [a])
                          (pred n) [ret]
           | None => SucceedWith []
        end).

    (* Repeats the underlying parser, merging intermediate results. Returns the final merged result. *)
    Definition RepMerge {X : Type} (underlying : Parser X) (merger : X -> X -> X) : Parser X :=
      Bind (Maybe underlying)
        (fun (result : option X) =>
           match result with
           | Some ret => Rep underlying merger ret
           | None => FailWith "No first element in RepMerge" Failure.Recoverable
           end).

    (* Repeats the underlying parser, merging intermediate results exactly N time.
       Returns the final merged result. *)
    Definition RepMergeN {X : Type} (underlying : Parser X) (merger : X -> X -> X) (n : nat) : Parser X :=
      Bind (Maybe underlying)
        (fun (result : option X) =>
           match result with
           | Some ret => RepN underlying merger (pred n) ret
           | None => FailWith "No first element in RepMergeN" Failure.Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results.
     Returns the final merged result. *)
    Definition RepSepMerge {A B : Type} (underlying : Parser A) (separator : Parser B) (merger : A -> A -> A) :
      Parser A :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => Rep (ConcatKeepRight separator underlying) merger ret
           | None => FailWith "No first element in RepSepMerge" Failure.Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results,
       exactly N times. Returns the final merged result. *)
    Definition RepSepMergeN {A B : Type} (underlying : Parser A) (separator : Parser B)
      (merger : A -> A -> A) (n : nat) : Parser A :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN (ConcatKeepRight separator underlying) merger (pred n) ret
           | None => FailWith "No first element in RepSepMergeN" Failure.Recoverable
           end).

    (* Repeated the underlying parser until the first failure that accepts alternatives, and returns the
       underlying sequence. *)
    Definition ZeroOrMore {X : Type} (underlying : Parser X) : Parser (list X) :=
      Rep underlying (fun (acc : list X) (x : X) => acc ++ [x]) [].

    (* Like ZeroOrMore but will return a failure if there is not at least one match. *)
    Definition OneOrMore {X : Type} (underlying : Parser X) : Parser (list X) :=
      Bind underlying
        (fun x =>
           Rep underlying (fun (acc : list X) (x : X) => acc ++ [x]) [x]).

    Definition SeqN {X : Type} (underlying : Parser X) (n : nat) : Parser (list X) :=
      RepN underlying (fun (acc : list X) (x : X) => acc ++ [x]) n [].

    Definition RecursiveProgressError {R : Type} (name : string) (inp : Input) (remaining : Input) :
      Result R :=
      if Length remaining == Length inp then
        Failure Failure.Recoverable (Failure.mkData (name ++ " no progress in recursive parser") remaining None)
      else
        Failure Failure.Fatal (Failure.mkData
                              (name ++ " fixpoint called with an increasing remaining sequence")
                              remaining None).

    Definition recur_step {X : Type}
      (underlying : Parser X -> Parser X)
      (inp : Input)
      (rec_call : forall inp__n : Input, Length inp__n < Length inp -> Result X)
      (inp__next : Input) : Result X :=
      match decide (Length inp__next < Length inp) with
      | left pf => rec_call inp__next pf
      | right _ => RecursiveProgressError "Parser.Recursive" inp inp__next
      end.

    Program Fixpoint recur {X : Type} (underlying : Parser X -> Parser X) (inp : Input)
      {measure (Length inp)} : Result X :=
      underlying (recur_step underlying inp (fun inp__n _ => recur underlying inp__n)) inp.

    (* Given a function that requires a parser to return a parser, provide the result
       of this parser to that function itself.

       WARN: This function is not tail-recursive.*)
    Definition Recursive {X : Type} (underlying : Parser X -> Parser X) : Parser X :=
      recur underlying.

    Definition recur_step_st {X S : Type}
      (underlying : (S -> Parser X) -> (S -> Parser X))
      (inp : Input)
      (rec_call : forall (st : S) (inp__n : Input), Length inp__n < Length inp -> Result X)
      (st : S)
      (inp__n : Input) : Result X :=
      match decide (Length inp__n < Length inp) with
      | left pf => rec_call st inp__n pf
      | right _ => RecursiveProgressError "Parser.RecursiveState" inp inp__n
      end.

    Program Fixpoint recur_st {X S : Type}
      (underlying : (S -> Parser X) -> S -> Parser X)
      (st : S) (inp : Input) {measure (Length inp)} : Result X :=
      underlying (recur_step_st underlying inp
                    (fun st__n inp__n _ => recur_st underlying st__n inp__n)) st inp.

    Definition RecursiveState {X S : Type}
      (underlying : (S -> Parser X) -> (S -> Parser X)) (st : S) : Parser X :=
      recur_st underlying st.
      
    End Combinators.
End Parsers.
