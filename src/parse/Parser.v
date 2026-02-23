From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Result.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Parsers (InputModule : AbstractInput).
  Module R := Result(InputModule).
  Import R.
  Import InputModule.

  Arguments Result X : clear implicits.
  Definition Remaining {X : Type} (pr : Result X) : Input := getEnc pr.

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
    Definition FailWith {X : Type} (message : string) (level : Level) : Parser X :=
      fun inp => Failure level $ mkData message inp None.

    (* A parser that always returns the given result *)
    Definition ResultWith {X : Type} (result : Result X) : Parser X :=
      fun inp => result.

    (* A parser that fails if the string has not been entirely consumed *)
    Definition EndOfInput : Parser unit :=
      fun inp => if Length inp == 0 then
                Success () inp
              else
                Failure Recoverable
                  (mkData "expected end of input" inp None).

    (* A parser that fails if the left parser fails. If the left parser succeeds, provides its
     result and the remaining sequence to the right parser generator. *)
    Definition Bind {L R : Type} (left : Parser L) (right : L -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | Success l_result l_rem => match right l_result l_rem with
                                   | Success r_result r_rem as s => s
                                   | Failure lvl data => Failure lvl $
                                                          mkData
                                                          "Bind right failed"
                                                          l_rem
                                                          (Some data)
                                   end
        | Failure lvl data => Failure lvl $
                               mkData
                               "Bind left failed"
                               inp
                               (Some data)
        end.

    (* A parser that fails if the left parser fails. If the left parser
     succeeds, provides its result to the right parser generator and returns its
     result applied to the remaining input *)
    Definition BindSucceeds {L R : Type} (left : Parser L) (right : L -> Input -> Parser R) : Parser R :=
      fun inp =>
        match left inp with
        | Success l_result l_rem => match right l_result l_rem l_rem with
                                   | Success r_result r_rem as s => s
                                   | Failure lvl data => Failure lvl $
                                                          mkData
                                                          "BindSucceeds right failed"
                                                          l_rem
                                                          (Some data)
                                   end
        | Failure lvl data => Failure lvl $
                               mkData
                               "BindSucceeds left failed"
                               inp
                               (Some data)
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
        | Success l_result l_rem => match right l_rem with
                                   | Success r_result r_rem => Success (l_result, r_result) r_rem
                                   | Failure lvl data => Failure lvl $
                                                          mkData
                                                          "Concat right failed"
                                                          l_rem
                                                          (Some data)
                                   end
        | Failure lvl data => Failure lvl $
                               mkData
                               "Concat left failed"
                               inp
                               (Some data)
        end.

    (* Apply two consecutive parsers consecutively. If both succeed, apply the mapper to the results
     and return it *)
    Definition ConcatMap {L R T : Type} (left : Parser L) (right : Parser R) (mapper : L -> R -> T) : Parser T :=
      fun inp =>
        match left inp with
        | Success l_result l_rem => match right l_rem with
                                   | Success r_result r_rem => Success (mapper l_result r_result) r_rem
                                   | Failure lvl data => Failure lvl $
                                                          mkData
                                                          "ConcatMap right failed"
                                                          l_rem
                                                          (Some data)
                                   end
        | Failure lvl data => Failure lvl $
                               mkData
                               "ConcatMap left failed"
                               inp
                               (Some data)
        end.

    (* Return only the result of the right parser if the two parsers match *)
    Definition ConcatKeepRight {L R : Type} (left : Parser L) (right : Parser R) : Parser R :=
      ConcatMap left right (fun l r => r).
    
    (* Return only the result of the left parser if the two parsers match *)
    Definition ConcatKeepLeft {L R : Type} (left : Parser L) (right : Parser R) : Parser L :=
      ConcatMap left right (fun l r => l).
    
    (* Limit the underlying parser to only access the first N tokens in the input. *)
    Definition Limit {X : Type} (underlying : Parser X) (n : nat) : Parser X :=
      fun inp => let inp' := Slice inp 0 n in
              match underlying inp' with
              | Success r rem => Success r (App rem (Drop inp n))
              | Failure lvl data => Failure lvl $
                                     mkData
                                     "Limit underlying failed"
                                     inp'
                                     (Some data)
              end.

    Definition Len {X : Type} (len : Parser nat) (underlying : Parser X) : Parser X :=
      Bind len (fun l => Limit underlying l).

    (* A parser combinator that makes it possible to transform the result of a parser in another one. *)
    Definition Map {A B : Type} (underlying : Parser A) (f : A -> B) : Parser B :=
      fun inp =>
        match underlying inp with
        | Success result remaining => Success (f result) remaining
        | Failure lvl data => Failure lvl $
                               mkData
                               "Map underlying failed"
                               inp
                               (Some data)
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
        | Success _ _ => Failure Recoverable (mkData "Not failed" inp None)
        end.

    (* Make the two parsers parse the same string and, if both succeed, return a pair of the
     two results, with the remaining of the right parser.

     If one parser fails, return that parse failure. If both fail, return the left failure
     *)
    Definition And {A B : Type} (left : Parser A) (right : Parser B) : Parser (A * B) :=
      fun inp =>
        match left inp, right inp with
        | Success a _, Success b rr => Success (a, b) rr
        | Failure lvl data, Success _ _ => Failure lvl $ mkData
                                            "And left failed"
                                            inp
                                            (Some data)
        | Success _ _, Failure lvl data => Failure lvl $ mkData
                                            "And right failed"
                                            inp
                                            (Some data)
        | Failure l_lvl l_data, Failure r_lvl r_data => Failure (maxLevel l_lvl r_lvl) $
                                                         mkData
                                                         "And both parsers failed"
                                                         inp
                                                         (Some $ ConcatData l_data r_data)
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
                MapRecoverableError p2 (fun dataRight =>
                                          mkData
                                            "Or both options failed"
                                            inp
                                            (Some $ ConcatData data dataRight))
        end.

    (* Like Or, but takes as many parsers as needed *)
    Fixpoint OrSeq {X : Type} (alternatives : list (Parser X)) : Parser X :=
      match alternatives with
      | [] => FailWith "no alternatives" Recoverable
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
        | Failure Fatal data as p => p
        | Failure Recoverable data =>
            Failure Recoverable (mkData (getMsg data) inp None)
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
        | Failure Fatal data as p => p
        | Failure Recoverable data =>
            Failure Recoverable (mkData (getMsg data) inp None)
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
        | Failure Fatal data as pr => Propagate pr I
        | Failure Recoverable data as pr =>
            if negb $ NeedsAlternative pr inp then
              Propagate pr I
            else
              Success None inp
        end.

    Program Fixpoint rep' {X : Type} (underlying : Parser X) (inp : Input)
      {measure (Length inp)} : Result (list X) :=
      match underlying inp with
      | Success x rem => if decide (Length rem < Length inp) then
                          match rep' underlying rem with
                          | Success xs rest => Success (x :: xs) rest
                          | Failure Recoverable data => Success [x] rem
                          | Failure Fatal data => Failure Fatal data
                          end
                        else
                          Failure Fatal $ mkData
                            "Parser.Rep underlying increased input length" rem None
      | Failure Recoverable (mkData _ rem _) => Success [] rem
      | Failure Fatal data => Failure Fatal data
      end.

    Definition Rep {X : Type} (underlying : Parser X) : Parser (list X) :=
      fun inp => rep' underlying inp.

    Program Fixpoint rep_fold' {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A) (inp : Input)
      {measure (Length inp)} : Result A :=
      match underlying inp with
      | Success ret rem => if decide (Length rem < Length inp) then
                            rep_fold' underlying combine (combine acc ret) rem
                          else
                            Success acc inp
      | Failure lvl data as f => if NeedsAlternative f inp then
                                  Success acc inp
                                else
                                  @Propagate A _ (Failure lvl data) I
      end.
    
    (* Repeats the underlying parser until the first failure that accepts alternatives, combining results
     into an accumulator and return the final accumulated result. *)
    Definition RepFold {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (acc : A) :
      Parser A :=
      fun inp => rep_fold' underlying combine acc inp.

    (* Repeats the underlying parser N times, combining results into an accumulator and returning the
       final accumulated result. *)
    Fixpoint RepN {A B : Type} (underlying : Parser B) (combine : A -> B -> A) (n : nat) (acc : A) : Parser A :=
      fun inp => match n with
              | O => Success acc inp
              | S m => match underlying inp with
                      | Success b rem => RepN underlying combine m (combine acc b) rem
                      | Failure lvl data => Failure lvl $
                                             mkData
                                             "RepN underlying failed before N"
                                             inp
                                             (Some data)
                      end
              end.

    (* Repeats the underlying parser interleaved with a separator. Returns a sequence of results *)
    (* WARN: Unfortunately, without arrays or sequences with constant time accesses accumulating the list
       is an O(n^2) operation *)
    Definition RepSep {A B : Type} (underlying : Parser A) (separator : Parser B) : Parser (list A) :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepFold (ConcatKeepRight separator underlying)
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
           | Some ret => RepFold underlying merger ret
           | None => FailWith "No first element in RepMerge" Recoverable
           end).

    (* Repeats the underlying parser, merging intermediate results exactly N time.
       Returns the final merged result. *)
    Definition RepMergeN {X : Type} (underlying : Parser X) (merger : X -> X -> X) (n : nat) : Parser X :=
      Bind (Maybe underlying)
        (fun (result : option X) =>
           match result with
           | Some ret => RepN underlying merger (pred n) ret
           | None => FailWith "No first element in RepMergeN" Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results.
     Returns the final merged result. *)
    Definition RepSepMerge {A B : Type} (underlying : Parser A) (separator : Parser B) (merger : A -> A -> A) :
      Parser A :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepFold (ConcatKeepRight separator underlying) merger ret
           | None => FailWith "No first element in RepSepMerge" Recoverable
           end).

    (* Repeats the underlying parser separated by the given separator parser, merging intermediate results,
       exactly N times. Returns the final merged result. *)
    Definition RepSepMergeN {A B : Type} (underlying : Parser A) (separator : Parser B)
      (merger : A -> A -> A) (n : nat) : Parser A :=
      Bind (Maybe underlying)
        (fun (result : option A) =>
           match result with
           | Some ret => RepN (ConcatKeepRight separator underlying) merger (pred n) ret
           | None => FailWith "No first element in RepSepMergeN" Recoverable
           end).

    (* Repeated the underlying parser until the first failure that accepts alternatives, and returns the
       underlying sequence. *)
    Definition ZeroOrMore {X : Type} (underlying : Parser X) : Parser (list X) :=
      RepFold underlying (fun acc x => acc ++ [x]) [].

    (* Like ZeroOrMore but will return a failure if there is not at least one match. *)
    Definition OneOrMore {X : Type} (underlying : Parser X) : Parser (list X) :=
      Bind underlying
        (fun x => Map (Rep underlying) (fun xs => x :: xs)).

    Definition SeqN {X : Type} (underlying : Parser X) (n : nat) : Parser (list X) :=
      RepN underlying (fun (acc : list X) (x : X) => acc ++ [x]) n [].

    Definition RecursiveProgressError {R : Type} (name : string) (inp : Input) (remaining : Input) :
      Result R :=
      if Length remaining == Length inp then
        Failure Recoverable (mkData (name ++ " no progress in recursive parser") remaining None)
      else
        Failure Fatal (mkData
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
