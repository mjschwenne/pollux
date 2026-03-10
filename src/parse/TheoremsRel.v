(** * TheoremsRel: Relational P.Parser Correctness Theorems

    This module extends the correctness definitions from Theorems.v to handle
    cases where parser output is related to serializer input via a binary
    relation rather than strict equality. This is useful for:

    1. Low-level parsers where parsed values may be normalized (e.g., booleans
       parsed from integers, where any non-zero value becomes true)

    2. Descriptor-parameterized parsers where the schema may change between
       serialization and parsing (e.g., protobuf schema evolution where a
       field type changes but values remain compatible)
*)

From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Result.
From Pollux.parse Require Import Parser.
From Pollux.parse Require Import Serializer.
From Pollux.parse Require Import Theorems.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module TheoremsRel (InputModule : AbstractInput).
  Module R := Result(InputModule).
  Module P := Parsers(InputModule).
  Module S := Serializers(InputModule).
  Module T := Theorems(InputModule).
  Import InputModule.
  Import T.

  Section TheoremsRel.
    Context `{EqDecision Input}.

    (** ** Type Aliases *)

    Definition Output := Input.

    (** ** ParseOkSimpleRel: Relational Correctness for Simple Parsers

        This definition generalizes ParseOk for parsers that do not depend on
        descriptors or other external context. The relation R relates the
        serialized value to the parsed value.

        Example: A boolean serializer that writes 0 or 1, but a parser that
        treats any non-zero integer as true, would use a relation like:
        [R b b' := (b = true <-> b' = true)]
    *)

    (** Most specific: includes all parameters *)
    Definition ParseOkSimpleRel''' {X : Type} {wf : X -> Prop}
      (R : X -> X -> Prop)
      (par : P.Parser X) (ser : S.Serializer X wf)
      (x : X) (enc rest : Input) :=
      wf x ->
      ser x = S.mkSuccess enc ->
      exists x', par (App enc rest) = P.R.Success x' rest /\ R x x'.

    (** Abstract over rest *)
    Definition ParseOkSimpleRel'' {X : Type} {wf : X -> Prop}
      (R : X -> X -> Prop)
      (par : P.Parser X) (ser : S.Serializer X wf)
      (x : X) (enc : Input) :=
      forall (rest : Input), ParseOkSimpleRel''' R par ser x enc rest.

    (** Abstract over enc *)
    Definition ParseOkSimpleRel' {X : Type} {wf : X -> Prop}
      (R : X -> X -> Prop)
      (par : P.Parser X) (ser : S.Serializer X wf)
      (x : X) :=
      forall (enc : Input), ParseOkSimpleRel'' R par ser x enc.

    (** Final definition: abstract over x *)
    Definition ParseOkSimpleRel {X : Type} {wf : X -> Prop}
      (R : X -> X -> Prop)
      (par : P.Parser X) (ser : S.Serializer X wf) :=
      forall (x : X), ParseOkSimpleRel' R par ser x.

    (** ** ParseOkCompat: Relational Correctness with Descriptor Compatibility

        This definition handles parsers and serializers that are parameterized
        by descriptors (schemas). It allows the descriptor to change between
        serialization and parsing, with a compatibility relation R that relates
        values across descriptor changes.

        Example: In protobuf, a message serialized with schema d1 should be
        parseable with schema d2, where the resulting values are related by a
        compatibility relation that accounts for schema evolution (e.g., field
        additions, type changes that preserve meaning).

        The relation R has type [D -> D -> X -> X -> Prop] where:
        - First D is the serialization descriptor
        - Second D is the parsing descriptor
        - First X is the serialized value
        - Second X is the parsed value
    *)

    (** Most specific: includes all parameters *)
    Definition ParseOkCompat'''' {D X : Type} {wf : D -> X -> Prop}
      (R : D -> D -> X -> X -> Prop)
      (par : D -> P.Parser X)
      (ser : forall d, S.Serializer X (wf d))
      (d1 d2 : D) (x : X) (enc rest : Input) :=
      wf d1 x ->
      ser d1 x = S.mkSuccess enc ->
      exists x', par d2 (App enc rest) = P.R.Success x' rest /\ R d1 d2 x x'.

    (** Abstract over rest *)
    Definition ParseOkCompat''' {D X : Type} {wf : D -> X -> Prop}
      (R : D -> D -> X -> X -> Prop)
      (par : D -> P.Parser X)
      (ser : forall d, S.Serializer X (wf d))
      (d1 d2 : D) (x : X) (enc : Input) :=
      forall (rest : Input), ParseOkCompat'''' R par ser d1 d2 x enc rest.

    (** Abstract over enc *)
    Definition ParseOkCompat'' {D X : Type} {wf : D -> X -> Prop}
      (R : D -> D -> X -> X -> Prop)
      (par : D -> P.Parser X)
      (ser : forall d, S.Serializer X (wf d))
      (d1 d2 : D) (x : X) :=
      forall (enc : Input), ParseOkCompat''' R par ser d1 d2 x enc.

    (** Abstract over x *)
    Definition ParseOkCompat' {D X : Type} {wf : D -> X -> Prop}
      (R : D -> D -> X -> X -> Prop)
      (par : D -> P.Parser X)
      (ser : forall d, S.Serializer X (wf d))
      (d1 d2 : D) :=
      forall (x : X), ParseOkCompat'' R par ser d1 d2 x.

    (** Final definition: abstract over both descriptors *)
    Definition ParseOkCompat {D X : Type} {wf : D -> X -> Prop}
      (R : D -> D -> X -> X -> Prop)
      (par : D -> P.Parser X)
      (ser : forall d, S.Serializer X (wf d)) :=
      forall (d1 d2 : D), ParseOkCompat' R par ser d1 d2.

    (** ** RecursiveStateCompatCorrect: Correctness for Recursive State Parsers with Relations

        This theorem generalizes RecursiveStateCorrect from Theorems.v to handle
        compatibility relations. It allows serialization with state st1 and parsing
        with state st2, where the results are related via R st1 st2 x x'.

        This is essential for proving correctness of recursive parsers in schema
        evolution scenarios, where nested messages may be serialized with one schema
        version and parsed with another.

        The key difference from RecursiveStateCorrect is:
        - Serialization uses state st1
        - Parsing uses state st2
        - Results are related via R rather than being equal
    *)

    Theorem RecursiveStateCompatCorrect {X S : Type} {wf : S -> X -> Prop}
      (R : S -> S -> X -> X -> Prop)
      (par_underlying : (S -> P.Parser X) -> S -> P.Parser X)
      (ser_underlying : (forall s : S, S.Serializer X (wf s)) -> forall s : S, S.Serializer X (wf s))
      (valid_state : S -> X -> Prop)
      (depth : X -> nat)
      (st1 st2 : S)
      (x : X) :
      (forall (st1 st2 : S) (x : X) (enc rest : Input),
         wf st1 x -> valid_state st1 x ->
         (* Inductive hypothesis: recursive calls satisfy the relation *)
         (forall (inp__n : Input) (st1__n st2__n : S) (x__n : X),
            Length inp__n < Length (App enc rest) ->
            depth x__n < depth x ->
            wf st1__n x__n ->
            valid_state st1__n x__n ->
            forall rest__n,
            @S.recur_st _ _ wf ser_underlying depth st1__n x__n = S.mkSuccess inp__n ->
            exists x'__n, P.recur_st par_underlying st2__n (App inp__n rest__n) = P.R.Success x'__n rest__n /\
            R st1__n st2__n x__n x'__n) ->
         (* Serialization succeeds *)
         ser_underlying (@S.recur_step_st _ _ wf ser_underlying depth x
                           (fun st__n x__n _ => @S.recur_st _ _ wf ser_underlying depth st__n x__n)) st1 x = S.mkSuccess enc ->
         (* Parsing succeeds and result is related *)
         exists x',
           par_underlying (P.recur_step_st par_underlying (App enc rest)
                             (fun st__n inp__n _ => P.recur_st par_underlying st__n inp__n)) st2 (App enc rest) =
           P.R.Success x' rest /\ R st1 st2 x x') ->
      valid_state st1 x ->
      @ParseOkCompat'' S X wf R
        (P.RecursiveState par_underlying)
        (S.RecursiveState ser_underlying depth)
        st1 st2 x.
    Proof using Type.
      unfold ParseOkCompat', ParseOkCompat'', ParseOkCompat''', ParseOkCompat'''',
               P.RecursiveState, S.RecursiveState.
      intros H_underlying_ok Hstate_valid enc rest Hwf Hser.
    
      (* The proof proceeds by well-founded induction on depth x *)
      remember (depth x) as d eqn:Heq.
      revert st1 st2 x Hstate_valid enc rest Hwf Hser Heq.
      induction d as [d IH] using lt_wf_ind.
      intros st1 st2 x Hstate enc rest Hwf Hser Heq.
      
      rewrite par_recur_st_unfold.
      rewrite ser_recur_st_unfold in Hser.
      
      unfold P.recur_step_st in H_underlying_ok.
      eapply H_underlying_ok; eauto.
      
      intros inp__n st__n1 st__n2 r__n Hlen__n Hdepth__n Hwf__n Hstate__n rest__n Hser__n.
      
      eapply IH.
      - subst d. exact Hdepth__n.
      - exact Hstate__n.
      - exact Hwf__n.
      - exact Hser__n.
      - reflexivity.
    Qed.

  End TheoremsRel.
End TheoremsRel.
