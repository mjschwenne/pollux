(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Input.
From Pollux Require Import Failure.
From Pollux Require Import Parser.
From Pollux Require Import Serializer.
From Pollux Require Import Theorems.

Open Scope Z_scope.

Module InterParse.
  Module F := Failures(ByteInput).
  Module P := Parsers(ByteInput).
  Module S := Serializers(ByteInput).
  Module T := Theorems(ByteInput).
  Import ByteInput.
  Import T.

  (*** Intermediate Complexity Format *)

  (*
    This format is designed to build on what I've learned from the simple recursive format
    (SimplParse.v) by adding these features:
    - Encoding uses tagged key-value pairs which can be read in any order
    - Uses a single default value for everything / supports optional fields
    - Does not accept repeated fields
    - Drops unknown fields without error

    All of these features will be required for protobuf, and will mandate using the RecursiveState 
    combinator to have access to and change the descriptor during the parsing / serializing process.
   *)

  Section Desc.

    (* A descriptor is a primitive or a map from w8 to descriptor *)
    Inductive Desc' : Set := 
    | D_BOOL
    | D_INT
    | D_NEST (fields : gmap w8 Desc').

  (* The "problem" with this definition is that it combines incomplete primitive fields with
     nested ones, i.e. we can have D_BOOL as a stand-alone descriptor but that can't be serialized
     without knowing what the field number is.
   *)

    Inductive Desc : Set := DESC (fs : gmap w8 Field)
    with
      Field :=
    | F_MSG (d : Desc)
    | F_BOOL
    | F_INT.
    
  (* Instead, use a mutually recursive type so that fields and descriptors (fields with an identifier)
     are distinct.
   *)

    Inductive Value : Set := VALUE (vs : gmap w8 Val)
    with
      Val :=
    | V_MSG (v : Value)
    | V_BOOL (b : bool)
    | V_INT (b : Z)
    | V_MISSING.

  (* Define a Value type which matches the structure of the descriptor, with an extra option for
     missing values, which will also be used as a default value when creating an empty value. *)
    
  (* Now in order to use the RecursiveState combinator we need a proposition linking
     a Value to it's Descriptor. Valid : Desc -> Value -> Prop *)

    Fixpoint Valid (d : Desc) (v : Value) : Prop :=
      match d, v with
      | DESC fs, VALUE vs => map_fold (Valid__fold vs) True fs
      end
    with Valid__fold (vs : gmap w8 Val) (k : w8) (f : Field) (acc : Prop) : Prop :=
           match f with
           | F_BOOL => acc /\ exists b, vs !! k = Some (V_BOOL b)
           | F_INT => acc /\ exists z, vs !! k = Some (V_INT z)
           | F_MSG d => acc /\ exists v, vs !! k = Some (V_MSG v) /\ Valid d v
           end.

    Definition desc1 := DESC (list_to_map [
                                  (W8 1, F_BOOL);
                                  (W8 2, F_INT)
                          ]).
    Definition val1 := VALUE (list_to_map [
                                  (W8 1, V_BOOL false);
                                  (W8 2, V_INT 0)
                         ]).
    Lemma test_valid1 : Valid desc1 val1.
    Proof.
      simpl.
      unfold map_fold.
      unfold gmap_fold. 
    Abort.

  End Desc.

  Section Parse.
  End Parse.

  Section Serial.
  End Serial.

  Section Theorems.
  End Theorems.

End InterParse.
