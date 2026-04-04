(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux.parse Require Import Input.
From Pollux Require Import InterParse.Descriptor.
From Pollux.parse Require Import Castor.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Module C := Castor (ByteInput).
Import C.
Import InterParse.Descriptor.Descriptor.

(*! Encoding format *)

(*
    Both integer and boolean fields will be encoded into a 4-byte integer so that the descriptor is
    required to cast them into the correct final form.

    Each primitive field is tagged with the field number as a 1-byte integer, then the 4-byte payload.

    Nested messages still start with a 1-byte field number, and then are followed with a 4-byte length
    which represents the total encoding length of the nested message.

    Many of the low-level parsers, bytes, integers, bools, etc are taken from SimplParse.v.
 *)

Definition to_enc (l : list Z) : list byte := map (fun n => W8 n) l.

Section Parse.
  Definition ParseByte : P.Parser byte :=
    fun inp => match inp with
            | byt :: rest => Success byt rest
            | [] => Failure Recoverable (mkData "No more data to parse" inp None)
            end.

  Definition ParseUnsigned : P.Parser Z := P.Map ParseByte word.unsigned.

  Definition ParseNat : P.Parser nat := P.Map ParseByte (fun b => Z.to_nat $ word.unsigned b).

  (* Parse n bytes into an unsigned integer *)
  Definition ParseZN (n : nat) := P.Map (P.RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                      (n + 8, new ≪ n + v))
                                         n (0, 0))
                                  (fun ret => let (_, z) := ret in z).

  Definition ParseZ32 := ParseZN 4%nat.

  Definition ParseBool : P.Parser bool := P.Map ParseZ32 (fun z => z >? 0).

  Definition ParseVal (parse__msg : Desc -> P.Parser Value) (d : Desc) : P.Parser (Z * Val) :=
    P.DepConcat ParseUnsigned
      (fun z =>
         match (Fields d) !! z with
         | Some F_BOOL => P.Map ParseBool (fun b => V_BOOL b)
         | Some F_INT => P.Map ParseZ32 (fun z' => V_INT z')
         | Some (F_MSG d') => P.Map (P.Len ParseNat $ parse__msg d') (fun v => V_MSG v)
         | None => P.SucceedWith V_MISSING
         end).

  Definition Merge (f : option Field) (v : option Val) : option Val :=
    match f, v with
    | Some f, Some v => match f, v with
                       | F_BOOL, V_BOOL b => Some $ V_BOOL b
                       | F_INT, V_INT z => Some $ V_INT z
                       | F_MSG _, V_MSG v' => Some $ V_MSG v'
                       | _, _ => None
                       end
    | Some f, None => Some V_MISSING
    | None, _ => None
    end.
  
  Definition list_to_value (d : Desc) (vs : list (Z * Val)) : Value :=
    VALUE $ merge Merge (Fields d) (list_to_map vs : gmap Z Val).

  Definition ParseValue' (self : Desc -> P.Parser Value) (d : Desc) : P.Parser Value :=
    P.Map (P.Rep (ParseVal self d)) (fun vs => list_to_value d vs).

  Definition ParseValue (d : Desc) : P.Parser Value :=
    P.RecursiveState ParseValue' d.

End Parse.
