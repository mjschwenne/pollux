(** Intermediate Parser, building on the Simple Parser and pushing towards Protobuf *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Perennial Require Import Helpers.Word.Automation.
From Stdlib Require Import Structures.Equalities.

From Pollux.parse Require Import Input.
From Pollux Require Import InterParse.Parser.

Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Program.Wf.
From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Open Scope Z_scope.

Import Parser.C.
Import InterParse.Descriptor.Descriptor.

(*! Serializer *)

(*
    Both integer and boolean fields will be encoded into a 4-byte integer so that the descriptor is
    required to cast them into the correct final form.

    Each primitive field is tagged with the field number as a 1-byte integer, then the 4-byte payload.

    Nested messages still start with a 1-byte field number, and then are followed with a 4-byte length
    which represents the total encoding length of the nested message.

    Many of the low-level parsers, bytes, integers, bools, etc are taken from SimplParse.v.
 *)

Section Serializer.
  Definition SerialByte : S.Serializer byte S.Trivial_wf :=
    fun b => S.mkSuccess [b].

  Definition SerialUnsigned : S.Serializer Z (fun z => 0 <= z < 256) :=
    fun z => SerialByte $ W8 z.

  Definition SerialNat : S.Serializer nat (fun n => (0 <= n < 256)%nat) :=
    fun n => SerialByte $ W8 (Z.of_nat n).

  Definition Z__next (z : Z) : Z :=
    z ≫ 8.

  (* Create an n-byte little-endian list of z.
       If z doesn't fit into n bytes, the first n bytes are returned.
       If z fits into less than n bytes, the list is padded with zeros.
   *)
  Fixpoint Z_to_list (z : Z) (n : nat) : list byte :=
    match n with
    | O => []
    | S n' => W8 z :: Z_to_list (Z__next z) n'
    end.

  Definition SerialZ_wf (n : nat) (z : Z) : Prop :=
    (0 <= z < 2^(8 * Z.of_nat n)).

  Definition SerialZN (n : nat) : S.Serializer Z (SerialZ_wf n) :=
    fun z => S.Rep SerialByte (Z_to_list z n).

  Definition SerialZ32 := SerialZN 4%nat.

  Definition SerialBool : S.Serializer bool S.Trivial_wf :=
    fun b => if b then
            SerialZ32 1
          else
            SerialZ32 0.

  Fixpoint ValueDepth (v : Value) : nat :=
    match v with
    | VALUE vs => (map_fold ValueDepthFold 0 vs)%nat
    end
  with ValueDepthFold (k : Z) (v : Val) (acc : nat) :=
         match v with
         | V_BOOL _
         | V_INT _
         | V_MISSING => acc
         | V_MSG v' => acc `max` (ValueDepth v' + 1)
         end.

  Definition ValueDepth_eq := mk_eq ValueDepth.
  Definition ValueDepthFold_eq := mk_eq ValueDepthFold.

  Fixpoint ValueEncLen (v : Value) : nat :=
    match v with
    | VALUE vs => (map_fold ValueEncLenFold 0 vs)%nat
    end
  with ValueEncLenFold (k : Z) (v : Val) (acc : nat) :=
         match v with
         | V_BOOL _ => (acc + 5)%nat
         | V_INT _ => (acc + 5)%nat
         | V_MISSING => acc
         | V_MSG v' => (acc + 2 + ValueEncLen v')%nat
         end.

  Definition ValueEncLen_eq := mk_eq ValueEncLen.
  Definition ValueEncLenFold_eq := mk_eq ValueEncLenFold.

  Fixpoint ValueEncLen' (d : Desc) (v : Value) : nat :=
    match v, d with
    | VALUE vs, DESC ds => (map_fold (ValueEncLen'Fold ds) 0 vs)%nat
    end
  with ValueEncLen'Fold (ds : gmap Z Field) (k : Z) (v : Val) (acc : nat) : nat :=
         match ds !! k, v with
         | None, _ => acc
         | Some _, V_BOOL _ => (acc + 5)%nat
         | Some _, V_INT _ => (acc + 5)%nat
         | Some (F_MSG d), V_MSG val => (acc + 2 + ValueEncLen' d val)%nat
         | Some _, _ => acc
         end.

  Definition ValueEncLen'_eq := mk_eq ValueEncLen'.
  Definition ValueEncLen'Fold_eq := mk_eq ValueEncLen'Fold.

  Fixpoint Value_wf (d : Desc) (v : Value) : Prop :=
    match v, d with
    | VALUE vs, DESC ds => map_fold (Val_wf_fold ds) True vs
    end
  with Val_wf_fold (ds : gmap Z Field) (k : Z) (v : Val) (acc : Prop) : Prop :=
         match ds !! k, v with
         | None, _ => acc (* Skip fields that will be dropped *)
         | Some F_BOOL, V_BOOL _ => acc (* All Booleans are intrinsically well-formed *)
         | Some F_INT, V_INT z => acc /\ 0 <= z < 2^32 (* Integer fits in bounds *)
         | Some (F_MSG d), V_MSG val => acc /\ Value_wf d val (* Nested message is also well-formed *)
         | _, _ => False
         end.
        
  Definition Value_wf_eq := mk_eq Value_wf.
  Definition Val_wf_fold_eq := mk_eq Val_wf_fold.

  Lemma Val_wf_fold_unfold :
    forall d key val,
    Val_wf_fold (Fields d) key val True =
    match (Fields d) !! key, val with
    | None, _ => True (* Skip fields that will be dropped *)
    | Some F_BOOL, V_BOOL _ => True (* All Booleans are intrinsically well-formed *)
    | Some F_INT, V_INT z => True /\ 0 <= z < 2^32 (* Integer fits in bounds *)
    | Some (F_MSG d), V_MSG val => True /\ Value_wf d val (* Nested message is also well-formed *)
    | _, _ => False
    end.
  Proof using Type.
    intros [ds] k v.
    unfold Val_wf_fold, Fields.
    destruct v; destruct (ds !! k) eqn:Hin_d; try reflexivity.
  Qed.

  (* Helper definition to shim between Val_wf_fold and Serializer API *)
  Definition Val_wf (d : Desc) (v : Z * Val) : Prop :=
    let (key, val) := v in  
    Val_wf_fold (Fields d) key val True.

  Definition SerialVal (serial__msg : forall d : Desc, S.Serializer Value $ Value_wf d) (d : Desc) :
    S.Serializer (Z * Val) (Val_wf d) := 
    fun val => let (id, v) := val in
               match (Fields d) !! id with
               | Some F_BOOL => match v with
                                | V_BOOL b => S.Bind' (fun _ => id) SerialUnsigned SerialBool b
                                | V_MISSING => S.mkSuccess []
                                | _ => Failure Recoverable
                                         (mkData "Expected Boolean" Input_default None)
                                end
               | Some F_INT => match v with
                              | V_INT z => S.Bind' (fun _ => id) SerialUnsigned SerialZ32 z
                              | V_MISSING => S.mkSuccess []
                              | _ => Failure Recoverable
                                      (mkData "Expected Integer" Input_default None)
                              end
               | Some (F_MSG d') => match v with
                                   | V_MSG z => S.Bind' (fun _ => id) SerialUnsigned
                                                 (S.Len' SerialNat (serial__msg d')) z
                                   | V_MISSING => S.mkSuccess []
                                   | _ => Failure Recoverable
                                           (mkData "Expected nested message" Input_default None)
                                   end
               | None => S.mkSuccess Input_default
               end.

  Definition Filter (f : option Field) (v : option Val) : option Val := 
    match f, v with
    | None, None => None (* Make the function total...
                             My understanding is that one of the args should be Some *)
    | Some _, Some V_MISSING => None (* Filter out missing values *)
    | Some f, None => None (* Skip fully missing fields *)
    | None, Some _ => None (* Filter out extra values *)
    | Some f, Some v => Some v (* Include everything else, type checking later in the serializer process *)
    end.

  Definition ValList' (d : Desc) (v : Value) : list (Z * Val) :=
    map_to_list (merge Filter (Fields d) (Vals v)).
    
  Definition ValList_filter_p (d : Desc) (kv : Z * Val) : Prop :=
    match (Fields d) !! (fst kv), (snd kv) with
    | Some _, V_MISSING => False
    | None, _ => False
    | _, _ => True
    end.

  Global Instance ValList_filter_Decision (d : Desc) : forall kv : Z * Val, Decision (ValList_filter_p d kv).
  Proof.
    intros [k v].
    unfold ValList_filter_p, fst, snd.
    destruct (Fields d !! k); last apply False_dec.
    destruct v; (apply True_dec || apply False_dec).
  Defined.

  Definition ValList (d : Desc) (v : Value) : list (Z * Val) :=
    filter (ValList_filter_p d) (map_to_list (Vals v)).
    
  Definition field_val_match (f : Field) (v : Val) : Prop :=
    match v, f with
    | V_BOOL _, F_BOOL
    | V_INT _, F_INT
    | V_MSG _, F_MSG _ => True
    | _, _ => False
    end.

  Definition WillEncode (d : Desc) (kv : Z * Val) : Prop :=
    exists f, (Fields d) !! (fst kv) = Some f /\ Val_wf d kv. 

  Definition SerialValueList_wf (d : Desc) (vs : list (Z * Val)) : Prop :=
    Forall (WillEncode d) vs.

  Definition SerialValue' (self : forall d : Desc, S.Serializer Value $ Value_wf d) (d : Desc) :
    S.Serializer Value $ Value_wf d :=
    S.Map (S.Rep (SerialVal self d : S.Serializer _ (WillEncode d))) (ValList d).

  Definition SerialValue (d : Desc) : S.Serializer Value $ Value_wf d :=
    S.RecursiveState SerialValue' ValueDepth d.

End Serializer.
