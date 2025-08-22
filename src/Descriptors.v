From Stdlib Require Import Strings.String.
From coqutil Require Import Word.Interface.
From Flocq Require Import IEEE754.Binary.
From Perennial Require Import Helpers.Word.Integers.
From stdpp Require Import gmap.
From stdpp Require Import mapset.

Module Descriptors.

  Inductive deco_desc :=
  | D_IMPLICIT
  | D_OPTIONAL
  | D_REPEATED.
  
  Definition reserved_id := nat.
  (* Which one of these should the later definitions use? While I think that the prop is largely
   more useful, somehow having a prop in the set of a message descriptor doesn't feel right... *)
  Definition reserved_set := (mapset (gmap reserved_id)).
  Definition reserved_set_prop := FinSet reserved_id reserved_set.

  Definition width_prop (n : nat) : Prop := n = 32%nat \/ n = 64%nat.
  Definition width := {n : nat | width_prop n }.

  Lemma width_32_prop : width_prop 32.
  Proof. unfold width_prop. left. reflexivity. Qed.

  Lemma width_64_prop : width_prop 64.
  Proof. unfold width_prop. right. reflexivity. Qed.

  Definition width32 : width := exist width_prop 32 width_32_prop.
  Definition width64 : width := exist width_prop 64 width_64_prop.

  Inductive val_desc : Type :=
  | D_DOUBLE :            deco_desc -> val_desc
  | D_FLOAT  :            deco_desc -> val_desc
  | D_INT    :    width -> deco_desc -> val_desc
  | D_UINT   :    width -> deco_desc -> val_desc
  | D_SINT   :    width -> deco_desc -> val_desc
  | D_FIXED  :    width -> deco_desc -> val_desc
  | D_SFIXED :    width -> deco_desc -> val_desc
  | D_BOOL   :            deco_desc -> val_desc
  | D_STRING :            deco_desc -> val_desc
  | D_BYTES  :            deco_desc -> val_desc
  | D_MSG    : msg_desc -> deco_desc -> val_desc
  | D_ENUM   :            deco_desc -> val_desc
                      
  (*
    Looks like I can't define a mfield_desc as a record, like in F*, since I'm getting this error:

    Error: Mixed record-inductive definitions are not allowed.

    The rocq manual seems to support this topic, stating that

    "Records cannot be defined as part of mutually inductive (or co-inductive) definitions,
    whether with records only or mixed with standard definitions." 

    Although, without providing an example, it does claim that mutually inductive record
    definitions are allow if "as long as all of the types in the block are records."
   *)
    with field_desc := D_FIELD : string -> nat -> val_desc -> field_desc
    with msg_desc := D_MESSAGE : reserved_set -> list field_desc -> msg_desc.

  Definition field_desc_get_name (f:field_desc) : string :=
    match f with
    | D_FIELD name _ _ => name
    end.
  
  Definition field_desc_get_id (f:field_desc) : nat :=
    match f with
    | D_FIELD _ id _ => id
    end.

  Definition field_desc_get_val (f:field_desc) : val_desc :=
    match f with
    | D_FIELD _ _ val => val
    end.

  Definition msg_desc_get_reserved (m:msg_desc) : reserved_set :=
    match m with
    | D_MESSAGE rset _ => rset
    end.

  Definition msg_desc_get_fields (m:msg_desc) : list field_desc :=
    match m with
    | D_MESSAGE _ fields => fields
    end.

  Inductive deco_val {v : Type} : Type :=
    | V_IMPLICIT : v -> deco_val
    | V_OPTIONAL : option v -> deco_val
    | V_REPEATED : list v -> deco_val.

  Definition f32 := binary_float 24 128.
  Definition f32_zero := B754_zero 24 128 false.
  Definition f64 := binary_float 53 1024.
  Definition f64_zero := B754_zero 53 1024 false.
  
  Inductive val_val :=
  | V_DOUBLE : @deco_val f64 -> val_val
  | V_FLOAT  : @deco_val f32 -> val_val
  | V_INT    : @deco_val Z -> val_val
  | V_BOOL   : @deco_val bool -> val_val
  | V_STRING : @deco_val string -> val_val
  | V_BYTES  : @deco_val (list u8) -> val_val
  | V_MSG    : @deco_val msg_val -> val_val
  | V_ENUM   : @deco_val unit -> val_val

  with field_val := V_FIELD : string -> val_val -> field_val
  with msg_val := V_MESSAGE : list field_val -> msg_val.

  Definition empty_message : msg_val := V_MESSAGE nil.
  
  (* MESSAGE INITIALIZATION *)

  Definition init_deco {A : Type} (deco : deco_desc) (def : A) :=
    match deco with
    | D_IMPLICIT => V_IMPLICIT def
    | D_OPTIONAL => V_OPTIONAL None
    | D_REPEATED => V_REPEATED nil
    end.

  (* I originally had each function accessible and mutually recursive via the 'with' keyword,
     but coq kept complaining about ill-formed recursive definitions at the init_field call
     in init_fields. That would be sound in the sense that any potential calls back to init_msg
     are operating over a different msg_desc, Rocq didn't seem to think so. Per this stackexchange
     post, this issue can be fixed by moving the fixpoints inside one another, although I'm not sure
     why this helps.

     https://cs.stackexchange.com/a/120
   *)
  Fixpoint init_msg (m:msg_desc) : msg_val := 
  let init_field := (fix init_field (f:field_desc) : field_val :=
    V_FIELD (field_desc_get_name f)
      (match (field_desc_get_val f) with
       | D_DOUBLE dd => V_DOUBLE (init_deco dd f64_zero)
       | D_FLOAT dd => V_FLOAT (init_deco dd f32_zero)
       | D_INT _ dd
       | D_UINT _ dd
       | D_SINT _ dd
       | D_FIXED _ dd
       | D_SFIXED _ dd => V_INT (init_deco dd 0%Z)
       | D_BOOL dd => V_BOOL (init_deco dd false)
       | D_STRING dd => V_STRING (init_deco dd EmptyString)
       | D_BYTES dd => V_BYTES (init_deco dd nil)
       | D_MSG m dd => V_MSG (init_deco dd (init_msg m))
       | D_ENUM dd => V_ENUM (init_deco dd ())
       end)) in
  let init_fields := (fix init_fields (fs:list field_desc) : list field_val :=
    match fs with
    | nil => nil
    | hd :: tl => init_field hd :: init_fields tl
    end) in
  V_MESSAGE (init_fields $ msg_desc_get_fields m).

(* TODO / FIXME:

   What has been lost porting from F*?

   There is no longer type-level enforcements that the list of field descriptors
   have unique field id numbers and names. In F* that was defined via a refinement on
   the list of field descriptors. This file uses Rocq's refinement types, but having to
   manually prove that each element is in the refinement is frankly annoying, so while
   it works for something as simple as the bit width, I going to try to avoid it in
   the rest of the port. This property on the descriptors will need to be restored via
   a predicate over the descriptor and proven or assumed in all the proofs.
 *)
End Descriptors.
