From coqutil Require Import Word.Bitwidth.
From stdpp Require Import gmap.
From stdpp Require Import mapset.

Module Descriptors.

  Inductive decorator :=
  | IMPLICIT
  | OPTIONAL
  | REPEATED.
  
  Definition reserved_id := nat.
  (* Which one of these should the later definitions use? While I think that the prop is largely
   more useful, somehow having a prop in the set of a message descriptor doesn't feel right... *)
  Definition reserved_set := (mapset (gmap reserved_id)).
  Definition reserved_set_prop := FinSet reserved_id reserved_set.

  Inductive field_desc : Type :=
  | F_DOUBLE : decorator -> field_desc
  | F_FLOAT : decorator -> field_desc
  | F_INT : Bitwidth -> decorator -> field_desc
  | F_UINT : decorator -> field_desc
  | F_SINT : decorator -> field_desc
  | F_FIXED : decorator -> field_desc
  | F_SFIXED : decorator -> field_desc
  | F_BOOL : decorator -> field_desc
  | F_STRING : decorator -> field_desc
  | F_BYTES : decorator -> field_desc
  | F_MSG : msg_desc -> decorator -> field_desc
  | F_ENUM : decorator -> field_desc
                      
  (*
    Looks like I can't define a mfield_desc as a record, like in F*, since I'm getting this error:

    Error: Mixed record-inductive definitions are not allowed.

    The rocq manual seems to support this topic, stating that

    "Records cannot be defined as part of mutually inductive (or co-inductive) definitions,
    whether with records only or mixed with standard definitions." 

    Although, without providing an example, it does claim that mutually inductive record
    definitions are allow if "as long as all of the types in the block are records."
   *)
    with msg_desc : Type := D_MSG : reserved_set -> list field_desc -> msg_desc.

End Descriptors.
