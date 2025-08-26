From Pollux Require Import Prelude.

Module Descriptors.

  Inductive DecoDesc :=
  | D_IMPLICIT
  | D_OPTIONAL
  | D_REPEATED.
  
  Definition ReservedId := nat.
  Definition ReservedSet := (mapset (gmap ReservedId)).
  Definition ReservedSetProp := FinSet ReservedId ReservedSet.

  Definition WidthProp (z : Z) : Prop := z = 32%Z \/ z = 64%Z.
  Definition Width := {z : Z | WidthProp z }.

  Lemma width_32_prop : WidthProp 32.
  Proof. unfold WidthProp. left. reflexivity. Qed.

  Lemma width_64_prop : WidthProp 64.
  Proof. unfold WidthProp. right. reflexivity. Qed.

  Definition width32 : Width := exist WidthProp 32%Z width_32_prop.
  Definition width64 : Width := exist WidthProp 64%Z width_64_prop.

  Definition unwrap_width (w : Width) : Z := match w with
                                             | exist _ z _ => z
                                             end.

  Inductive ValDesc : Type :=
  | D_DOUBLE (deco: DecoDesc)
  | D_FLOAT  (deco: DecoDesc)
  | D_INT    (w: Width) (deco: DecoDesc)
  | D_UINT   (w: Width) (deco: DecoDesc)
  | D_SINT   (w: Width) (deco: DecoDesc)
  | D_FIXED  (w: Width) (deco: DecoDesc)
  | D_SFIXED (w: Width) (deco: DecoDesc)
  | D_BOOL   (deco: DecoDesc)
  | D_STRING (deco: DecoDesc)
  | D_BYTES  (deco: DecoDesc)
  | D_MSG    (msg: MsgDesc) (deco: DecoDesc)
  | D_ENUM   (deco: DecoDesc)
                      
  (*
    Looks like I can't define a mfield_desc as a record, like in F*, since I'm getting this error:

    Error: Mixed record-inductive definitions are not allowed.

    The rocq manual seems to support this topic, stating that

    "Records cannot be defined as part of mutually inductive (or co-inductive) definitions,
    whether with records only or mixed with standard definitions." 

    Although, without providing an example, it does claim that mutually inductive record
    definitions are allow if "as long as all of the types in the block are records."
   *)
    with FieldDesc := D_FIELD (name: string) (id: nat) (val: ValDesc)
    with MsgDesc := D_MESSAGE (reserved: ReservedSet) (fields: list FieldDesc).

  Definition field_desc_get_name (f:FieldDesc) : string :=
    match f with
    | D_FIELD name _ _ => name
    end.
  
  Definition field_desc_get_id (f:FieldDesc) : nat :=
    match f with
    | D_FIELD _ id _ => id
    end.

  Definition field_desc_get_val (f:FieldDesc) : ValDesc :=
    match f with
    | D_FIELD _ _ val => val
    end.

  Definition msg_desc_get_reserved (m:MsgDesc) : ReservedSet :=
    match m with
    | D_MESSAGE rset _ => rset
    end.

  Definition msg_desc_get_fields (m:MsgDesc) : list FieldDesc :=
    match m with
    | D_MESSAGE _ fields => fields
    end.

  Definition msg_desc_get_field_ids (m:MsgDesc) : list nat :=
    map field_desc_get_id (msg_desc_get_fields m).

  Definition msg_desc_get_field_names (m:MsgDesc) : list string :=
    map field_desc_get_name (msg_desc_get_fields m).
  
  Definition msg_desc_get_field_vals (m:MsgDesc) : list ValDesc :=
    map field_desc_get_val (msg_desc_get_fields m).

  Definition valid_desc (d : MsgDesc) : Prop :=
    NoDup (msg_desc_get_field_ids d) /\ NoDup (msg_desc_get_field_names d).

  Inductive DecoVal {v : Type} : Type :=
    | V_IMPLICIT (x : v)
    | V_OPTIONAL (x : option v)
    | V_REPEATED (x : list v).

  Arguments DecoVal v : clear implicits.

  Definition f32 := binary_float 24 128.
  Definition f32_zero := B754_zero 24 128 false.
  Definition f64 := binary_float 53 1024.
  Definition f64_zero := B754_zero 53 1024 false.
  
  Inductive ValVal :=
  | V_DOUBLE (v: DecoVal f64)
  | V_FLOAT  (v: DecoVal f32)
  | V_INT    (v: DecoVal Z)
  | V_BOOL   (v: DecoVal bool)
  | V_STRING (v: DecoVal string)
  | V_BYTES  (v: DecoVal (list w8))
  | V_MSG    (v: DecoVal MsgVal)
  | V_ENUM   (v: DecoVal unit)

  with FieldVal := V_FIELD (name: string) (v: ValVal)
  with MsgVal := V_MESSAGE (fields: list FieldVal).

  Definition empty_message : MsgVal := V_MESSAGE nil.
  
  (* MESSAGE INITIALIZATION *)

  Definition init_deco {A : Type} (deco : DecoDesc) (def : A) :=
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
  Fixpoint init_msg (m:MsgDesc) : MsgVal := 
  let init_field := (fix init_field (f:FieldDesc) : FieldVal :=
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
  let init_fields := (fix init_fields (fs:list FieldDesc) : list FieldVal :=
    match fs with
    | [] => []
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
