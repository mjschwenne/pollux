From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.

Module Parse.

  Include Descriptors.
  Infix "%" := Z.modulo (at level 35) : Z_scope.
  Infix "==" := Z.eqb (at level 35) : Z_scope.

  Definition parity (z : Z) : Z :=
    if ((z % 2) == 0)%Z then 1 else (-1).

  Definition idn (c : bool) : Z := if c then 1 else 0.

  Definition uint_change_w (w : Width) (v : Z) : Z := v % (2^(unwrap_width w)).
  Definition int_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                     (v `mod` pow2__w - pow2__w * idn (( v / pow2__w) % 2 == 1)).
  Definition sint_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                      (v `mod` pow2__w - pow2__w * idn (Z.ltb v 0)).
  Definition uint_int (w : Width) (v : Z) : Z := v - (2^(unwrap_width w)) *
                                                       (idn (Z.geb v (2^(unwrap_width w - 1))%Z)).
  Definition int_uint (w : Width) (v : Z) : Z := v + (2^(unwrap_width w)) * (idn (Z.ltb v 0)).
  Definition uint_sint (w : Width) (v : Z) : Z := parity v * (v / 2) - (v % 2).
  Definition sint_uint (w : Width) (v : Z) : Z := 2 * (Z.abs v) - idn (Z.ltb v 0).
  Definition int_sint (w : Width) (v : Z) : Z := if Z.geb v 0 then
                                                   parity v * (v / 2) - (v % 2)
                                                 else
                                                   parity v * (v + (2^(unwrap_width w - 1)) - (v / 2)).
  Definition sint_int (w : Width) (v : Z) : Z := if Z.leb (- 2^(unwrap_width w - 2)) v &&
                                                      Z.leb v (2^(unwrap_width w - 2)) then
                                                   2 * (Z.abs v) - idn (Z.ltb v 0)
                                                 else
                                                   2 * (Z.abs v) - (2^(unwrap_width w)) - idn (Z.ltb v 0).

    (* NOTE: Compared to the F* version, these functions no longer have type-level assurances
       that the resulting integer is in-bounds for the given width. Now, the F* functions only
       had this assurance, so the formula could still be wrong, which is why there were / are
       tested against the official protobuf implementation.
     *)

  Inductive Tag :=
  | VARINT
  | I64
  | LEN
  | I32.
  
  Definition tag_num (t:Tag) : Z :=
    match t with
    | VARINT => 0
    | I64 => 1
    | LEN => 2
    | I32 => 5
    end.
  
  Definition find_field_string (msg : MsgDesc) (id : string) : option FieldDesc :=
   find (fun f => String.eqb (field_desc_get_name f) id) (msg_desc_get_fields msg). 
  
  Definition find_tag (d : ValDesc) : Tag :=
    match d with
    | D_INT _ D_REPEATED
    | D_UINT _ D_REPEATED
    | D_SINT _ D_REPEATED
    | D_BOOL D_REPEATED
    | D_ENUM D_REPEATED
    | D_FIXED _ D_REPEATED
    | D_SFIXED _ D_REPEATED
    | D_FLOAT D_REPEATED
    | D_DOUBLE D_REPEATED => LEN
    | D_INT _ _
    | D_UINT _ _
    | D_SINT _ _
    | D_BOOL _
    | D_ENUM _ => VARINT
    | D_FIXED (exist _ 32%Z _) _
    | D_SFIXED (exist _ 32%Z _) _
    | D_FLOAT _ => I32
    | D_FIXED (exist _ 64%Z _) _
    | D_SFIXED (exist _ 64%Z _) _
    | D_DOUBLE _ => I64
    | _ => LEN
    end.

  (* FIXME / TODO: The loss of let? is going to make the rest of this code a lot more annoying to
     translate from F*... *)
  Definition encode_header (msg : MsgDesc) (name : string) : option w64 :=
    (* TODO: Check tag number. Valid numbers are 1 to 536870911 excluding 19000 - 19999 *)
    match find_field_string msg name with
      | Some f => let id_n := W64 $ Z.of_nat (field_desc_get_id f) in
                 let tag_n := W64 (tag_num (find_tag (field_desc_get_val f))) in
                 Some (word.or (word.slu id_n (W64 3)) tag_n)
      | None => None
    end.

  (* Since W64 handles cases like negative numbers correctly, explicitly casting from signed
     to unsigned isn't needed. *)

  Definition encode_int (z : Z) : list byte := Varint.encode $ W64 z.
  Definition encode_sint32 (s : Z) : list byte := encode_int $ sint_uint width32 (uint.Z (W32 s)).
  Definition encode_sint64 (s : Z) : list byte := encode_int $ sint_uint width64 (uint.Z (W64 s)).

  Definition encode_fixed32 (f : Z) : list byte := u32_le $ W32 f.
  Definition encode_fixed64 (f : Z) : list byte := u64_le $ W64 f.
  Definition encode_bool (b : bool) : list byte := if b then [(W8 1)] else [(W8 0)].
  (* FIXME: Is the rev needed? This should shift us back to big-endian which I think (?)
     we need for encoding a float... *)
  Definition encode_float (f : f32) : list byte := rev (u32_le $ W32 (bits_of_b32 f)).
  Definition encode_double (f : f64) : list byte := rev (u64_le $ W64 (bits_of_b64 f)).
  Definition float_eqb (f1 : f32) (f2 : f32) : bool :=
    match b32_compare f1 f2 with
    | Some comp => match comp with
                  | Eq => true
                  | _ => false
                  end
    (* May not be the best choice, but it will work for detecting the default value, I hope... *)
    | None => false
    end.
  Definition double_eqb (f1 : f64) (f2 : f64) : bool :=
    match b64_compare f1 f1 with
    | Some comp => match comp with
                  | Eq => true
                  | _ => false
                  end
    | None => false
    end.

  (* Higher order encoding functions *)
  (* TODO is there a better way to handle decidable equality? I was honestly expecting
     that I would just need to restrict to a typeclass, but such a wide-spread type class
     doesn't seem to exist in the Core / Standard libraries... *)
  Definition encode_implicit {A: Type} (v : A) (d : A) (eq : A -> A -> bool) (enc : A -> list byte) :
    option (list byte) := 
    if eq v d then None else Some (enc v).

  Definition len_prefix (b : list byte) : list byte :=
    let length := encode_int (Z.of_nat $ length b) in
    length ++ b.

  Definition encode_packed {A : Type} (l : list A) (enc_one : A -> list byte) : list byte :=
    len_prefix $ fold_left (++) (map enc_one l) [].

  Definition encode_unpacked {A : Type} (l : list A) (header : list byte) (enc_one : A -> list byte) :
    list byte :=
    fold_left (fun bytes next => bytes ++ header ++ next) (map enc_one l) [].

  Fixpoint encode_unpacked_opt {A : Type} (l : list A) (header : list byte)
    (enc_one : A -> option (list byte)) : option (list byte) :=
    match l with
    | [] => None
    | v :: tl => match encode_unpacked_opt tl header enc_one with
               | None => None
               | Some rest => match enc_one v with
                             | Some next => Some (header ++ next ++ rest)
                             | None => None
                             end
               end
    end.

  (* Add the length prefix, using a separate function for consistency *)
  Definition encode_bytes := len_prefix.
  Fixpoint bytes_eqb (b1 : list byte) (b2 : list byte) : bool :=
    match b1, b2 with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | (h1 :: t1), (h2 :: t2) => if (word.eqb h1 h2) then
                                 bytes_eqb t1 t2
                               else
                                 false
    end.
        
  (* TODO looks like we lost native UTF-8 support. *)
  Definition encode_string (s : string) : list byte := len_prefix
                                                         (* This collection of casts is ugly... *)
                                                         (map (fun b => W8 (Z.of_nat $ Byte.to_nat b))
                                                            (list_byte_of_string s)).

  Definition encode_deco_packed {A : Type} (deco : DecoVal A) (def : A) (eq : A -> A -> bool)
    (enc_one : A -> list byte) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v => encode_implicit v def eq enc_one
    | V_OPTIONAL (Some v) => Some (header ++ enc_one v)
    | V_REPEATED (vh :: vt) => Some (header ++ encode_packed (vh :: vt) enc_one)
    | _ => None
    end.

  Definition encode_deco_unpacked {A : Type} (deco : DecoVal A) (def : A) (eq : A -> A -> bool)
    (enc_one : A -> list byte) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v
    | V_OPTIONAL (Some v) => if eq v def then None else Some (enc_one v)
    | V_REPEATED (vh :: vt) => Some (encode_unpacked (vh :: vt) header enc_one)
    | _ => None
    end.

  Definition encode_deco_unpacked_opt {A : Type} (deco : DecoVal A) (def : A) (eq : A -> A -> bool)
    (enc_one : A -> option (list byte)) (header : list byte) : option (list byte) :=
    match deco with
    | V_IMPLICIT v
    | V_OPTIONAL (Some v) => if eq v def then None else enc_one v
    | V_REPEATED (vh :: vt) => encode_unpacked_opt (vh :: vt) header enc_one
    | _ => None
    end.

  Definition find_int_enc_one (m : MsgDesc) (name : string) : option (Z -> list byte) :=
    match find_field_string m name with
    | Some f => (match field_desc_get_val f with
                | D_INT _ _ => Some encode_int
                | D_UINT _ _ => Some encode_int
                | D_SINT (exist _ 32%Z _) _ => Some encode_sint32
                | D_SINT (exist _ 64%Z _) _ => Some encode_sint64
                | D_FIXED (exist _ 32%Z _) _
                | D_SFIXED (exist _ 32%Z _) _ => Some encode_fixed32
                | D_FIXED (exist _ 64%Z _) _
                | D_SFIXED (exist _ 64%Z _) _ => Some encode_fixed64
                | _ => None
                end)
    | None => None
    end.

  Definition opt_append {A : Type} (l1 : list A) (l2 : option (list A)) : list A :=
    match l2 with
    | None => l1
    | Some l2 => l1 ++ l2
    end.

  Definition opt_append_opt {A : Type} (l1 : option (list A)) (l2 : option (list A)) : option (list A) :=
    match l1, l2 with 
    | None, None 
    | None, Some _
    | Some _, None => None
    | Some l1', Some l2' => Some (l1' ++ l2')
    end.

  Fixpoint find_nested_md_f (fs : list FieldDesc) (f : FieldVal) : option MsgDesc :=
    match fs with
    | [] => None
    | h :: t => if String.eqb (field_desc_get_name h) (field_val_get_name f) then
                 match field_desc_get_val h with
                 | D_MSG m _ => Some m
                 | _ => None
                 end
               else
                 find_nested_md_f t f
    end.
  Definition find_nested_msg_desc (m : MsgDesc) (f : FieldVal) : option MsgDesc :=
    find_nested_md_f (msg_desc_get_fields m) f.

  (* NOTE I /really/ want to move encode_fields, encode_message and encode_messages to
     mutually recursive functions via the `with` keyword. However, moving any of them
     outside the body of encode_field causes an error about not knowing which argument
     is the decreasing one. Annotating that Fixpoint with Program and a {struct f} field
     lets Rocq accept the fixpoint, but it also generates some complex Obligations that
     I'd rather not deal with. Given all that, I've elected to leave the functions
     internal to encode_field. Proving correctness of this function will also be hard. *)
  Fixpoint encode_field (m : MsgDesc) (f : FieldVal) : option (list byte) :=
    match encode_header m (field_val_get_name f) with
    | Some header => let header_bytes := Varint.encode header in
                    let encode_fields := fun m' fs => fold_left opt_append_opt (map (encode_field m') fs)
                                                     (Some header_bytes) in
                    let encode_message := fun m' msg => encode_fields m' (msg_val_get_fields msg) in
                    let encode_messages := fun m' ms => fold_left opt_append_opt (map (encode_message m') ms)
                                                       (Some []) in
                    match (field_val_get_val f) with
                    | V_DOUBLE v => encode_deco_packed v f64_zero double_eqb encode_double header_bytes
                    | V_FLOAT v => encode_deco_packed v f32_zero float_eqb encode_float header_bytes
                    | V_INT v => match find_int_enc_one m (field_val_get_name f) with
                                | Some enc_one => encode_deco_packed v 0%Z Z.eqb enc_one header_bytes
                                | None => None
                                end
                    | V_BOOL v => encode_deco_packed v false eqb encode_bool header_bytes
                    | V_STRING v => encode_deco_unpacked v EmptyString String.eqb encode_string header_bytes
                    | V_BYTES v => encode_deco_unpacked v [] bytes_eqb encode_bytes header_bytes
                    | V_MSG (V_IMPLICIT v)
                    | V_MSG (V_OPTIONAL (Some v)) => match find_nested_msg_desc m f with
                                                    | Some m' => encode_message m' v
                                                    | None => None
                                                    end
                    | V_MSG (V_REPEATED (ms)) => match find_nested_msg_desc m f with
                                                | Some m' => encode_messages m' ms
                                                | None => None
                                                end
                    | _ => None
                    end
    | None => None
    end.

  Definition encode_message (m : MsgDesc) (msg : MsgVal) : option (list byte) :=
    fold_left opt_append_opt (map (encode_field m) (msg_val_get_fields msg)) (Some []).

  Definition tag_from_num (n : Z) : option Tag :=
    match n with
    | 0%Z => Some VARINT
    | 1%Z => Some I64
    | 2%Z => Some LEN
    | 5%Z => Some I32
    | _ => None
    end.

  Definition decode_header (enc : list byte) : option (Z * Tag * list byte) :=
    match Varint.extract_varint enc with
    | Some (header_bytes, bs) => let header : w64 := Varint.decode header_bytes in
                                let fid : Z := uint.Z $ word.sru header (U64 3) in
                                let tag_n : Z := uint.Z $ word.and header (U64 7) in
                                match tag_from_num tag_n with
                                | None => None
                                | Some tag => Some (fid, tag, bs)
                                end
    | None => None
    end.

End Parse.
