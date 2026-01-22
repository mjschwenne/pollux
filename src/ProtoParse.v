From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Stdlib Require Import Structures.Equalities.

From Stdlib Require Import Program.Wf.
From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.
From Equations Require Import Equations.

From Pollux Require Import Parser.
From Pollux Require Import Input.

Module ProtoParse.

  Import Descriptors.

  Notation "x %% y" := (Z.modulo x y) (at level 35) : Z_scope.

  Definition parity (z : Z) : Z :=
    if ((z %% 2) == 0%Z) then 1 else (-1).

  Definition idn__p {P} (c : {P} + {¬ P}) : Z := if c then 1 else 0.
  Definition idn__b (c : bool) : Z := if c then 1 else 0.

  Definition uint_change_w (w : Width) (v : Z) : Z := v %% (2^(unwrap_width w)).
  Definition int_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                     (v %% pow2__w - pow2__w * idn__p (( v / pow2__w) %% 2 == 1%Z)).
  Definition sint_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                      (v %% pow2__w - pow2__w * idn__b (Z.ltb v 0)).
  Definition uint_int (w : Width) (v : Z) : Z := v - (2^(unwrap_width w)) *
                                                       (idn__b (Z.geb v (2^(unwrap_width w - 1))%Z)).
  Definition int_uint (w : Width) (v : Z) : Z := v + (2^(unwrap_width w)) * (idn__b (Z.ltb v 0)).
  Definition uint_sint (w : Width) (v : Z) : Z := parity v * (v / 2) - (v %% 2).
  Definition sint_uint (w : Width) (v : Z) : Z := 2 * (Z.abs v) - idn__b (Z.ltb v 0).
  Definition int_sint (w : Width) (v : Z) : Z := if Z.geb v 0 then
                                                   parity v * (v / 2) - (v %% 2)
                                                 else
                                                   parity v * (v + (2^(unwrap_width w - 1)) - (v / 2)).
  Definition sint_int (w : Width) (v : Z) : Z := if Z.leb (- 2^(unwrap_width w - 2)) v &&
                                                      Z.leb v (2^(unwrap_width w - 2)) then
                                                   2 * (Z.abs v) - idn__b (Z.ltb v 0)
                                                 else
                                                   2 * (Z.abs v) - (2^(unwrap_width w)) - idn__b (Z.ltb v 0).

    (* NOTE: Compared to the F* version, these functions no longer have type-level assurances
       that the resulting integer is in-bounds for the given width. Now, the F* functions only
       had this assurance, so the formula could still be wrong, which is why there were / are
       tested against the official protobuf implementation.
     *)

  Module ByteParsers := Parsers(ByteInput).
  Import ByteInput.
  Import ByteParsers.
  Import Descriptors.

  Definition Byte : @Parser byte :=
    fun inp => match inp with
            | byt :: rest => ParseSuccess byt rest
            | [] => ParseFailure Recoverable (mkFailureData "No more data to parse" inp None)
            end.

  Definition Unsigned : @Parser Z := ParseMap Byte word.unsigned.   

  (* Parses an unsigned integer from the byte stream.
     If successful, check that the byte satisfies the input predicate.
     If it does, return the potentially transformed integer as a success.
     Else, manually build a non-committing parse failure and return that.
     This makes it usable with repeated parsing without always having to parse twice, it it would
     if we were using the If parser with a Lookahead. *)
  Definition FilterByte (filter : Z -> bool) (transform : Z -> Z) (msg : string) : @Parser Z :=
    ParseBindSucceeds Unsigned 
      (fun z rest => if filter z then
                    ParseSucceedWith (transform z)
                  else
                    ParseResultWith
                      (ParseFailure Recoverable
                         (mkFailureData msg (App (ToInput [W8 z]) rest) None))).
                                         
  Definition VarintNonTerm := FilterByte (Z.leb 128%Z) (flip Z.sub 128%Z) "Expected varint non-terminal byte".

  Definition VarintTerm (acc : Z * Z) := FilterByte (fun _ => true)
                                           (fun z => let (n, v) := acc in
                                                  (z ≪ n + v)%Z)
                                           "Expected varint terminal byte".

  (* Protobuf uses a little-endian encoding, which I'm directly converting from. It's less
     convenient than big-endian since I have to track the byte length explicitly. *)
  Definition VarintPrefix := Rep VarintNonTerm
                               (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                            ((n + 7)%Z, (new ≪ n + v)%Z))
                               (0%Z, 0%Z).

  Definition Varint := ParseBind VarintPrefix VarintTerm.

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

  Definition tag_from_num (n : Z) : option Tag :=
    match n with
    | 0%Z => Some VARINT
    | 1%Z => Some I64
    | 2%Z => Some LEN
    | 5%Z => Some I32
    | _ => None
    end.

(* TODO Field parsing. Plan:
   - Write parser for I32 tag. Be sure to check endianess!
   - Write parser for I64 tag. Be sure to check endianess!
   - Write parser for LEN tag. I don't want to defer computation like in the old version, so this one
     will be tricky. I'll need a field header parser which can inject the final type of the field,
     so I know where or not to build up a (1) string (2) packed integer (3) message.

     That last one is even harder since it makes the LEN parser mutually recursive with the message parser.
     For now, don't do it. OK, maybe I do need to chunk things here and call a separate parser on them later. *)

  (* Parse n bytes into an unsigned integer *)
  Definition ZN (n : nat) := ParseMap (RepN Unsigned
                                  (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                               ((n + 8)%Z, (new ≪ n + v)%Z))
                                  n (0%Z, 0%Z))
                             (fun ret => let (_, z) := ret in z).

  Definition Z32 := ZN 4.

  Definition Z64 := ZN 8.

  Compute Z64 [(W8 0); (W8 0); (W8 0); (W8 0); (W8 0); (W8 0); (W8 0); (W8 128)].

  Definition find_field (m : MsgDesc) (id : Z) : option FieldDesc :=
    (* Hide the recursion on the fields via a nested fix *)
    let find_field := (fix find_field (fs : list FieldDesc) : option FieldDesc :=
                         match fs with
                         | [] => None
                         | h :: t => if (Nat.eqb (Z.to_nat id) $ field_desc_get_id h) then
                                     Some h
                                   else
                                     find_field t
                         end
                      ) in
    find_field (msg_desc_get_fields m).

  Definition FieldHeader := ParseBind Varint (fun z =>
                                                let (fid, tag_n) := ((z ≫ 3)%Z, (Z.land z 7)%Z) in
                                                match tag_from_num tag_n with
                                                | Some tag => ParseSucceedWith (fid, tag)
                                                | None => ParseFailWith "Unknown field type" Recoverable
                                                end).

  Definition TypedFieldHeader (md : MsgDesc) := ParseMap FieldHeader
                                                  (fun (h : Z * Tag) =>
                                                     let (fid, tag) := h in
                                                     (fid, tag, find_field md fid)).

  Definition LenBody := ParseBind Varint (fun len => SeqN Byte $ Z.to_nat len).

  Definition Discard {A : Type} (parser : @Parser A) : @Parser unit := ParseMap parser (fun _ => ()). 

  Definition DiscardPayload (tag : Tag) :=
    match tag with
    | VARINT => Discard Varint
    | I64 => Discard Z64
    | LEN => Discard LenBody
    | I32 => Discard Z32
    end.

  Definition ParseIntField (w : Width) (deco : DecoDesc) : @Parser ValVal :=
    ParseMap Varint (fun z => match deco with
                      | D_IMPLICIT => V_INT $ V_IMPLICIT $ int_change_w w $ uint_int width64 z
                      | D_OPTIONAL => V_INT $ V_OPTIONAL $ Some (int_change_w w $ uint_int width64 z)
                      | D_REPEATED => V_INT $ V_REPEATED $ [int_change_w w $ uint_int width64 z]
                      end).

  Definition ParseUintField (w : Width) (deco : DecoDesc) : @Parser ValVal :=
    ParseMap Varint (fun z => match deco with
                      | D_IMPLICIT => V_INT $ V_IMPLICIT $ uint_change_w w z
                      | D_OPTIONAL => V_INT $ V_OPTIONAL $ Some (uint_change_w w z)
                      | D_REPEATED => V_INT $ V_REPEATED $ [uint_change_w w z]
                      end).

  Definition ParseSintField (w : Width) (deco : DecoDesc) : @Parser ValVal :=
    ParseMap Varint (fun z => match deco with
                      | D_IMPLICIT => V_INT $ V_IMPLICIT $ sint_change_w w $ uint_sint width64 z
                      | D_OPTIONAL => V_INT $ V_OPTIONAL $ Some (sint_change_w w $ uint_sint width64 z)
                      | D_REPEATED => V_INT $ V_REPEATED $ [sint_change_w w $ uint_sint width64 z]
                      end).

  Definition GetFixedParser (w : Width) := match w with
                                           | exist _ 32%Z _ => Z32
                                           | exist _ 64%Z _ => Z64
                                           | _ => ParseFailWith "This is literally impossible." Fatal
                                           end.

  Definition ParseFixedField (w : Width) (deco : DecoDesc) : @Parser ValVal :=
    ParseMap (GetFixedParser w) (fun z => match deco with
                                  | D_IMPLICIT => V_INT $ V_IMPLICIT $ uint_change_w w z
                                  | D_OPTIONAL => V_INT $ V_OPTIONAL $ Some (uint_change_w w z)
                                  | D_REPEATED => V_INT $ V_REPEATED $ [uint_change_w w z]
                                  end).

  Definition ParseSfixedField (w : Width) (deco : DecoDesc) : @Parser ValVal :=
    ParseMap (GetFixedParser w) (fun z => match deco with
                                  | D_IMPLICIT => V_INT $ V_IMPLICIT $ uint_change_w w $ uint_int width64 z
                                  | D_OPTIONAL => V_INT $ V_OPTIONAL $ Some
                                                   (uint_change_w w $ uint_int width64 z)
                                  | D_REPEATED => V_INT $ V_REPEATED $ [uint_change_w w $ uint_int width64 z]
                                  end).

  Definition ParseBoolField (deco : DecoDesc) : @Parser ValVal := 
    ParseMap Varint (fun z => match deco with
                      | D_IMPLICIT => V_BOOL $ V_IMPLICIT $ negb (Z.eqb z 0)
                      | D_OPTIONAL => V_BOOL $ V_OPTIONAL $ Some (negb (Z.eqb z 0))
                      | D_REPEATED => V_BOOL $ V_REPEATED $ [negb (Z.eqb z 0)]
                      end).

  Definition DecoMerger {A : Type} (a_deco : DecoVal A) (b_deco : DecoVal A) : DecoVal A :=
    match a_deco, b_deco with
    | V_IMPLICIT _, V_IMPLICIT v => V_IMPLICIT v
    | V_OPTIONAL _, V_OPTIONAL v => V_OPTIONAL v
    | V_REPEATED v, V_REPEATED v' => V_REPEATED (v ++ v')
    | _, _ => a_deco (* This case should be impossible... *)
    end.

  Definition ValMerger (acc : option ValVal) (new : ValVal) : option ValVal :=
    match acc, new with
    | None, val => Some val
    | Some (V_INT a_deco), V_INT b_deco => Some (V_INT $ DecoMerger a_deco b_deco)
    | Some (V_BOOL a_deco), V_BOOL b_deco => Some (V_BOOL $ DecoMerger a_deco b_deco)
    | Some (V_STRING a_deco), V_STRING b_deco => Some (V_STRING $ DecoMerger a_deco b_deco)
    | Some (V_BYTES a_deco), V_BYTES b_deco => Some (V_BYTES $ DecoMerger a_deco b_deco)
    | _, _ => None
    end.

  Definition WrapPacked (tag : Tag) (underlying : @Parser ValVal) : @Parser ValVal :=
    match tag with
    | VARINT => underlying
    | I64 => underlying
    | LEN => ParseBind LenBody (fun body => match Rep underlying ValMerger None body with
                                        | ParseSuccess (Some v) rem => ParseResultWith (ParseSuccess v rem)
                                        | ParseSuccess None rem => ParseResultWith
                                                                    (ParseFailure Recoverable
                                                                       (mkFailureData "Illegal value merger"
                                                                          body None))
                                        | ParseFailure lvl data as f => ParseResultWith (PropagateFailure f I)
                                        end)
    | I32 => underlying
    end.

  Definition WrapPackedField (tag : Tag) (name : string) (underlying : @Parser ValVal) :=
    ParseMap (WrapPacked tag underlying) (fun vv => V_FIELD name vv).

  Definition ParseFieldVal (header : Z * Tag * option FieldDesc) : @Parser FieldVal :=
    match header with
    | ((_, tag), Some (D_FIELD name _ (D_INT w deco))) => WrapPackedField tag name (ParseIntField w deco)
    | ((_, tag), Some (D_FIELD name _ (D_UINT w deco))) => WrapPackedField tag name (ParseUintField w deco)
    | ((_, tag), Some (D_FIELD name _ (D_SINT w deco))) => WrapPackedField tag name (ParseSintField w deco)
    | ((_, tag), Some (D_FIELD name _ (D_FIXED w deco))) => WrapPackedField tag name (ParseFixedField w deco)
    | ((_, tag), Some (D_FIELD name _ (D_SFIXED w deco))) => WrapPackedField tag name (ParseSfixedField w deco)
    | ((_, tag), Some (D_FIELD name _ (D_BOOL deco))) => WrapPackedField tag name (ParseBoolField deco)
    (* | (name, _, D_STRING deco) => *)
    (* | (name, _, D_Bytes deco) => *)
    | _ => ParseFailWith "Field type unsupported" Recoverable
    end.

  Definition ProtoField (md : MsgDesc) := ParseBind (TypedFieldHeader md) ParseFieldVal.

  Definition test_field__varint := [(W8 128); (W8 1); (W8 165); (W8 2); (W8 6)].
  Definition test_field__I32 := [(W8 133); (W8 1); (W8 37); (W8 1); (W8 0); (W8 0)].
  Definition test_field__I64 := [(W8 129); (W8 1);
                               (W8 37); (W8 1); (W8 0); (W8 0);
                               (W8 0); (W8 0); (W8 0); (W8 0)].
  Definition test_field__Len := [(W8 130); (W8 1); (W8 2); (W8 72); (W8 105)].

  Compute FieldHeader test_field__varint.
  Fail Compute ProtoField test_field__varint.
  Compute FieldHeader test_field__I32.
  Fail Compute ProtoField test_field__I32.
  Compute FieldHeader test_field__I64.
  Fail Compute ProtoField test_field__I64.
  Compute FieldHeader test_field__Len.
  Fail Compute ProtoField test_field__Len.

End ProtoParse.
