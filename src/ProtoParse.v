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
  Module ByteParsers := Parsers(ByteInput).
  Import ByteInput.
  Import ByteParsers.

  Definition Byte : @Parser byte :=
    fun inp => match inp with
            | byt :: rest => ParseSuccess byt rest
            | [] => ParseFailure Recoverable (mkFailureData "No more data to parse" inp None)
            end.

  Definition Unsigned : @Parser Z := Map Byte word.unsigned.   

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

  Definition FieldHeader := ParseBind Varint (fun z =>
                                                let (fid, tag_n) := ((z ≫ 3)%Z, (Z.land z 7)%Z) in
                                                match tag_from_num tag_n with
                                                | Some tag => ParseSucceedWith (fid, tag)
                                                | None => ParseFailWith "Unknown field type" Recoverable
                                                end).

  Definition test_varint := [(W8 128); (W8 1); (W8 165); (W8 2); (W8 6)].

  Compute Varint test_varint.
  Compute FieldHeader test_varint.
  (* This isn't repeatable since if there is an unknown field type, the whole thing fails.
     I would need to be able to serialize a varint to "replace" it in case of failure, but
     I honestly don't think I'd need to use the field header parser like that. *)
  Compute (Rep FieldHeader) (fun acc new => acc ++ [new]) [] test_varint.

(* TODO Field parsing. Plan:
   - Write parser for I32 tag. Be sure to check endianess!
   - Write parser for I64 tag. Be sure to check endianess!
   - Write parser for LEN tag. I don't want to defer computation like in the old version, so this one
     will be tricky. I'll need a field header parser which can inject the final type of the field,
     so I know where or not to build up a (1) string (2) packed integer (3) message.

     That last one is even harder since it makes the LEN parser mutually recursive with the message parser.
     For now, don't do it. OK, maybe I do need to chunk things here and call a separate parser on them later. *)
  
End ProtoParse.
