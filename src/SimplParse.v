(** Simple Parser, to establish some of the theory *)

From Pollux Require Import Prelude.
From Perennial Require Import Helpers.Word.LittleEndian.
From Stdlib Require Import Structures.Equalities.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.
From Equations Require Import Equations.

From Pollux Require Import Parser.
From Pollux Require Import Input.

Module SimplParser.
  Module ByteParsers := Parsers(ByteInput).
  Import ByteInput.
  Import ByteParsers.

  (* Taken from Section 9.3 of Certified Programming with Dependent Types *)
  Section hlist.
    Variable A : Set.
    Variable B : A -> Type.

    Fixpoint fhlist (ls : list A) : Type :=
      match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
      end%type.

    Variable elm : A.
    Fixpoint fmember (ls : list A) : Type :=
      match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + fmember ls'
      end%type.

    Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
      match ls with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
                     match idx with
                     | inl pf => match pf with
                                | eq_refl => fst mls
                                end
                     | inr idx' => fhget ls' (snd mls) idx'
                     end
      end.

  End hlist.
  Arguments fhget [A B elm ls] _ _.

  Section Desc.

    (* A field can be either an integer or a Boolean *)
    Inductive FieldDesc : Set :=
    | D_INT
    | D_BOOL.

    (* A descriptor is either a base field, or two nested descriptors. *)
    Inductive Desc : Set :=
    | D_BASE (n : string) (f : FieldDesc)
    | D_NEST (d1 : Desc) (d2 : Desc).

    Definition FDescTy (f : FieldDesc) : Set :=
      match f with
      | D_INT => Z
      | D_BOOL => bool
      end.

    (* A value corresponding to some descriptor is a large tuple, using names as
       strings and values as either ints or bools, respectively. *)
    Fixpoint Denote (d : Desc) : Set :=
      match d with
      | D_BASE n f => string * FDescTy f
      | D_NEST d1 d2 => (prod (Denote d1) (Denote d2))
      end.

    Definition test_desc1 : Desc := D_BASE "f1" D_INT.
    Compute Denote test_desc1.
    Definition test_val1 : Denote test_desc1 := ("f1"%string, 32%Z).

    Definition test_desc2 : Desc := D_NEST (D_BASE "f1" D_INT) (D_BASE "f2" D_BOOL).
    Compute Denote test_desc2.
    Definition test_val2 : Denote test_desc2 := ("f1"%string, 1%Z, ("f2"%string, true)).

    Definition test_desc3 : Desc := D_NEST (D_BASE "f1" D_INT)
                                      (D_NEST (D_BASE "f2" D_INT) (D_BASE "f3" D_BOOL)).
    Compute Denote test_desc3.
    Definition test_val3 : Denote test_desc3 := ("f1"%string, 32%Z, ("f2"%string, 64%Z, ("f3"%string, false))).

    Definition test_desc4 : Desc := D_NEST (D_NEST (D_BASE "f1" D_INT) (D_BASE "f2" D_BOOL))
                                      (D_NEST (D_BASE "f3" D_INT) (D_BASE "f4" D_BOOL)).
    Compute Denote test_desc4.
    Definition test_val4 : Denote test_desc4 := ("f1"%string, 2%Z, ("f2"%string, false),
                                                   ("f3"%string, 4%Z, ("f4"%string, true))).
    Definition test_val4' : Denote test_desc4 := (("f1"%string, 2%Z, ("f2"%string, false)),
                                                    ("f3"%string, 4%Z, ("f4"%string, true))).

    Fixpoint DescMem (d : Desc) (s : string) : Type :=
      match d with
      | D_BASE n _ => (n = s)
      | D_NEST d1 d2 => DescMem d1 s + DescMem d2 s
      end.

    Compute DescMem test_desc1 "f1".
    Definition test_mem1 : DescMem test_desc1 "f1" := eq_refl.
    Compute DescMem test_desc2 "f2".
    Definition test_mem2 : DescMem test_desc2 "f2" := inr eq_refl.
    Compute DescMem test_desc3 "f3".
    Definition test_mem3 : DescMem test_desc3 "f3" := inr $ inr eq_refl.
    Compute DescMem test_desc4 "f2".
    Definition test_mem4 : DescMem test_desc4 "f2" := inl $ inr eq_refl.

    (* A type representing how to get to the field we want in the descriptor.
       Names aren't actually really used here... *)
    Fixpoint DescMemF (d : Desc) (f : FieldDesc) : Type :=
      match d with
      | D_BASE _ fd => (fd = f)
      | D_NEST d1 d2 => DescMemF d1 f + DescMemF d2 f
      end.

    Compute DescMemF test_desc1 D_INT.
    Definition test_memf1 : DescMemF test_desc1 D_INT := eq_refl.
    Compute DescMemF test_desc2 D_BOOL.
    Definition test_memf2 : DescMemF test_desc2 D_BOOL := inr eq_refl.
    Compute DescMemF test_desc3 D_BOOL.
    Definition test_memf3 : DescMemF test_desc3 D_BOOL := inr $ inr eq_refl.
    Compute DescMemF test_desc4 D_BOOL.
    Definition test_memf4 : DescMemF test_desc4 D_BOOL := inl $ inr eq_refl.

    Fixpoint Get (d : Desc) (f : FieldDesc) : Denote d -> DescMemF d f -> FDescTy f :=
      match d with
      | D_BASE n f => fun mls mem => match mem with
                                 | eq_refl => (snd mls)
                                 end
      | D_NEST d1 d2 => fun mls mem =>
                         match mem with
                         | inl pf => Get d1 f (fst mls) pf
                         | inr pf => Get d2 f (snd mls) pf
                         end
      end.
    Arguments Get [d f] _ _.

    Fixpoint NameP (d : Desc) (s : string) : bool :=
      match d with
      | D_BASE n _ => String.eqb n s
      | D_NEST d1 d2 => if NameP d1 s then true
                       else
                         NameP d2 s
      end.

    Fixpoint GenMem (d : Desc) (s : string) : option (DescMem d s) :=
      match d with
      | D_BASE n _ => match decide (n = s) with
                     | left e => Some e
                     | right _ => None
                     end
      | D_NEST d1 d2 => match GenMem d1 s, GenMem d2 s with
                       | Some m, _ => Some (inl m)
                       | None, Some m => Some (inr m)
                       | None, None => None
                       end
      end.

    Fixpoint SDescTy (d : Desc) (s : string) : DescMem d s -> Set :=
      match d with
      | D_BASE n f => fun mem => match mem with
                             | eq_refl => FDescTy f
                             end
      | D_NEST d1 d2 => fun mem => match mem with
                               | inl pf => SDescTy d1 s pf
                               | inr pf => SDescTy d2 s pf
                               end
      end.

    Definition SDescTyOpt (d : Desc) (s : string) : option (DescMem d s) -> Set :=
      fun opt_mem => match opt_mem with
                  | Some mem => SDescTy d s mem
                  | None => Empty_set
                  end.

    Compute SDescTy test_desc1 "f1" test_mem1.
    Compute SDescTy test_desc2 "f2" test_mem2.
    Compute SDescTy test_desc3 "f3" test_mem3.
    Compute SDescTy test_desc4 "f2" test_mem4.

    Fixpoint GetName (d : Desc) (s : string) : Denote d -> forall (m : DescMem d s), SDescTy d s m :=
      match d with
      | D_BASE n f => fun v mem => match mem with
                               | eq_refl => snd v
                               end
      | D_NEST d1 d2 => fun v mem => match mem with
                                 | inl pf => GetName d1 s (fst v) pf
                                 | inr pf => GetName d2 s (snd v) pf
                                 end
      end.
    Arguments GetName [d s] _ _.

    Definition GetNameOpt {d : Desc} (s : string) (v : Denote d) :=
      match GenMem d s as x return option (SDescTyOpt d s x) with
      | Some mem => Some $ GetName v mem
      | None => None
      end.

    Definition f1 : option Z := GetNameOpt "f1"%string test_val1.
    Compute f1.
    Definition f1' : option Empty_set := GetNameOpt "f8"%string test_val1.
    Definition f2 : option bool := GetNameOpt "f2"%string test_val2.
    Compute f2.
    Definition f3 : option bool := GetNameOpt "f3"%string test_val3.
    Compute f3.
    Definition f4 := GetNameOpt "f3"%string test_val4.
    Compute f4.

  End Desc.

  (** ENCODING FORMAT *)

  (*
    While this is a simple descriptor setup, it is important to define what the binary format
    will be.

    Each descriptor will be serialized as a tag for the type
    - Base descriptor => 0
    - Nested descriptor => 1

    For the base descriptors, the next byte is another tag for the type of the field
    - Integer field => 0
    - Boolean field => 1

    (Note: This could be removed if integer and Boolean fields both used the same [length] encoding)

    The integer's will be encoded into a 4-byte little endian blob while the Booleans are
    encoded as 1-byte with 0 for false and any positive number for true.

    Nested messages will be length prefixed with the number of bytes the rest of the message
    takes and then the encoded message.
   *)

  Section Parser.

    Definition ParseByte : Parser byte :=
      fun inp => match inp with
              | byt :: rest => ParseSuccess byt rest
              | [] => ParseFailure Recoverable (mkFailureData "No more data to parse" inp None)
              end.

    Definition ParseUnsigned : Parser Z := Map ParseByte word.unsigned.

    (* Parse n bytes into an unsigned integer *)
    Definition ParseZN (n : nat) := Map (RepN ParseUnsigned
                                         (fun (acc : Z * Z) (new : Z) => let (n, v) := acc in
                                                                      ((n + 8)%Z, (new ≪ n + v)%Z))
                                         n (0%Z, 0%Z))
                                    (fun ret => let (_, z) := ret in z).

    Definition ParseZ32 := ParseZN 4.

    Definition ParseBool : Parser bool := Map ParseUnsigned (fun z => (z >? 0)%Z).

    (* Parse an integer field given a descriptor. The key to making this work with
       dependent types is using "match d as d' return Parser (Denote d')" which
       tells Coq that the return type depends on the matched value d'.

       In the D_BASE n D_INT branch, Coq knows that Denote (D_BASE n D_INT) = (string * Z),
       so ParseSucceedWith (n, z) has the correct type.

       In other branches, ParseFailWith can produce any type (it's polymorphic in R),
       so it unifies with whatever Denote d' is in that branch. *)
    Definition ParseIntField (d : Desc) : Parser (Denote d) :=
      ParseBind ParseZ32
        (fun z => match d as d' return Parser (Denote d') with
               | D_BASE n D_INT => ParseSucceedWith (n, z)
               | _ => ParseFailWith "Provided desc isn't for base int" Recoverable
               end).

    (* Parse a boolean field given a descriptor, following the same pattern *)
    Definition ParseBoolField (d : Desc) : Parser (Denote d) :=
      ParseBind ParseBool
        (fun b => match d as d' return Parser (Denote d') with
               | D_BASE n D_BOOL => ParseSucceedWith (n, b)
               | _ => ParseFailWith "Provided desc isn't for base bool" Recoverable
               end).

    Definition ParseBaseDesc (d : Desc) : Parser (Denote d) :=
        ParseBind ParseUnsigned
          (fun z => match z with
                 | 0%Z => ParseIntField d
                 | 1%Z => ParseBoolField d
                 | _ => ParseFailWith "Unknown field tag" Recoverable
                 end).

    Definition test_field := [W8 1; W8 32; W8 0; W8 0; W8 0].
    Compute ParseBaseDesc (D_BASE "f1" D_INT) test_field.
    Compute ParseBaseDesc (D_BASE "f1" D_BOOL) test_field.

    Definition LenLimit {R : Type} (underlying : Parser R) : Parser R := 
      ParseBind ParseUnsigned
                (fun len => ParseLimit underlying $ Z.to_nat len).

    Fixpoint ParseDesc (d : Desc) : Parser (Denote d) :=
      ParseBind ParseUnsigned
        (fun z => 
           match z, d as d' return Parser (Denote d') with
           | 0%Z, D_BASE n f as bd => ParseBaseDesc bd
           | 1%Z, D_NEST d1 d2 => LenLimit (ParseConcat (ParseDesc d1) (ParseDesc d2))
           | 0%Z, D_NEST _ _ => ParseFailWith "Mismatched tag (0) and desc (NEST)" Recoverable
           | 1%Z, D_BASE _ _ => ParseFailWith "Mismatched tag (1) and desc (BASE)" Recoverable
           | _, _ => ParseFailWith "Unknown tag" Recoverable
           end).

    Definition to_enc (l : list nat) : list byte := map (fun n => W8 $ Z.of_nat n) l.

    Definition test_enc1 := to_enc [0; 0; 32; 0; 0; 0].
    Compute ParseDesc test_desc1 test_enc1.

    Definition test_enc2 := to_enc [1; 9; 0; 0; 1; 0; 0; 0; 0; 1; 1].
    Compute ParseDesc test_desc2 test_enc2.

    Definition test_enc3 := to_enc [1; 17; 0; 0; 32; 0; 0; 0; 1; 9; 0; 0; 64; 0; 0; 0; 0; 1; 0].
    Compute ParseDesc test_desc3 test_enc3.
    Compute ParseDesc test_desc3 test_enc2.

    Definition test_enc4 := to_enc [1; 22;
                                    1; 9; 0; 0; 2; 0; 0; 0; 0; 1; 0;
                                    1; 9; 0; 0; 4; 0; 0; 0; 0; 1; 1].
    Compute ParseDesc test_desc4 test_enc4.

  (* So, despite having nested messages here, I didn't use the recursive combinator. The /critical/
     observation here is, as always, in the types:

     Recursive : ∀ {R : Type}, (Parser R → Parser R) → Parser R

     When the parser "generator" needs to respect something like a descriptor, particularly for a
     format with nested descriptors, we actually want to write something like this:

     ParseDesc (d : Desc) (par : ∀ d', Parser (Denote d')) : Parser (Denote d)

     So that we can change the descriptor during recursive calls, an basically take steps in the
     descriptors just like how we take steps in the encoding to only consider certain parts of the
     encoding (i.e. the part encoding this specific integer field).

     The parsing happening in the simple format is extremely descriptor-centric. A simple Fixpoint
     definition works since we only recursive down on the descriptor. The format doesn't have several
     more complex features that are present in Protobuf, namely
     - Parsing fields in any order
     - Inferring the default value for any missing fields (which actually has to happen during serialization
       since the tuple types here can't have missing values).

     Since, I learned a lot doing this exercise (mostly about dependent types) since I implemented features like
     - Have a denotation for a descriptor which generates a type for values of that descriptor rather than
       having a universal representation for all values.
     - Writing getter functions for these values (thanks, CPDT for the excellent starting point!).
     - Writing my first truly recursive parser.
     - Implementing a limiting combinator which limits how far ahead an underlying parser can consume.
   *)

  End Parser.

  Section Serializer.

    Definition SerialByte : Serializer byte serial_trivial_wf :=
      fun b => SerialSuccess [b].

    Definition Z__next (z : Z) : Z :=
      (z ≫ 8)%Z.

    (* Create an n-byte little-endian list of z.
       If z doesn't fit into n bytes, the first n bytes are returned.
       If z fits into less than n bytes, the list is padded with zeros.
     *)
    Fixpoint Z_to_list (z : Z) (n : nat) : list byte :=
      match n with
      | O => []
      | S n' => W8 z :: Z_to_list (Z__next z) n'
      end.

    Compute Z_to_list 16777215%Z 4.

    Definition SerialZN (n : nat) : Serializer Z serial_trivial_wf :=
      fun z => SerialRep SerialByte (Z_to_list z n).

    Definition SerialZ4 := SerialZN 4.

    Compute SerialZ4 16777215%Z.

    Definition SerialBool : Serializer bool serial_trivial_wf :=
      fun b => if b then
              SerialByte (W8 1)
            else
              SerialByte (W8 0).

    Compute SerialBool true.
    Compute SerialBool false.

    Definition TagDesc (d : Desc) : Z :=
      match d with
      | D_BASE _ _ => 0%Z
      | D_NEST _ _ => 1%Z
      end.

    Definition TagField (f : FieldDesc) : byte :=
      match f with
      | D_INT => W8 0
      | D_BOOL => W8 1
      end.

    Definition SerialFieldTag : Serializer FieldDesc serial_trivial_wf :=
      fun f => SerialByte (TagField f).

    Definition SerialTags : Serializer Desc serial_trivial_wf :=
      fun d => match d with
            | D_BASE _ fd => SerialConcat SerialByte SerialFieldTag (W8 0, fd)
            | D_NEST _ _ => SerialByte (W8 1)
            end.

    Definition SerialMsgLen : Serializer nat (fun n => n < 256) :=
      fun n =>
        SerialByte (W8 $ Z.of_nat n).

    Fixpoint SerialDesc' (d : Desc) : Serializer (Denote d) serial_trivial_wf :=
      match d as d' return Serializer (Denote d') serial_trivial_wf with
      | D_BASE n D_INT as d'' => fun v => SerialConcat SerialTags SerialZ4 (d'', (snd v))
      | D_BASE n D_BOOL as d'' => fun v => SerialConcat SerialTags SerialBool (d'', (snd v))
      | D_NEST d1 d2 as d'' => fun v => SerialConcat SerialTags
                                      (SerialLen SerialMsgLen $
                                         SerialConcat (SerialDesc' d1) (SerialDesc' d2)) (d'', v)
      end.

    Definition SerialDesc {d : Desc} (v : Denote d) : SerializeResult :=
      SerialDesc' d v.

    Definition enc_eq {d : Desc} (v : Denote d) (e : Output) : bool :=
      match SerialDesc v with
      | SerialSuccess enc => if decide (enc = e) then true else false
      | SerialFailure _ _ => false
      end.

    Compute SerialDesc test_val1.
    Compute enc_eq test_val1 test_enc1.
                                    
    Compute SerialDesc test_val2.
    Compute enc_eq test_val2 test_enc2.

    Compute SerialDesc test_val3.
    Compute enc_eq test_val3 test_enc3.

    Compute SerialDesc test_val4.
    Compute enc_eq test_val4 test_enc4.

  End Serializer.

  Theorem SimplParseOk : forall (d : Desc), ParseOk (ParseDesc d) (SerialDesc' d).
  Proof.
    intros.
    unfold ParseOk, ParseOk', ParseOk'', ParseOk'''.
    intros v enc rest _.
    induction d.
    - destruct f eqn:Hf.
      + simpl. intro HSucc. inversion HSucc as [Henc].
        unfold ParseBind. simpl. replace (uint.Z $ W8 0) with 0%Z; last reflexivity.
        unfold ParseBaseDesc, ParseBind. simpl.
        replace (uint.Z $ W8 0) with 0%Z; last reflexivity.
        unfold ParseIntField, ParseBind. simpl. 
        rewrite Z.shiftl_0_r. rewrite Z.add_0_r.
        unfold Z__next. rewrite ?Z.shiftr_shiftr; try done.
        rewrite ?Z.add_0_l. rewrite ?Z.add_assoc.
        replace (8 + 8)%Z with 16%Z; last reflexivity.
        replace (16 + 8)%Z with 24%Z; last reflexivity.
  Abort.

  Section Theorems.

  End Theorems.

End SimplParser.
