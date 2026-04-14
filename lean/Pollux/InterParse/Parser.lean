/-
  Pollux.InterParse.Parser — Parsers for the intermediate format.

  Corresponds to src/InterParse/Parser.v in the Rocq development.

  Both integer and boolean fields are encoded as 4-byte little-endian integers
  so that the descriptor determines the final type. Each primitive field is
  tagged with a 1-byte field number, then a 4-byte payload. Nested messages
  start with a 1-byte field number followed by a 4-byte length prefix.
-/
import Pollux.Parse.Parser
import Pollux.InterParse.Descriptor

namespace Pollux.InterParse

open Pollux.Parse

/-- Convert a list of integers to a byte list. Corresponds to `to_enc`. -/
def toEnc (l : List Int) : List UInt8 :=
  l.map (fun n => UInt8.ofNat n.toNat)

/-! ## Low-level byte parsers -/

/-- Parse a single byte from the input. -/
def parseByte : Parser (List UInt8) UInt8 :=
  fun inp =>
    match inp with
    | byt :: rest => .success byt rest
    | [] => .failure .recoverable ⟨"No more data to parse", inp, .none⟩

/-- Parse a byte and return its unsigned integer value. -/
def parseUnsigned : Parser (List UInt8) Int :=
  Parser.map parseByte (fun b => Int.ofNat b.toNat)

/-- Parse a byte and return its value as a natural number. -/
def parseNat : Parser (List UInt8) Nat :=
  Parser.map parseByte (fun b => b.toNat)

/-- Parse `n` bytes into a little-endian unsigned integer.
    Reads bytes one at a time, shifting and accumulating. -/
def parseZN (n : Nat) : Parser (List UInt8) Int :=
  Parser.map
    (Parser.repN parseUnsigned
      (fun (acc : Int × Int) (new : Int) =>
        let (shift, v) := acc
        (shift + 8, (new <<< shift.toNat) + v))
      n (0, 0))
    (fun ret => ret.2)

/-- Parse a 4-byte little-endian unsigned integer. -/
def parseZ32 : Parser (List UInt8) Int := parseZN 4

/-- Parse a 4-byte integer and convert to boolean (nonzero = true). -/
def parseBool : Parser (List UInt8) Bool :=
  Parser.map parseZ32 (fun z => z > 0)

/-! ## Value parser -/

/-- Parse a single tagged field value. The field number is read first, then
    the descriptor determines which kind of value to parse.
    Takes a recursive parser for nested messages. -/
def parseVal (parseMsg : Desc → Parser (List UInt8) Value) (d : Desc) :
    Parser (List UInt8) (Int × Val) :=
  Parser.depConcat parseUnsigned fun z =>
    match d.fields.lookup z with
    | some .bool => Parser.map parseBool (fun b => .bool b)
    | some .int  => Parser.map parseZ32 (fun z' => .int z')
    | some (.msg d') => Parser.map (Parser.len parseNat (parseMsg d')) (fun v => .msg v)
    | none => Parser.succeedWith .missing

/-- Parse a complete value: repeatedly parse tagged fields and merge the
    results according to the descriptor.
    This is the "step" of the recursive parser. -/
def parseValue' (self : Desc → Parser (List UInt8) Value) (d : Desc) :
    Parser (List UInt8) Value :=
  Parser.map (Parser.rep (parseVal self d)) (fun vs => listToValue d vs)

/-- Parse a value using the recursive stateful parser combinator.
    The descriptor is threaded as state; recursion terminates because
    nested messages are length-delimited. -/
def parseValue (d : Desc) : Parser (List UInt8) Value :=
  Parser.recursiveState parseValue' d

end Pollux.InterParse
