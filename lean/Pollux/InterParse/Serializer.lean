/-
  Pollux.InterParse.Serializer — Serializers for the intermediate format.

  Corresponds to src/InterParse/Serializer.v in the Rocq development.

  Both integer and boolean fields are encoded as 4-byte little-endian integers.
  Each primitive field is tagged with a 1-byte field number then a 4-byte payload.
  Nested messages start with a 1-byte field number then a 4-byte length prefix.
-/
import Pollux.Parse.Serializer
import Pollux.InterParse.Descriptor

namespace Pollux.InterParse

open Pollux.Parse

/-! ## Low-level byte serializers -/

/-- Serialize a single byte. -/
def serialByte : Serializer (List UInt8) UInt8 Serializer.trivialWf :=
  fun b => .success () [b]

/-- Serialize an integer as a single byte (truncating to 0–255). -/
def serialUnsigned : Serializer (List UInt8) Int (fun z => 0 ≤ z ∧ z < 256) :=
  fun z => serialByte (UInt8.ofNat z.toNat)

/-- Serialize a natural number as a single byte. -/
def serialNat : Serializer (List UInt8) Nat (fun n => 0 ≤ n ∧ n < 256) :=
  fun n => serialByte (UInt8.ofNat n)

/-- Serialize a natural number as a single byte, failing if out of range. -/
def serialNatStrict : Serializer (List UInt8) Nat (fun n => 0 ≤ n ∧ n < 256) :=
  fun n =>
    if n < 256 then serialNat n
    else .failure .recoverable ⟨"Nat too large for one byte", Input.default, .none⟩

/-- Shift an integer right by 8 bits (for little-endian byte extraction). -/
def zNext (z : Int) : Int := z >>> 8

/-- Produce an n-byte little-endian encoding of `z`.
    If `z` doesn't fit in `n` bytes, the first `n` bytes are returned.
    If `z` fits in fewer than `n` bytes, the list is zero-padded. -/
def zToList (z : Int) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat z.toNat :: zToList (zNext z) n

/-- Well-formedness for n-byte integer serialization. -/
def serialZWf (n : Nat) (z : Int) : Prop :=
  0 ≤ z ∧ z < 2 ^ (8 * n)

/-- Serialize an integer as `n` little-endian bytes. -/
def serialZN (n : Nat) : Serializer (List UInt8) Int (serialZWf n) :=
  fun z => Serializer.rep serialByte (zToList z n)

/-- Serialize an integer as 4 little-endian bytes. -/
def serialZ32 : Serializer (List UInt8) Int (serialZWf 4) := serialZN 4

/-- Serialize a boolean as a 4-byte integer (true → 1, false → 0). -/
def serialBool : Serializer (List UInt8) Bool Serializer.trivialWf :=
  fun b => if b then serialZ32 1 else serialZ32 0

/-! ## Value serializer -/

/-- Serialize a single tagged field value. The field number is serialized first,
    then the value payload determined by the descriptor.
    Takes a recursive serializer for nested messages. -/
def serialVal (serialMsg : ∀ d : Desc, Serializer (List UInt8) Value (valueWf d))
    (d : Desc) : Serializer (List UInt8) (Int × Val) (valWf d) :=
  fun val =>
    match d.fields.lookup val.1 with
    | some .bool =>
      Serializer.map
        (Serializer.opt
          (Serializer.concat serialUnsigned
            (Serializer.partMap serialBool
              (fun v => match v with | .bool b => some b | _ => none)
              "Expected Boolean")))
        (fun (k, v) => match v with | .missing => none | _ => some (k, v)) val
    | some .int =>
      Serializer.map
        (Serializer.opt
          (Serializer.concat serialUnsigned
            (Serializer.partMap serialZ32
              (fun v => match v with | .int z => some z | _ => none)
              "Expected Integer")))
        (fun (k, v) => match v with | .missing => none | _ => some (k, v)) val
    | some (.msg d') =>
      Serializer.map
        (Serializer.opt
          (Serializer.concat serialUnsigned
            (Serializer.partMap (Serializer.len' serialNatStrict (serialMsg d'))
              (fun v => match v with | .msg x => some x | _ => none)
              "Expected nested message")))
        (fun (k, v) => match v with | .missing => none | _ => some (k, v)) val
    | none => .success () Input.default

/-- The "step" of the recursive serializer: serialize all filtered fields. -/
def serialValue' (self : ∀ d : Desc, Serializer (List UInt8) Value (valueWf d))
    (d : Desc) : Serializer (List UInt8) Value (valueWf d) :=
  Serializer.map (Serializer.rep (serialVal self d)) (valList d)

/-- Serialize a value using the recursive stateful serializer combinator.
    The descriptor is threaded as state; recursion terminates because
    `valueDepth` strictly decreases at nested messages. -/
def serialValue (d : Desc) : Serializer (List UInt8) Value (valueWf d) :=
  Serializer.recursiveState serialValue' valueDepth d

end Pollux.InterParse
