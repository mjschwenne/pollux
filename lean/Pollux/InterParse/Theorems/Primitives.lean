/-
  Pollux.InterParse.Theorems.Primitives — Roundtrip correctness for primitive
  parsers/serializers (byte, unsigned, nat, z32, bool).
-/
import Pollux.Parse.Theorems
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer

namespace Pollux.InterParse

open Pollux.Parse
open Pollux.Parse.Theorems

/-! ## Roundtrip correctness for primitive parsers/serializers -/

theorem byteParseOk : ParseOk parseByte serialByte := by
  intro a enc rest _ h
  cases h; tauto

theorem unsignedParseOk : ParseOk parseUnsigned serialUnsigned := by
  intro x
  unfold ParseOk' ParseOk'' ParseOk'''
  unfold serialUnsigned parseUnsigned; simp +decide [serialByte]
  rintro enc rest hx₁ hx₂ rfl; interval_cases x <;> trivial

theorem unsignedLength (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc = 1 := by
  unfold serialUnsigned
  unfold serialByte at *; aesop

theorem unsignedNonEmpty (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc > 0 := by
  intro h; have := unsignedLength x enc h; omega

theorem natParseOk : ParseOk parseNat serialNat := by
  intro x enc rest hx hser
  cases hser
  rcases hx with ⟨_, _⟩; interval_cases x <;> rfl

theorem natStrictParseOk : ParseOk parseNat serialNatStrict := by
  have h_nat : ParseOk parseNat serialNat := natParseOk
  intro x enc rest
  unfold ParseOk'''
  unfold serialNatStrict
  split_ifs <;> aesop

theorem natStrictStrict (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → 0 ≤ x ∧ x < 256 := by
  unfold serialNatStrict
  grind

theorem natStrictLength (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → Input.length enc = 1 := by
  intro h
  unfold serialNatStrict at h
  simp [serialNat] at h
  split_ifs at h; cases h
  rfl

private theorem serialZ32_enc (z : Int) :
    serialZ32 z = .success () (zToList z 4) :=
  rfl

private theorem parseZ32_roundtrip (z : Int) (rest : List UInt8) :
    0 ≤ z → z < 2 ^ 32 →
    parseZ32 (zToList z 4 ++ rest) = .success z rest := by
  unfold parseZ32 zToList
  unfold parseZN; simp +decide [zNext]
  unfold parseUnsigned; simp +decide [zToList]
  intro hz₁ hz₂; rw [Parser.map]; simp +decide [Parser.repN]
  simp +decide [Parser.map, parseByte]
  norm_num [Int.shiftLeft_eq, zNext]
  have h_simp : ∀ n : ℕ, n < 4294967296 →
      (n >>> 8 >>> 8 >>> 8) % 256 * 16777216 +
      ((n >>> 8 >>> 8) % 256 * 65536 +
       ((n >>> 8) % 256 * 256 + n % 256)) = n := by
    omega
  grind +suggestions

theorem z32ParseOk : ParseOk parseZ32 serialZ32 := by
  intro x enc rest ⟨h1, h2⟩ hser
  have henc := serialZ32_enc x
  rw [henc] at hser; cases hser
  exact parseZ32_roundtrip x rest h1 h2

theorem z32Length (x : Int) (enc : List UInt8) :
    serialZ32 x = .success () enc → Input.length enc = 4 := by
  intro h
  cases h; rfl

theorem boolParseOk : ParseOk parseBool serialBool := by
  intro b enc rest _ hser
  cases b <;> simp [serialBool] at hser <;>
  · have := z32ParseOk _ enc rest (by constructor <;> omega) hser
    simp [parseBool, Parser.map, this]

end Pollux.InterParse
