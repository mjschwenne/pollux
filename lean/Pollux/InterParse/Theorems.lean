/-
  Pollux.InterParse.Theorems — Correctness theorems for the intermediate format.

  Corresponds to src/InterParse.v (Section Theorems) in the Rocq development.

  Contains roundtrip correctness theorems for individual parsers/serializers,
  the `SchemaCorrect` inductive relation between descriptors and values,
  the `Compatible` relation for schema evolution, and the top-level
  `interParseOk` correctness theorem.
-/
import Pollux.Parse.Theorems
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer

namespace Pollux.InterParse

open Pollux.Parse
open Pollux.Parse.Theorems

/-! ## Roundtrip correctness for primitive parsers/serializers -/

theorem byteParseOk : ParseOk parseByte serialByte := by sorry

theorem unsignedParseOk : ParseOk parseUnsigned serialUnsigned := by sorry

theorem unsignedLength (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc = 1 := by sorry

theorem unsignedNonEmpty (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc > 0 := by sorry

theorem natParseOk : ParseOk parseNat serialNat := by sorry

theorem natStrictParseOk : ParseOk parseNat serialNatStrict := by sorry

theorem natStrictStrict (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → 0 ≤ x ∧ x < 256 := by sorry

theorem natStrictLength (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → Input.length enc = 1 := by sorry

theorem z32ParseOk : ParseOk parseZ32 serialZ32 := by sorry

theorem z32Length (x : Int) (enc : List UInt8) :
    serialZ32 x = .success () enc → Input.length enc = 4 := by sorry

theorem boolParseOk : ParseOk parseBool serialBool := by sorry

/-! ## Validity lemmas -/

theorem validDropFirst (d : Desc) (z : Int) (val : Val) (v : Value) :
    v.get? z = none →
    valid' d (v.insert z val) → valid' d v := by sorry

theorem valueDepthDropFirst (z : Int) (val : Val) (v : Value) :
    v.get? z = none →
    valueDepth v ≤ valueDepth (v.insert z val) := by sorry

theorem validInsert (d : Desc) (k : Int) (val : Val) (v : Value) :
    v.get? k = none →
    (valid' d (v.insert k val) ↔
     valid'Fold d.fields k val True ∧ valid' d v) := by sorry

/-! ## Encoding length lemmas -/

theorem valueEncLength_unfold (d : Desc) (k : Int) (val : Val) (v : Value) :
    v.get? k = none →
    valueEncLen' d (v.insert k val) =
    valueEncLen'Fold d.fields k val 0 + valueEncLen' d v := by sorry

theorem valInMap_smallerDepth' (v : Value) (k : Int) (val : Value) :
    v.get? k = some (.msg val) →
    valueDepth val < valueDepth v := by sorry

/-! ## SchemaCorrect inductive relation

The `SchemaCorrect` relation establishes a correspondence between a descriptor
and a value: every field in the descriptor has a correctly-typed entry in the
value and vice versa, with no `V_MISSING` entries. -/

inductive SchemaCorrect : Desc → Value → Prop where
  | empty : SchemaCorrect (∅ : Desc) (∅ : Value)
  | insert (k : Int) (f : Field) (v : Val) (ds : Desc) (vs : Value) :
    fieldValMatch f v →
    (∀ d' v', f = .msg d' → v = .msg v' → SchemaCorrect d' v') →
    ds.get? k = none →
    vs.get? k = none →
    SchemaCorrect ds vs →
    SchemaCorrect (ds.insert k f) (vs.insert k v)

notation "⟨ " v " ∷ " d " ⟩" => SchemaCorrect d v

/-! ## SchemaCorrect lemmas -/

theorem sc_insert_field (k : Int) (f : Field) (val : Val) (d : Desc) (v : Value) :
    fieldValMatch f val →
    (∀ d' v', f = .msg d' → val = .msg v' → ⟨ v' ∷ d' ⟩) →
    d.get? k = none →
    v.get? k = none →
    ⟨ v ∷ d ⟩ →
    ⟨ v.insert k val ∷ d.insert k f ⟩ :=
  SchemaCorrect.insert k f val d v

theorem sc_empty : ⟨ (∅ : Value) ∷ (∅ : Desc) ⟩ :=
  SchemaCorrect.empty

/-- Every field in the value exists in the descriptor. -/
theorem sc_implies_val_in_desc (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val → ∃ f, d.get? k = some f := by sorry

/-- Every field in the value exists in the descriptor with matching type. -/
theorem sc_implies_val_in_desc_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val →
    ∃ f, d.get? k = some f ∧ fieldValMatch f val := by sorry

/-- Every field in the descriptor exists in the value. -/
theorem sc_implies_desc_in_val (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f → ∃ val, v.get? k = some val := by sorry

/-- Every field in the descriptor exists in the value with matching type. -/
theorem sc_implies_desc_in_val_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f →
    ∃ val, v.get? k = some val ∧ fieldValMatch f val := by sorry

/-- No `V_MISSING` values in a schema-correct value. -/
theorem sc_implies_no_missing (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k, v.get? k ≠ some .missing := by sorry

/-- Nested messages are schema-correct with their subdescriptors. -/
def nestedCorrect (d : Desc) (k : Int) (v : Val) : Prop :=
  match d.fields.lookup k, v with
  | some (.msg d'), .msg v' => ⟨ v' ∷ d' ⟩
  | _, _ => True

theorem sc_implies_nested_correct (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2 := by sorry

/-- Combined: all four properties of schema correctness. -/
theorem sc_implies_properties (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by sorry

/-- Combined with typed witnesses. -/
theorem sc_implies_properties_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f ∧ fieldValMatch f val) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val ∧ fieldValMatch f val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by sorry

theorem sc_delete_key (d : Desc) (v : Value) (k : Int) :
    ⟨ v ∷ d ⟩ → ⟨ v.erase k ∷ d.erase k ⟩ := by sorry

theorem sc_dom_eq (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → (v.vals.map Prod.fst) = (d.fields.map Prod.fst) := by sorry

/-! ## SchemaCorrectOrdered -/

/-- Ordered variant of `SchemaCorrect` that additionally requires inserted keys
    to be first in the map ordering. Equivalent to `SchemaCorrect` for
    well-ordered maps. -/
inductive SchemaCorrectOrdered : Desc → Value → Prop where
  | empty : SchemaCorrectOrdered (∅ : Desc) (∅ : Value)
  | insert (k : Int) (f : Field) (val : Val) (d : Desc) (v : Value) :
    fieldValMatch f val →
    (∀ d' v', f = .msg d' → val = .msg v' → SchemaCorrectOrdered d' v') →
    d.get? k = none →
    v.get? k = none →
    SchemaCorrectOrdered d v →
    SchemaCorrectOrdered (d.insert k f) (v.insert k val)

notation "⟪ " v " ∷ " d " ⟫" => SchemaCorrectOrdered d v

theorem sc_sco (v : Value) (d : Desc) : ⟨ v ∷ d ⟩ ↔ ⟪ v ∷ d ⟫ := by sorry

/-! ## Descriptor invariance -/

/-- If a value is schema-correct for two descriptors, the descriptors are equal. -/
theorem sc_desc_inv (v : Value) (d1 d2 : Desc) :
    ⟨ v ∷ d1 ⟩ → ⟨ v ∷ d2 ⟩ → d1 = d2 := by sorry

/-! ## Compatible relation

The `Compatible` relation captures when two descriptor/value pairs represent
the same information — used for proving schema-evolution correctness. -/

inductive Compatible : Desc → Desc → Value → Value → Prop where
  | refl (d1 d2 : Desc) (v : Value) :
    ⟨ v ∷ d1 ⟩ → ⟨ v ∷ d2 ⟩ → Compatible d1 d2 v v
  | add (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value)
    (k : Int) (f1 f2 : Field) (v'1 v'2 : Val) :
    ⟨ v1 ∷ d1 ⟩ → ⟨ v2 ∷ d2 ⟩ →
    Compatible d1 d2 v1 v2 →
    v1.get? k = none →
    v2.get? k = none →
    d1.get? k = none →
    d2.get? k = none →
    v'1 = v'2 → f1 = f2 →
    Compatible (d1.insert k f1) (d2.insert k f2)
      (v1.insert k v'1) (v2.insert k v'2)

notation "⟨ " v1 " ∷ " d1 " ⟩≼⟨ " v2 " ∷ " d2 " ⟩" =>
  Compatible d1 d2 v1 v2

theorem compatibleEqual (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value) :
    Compatible d1 d2 v1 v2 → d1 = d2 → v1 = v2 := by sorry

/-! ## Serialization correctness helper lemmas -/

theorem willEncode_nonEmpty (d : Desc) (k : Int) (v : Val) (enc : List UInt8) :
    willEncode d (k, v) →
    serialVal serialValue d (k, v) = .success () enc →
    Input.length enc > 0 := by sorry

/-- `field_val_type_match` for serializer error data. -/
def fieldValTypeMatch (f : Field) (v : Val) : Prop :=
  match f, v with
  | .bool, .bool _ | .int, .int _ | .msg _, .msg _ => True
  | _, _ => False

/-! ## ValList correctness -/

theorem valList_drop_ok (v : Value) (k : Int) (d : Desc) (f : Field) :
    v.get? k = none → valList (d.insert k f) v = valList d v := by sorry

theorem valList_elem_of (v : Value) (d : Desc) (k : Int) (val : Val) :
    (k, val) ∈ valList d v → v.get? k = some val := by sorry

/-- Serializing and then parsing a schema-correct value recovers the original
    (up to list-to-value reconstruction). -/
theorem list_to_value_id (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → v = listToValue d (valList d v) := by sorry

theorem sc_filter_self (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → ⟨ listToValue d (valList d v) ∷ d ⟩ := by sorry

theorem fullDescriptor_roundTrip (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → Compatible d d v (listToValue d (valList d v)) := by sorry

/-! ## Well-formedness -/

theorem valueWf_weaken (v : Value) (d : Desc) (k : Int) :
    v.get? k = none → (valueWf d v ↔ valueWf (d.erase k) v) := by sorry

theorem willEncode_weaken (kv : Int × Val) (d : Desc) (k : Int) (v : Value) :
    kv ∈ valList (d.erase k) v →
    (willEncode d kv ↔ willEncode (d.erase k) kv) := by sorry

theorem parseOk_wf (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → valueWf d v →
    Serializer.repWf (willEncode d) (valList d v) := by sorry

/-! ## Top-level correctness theorem

This is the main result: for any schema-correct value, serializing with
`serialValue` and then parsing with `parseValue` recovers a compatible value. -/

theorem interParseOk (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ →
    LimitParseOkCompat'' Compatible parseValue serialValue d d v := by sorry

/-! ## Serializer inversion lemmas -/

theorem serialValueInversion (d : Desc) (k : Int) (v : Val) (m : Value)
    (enc : List UInt8) :
    m.get? k = none →
    (serialValue d (m.insert k v) = .success () enc ↔
    ∃ encV encRest,
      serialValue d m = .success () encRest ∧
      serialVal serialValue d (k, v) = .success () encV ∧
      enc = Input.app encV encRest) := by sorry

/-- Encoding length matches the predicted length. -/
theorem valueEncLength_length (v : Value) (d : Desc) (enc : List UInt8) :
    valid' d v →
    serialValue d v = .success () enc →
    Input.length enc = valueEncLen' d v := by sorry

end Pollux.InterParse
