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

theorem byteParseOk : ParseOk parseByte serialByte := by
  intro a enc;
  intro rest;
  intro _ h;
  cases h ; tauto

theorem unsignedParseOk : ParseOk parseUnsigned serialUnsigned := by
  intro x
  generalize_proofs at *;
  unfold ParseOk';
  unfold ParseOk'';
  unfold ParseOk''';
  unfold serialUnsigned; unfold parseUnsigned; simp +decide [ serialByte, parseByte ] ;
  rintro enc rest hx₁ hx₂ rfl; interval_cases x <;> trivial;

theorem unsignedLength (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc = 1 := by
      unfold serialUnsigned;
      unfold serialByte at * ; aesop

theorem unsignedNonEmpty (x : Int) (enc : List UInt8) :
    serialUnsigned x = .success () enc → Input.length enc > 0 := by
      exact fun h => by have := unsignedLength x enc h; aesop;

theorem natParseOk : ParseOk parseNat serialNat := by
  intro x;
  intro enc rest;
  intro hx hser;
  cases hser;
  rcases hx with ⟨ hx₁, hx₂ ⟩ ; interval_cases x <;> rfl

theorem natStrictParseOk : ParseOk parseNat serialNatStrict := by
  have h_nat : ParseOk parseNat serialNat := by
    exact natParseOk;
  intro x enc rest;
  unfold ParseOk''';
  unfold serialNatStrict;
  split_ifs <;> aesop

theorem natStrictStrict (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → 0 ≤ x ∧ x < 256 := by
      unfold serialNatStrict;
      grind

theorem natStrictLength (x : Nat) (enc : List UInt8) :
    serialNatStrict x = .success () enc → Input.length enc = 1 := by
      intro h
      unfold serialNatStrict at h
      simp [serialNat] at h;
      split_ifs at h ; cases h;
      rfl

private theorem serialZ32_enc (z : Int) :
    serialZ32 z = .success () (zToList z 4) := by
      rfl

private theorem parseZ32_roundtrip (z : Int) (rest : List UInt8) :
    0 ≤ z → z < 2 ^ 32 →
    parseZ32 (zToList z 4 ++ rest) = .success z rest := by
      unfold parseZ32 zToList;
      unfold parseZN; simp +decide [ zNext ] ;
      unfold parseUnsigned; simp +decide [ zToList ] ;
      intro hz₁ hz₂; rw [ Parser.map ] ; simp +decide [ Parser.repN ] ;
      simp +decide [ Parser.map, parseByte ];
      norm_num [ Int.shiftLeft_eq, zNext ];
      have h_simp : ∀ n : ℕ, n < 4294967296 → (n >>> 8 >>> 8 >>> 8) % 256 * 16777216 + ((n >>> 8 >>> 8) % 256 * 65536 + ((n >>> 8) % 256 * 256 + n % 256)) = n := by
        omega;
      grind +suggestions

theorem z32ParseOk : ParseOk parseZ32 serialZ32 := by
  intro x enc rest ⟨h1, h2⟩ hser
  have henc := serialZ32_enc x
  rw [henc] at hser; cases hser
  exact parseZ32_roundtrip x rest h1 h2

theorem z32Length (x : Int) (enc : List UInt8) :
    serialZ32 x = .success () enc → Input.length enc = 4 := by
      intro h;
      cases h ; exact rfl

theorem boolParseOk : ParseOk parseBool serialBool := by
  intro b enc rest hwf hser
  cases b <;> simp [serialBool] at hser <;>
  · have := z32ParseOk _ enc rest (by constructor <;> omega) hser
    simp [parseBool, Parser.map, this]

/-! ## Validity lemmas -/

theorem validDropFirst (d : Desc) (z : Int) (val : Val) (v : Value) :
    v.get? z = none →
    valid' d (v.insert z val) → valid' d v := by sorry

theorem valueDepthDropFirst (z : Int) (val : Val) (v : Value) :
    v.get? z = none →
    valueDepth v ≤ valueDepth (v.insert z val) := by
      -- If `v.get? z = none`, then `v.insert z val` is just `v` with `val` added at `z`. Therefore, the length of the `vals` list increases by 1, but the value depth should not increase.
      intro h_none
      simp [Value.insert, Value.get?] at *;
      have h_sortedInsert : ∀ (l : List (Int × Val)), ∀ (z : Int) (val : Val), (∀ (a : Int) (b : Val), (a, b) ∈ l → ¬z = a) → (z, val) ∉ l → valueDepthList (Value.sortedInsert z val l) ≥ valueDepthList l := by
        intros l z val h_none h_not_in_l; induction' l with l_head l_tail ih generalizing z val <;> simp_all +decide [ Value.sortedInsert ] ;
        · simp +decide [ valueDepthList ];
          exact fun x => by cases val <;> simp +decide [ valueDepthFold ] ;
        · split_ifs <;> simp_all +decide [ valueDepthList ];
          · intro x; specialize ih z val ( fun a b hab => h_none a b ( Or.inr hab ) ) h_not_in_l.2; simp_all +decide [ valueDepthList ] ;
            refine' Nat.le_induction _ _ _ ( show valueDepthFold l_head.2 x ≤ valueDepthFold l_head.2 ( valueDepthFold val x ) from _ );
            · refine' Nat.le_induction _ _ _ ( show x ≤ valueDepthFold val x from _ );
              · unfold valueDepthFold; aesop;
              · rfl;
              · intro n hn ih; exact le_trans ih ( by
                  unfold valueDepthFold; simp +decide [ * ] ;
                  cases l_head.2 <;> simp +decide [ * ];
                  exact Nat.le_succ_of_le ( Nat.le_max_left _ _ ) ) ;
            · rfl;
            · intro n hn hn'; exact le_trans hn' ( by
                have h_monotone : ∀ (l : List (Int × Val)) (n : Nat), valueDepthList l n ≤ valueDepthList l (n + 1) := by
                  intros l n; induction' l with l_head l_tail ih generalizing n <;> simp_all +decide [ valueDepthList ] ;
                  exact monotone_nat_of_le_succ ( fun n => ih n ) ( by exact Nat.le_of_lt_succ ( by
                    exact Nat.lt_succ_of_le ( by exact Nat.le_induction ( by tauto ) ( fun k hk ih => by exact le_trans ih ( by exact Nat.le_of_lt_succ ( by
                      cases l_head.2 <;> simp +decide [ valueDepthFold ] at * ; omega ) ) ) _ ( show n ≤ n + 1 from Nat.le_succ _ ) ) ) );
                exact h_monotone _ _ ) ;
          · exact False.elim <| h_none _ _ ( Or.inl rfl ) rfl;
          · intro x; exact (by
            specialize ih z val (fun a b hab => h_none a b (Or.inr hab)) h_not_in_l.2;
            exact ih _);
      cases v ; aesop

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
    valueDepth val < valueDepth v := by
      exact fun a => valInMap_smallerDepth v k val a

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

/-
Every field in the value exists in the descriptor.
-/
theorem sc_implies_val_in_desc (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val → ∃ f, d.get? k = some f := by
      contrapose!; simp_all +decide [ Value.get? ] ;
      intro k val h₁ h₂ h₃;
      induction' h₃ with k' f val' d' v' h₄ h₅ h₆ h₇ h₈;
      · cases h₁;
      · by_cases hk : k = k' <;> simp_all +decide [ Value.insert ];
        · contrapose! h₂; simp_all +decide [ Value.get? ] ;
          -- By definition of `sortedInsert`, inserting `k'` into `d'.fields` will result in a list where `k'` is the first element.
          have h_sortedInsert : List.lookup k' (Desc.sortedInsert k' f d'.fields) = some f := by
            induction' d'.fields with k'' f'' d'' ih <;> simp_all +decide [ Desc.sortedInsert ];
            grind +qlia;
          exact ⟨ f, h_sortedInsert ⟩;
        · -- Since k is not equal to k', the lookup in the sortedInsert is the same as the lookup in the original list.
          have h_lookup_eq : List.lookup k (Value.sortedInsert k' val' v'.vals) = List.lookup k v'.vals := by
            have h_lookup_eq : ∀ {l : List (Int × Val)}, k ≠ k' → List.lookup k (Value.sortedInsert k' val' l) = List.lookup k l := by
              intros l hk; induction' l with hd tl ih <;> simp_all +decide [ Value.sortedInsert ] ;
              grind;
            exact h_lookup_eq hk;
          rename_i h₉ h₁₀;
          obtain ⟨ x, hx ⟩ := h₁₀ ( h_lookup_eq.symm.trans h₁ );
          exact h₂ x ( by rw [ show ( d'.insert k' f ).get? k = d'.get? k from by
                                have h_lookup_eq : ∀ {l : List (Int × Field)}, k ≠ k' → List.lookup k (Desc.sortedInsert k' f l) = List.lookup k l := by
                                  intros l hk; induction' l with l ih <;> simp +decide [ Desc.sortedInsert, hk ] ;
                                  grind;
                                exact h_lookup_eq hk ] ; exact hx )

/-- Every field in the value exists in the descriptor with matching type. -/
theorem sc_implies_val_in_desc_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val →
    ∃ f, d.get? k = some f ∧ fieldValMatch f val := by sorry

/-
Every field in the descriptor exists in the value.
-/
theorem sc_implies_desc_in_val (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f → ∃ val, v.get? k = some val := by
      intro h k f hf
      induction' h with d' v' f' k' h_valid h_ind;
      · cases hf;
      · have h_lookup_insert : ∀ (l : List (Int × Field)) (k : Int) (d' : Int) (v' : Field), k ≠ d' → (List.lookup k (Desc.sortedInsert d' v' l)) = (List.lookup k l) := by
          intros l k d' v' hk_ne_d'; induction' l with l ih generalizing k d' v' <;> simp_all +decide [ Desc.sortedInsert ] ;
          grind;
        unfold Value.get? at *; by_cases h : k = d' <;> simp_all +decide [ Value.insert ] ;
        · have h_lookup_insert : ∀ (l : List (Int × Val)) (k : Int) (d' : Int) (v' : Val), k = d' → List.lookup k (Value.sortedInsert d' v' l) = some v' := by
            intros l k d' v' hk; induction' l with hd tl ih <;> simp_all +decide [ Value.sortedInsert ] ;
            grind;
          exact ⟨ _, h_lookup_insert _ _ _ _ rfl ⟩;
        · have h_lookup_insert : ∀ (l : List (Int × Val)) (k : Int) (d' : Int) (v' : Val), k ≠ d' → (List.lookup k (Value.sortedInsert d' v' l)) = (List.lookup k l) := by
            intros l k d' v' hk_ne_d'; induction' l with l ih generalizing k d' v' <;> simp_all +decide [ Value.sortedInsert ] ;
            grind +splitImp;
          simp_all +decide [ Value.vals ];
          exact ‹List.lookup k k'.fields = some f → ∃ val, List.lookup k _ = some val› ( by rename_i h₁ h₂ h₃ h₄ h₅ h₆; exact h₆ _ _ _ _ h ▸ hf )

/-
Every field in the descriptor exists in the value with matching type.
-/
theorem sc_implies_desc_in_val_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f →
    ∃ val, v.get? k = some val ∧ fieldValMatch f val := by
      intro hd k f hkf
      obtain ⟨val, hval⟩ : ∃ val, v.get? k = some val := by
        exact sc_implies_desc_in_val d v hd k f hkf;
      have := sc_implies_val_in_desc_typed d v hd k val hval; aesop;

/-
No `V_MISSING` values in a schema-correct value.
-/
theorem sc_implies_no_missing (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k, v.get? k ≠ some .missing := by
      intros h k;
      have := sc_implies_desc_in_val_typed d v h k;
      have := sc_implies_val_in_desc d v h k Val.missing; aesop;

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