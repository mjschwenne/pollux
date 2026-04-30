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
    valueEncLen'Fold d.fields k val 0 + valueEncLen' d v := by
      intro h;
      -- By definition of `sortedInsert`, we can split the list into the part before `k` and the part after `k`.
      have h_split : ∀ (l : List (ℤ × Val)) (k : ℤ) (val : Val), ¬(k ∈ List.map Prod.fst l) → valueEncLen'List d.fields (Value.sortedInsert k val l) 0 = valueEncLen'List d.fields l 0 + valueEncLen'Fold d.fields k val 0 := by
        intros l k val hk;
        induction' l with l ih generalizing k val <;> simp_all +decide [ Value.sortedInsert ];
        · unfold valueEncLen'List; simp +decide [ valueEncLen'List ] ;
        · split_ifs <;> simp_all +decide [ valueEncLen'List ];
          · have h_split : ∀ (l : List (ℤ × Val)) (k : ℤ) (val : Val) (acc : Nat), valueEncLen'List d.fields l (valueEncLen'Fold d.fields k val acc) = valueEncLen'List d.fields l acc + valueEncLen'Fold d.fields k val 0 := by
              intros l k val acc; induction' l with l ih generalizing k val acc <;> simp_all +decide [ valueEncLen'List ] ;
              · grind +suggestions;
              · ring;
            rw [ h_split, h_split ];
            rw [ h_split ] ; ring;
          · convert congr_arg ( fun x => x + valueEncLen'Fold d.fields l.1 l.2 0 ) ( ‹∀ ( k : ℤ ) ( val : Val ), ( ∀ x : Val, ( k, x ) ∉ ih ) → valueEncLen'List d.fields ( Value.sortedInsert k val ih ) 0 = valueEncLen'List d.fields ih 0 + valueEncLen'Fold d.fields k val 0› k val hk.2 ) using 1;
            · have h_split : ∀ (l : List (ℤ × Val)) (k : ℤ) (val : Val) (acc : Nat), valueEncLen'List d.fields l acc = valueEncLen'List d.fields l 0 + acc := by
                intros l k val acc; induction' l with l ih generalizing k val acc <;> simp_all +decide [ valueEncLen'List ] ;
                nontriviality;
                rename_i h₁ h₂ h₃;
                convert h₂ l.2 ( valueEncLen'Fold d.fields l.1 l.2 acc ) using 1;
                rw [ h₂ ];
                · grind +suggestions;
                · exact Val.missing;
              exact?;
            · have h_split : ∀ (l : List (ℤ × Val)) (k : ℤ) (val : Val) (acc : Nat), valueEncLen'List d.fields l (acc + valueEncLen'Fold d.fields k val 0) = valueEncLen'List d.fields l acc + valueEncLen'Fold d.fields k val 0 := by
                intros l k val acc; induction' l with l ih generalizing k val acc <;> simp_all +decide [ valueEncLen'List ] ;
                grind +suggestions;
              rw [ show valueEncLen'List d.fields ih ( valueEncLen'Fold d.fields l.1 l.2 0 ) = valueEncLen'List d.fields ih 0 + valueEncLen'Fold d.fields l.1 l.2 0 from ?_ ] ; ring;
              convert h_split ih l.1 l.2 0 using 1;
              norm_num;
      rw [ add_comm ];
      unfold Value.get? at h;
      convert h_split v.vals k val _ using 1;
      · cases d ; rfl;
      · cases d ; cases v ; rfl;
      · grind

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

/-
Every field in the value exists in the descriptor with matching type.
-/
private theorem sortedInsert_lookup_ne_val (k k' : Int) (v : Val) (l : List (Int × Val)) :
    k ≠ k' → List.lookup k (Value.sortedInsert k' v l) = List.lookup k l := by
  intro hne; induction l with
  | nil => simp [Value.sortedInsert, hne]
  | cons hd tl ih =>
    unfold Value.sortedInsert; split_ifs <;> simp_all [List.lookup]
    · rw [show (k == k') = false from by rw [beq_eq_decide]; simp [hne]]
    · grind

private theorem sortedInsert_lookup_ne_desc (k k' : Int) (f : Field) (l : List (Int × Field)) :
    k ≠ k' → List.lookup k (Desc.sortedInsert k' f l) = List.lookup k l := by
  intro hne; induction l with
  | nil => simp [Desc.sortedInsert, hne]
  | cons hd tl ih =>
    unfold Desc.sortedInsert; split_ifs <;> simp_all [List.lookup]
    · rw [show (k == k') = false from by rw [beq_eq_decide]; simp [hne]]
    · grind

theorem sc_implies_val_in_desc_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val →
    ∃ f, d.get? k = some f ∧ fieldValMatch f val := by
      intro h
      induction' h with kk fld val' d' v' h_match h_nested ih_nested h_dnone h_vnone h_sc ih
      · intro k val hval
        simp [Value.get?, Value.vals] at hval
      · intro k val hval
        by_cases hk : k = kk
        · subst hk
          refine ⟨fld, ?_, ?_⟩
          · unfold Desc.get? Desc.insert
            cases d'
            simp +decide [Desc.fields]
            have h_lookup_insert : ∀ (l : List (Int × Field)),
                List.lookup k (Desc.sortedInsert k fld l) = some fld := by
              intros l
              induction' l with hd tl ih2 <;> simp_all +decide [ Desc.sortedInsert ]
              grind
            exact h_lookup_insert _
          · unfold Value.get? Value.insert at hval
            cases v'
            simp +decide [Value.vals] at hval
            have h_lookup_insert : ∀ (l : List (Int × Val)),
                List.lookup k (Value.sortedInsert k val' l) = some val' := by
              intros l
              induction' l with hd tl ih2 <;> simp_all +decide [ Value.sortedInsert ]
              grind
            rw [h_lookup_insert] at hval
            cases hval
            exact h_match
        · have h_lookup_v : v'.get? k = some val := by
            unfold Value.get? Value.insert at hval
            cases v'
            simp +decide [Value.vals] at hval
            simp [Value.get?, Value.vals]
            rw [← sortedInsert_lookup_ne_val k kk val' _ hk]
            exact hval
          obtain ⟨f', hf', hmatch⟩ := ih k val h_lookup_v
          refine ⟨f', ?_, hmatch⟩
          unfold Desc.get? Desc.insert
          cases d'
          simp +decide [Desc.fields]
          rw [sortedInsert_lookup_ne_desc k kk fld _ hk]
          simp [Desc.get?, Desc.fields] at hf'
          exact hf'

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

/-- Membership in a sorted-insert: the inserted pair, or one of the originals. -/
private theorem mem_value_sortedInsert (k : Int) (v : Val)
    (l : List (Int × Val)) (kv : Int × Val) :
    kv ∈ Value.sortedInsert k v l → kv = (k, v) ∨ kv ∈ l := by
  induction l with
  | nil => intro h; simp [Value.sortedInsert] at h; exact Or.inl h
  | cons hd tl ih =>
    intro h
    unfold Value.sortedInsert at h
    split_ifs at h
    · -- k < hd.1: result is (k, v) :: hd :: tl
      simp at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · -- k = hd.1: result is (k, v) :: tl
      simp at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · -- k > hd.1: result is hd :: sortedInsert k v tl
      simp at h
      rcases h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · rcases ih h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- If `vs.get? k = none`, then no entry in `vs.vals` has key `k`. -/
private theorem ne_of_get?_none (v : Value) (k : Int) (kv : Int × Val) :
    v.get? k = none → kv ∈ v.vals → kv.1 ≠ k := by
  intro hget hmem heq
  unfold Value.get? at hget
  rw [List.lookup_eq_none_iff] at hget
  have hbne := hget kv hmem
  rw [heq] at hbne
  -- hbne : k != k, which is false
  grind

theorem sc_implies_nested_correct (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2 := by
  intro h
  induction' h with kk f val' d' v' h_match h_nested h_dn h_vn _ ih_nested ih
  · intro kv hkv
    -- (∅ : Value).vals = []
    simp [Value.vals] at hkv
  · intro kv hkv
    -- kv is in (v'.insert kk val').vals = sortedInsert kk val' v'.vals
    have hkv' : kv ∈ Value.sortedInsert kk val' v'.vals := by
      rcases v' with ⟨vs⟩
      simp [Value.insert, Value.vals] at hkv
      exact hkv
    rcases mem_value_sortedInsert kk val' v'.vals kv hkv' with heq | hmem
    · -- kv = (kk, val')
      subst heq
      -- Need: lookup kk in (d'.insert kk f).fields = some f
      have hlk : (d'.insert kk f).fields.lookup kk = some f := by
        unfold Desc.insert
        cases d'
        simp +decide [Desc.fields]
        have h_lookup_insert : ∀ (l : List (Int × Field)),
            List.lookup kk (Desc.sortedInsert kk f l) = some f := by
          intros l
          induction' l with hd tl ih2 <;> simp_all +decide [ Desc.sortedInsert ]
          grind
        exact h_lookup_insert _
      show nestedCorrect (d'.insert kk f) kk val'
      unfold nestedCorrect
      rw [hlk]
      cases f with
      | msg d'' =>
        cases val' with
        | msg v'' => exact h_nested d'' v'' rfl rfl
        | bool _ => exact trivial
        | int _ => exact trivial
        | missing => exact trivial
      | bool => exact trivial
      | int => exact trivial
    · -- kv ∈ v'.vals; kv.1 ≠ kk
      have hne : kv.1 ≠ kk := ne_of_get?_none v' kk kv h_vn hmem
      have hnc : nestedCorrect d' kv.1 kv.2 := ih kv hmem
      have hlk_eq : (d'.insert kk f).fields.lookup kv.1 = d'.fields.lookup kv.1 := by
        cases d' with | mk fs =>
        simp [Desc.insert, Desc.fields]
        exact sortedInsert_lookup_ne_desc kv.1 kk f fs hne
      show nestedCorrect (d'.insert kk f) kv.1 kv.2
      unfold nestedCorrect at hnc ⊢
      rw [hlk_eq]
      exact hnc

/-- Combined: all four properties of schema correctness. -/
theorem sc_implies_properties (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by
  intro h
  exact ⟨sc_implies_val_in_desc d v h,
         sc_implies_desc_in_val d v h,
         sc_implies_no_missing d v h,
         sc_implies_nested_correct d v h⟩

/-- Combined with typed witnesses. -/
theorem sc_implies_properties_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f ∧ fieldValMatch f val) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val ∧ fieldValMatch f val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by
  intro h
  exact ⟨sc_implies_val_in_desc_typed d v h,
         sc_implies_desc_in_val_typed d v h,
         sc_implies_no_missing d v h,
         sc_implies_nested_correct d v h⟩

/-- Erasing a key after inserting it (when not previously present) recovers the
    original descriptor field list. -/
private theorem desc_sortedErase_sortedInsert (k : Int) (f : Field)
    (l : List (Int × Field)) (h : List.lookup k l = none) :
    Desc.sortedErase k (Desc.sortedInsert k f l) = l := by
  induction' l with hd tl ih
  · simp [Desc.sortedInsert, Desc.sortedErase]
  · unfold Desc.sortedInsert
    by_cases hk1 : k < hd.1
    · simp [hk1, Desc.sortedErase]
    · by_cases hk2 : k = hd.1
      · exfalso
        rw [show List.lookup k (hd :: tl) = some hd.2 from by simp [List.lookup, hk2]] at h
        cases h
      · have hbeq : ¬ (k == hd.1) := by rw [beq_eq_decide]; simp [hk2]
        simp [hk1, hbeq, Desc.sortedErase]
        have htl : List.lookup k tl = none := by
          rw [show List.lookup k (hd :: tl) = List.lookup k tl from by
            simp [List.lookup]
            rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hk2]]] at h
          exact h
        rw [ih htl]

theorem sc_delete_key (d : Desc) (v : Value) (k : Int) :
    ⟨ v ∷ d ⟩ → ⟨ v.erase k ∷ d.erase k ⟩ := by sorry

theorem sc_dom_eq (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → (v.vals.map Prod.fst) = (d.fields.map Prod.fst) := by
      -- We'll use induction on the structure of the schema correctness.
      intro h
      induction' h with d v h_ind;
      · native_decide +revert;
      · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
        have h_keys_eq : ∀ (l : List (Int × Val)) (l' : List (Int × Field)), List.map Prod.fst l = List.map Prod.fst l' → List.map Prod.fst (Value.sortedInsert d h_ind l) = List.map Prod.fst (Desc.sortedInsert d v l') := by
          intros l l' h_keys_eq;
          induction' l with l_head l_tail ih generalizing l' <;> induction' l' with l'_head l'_tail ih' <;> simp_all +decide [ Value.sortedInsert, Desc.sortedInsert ];
          grind +splitImp;
        exact h_keys_eq _ _ h₆

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

theorem sc_sco (v : Value) (d : Desc) : ⟨ v ∷ d ⟩ ↔ ⟪ v ∷ d ⟫ := by
  constructor <;> intro h;
  · induction' h with k f val d v ih;
    · constructor;
    · exact SchemaCorrectOrdered.insert k f val d v ih ‹_› ‹_› ‹_› ‹_›;
  · induction h;
    · constructor;
    · constructor <;> assumption

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
    Compatible d1 d2 v1 v2 → d1 = d2 → v1 = v2 := by
      intro hc
      induction hc with
      | refl _ _ _ _ _ => intro _; rfl
      | add d1' v1' d2' v2' k f1 f2 vv1 vv2 _ _ _ hv1n hv2n hd1n hd2n hveq hfeq ih =>
        intro hd
        subst hveq; subst hfeq
        have hd_eq : d1' = d2' := by
          cases d1' with | mk fs1 =>
          cases d2' with | mk fs2 =>
          have hd' : Desc.sortedInsert k f1 fs1 = Desc.sortedInsert k f1 fs2 := by
            unfold Desc.insert at hd
            simp [Desc.fields] at hd
            exact hd
          have hd1_lookup : List.lookup k fs1 = none := hd1n
          have hd2_lookup : List.lookup k fs2 = none := hd2n
          have heq : Desc.sortedErase k (Desc.sortedInsert k f1 fs1)
                     = Desc.sortedErase k (Desc.sortedInsert k f1 fs2) := by rw [hd']
          rw [desc_sortedErase_sortedInsert k f1 fs1 hd1_lookup,
              desc_sortedErase_sortedInsert k f1 fs2 hd2_lookup] at heq
          exact congrArg Desc.mk heq
        have hv_eq := ih hd_eq
        exact congrArg (fun v => v.insert k vv1) hv_eq

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
    v.get? k = none → valList (d.insert k f) v = valList d v := by
      intro h;
      -- Since `v` does not contain `k`, the filtering condition `valListFilterP (d.insert k f)` is equivalent to `valListFilterP d`.
      have h_filter : ∀ kv ∈ v.vals, valListFilterP (d.insert k f) kv = valListFilterP d kv := by
        intro kv hk; by_cases h : kv.1 = k <;> simp +decide [ h, valListFilterP ] ;
        · have h_filter : ∀ {k : ℤ} {v : Value}, v.get? k = none → ∀ kv ∈ v.vals, kv.1 ≠ k := by
            intros k v hv kv hk; contrapose! hv; simp_all +decide [ Value.get? ] ;
            exact ⟨ kv.2, hv ▸ hk ⟩;
          exact False.elim <| h_filter ‹_› kv hk h;
        · rw [ show List.lookup kv.1 ( d.insert k f ).fields = List.lookup kv.1 d.fields from by
                rw [ Desc.insert ];
                have h_sortedInsert : ∀ (l : List (ℤ × Field)) (k : ℤ) (f : Field), kv.1 ≠ k → List.lookup kv.1 (Desc.sortedInsert k f l) = List.lookup kv.1 l := by
                  intros l k f hk; induction' l with l ih generalizing k f <;> simp +decide [ *, Desc.sortedInsert ] ;
                  grind +splitImp;
                exact h_sortedInsert _ _ _ h ];
      exact List.filter_congr fun x hx => h_filter x hx

theorem valList_elem_of (v : Value) (d : Desc) (k : Int) (val : Val) :
    v.WF → (k, val) ∈ valList d v → v.get? k = some val := by
  intro hwf hin
  unfold valList at hin
  -- Membership in the filtered list implies membership in `v.vals`.
  have hmem : (k, val) ∈ v.vals := (List.mem_filter.mp hin).1
  -- Unique-key list with `(k, val) ∈ vs` implies `vs.lookup k = some val`.
  have h_lookup_mem : ∀ (l : List (Int × Val)), (l.map Prod.fst).Nodup →
      (k, val) ∈ l → l.lookup k = some val := by
    intro l hnd hmem
    induction' l with hd tl ih
    · cases hmem
    · obtain ⟨k', val'⟩ := hd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with heq | hin'
      · -- (k, val) is the head: heq : (k, val) = (k', val')
        cases heq
        simp [List.lookup_cons]
      · -- (k, val) is in the tail
        have hne : k ≠ k' := by
          intro heq
          exact hnd.1 (List.mem_map.mpr ⟨(k, val), hin', heq⟩)
        simp only [List.lookup_cons,
                   show (k == k') = false from by simp [hne]]
        exact ih hnd.2 hin'
  -- Apply to v's underlying list.
  obtain ⟨vs⟩ := v
  unfold Value.get?
  show vs.lookup k = some val
  have hnd : (vs.map Prod.fst).Nodup := hwf.2
  exact h_lookup_mem vs hnd hmem

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
    d.WF → v.get? k = none → (valueWf d v ↔ valueWf (d.erase k) v) := by
  intro hwf hno
  -- All keys in `v.vals` differ from `k`.
  have h_keys_ne : ∀ kv ∈ v.vals, kv.1 ≠ k := by
    intro kv hkv hk
    unfold Value.get? at hno
    rw [List.lookup_eq_none_iff] at hno
    have := hno kv hkv
    -- this : k != kv.1 (as Prop, i.e. (k != kv.1) = true)
    simp_all
  -- For any key `k' ≠ k`, lookup in `d.fields` and `(d.erase k).fields` agree.
  have h_lookup_eq : ∀ k', k' ≠ k → (d.erase k).fields.lookup k' = d.fields.lookup k' := by
    intro k' hne
    have := Desc.get?_erase_ne d k k' hwf (Ne.symm hne)
    unfold Desc.get? at this
    exact this
  -- Destructure to expose underlying lists, then induct.
  rcases v with ⟨vs⟩
  rcases d with ⟨fs⟩
  simp only [Value.vals] at h_keys_ne
  -- Specialize the lookup-equality helper to the destructured form.
  have h_lookup_eq' : ∀ k', k' ≠ k → (Desc.sortedErase k fs).lookup k' = fs.lookup k' := by
    intro k' hne
    have := h_lookup_eq k' hne
    simpa [Desc.fields, Desc.erase] using this
  -- Generalize the accumulator and prove by induction.
  suffices h : ∀ (vs : List (Int × Val)) (acc : Prop),
      (∀ kv ∈ vs, kv.1 ≠ k) →
      (valWfFoldList fs vs acc ↔ valWfFoldList (Desc.sortedErase k fs) vs acc) by
    -- Both sides reduce to `valWfFoldList _ vs True` since both `Desc` and `Value` are now in
    -- constructor form.
    show valWfFoldList fs vs True ↔ valWfFoldList (Desc.sortedErase k fs) vs True
    exact h vs True h_keys_ne
  intro vs acc hkeys
  induction' vs with hd tl ih generalizing acc
  · exact Iff.rfl
  · obtain ⟨k', val⟩ := hd
    have hne : k' ≠ k := hkeys (k', val) (List.mem_cons_self)
    have hne_keys_tl : ∀ kv ∈ tl, kv.1 ≠ k :=
      fun kv hkv => hkeys kv (List.mem_cons_of_mem _ hkv)
    -- The two folds will agree if `valWfFold` agrees on the head.
    have hfold_eq : valWfFold fs k' val acc
                   = valWfFold (Desc.sortedErase k fs) k' val acc := by
      unfold valWfFold
      rw [h_lookup_eq' k' hne]
    show valWfFoldList fs tl (valWfFold fs k' val acc)
       ↔ valWfFoldList (Desc.sortedErase k fs) tl (valWfFold (Desc.sortedErase k fs) k' val acc)
    rw [hfold_eq]
    exact ih _ hne_keys_tl

theorem willEncode_weaken (kv : Int × Val) (d : Desc) (k : Int) (v : Value) :
    d.WF →
    kv ∈ valList (d.erase k) v →
    (willEncode d kv ↔ willEncode (d.erase k) kv) := by
  intro hwf hin
  -- Membership in `valList (d.erase k) v` implies the filter holds.
  have hfilt : valListFilterP (d.erase k) kv = true := by
    unfold valList at hin
    exact (List.mem_filter.mp hin).2
  -- The filter requires the lookup to be `some _` and val ≠ missing.
  have hlk_erase : ∃ f, (d.erase k).fields.lookup kv.1 = some f := by
    unfold valListFilterP at hfilt
    -- Make the lookup non-`none` from the filter, then extract a witness.
    have h_ne_none : (d.erase k).fields.lookup kv.1 ≠ none := by
      intro hnone
      rw [hnone] at hfilt
      simp at hfilt
    exact Option.ne_none_iff_exists'.mp h_ne_none
  -- Show kv.1 ≠ k.
  have hne : kv.1 ≠ k := by
    intro heq
    obtain ⟨f, hf⟩ := hlk_erase
    rw [heq] at hf
    have := Desc.get?_erase_same d k hwf
    unfold Desc.get? at this
    rw [this] at hf
    cases hf
  -- Now, lookup in `d.fields` and `(d.erase k).fields` agree at `kv.1`.
  have hlk_eq : (d.erase k).fields.lookup kv.1 = d.fields.lookup kv.1 := by
    have := Desc.get?_erase_ne d k kv.1 hwf (Ne.symm hne)
    unfold Desc.get? at this
    exact this
  -- And `valWf d kv ↔ valWf (d.erase k) kv`.
  have hvwf_eq : valWf d kv = valWf (d.erase k) kv := by
    unfold valWf valWfFold
    rw [hlk_eq]
  -- Conclude.
  unfold willEncode
  constructor
  · rintro ⟨f, hf, hwfd⟩
    refine ⟨f, ?_, ?_⟩
    · rw [hlk_eq, hf]
    · rw [← hvwf_eq]; exact hwfd
  · rintro ⟨f, hf, hwfd⟩
    refine ⟨f, ?_, ?_⟩
    · rw [← hlk_eq, hf]
    · rw [hvwf_eq]; exact hwfd

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