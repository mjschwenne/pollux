/-
  Pollux.InterParse.Theorems.SortedHelpers — Lemmas about `sortedInsert` and
  `sortedErase` on the underlying lists of `Desc` and `Value`.

  These are all generic, schema-independent map-on-sorted-list facts. They are
  used throughout the SchemaCorrect / Compatible / serializer proofs.
-/
import Pollux.InterParse.Descriptor

namespace Pollux.InterParse

/-- Lookup at a different key is unaffected by `Value.sortedInsert`. -/
theorem sortedInsert_lookup_ne_val (k k' : Int) (v : Val) (l : List (Int × Val)) :
    k ≠ k' → List.lookup k (Value.sortedInsert k' v l) = List.lookup k l := by
  intro hne; induction l with
  | nil => simp [Value.sortedInsert, hne]
  | cons hd tl ih =>
    unfold Value.sortedInsert; split_ifs <;> simp_all [List.lookup]
    · rw [show (k == k') = false from by rw [beq_eq_decide]; simp [hne]]
    · grind

/-- Lookup at a different key is unaffected by `Desc.sortedInsert`. -/
theorem sortedInsert_lookup_ne_desc (k k' : Int) (f : Field) (l : List (Int × Field)) :
    k ≠ k' → List.lookup k (Desc.sortedInsert k' f l) = List.lookup k l := by
  intro hne; induction l with
  | nil => simp [Desc.sortedInsert, hne]
  | cons hd tl ih =>
    unfold Desc.sortedInsert; split_ifs <;> simp_all [List.lookup]
    · rw [show (k == k') = false from by rw [beq_eq_decide]; simp [hne]]
    · grind

/-- Membership in a `Value.sortedInsert`: the inserted pair, or one of the
    originals. -/
theorem mem_value_sortedInsert (k : Int) (v : Val)
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
theorem ne_of_get?_none (v : Value) (k : Int) (kv : Int × Val) :
    v.get? k = none → kv ∈ v.vals → kv.1 ≠ k := by
  intro hget hmem heq
  unfold Value.get? at hget
  rw [List.lookup_eq_none_iff] at hget
  have hbne := hget kv hmem
  rw [heq] at hbne
  -- hbne : k != k, which is false
  grind

/-- Erasing a key after inserting it (when not previously present) recovers the
    original descriptor field list. -/
theorem desc_sortedErase_sortedInsert (k : Int) (f : Field)
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

/-- Erasing a key after inserting the same key is the identity, when the key
    was not previously present. (Desc version.) -/
theorem desc_sortedErase_sortedInsert_same
    (k : Int) (f : Field) (l : List (Int × Field)) :
    l.lookup k = none →
    Desc.sortedErase k (Desc.sortedInsert k f l) = l :=
  desc_sortedErase_sortedInsert k f l

/-- Erasing a key after inserting the same key is the identity, when the key
    was not previously present. (Value version.) -/
theorem value_sortedErase_sortedInsert_same
    (k : Int) (val : Val) (l : List (Int × Val)) :
    l.lookup k = none →
    Value.sortedErase k (Value.sortedInsert k val l) = l := by
  intro h
  induction' l with hd tl ih
  · simp [Value.sortedInsert, Value.sortedErase]
  · unfold Value.sortedInsert
    by_cases hk1 : k < hd.1
    · simp [hk1, Value.sortedErase]
    · by_cases hk2 : k = hd.1
      · exfalso
        rw [show List.lookup k (hd :: tl) = some hd.2 from by simp [List.lookup, hk2]] at h
        cases h
      · have hbeq : ¬ (k == hd.1) := by rw [beq_eq_decide]; simp [hk2]
        simp [hk1, hbeq, Value.sortedErase]
        have htl : List.lookup k tl = none := by
          rw [show List.lookup k (hd :: tl) = List.lookup k tl from by
            simp [List.lookup]
            rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hk2]]] at h
          exact h
        rw [ih htl]

/-- Erasing commutes with inserting a different key, on a sorted list.
    (Desc version.) -/
theorem desc_sortedErase_sortedInsert_ne
    (k k0 : Int) (f : Field) (l : List (Int × Field)) :
    k ≠ k0 →
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) l →
    Desc.sortedErase k (Desc.sortedInsert k0 f l) =
      Desc.sortedInsert k0 f (Desc.sortedErase k l) := by
  sorry

/-- Erasing commutes with inserting a different key, on a sorted list.
    (Value version.) -/
theorem value_sortedErase_sortedInsert_ne
    (k k0 : Int) (val : Val) (l : List (Int × Val)) :
    k ≠ k0 →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) l →
    Value.sortedErase k (Value.sortedInsert k0 val l) =
      Value.sortedInsert k0 val (Value.sortedErase k l) := by
  sorry

/-- Lookup after `sortedErase` at a different key. (Desc version, no WF.) -/
theorem desc_lookup_sortedErase_ne
    (k k0 : Int) (l : List (Int × Field)) :
    k0 ≠ k →
    List.lookup k0 (Desc.sortedErase k l) = List.lookup k0 l := by
  intro hne
  induction l with
  | nil => simp [Desc.sortedErase]
  | cons hd tl ih =>
    unfold Desc.sortedErase
    by_cases h1 : k == hd.1
    · rw [if_pos h1]
      rw [beq_iff_eq] at h1
      have hk0_ne_hd : (k0 == hd.1) = false := by
        rw [beq_eq_decide]; simp; rw [← h1]; exact hne
      simp [List.lookup, hk0_ne_hd]
    · rw [if_neg h1]
      split_ifs with h2
      · rfl
      · by_cases h3 : k0 == hd.1
        · simp [List.lookup, h3]
        · simp [List.lookup, h3]; exact ih

/-- Lookup after `sortedErase` at a different key. (Value version.) -/
theorem value_lookup_sortedErase_ne
    (k k0 : Int) (l : List (Int × Val)) :
    k0 ≠ k →
    List.lookup k0 (Value.sortedErase k l) = List.lookup k0 l := by
  intro hne
  induction l with
  | nil => simp [Value.sortedErase]
  | cons hd tl ih =>
    unfold Value.sortedErase
    by_cases h1 : k == hd.1
    · rw [if_pos h1]
      rw [beq_iff_eq] at h1
      have hk0_ne_hd : (k0 == hd.1) = false := by
        rw [beq_eq_decide]; simp; rw [← h1]; exact hne
      simp [List.lookup, hk0_ne_hd]
    · rw [if_neg h1]
      split_ifs with h2
      · rfl
      · by_cases h3 : k0 == hd.1
        · simp [List.lookup, h3]
        · simp [List.lookup, h3]; exact ih

end Pollux.InterParse
