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

/-- If `k0` is less than every key in `l`, then `sortedInsert` produces a
    cons. (Desc version.) -/
private theorem desc_sortedInsert_cons_of_lt_all (k0 : Int) (f : Field)
    (l : List (Int × Field)) :
    (∀ p ∈ l, k0 < p.1) →
    Desc.sortedInsert k0 f l = (k0, f) :: l := by
  intro h
  cases l with
  | nil => rfl
  | cons hd tl =>
    have : k0 < hd.1 := h hd (List.mem_cons_self)
    simp [Desc.sortedInsert, this]

/-- If `k0` is less than every key in `l`, then `sortedInsert` produces a
    cons. (Value version.) -/
private theorem value_sortedInsert_cons_of_lt_all (k0 : Int) (val : Val)
    (l : List (Int × Val)) :
    (∀ p ∈ l, k0 < p.1) →
    Value.sortedInsert k0 val l = (k0, val) :: l := by
  intro h
  cases l with
  | nil => rfl
  | cons hd tl =>
    have : k0 < hd.1 := h hd (List.mem_cons_self)
    simp [Value.sortedInsert, this]

/-- Erasing commutes with inserting a different key, on a sorted list.
    (Desc version.) -/
theorem desc_sortedErase_sortedInsert_ne
    (k k0 : Int) (f : Field) (l : List (Int × Field)) :
    k ≠ k0 →
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) l →
    Desc.sortedErase k (Desc.sortedInsert k0 f l) =
      Desc.sortedInsert k0 f (Desc.sortedErase k l) := by
  intro hne hsorted
  induction l with
  | nil =>
    -- sortedInsert k0 f [] = [(k0, f)]; erase by k ≠ k0 leaves it
    have hk_ne_k0_beq : (k == k0) = false := by
      rw [beq_eq_decide]; simp [hne]
    by_cases hk : k < k0
    · simp [Desc.sortedInsert, Desc.sortedErase, hk_ne_k0_beq, hk]
    · simp [Desc.sortedInsert, Desc.sortedErase, hk_ne_k0_beq, hk]
  | cons hd tl ih =>
    have hsorted_tl : List.Pairwise (fun a b : Int × Field => a.1 < b.1) tl :=
      hsorted.tail
    have hk_ne_k0_beq : (k == k0) = false := by
      rw [beq_eq_decide]; simp [hne]
    -- Case split on k0 vs hd.1, then on k vs hd.1
    by_cases hk0_lt : k0 < hd.1
    · -- sortedInsert k0 f (hd :: tl) = (k0, f) :: hd :: tl
      by_cases hk_lt_k0 : k < k0
      · -- k < k0 < hd.1
        have hk_lt_hd : k < hd.1 := lt_trans hk_lt_k0 hk0_lt
        have hk_ne_hd : (k == hd.1) = false := by
          rw [beq_eq_decide]; simp; omega
        simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk_ne_k0_beq,
              hk_lt_k0, hk_ne_hd, hk_lt_hd]
      · by_cases hk_lt_hd : k < hd.1
        · have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk_ne_k0_beq,
                hk_lt_k0, hk_ne_hd, hk_lt_hd]
        · by_cases hk_eq_hd : k = hd.1
          · have hk_beq_hd : (k == hd.1) = true := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            -- LHS = (k0, f) :: tl
            -- RHS = sortedInsert k0 f tl; need k0 < everything in tl
            have htl_gt_k0 : ∀ p ∈ tl, k0 < p.1 := by
              intro p hp
              have := List.rel_of_pairwise_cons hsorted hp
              omega
            simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk_ne_k0_beq,
                  hk_lt_k0, hk_beq_hd,
                  desc_sortedInsert_cons_of_lt_all k0 f tl htl_gt_k0]
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk_ne_k0_beq,
                  hk_lt_k0, hk_ne_hd, hk_lt_hd]
    · by_cases hk0_eq_hd : k0 = hd.1
      · -- sortedInsert k0 f (hd :: tl) = (k0, f) :: tl
        have hk0_beq_hd : (k0 == hd.1) = true := by
          rw [beq_eq_decide]; simp [hk0_eq_hd]
        by_cases hk_lt_k0 : k < k0
        · have hk_lt_hd : k < hd.1 := by omega
          have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          have hk0_nlt_hd : ¬ k0 < hd.1 := by omega
          simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk0_beq_hd,
                hk_ne_k0_beq, hk_lt_k0, hk_ne_hd, hk_lt_hd, hk0_nlt_hd]
        · have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          have hk_nlt_hd : ¬ k < hd.1 := by omega
          simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk0_beq_hd,
                hk_ne_k0_beq, hk_lt_k0, hk_ne_hd, hk_nlt_hd]
      · -- k0 > hd.1
        have hk0_gt_hd : hd.1 < k0 := by
          have : ¬ (k0 < hd.1 ∨ k0 = hd.1) := by tauto
          omega
        have hk0_ne_beq_hd : (k0 == hd.1) = false := by
          rw [beq_eq_decide]; simp [hk0_eq_hd]
        by_cases hk_eq_hd : k = hd.1
        · have hk_beq_hd : (k == hd.1) = true := by
            rw [beq_eq_decide]; simp [hk_eq_hd]
          -- LHS: sortedErase k (hd :: sortedInsert k0 f tl) = sortedInsert k0 f tl
          -- RHS: sortedInsert k0 f (sortedErase k (hd :: tl)) = sortedInsert k0 f tl
          simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk0_ne_beq_hd, hk_beq_hd]
        · by_cases hk_lt_hd : k < hd.1
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            -- LHS: hd :: sortedInsert k0 f tl
            -- RHS: sortedInsert k0 f (hd :: tl)
            simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk0_ne_beq_hd,
                  hk_ne_hd, hk_lt_hd]
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            have hk_nlt_hd : ¬ k < hd.1 := hk_lt_hd
            -- LHS: hd :: sortedErase k (sortedInsert k0 f tl)
            -- RHS: hd :: sortedInsert k0 f (sortedErase k tl)
            simp [Desc.sortedInsert, Desc.sortedErase, hk0_lt, hk0_ne_beq_hd,
                  hk_ne_hd, hk_nlt_hd, ih hsorted_tl]

/-- Erasing commutes with inserting a different key, on a sorted list.
    (Value version.) -/
theorem value_sortedErase_sortedInsert_ne
    (k k0 : Int) (val : Val) (l : List (Int × Val)) :
    k ≠ k0 →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) l →
    Value.sortedErase k (Value.sortedInsert k0 val l) =
      Value.sortedInsert k0 val (Value.sortedErase k l) := by
  intro hne hsorted
  induction l with
  | nil =>
    have hk_ne_k0_beq : (k == k0) = false := by
      rw [beq_eq_decide]; simp [hne]
    by_cases hk : k < k0
    · simp [Value.sortedInsert, Value.sortedErase, hk_ne_k0_beq, hk]
    · simp [Value.sortedInsert, Value.sortedErase, hk_ne_k0_beq, hk]
  | cons hd tl ih =>
    have hsorted_tl : List.Pairwise (fun a b : Int × Val => a.1 < b.1) tl :=
      hsorted.tail
    have hk_ne_k0_beq : (k == k0) = false := by
      rw [beq_eq_decide]; simp [hne]
    by_cases hk0_lt : k0 < hd.1
    · by_cases hk_lt_k0 : k < k0
      · have hk_lt_hd : k < hd.1 := lt_trans hk_lt_k0 hk0_lt
        have hk_ne_hd : (k == hd.1) = false := by
          rw [beq_eq_decide]; simp; omega
        simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk_ne_k0_beq,
              hk_lt_k0, hk_ne_hd, hk_lt_hd]
      · by_cases hk_lt_hd : k < hd.1
        · have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk_ne_k0_beq,
                hk_lt_k0, hk_ne_hd, hk_lt_hd]
        · by_cases hk_eq_hd : k = hd.1
          · have hk_beq_hd : (k == hd.1) = true := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            have htl_gt_k0 : ∀ p ∈ tl, k0 < p.1 := by
              intro p hp
              have := List.rel_of_pairwise_cons hsorted hp
              omega
            simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk_ne_k0_beq,
                  hk_lt_k0, hk_beq_hd,
                  value_sortedInsert_cons_of_lt_all k0 val tl htl_gt_k0]
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk_ne_k0_beq,
                  hk_lt_k0, hk_ne_hd, hk_lt_hd]
    · by_cases hk0_eq_hd : k0 = hd.1
      · have hk0_beq_hd : (k0 == hd.1) = true := by
          rw [beq_eq_decide]; simp [hk0_eq_hd]
        by_cases hk_lt_k0 : k < k0
        · have hk_lt_hd : k < hd.1 := by omega
          have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          have hk0_nlt_hd : ¬ k0 < hd.1 := by omega
          simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk0_beq_hd,
                hk_ne_k0_beq, hk_lt_k0, hk_ne_hd, hk_lt_hd, hk0_nlt_hd]
        · have hk_ne_hd : (k == hd.1) = false := by
            rw [beq_eq_decide]; simp; omega
          have hk_nlt_hd : ¬ k < hd.1 := by omega
          simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk0_beq_hd,
                hk_ne_k0_beq, hk_lt_k0, hk_ne_hd, hk_nlt_hd]
      · have hk0_gt_hd : hd.1 < k0 := by
          have : ¬ (k0 < hd.1 ∨ k0 = hd.1) := by tauto
          omega
        have hk0_ne_beq_hd : (k0 == hd.1) = false := by
          rw [beq_eq_decide]; simp [hk0_eq_hd]
        by_cases hk_eq_hd : k = hd.1
        · have hk_beq_hd : (k == hd.1) = true := by
            rw [beq_eq_decide]; simp [hk_eq_hd]
          simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk0_ne_beq_hd, hk_beq_hd]
        · by_cases hk_lt_hd : k < hd.1
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk0_ne_beq_hd,
                  hk_ne_hd, hk_lt_hd]
          · have hk_ne_hd : (k == hd.1) = false := by
              rw [beq_eq_decide]; simp [hk_eq_hd]
            have hk_nlt_hd : ¬ k < hd.1 := hk_lt_hd
            simp [Value.sortedInsert, Value.sortedErase, hk0_lt, hk0_ne_beq_hd,
                  hk_ne_hd, hk_nlt_hd, ih hsorted_tl]

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
