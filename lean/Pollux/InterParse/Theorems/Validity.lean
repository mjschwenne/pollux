/-
  Pollux.InterParse.Theorems.Validity — Validity (`valid'`) and encoding-length
  decomposition lemmas.
-/
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer

namespace Pollux.InterParse

/-! ## Validity lemmas -/

/-- The per-entry validity predicate `P fs k v` extracted from `valid'Fold`.
    By construction `valid'Fold fs k v acc` is exactly `P fs k v ∧ acc`. -/
private def vFoldP (fs : List (Int × Field)) (k : Int) (v : Val) : Prop :=
  match v with
  | .bool _ => fs.lookup k = some .bool
  | .int _  => fs.lookup k = some .int
  | .msg value => ∃ d, fs.lookup k = some (.msg d) ∧ valid' d value
  | .missing => True

/-- `valid'Fold fs k v acc` decomposes into `vFoldP fs k v ∧ acc`. -/
private theorem valid'Fold_eq (fs : List (Int × Field)) (k : Int) (v : Val) (acc : Prop) :
    valid'Fold fs k v acc ↔ vFoldP fs k v ∧ acc := by
  cases v
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- `valid'FoldList` is the conjunction over its entries. -/
private def vListP (fs : List (Int × Field)) : List (Int × Val) → Prop
  | [] => True
  | (k, v) :: rest => vFoldP fs k v ∧ vListP fs rest

/-- `valid'FoldList` decomposes via `vListP` and `acc`. -/
private theorem valid'FoldList_eq (fs : List (Int × Field)) :
    ∀ (l : List (Int × Val)) (acc : Prop),
    valid'FoldList fs l acc ↔ vListP fs l ∧ acc := by
  intros l
  induction l with
  | nil =>
    intro acc
    show acc ↔ True ∧ acc
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons hd tl ih =>
    intro acc
    obtain ⟨k, v⟩ := hd
    show valid'FoldList fs tl (valid'Fold fs k v acc) ↔
         (vFoldP fs k v ∧ vListP fs tl) ∧ acc
    rw [ih (valid'Fold fs k v acc), valid'Fold_eq fs k v acc]
    constructor
    · rintro ⟨htl, hp, hacc⟩; exact ⟨⟨hp, htl⟩, hacc⟩
    · rintro ⟨⟨hp, htl⟩, hacc⟩; exact ⟨htl, hp, hacc⟩

/-- Decomposition of `vListP` over `sortedInsert` when the key is fresh. -/
private theorem vListP_sortedInsert
    (fs : List (Int × Field)) (k : Int) (val : Val) :
    ∀ (l : List (Int × Val)),
    (∀ x ∈ l, x.1 ≠ k) →
    (vListP fs (Value.sortedInsert k val l) ↔
     vFoldP fs k val ∧ vListP fs l) := by
  intro l hfresh
  induction l with
  | nil =>
    show vListP fs [(k, val)] ↔ vFoldP fs k val ∧ True
    exact Iff.rfl
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    have hk' : k' ≠ k := by
      have := hfresh (k', v') (by simp)
      simpa using this
    have htl_fresh : ∀ x ∈ tl, x.1 ≠ k := fun x hx => hfresh x (by simp [hx])
    by_cases h1 : k < k'
    · show vListP fs (Value.sortedInsert k val ((k', v') :: tl)) ↔
           vFoldP fs k val ∧ vListP fs ((k', v') :: tl)
      rw [show Value.sortedInsert k val ((k', v') :: tl) =
             (k, val) :: (k', v') :: tl from by
        show (if k < k' then (k, val) :: (k', v') :: tl
              else if k == k' then (k, val) :: tl
              else (k', v') :: Value.sortedInsert k val tl) =
             (k, val) :: (k', v') :: tl
        simp [h1]]
      exact Iff.rfl
    · have hbeq : ¬ (k == k') := by
        rw [beq_eq_decide]; simp [hk'.symm]
      show vListP fs (Value.sortedInsert k val ((k', v') :: tl)) ↔
           vFoldP fs k val ∧ vListP fs ((k', v') :: tl)
      rw [show Value.sortedInsert k val ((k', v') :: tl) =
             (k', v') :: Value.sortedInsert k val tl from by
        show (if k < k' then (k, val) :: (k', v') :: tl
              else if k == k' then (k, val) :: tl
              else (k', v') :: Value.sortedInsert k val tl) =
             (k', v') :: Value.sortedInsert k val tl
        simp [h1, hbeq]]
      show vFoldP fs k' v' ∧ vListP fs (Value.sortedInsert k val tl) ↔
           vFoldP fs k val ∧ vFoldP fs k' v' ∧ vListP fs tl
      rw [ih htl_fresh]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩

/-- Decomposition of `valid'FoldList` over `sortedInsert` when the key is fresh. -/
private theorem valid'FoldList_sortedInsert
    (fs : List (Int × Field)) (k : Int) (val : Val) :
    ∀ (l : List (Int × Val)),
    (∀ x ∈ l, x.1 ≠ k) →
    (valid'FoldList fs (Value.sortedInsert k val l) True ↔
     valid'Fold fs k val True ∧ valid'FoldList fs l True) := by
  intro l hfresh
  rw [valid'FoldList_eq fs (Value.sortedInsert k val l) True,
      valid'FoldList_eq fs l True,
      valid'Fold_eq fs k val True,
      vListP_sortedInsert fs k val l hfresh]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, trivial⟩, h2, trivial⟩
  · rintro ⟨⟨h1, _⟩, h2, _⟩; exact ⟨⟨h1, h2⟩, trivial⟩

theorem validDropFirst (d : Desc) (z : Int) (val : Val) (v : Value) :
    v.get? z = none →
    valid' d (v.insert z val) → valid' d v := by
  intro hnone hvalid
  have hfresh : ∀ x ∈ v.vals, x.1 ≠ z := by
    intro x hx
    unfold Value.get? at hnone
    rw [List.lookup_eq_none_iff] at hnone
    have := hnone x hx
    grind
  rcases d with ⟨fs⟩
  rcases v with ⟨vs⟩
  have h2 : valid'FoldList fs (Value.sortedInsert z val vs) True := hvalid
  rw [valid'FoldList_sortedInsert fs z val vs hfresh] at h2
  exact h2.2

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
          · intro x; specialize ih z val ( fun a b hab => h_none a b ( Or.inr hab ) ) h_not_in_l.2; simp_all +decide ;
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
     valid'Fold d.fields k val True ∧ valid' d v) := by
  intro hnone
  have hfresh : ∀ x ∈ v.vals, x.1 ≠ k := by
    intro x hx
    unfold Value.get? at hnone
    rw [List.lookup_eq_none_iff] at hnone
    have := hnone x hx
    grind
  rcases d with ⟨fs⟩
  rcases v with ⟨vs⟩
  show valid'FoldList fs (Value.sortedInsert k val vs) True ↔
       valid'Fold fs k val True ∧ valid'FoldList fs vs True
  rw [valid'FoldList_sortedInsert fs k val vs hfresh]

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

/-- Per-entry validity extraction: if a list is `valid'`, then each entry
    in the list satisfies `valid'Fold`. -/
theorem valid'FoldList_mem (fs : List (Int × Field)) :
    ∀ (vs : List (Int × Val)) (z : Int) (val : Val),
    valid'FoldList fs vs True →
    (z, val) ∈ vs →
    valid'Fold fs z val True := by
  intro vs
  induction vs with
  | nil => intros z val _ hmem; cases hmem
  | cons hd tl ih =>
    intros z val hvalid hmem
    obtain ⟨k', v'⟩ := hd
    rw [valid'FoldList_eq fs ((k', v') :: tl) True] at hvalid
    obtain ⟨⟨hp_hd, hp_tl⟩, _⟩ := hvalid
    cases hmem with
    | head =>
      rw [valid'Fold_eq fs z val True]
      exact ⟨hp_hd, trivial⟩
    | tail _ hmem' =>
      apply ih z val _ hmem'
      rw [valid'FoldList_eq fs tl True]
      exact ⟨hp_tl, trivial⟩

end Pollux.InterParse
