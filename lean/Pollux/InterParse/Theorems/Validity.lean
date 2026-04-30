/-
  Pollux.InterParse.Theorems.Validity — Validity (`valid'`) and encoding-length
  decomposition lemmas.
-/
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer

namespace Pollux.InterParse

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

end Pollux.InterParse
