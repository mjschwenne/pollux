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
              (expose_names; exact Nat.succ_inj.mp
                  (congrArg Nat.succ (h_split (Value.sortedInsert k val ih) k_1 val_1 (valueEncLen'Fold d.fields l.1 l.2 0))));
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

/-! ## Generic `valid'Fold` / `valid'FoldList` manipulators -/

/-- Extract the accumulated predicate from `valid'Fold`. -/
theorem valid'Fold_extract (ds : List (Int × Field)) (k : Int) (v : Val) (P : Prop) :
    valid'Fold ds k v P → P := by
  unfold valid'Fold; cases v <;> simp

/-- Extract the accumulated predicate from `valid'FoldList`. -/
theorem valid'FoldList_extract (ds : List (Int × Field)) (vs : List (Int × Val)) (P : Prop) :
    valid'FoldList ds vs P → P := by
  induction vs generalizing P with
  | nil => exact id
  | cons hd tl ih =>
    intro h; exact valid'Fold_extract ds hd.1 hd.2 _ (ih _ h)

/-- Weaken the accumulator in `valid'Fold`. -/
theorem valid'Fold_weaken (ds : List (Int × Field)) (k : Int) (v : Val) (P Q : Prop) :
    (P → Q) → valid'Fold ds k v P → valid'Fold ds k v Q := by
  intro hPQ; unfold valid'Fold; cases v <;> simp <;> tauto

/-- Weaken the accumulator in `valid'FoldList`. -/
theorem valid'FoldList_weaken (ds : List (Int × Field)) (vs : List (Int × Val))
    (P Q : Prop) :
    (P → Q) → valid'FoldList ds vs P → valid'FoldList ds vs Q := by
  induction vs generalizing P Q with
  | nil => exact id
  | cons hd tl ih =>
    intro hPQ h
    show valid'FoldList ds tl (valid'Fold ds hd.1 hd.2 Q)
    exact ih _ _ (valid'Fold_weaken ds hd.1 hd.2 P Q hPQ) h

/-- Dropping the head preserves `valid'`. -/
theorem valid'_cons (ds : List (Int × Field)) (kv : Int × Val) (vs : List (Int × Val)) :
    valid'FoldList ds (kv :: vs) True → valid'FoldList ds vs True := by
  intro h; unfold valid'FoldList at h
  exact valid'FoldList_weaken ds vs _ _ (fun _ => trivial) h

/-- Extract info about the head entry from `valid'`. -/
theorem valid'_entry_head (ds : List (Int × Field)) (kv : Int × Val) (vs : List (Int × Val)) :
    valid'FoldList ds (kv :: vs) True → valid'Fold ds kv.1 kv.2 True := by
  intro h; unfold valid'FoldList at h
  exact valid'FoldList_extract ds vs _ h

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

/-! ## `valueWf` decomposition lemmas -/

/-- `valWfFold` is monotone in `acc`: it can be split into a closed-form
    "per-entry" predicate (`valWfFold _ _ _ True`) and `acc`. -/
private theorem valWfFold_split (fs : List (Int × Field)) (k : Int) (v : Val)
    (acc : Prop) :
    valWfFold fs k v acc ↔ valWfFold fs k v True ∧ acc := by
  unfold valWfFold
  cases fs.lookup k with
  | none =>
    simp only []
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | some f =>
    cases f <;> cases v <;>
      first
        | exact ⟨fun h => ⟨h, trivial⟩, fun h => h.elim⟩
        | (simp only [and_assoc]; tauto)

/-- `valWfFoldList fs vs acc` decomposes into per-entry constraints AND `acc`. -/
private theorem valWfFoldList_decomp (fs : List (Int × Field)) :
    ∀ (vs : List (Int × Val)) (acc : Prop),
    valWfFoldList fs vs acc ↔
      (∀ kv : Int × Val, kv ∈ vs → valWfFold fs kv.1 kv.2 True) ∧ acc := by
  intro vs
  induction vs with
  | nil =>
    intro acc
    show acc ↔
      (∀ kv : Int × Val, kv ∈ ([] : List (Int × Val)) → valWfFold fs kv.1 kv.2 True) ∧ acc
    simp
  | cons hd tl ih =>
    intro acc
    obtain ⟨k, v⟩ := hd
    show valWfFoldList fs tl (valWfFold fs k v acc) ↔
      (∀ kv : Int × Val, kv ∈ ((k, v) :: tl) → valWfFold fs kv.1 kv.2 True) ∧ acc
    rw [ih (valWfFold fs k v acc), valWfFold_split fs k v acc]
    constructor
    · rintro ⟨htl, hhd, hacc⟩
      refine ⟨?_, hacc⟩
      intro kv hkv
      cases List.mem_cons.mp hkv with
      | inl heq => subst heq; exact hhd
      | inr htl' => exact htl _ htl'
    · rintro ⟨hall, hacc⟩
      refine ⟨?_, hall (k, v) List.mem_cons_self, hacc⟩
      intro kv hkv
      exact hall kv (List.mem_cons_of_mem _ hkv)

/-- Helper: extract `valWfFold` for a specific entry from `valueWf`. -/
theorem valueWf_mem (d : Desc) (v : Value) :
    valueWf d v →
    ∀ (k : Int) (val : Val), (k, val) ∈ v.vals →
    valWfFold d.fields k val True := by
  intro hwf k val hmem
  rcases d with ⟨fs⟩
  rcases v with ⟨vs⟩
  have hwf' : valWfFoldList fs vs True := hwf
  exact ((valWfFoldList_decomp fs vs True).mp hwf').1 (k, val) hmem

/-- `valueWf` is invariant under erasing a key that doesn't appear in `v`. -/
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

/-! ## Generic `valWfFold` / `valWfFoldList` manipulators

These mirror the `valid'Fold` / `valid'FoldList` manipulators above.  They are
what lets the `IdCompatible` round-trip proof run off `valueWf` alone: on keys
present in the descriptor `valueWf` is strictly stronger than `valid'`, and on
keys absent from it `valueWf` imposes no constraint at all (which is exactly
the `IdCompatible.drop` case). -/

/-- Extract the accumulated predicate from `valWfFold`. -/
theorem valWfFold_extract (ds : List (Int × Field)) (k : Int) (v : Val) (P : Prop) :
    valWfFold ds k v P → P :=
  fun h => ((valWfFold_split ds k v P).mp h).2

/-- Extract the accumulated predicate from `valWfFoldList`. -/
theorem valWfFoldList_extract (ds : List (Int × Field)) (vs : List (Int × Val))
    (P : Prop) :
    valWfFoldList ds vs P → P :=
  fun h => ((valWfFoldList_decomp ds vs P).mp h).2

/-- Weaken the accumulator in `valWfFold`. -/
theorem valWfFold_weaken (ds : List (Int × Field)) (k : Int) (v : Val) (P Q : Prop) :
    (P → Q) → valWfFold ds k v P → valWfFold ds k v Q := by
  intro hPQ h
  rw [valWfFold_split] at h ⊢
  exact ⟨h.1, hPQ h.2⟩

/-- Weaken the accumulator in `valWfFoldList`. -/
theorem valWfFoldList_weaken (ds : List (Int × Field)) (vs : List (Int × Val))
    (P Q : Prop) :
    (P → Q) → valWfFoldList ds vs P → valWfFoldList ds vs Q := by
  intro hPQ h
  rw [valWfFoldList_decomp] at h ⊢
  exact ⟨h.1, hPQ h.2⟩

/-- Dropping the head entry preserves `valueWf`.  Mirrors `valid'_cons`. -/
theorem valueWf_cons (ds : List (Int × Field)) (kv : Int × Val) (vs : List (Int × Val)) :
    valWfFoldList ds (kv :: vs) True → valWfFoldList ds vs True := by
  intro h
  rw [valWfFoldList_decomp] at h ⊢
  exact ⟨fun kv' hkv' => h.1 kv' (List.mem_cons_of_mem _ hkv'), trivial⟩

/-- Extract info about the head entry from `valueWf`.  Mirrors `valid'_entry_head`. -/
theorem valueWf_entry_head (ds : List (Int × Field)) (kv : Int × Val)
    (vs : List (Int × Val)) :
    valWfFoldList ds (kv :: vs) True → valWfFold ds kv.1 kv.2 True := by
  intro h
  rw [valWfFoldList_decomp] at h
  exact h.1 kv List.mem_cons_self

/-- A successful `List.lookup` witnesses membership. -/
theorem mem_of_lookup_val (vs : List (Int × Val)) (k : Int) (val : Val) :
    vs.lookup k = some val → (k, val) ∈ vs := by
  induction vs with
  | nil => intro h; cases h
  | cons hd tl ih =>
    intro h; rw [List.lookup_cons] at h
    by_cases hkk : k = hd.1
    · subst hkk; simp at h; subst h; exact List.mem_cons_self
    · rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hkk]] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Extract the `valWfFold` constraint at a particular key.  The `valueWf`
    counterpart of `valid'_entry_at_key`. -/
theorem valueWf_at_key (d : Desc) (v : Value) (k : Int) (val : Val) :
    valueWf d v → v.get? k = some val → valWfFold d.fields k val True := by
  intro hwf hget
  rcases v with ⟨vs⟩
  simp only [Value.get?, Value.vals] at hget ⊢
  exact valueWf_mem d (.mk vs) hwf k val (mem_of_lookup_val vs k val hget)

/-! ### Per-entry field/value matching

`valid'Fold` states the field type directly, so callers read it off with an
`injection`.  `valWfFold` instead matches on the pair `(lookup, val)`, and is
vacuous when the lookup is `none`.  These lemmas recover the `valid'Fold`-style
interface *given* that the key is present in the descriptor, which is the only
situation the callers use it in. -/

/-- A `.bool` entry at a key present in the descriptor forces a `.bool` field. -/
theorem valWfFold_bool_field (fs : List (Int × Field)) (k : Int) (b : Bool)
    (f : Field) (P : Prop) :
    fs.lookup k = some f → valWfFold fs k (.bool b) P → f = .bool := by
  intro hlk h
  unfold valWfFold at h
  rw [hlk] at h
  cases f with
  | bool => rfl
  | int => exact h.elim
  | msg _ => exact h.elim

/-- An `.int` entry at a key present in the descriptor forces an `.int` field. -/
theorem valWfFold_int_field (fs : List (Int × Field)) (k : Int) (z : Int)
    (f : Field) (P : Prop) :
    fs.lookup k = some f → valWfFold fs k (.int z) P → f = .int := by
  intro hlk h
  unfold valWfFold at h
  rw [hlk] at h
  cases f with
  | bool => exact h.elim
  | int => rfl
  | msg _ => exact h.elim

/-- A `.msg` entry at a key present in the descriptor forces a `.msg` field,
    and hands back the nested `valueWf`. -/
theorem valWfFold_msg_field (fs : List (Int × Field)) (k : Int) (v' : Value)
    (f : Field) (P : Prop) :
    fs.lookup k = some f → valWfFold fs k (.msg v') P →
    ∃ d', f = .msg d' ∧ valueWf d' v' := by
  intro hlk h
  unfold valWfFold at h
  rw [hlk] at h
  cases f with
  | bool => exact h.elim
  | int => exact h.elim
  | msg d' => exact ⟨d', rfl, h.2.2.2⟩

/-- `valueWf` rejects `.missing` at a key that *is* in the descriptor.  This is
    why `IdCompatible.inputMissing` is unreachable from the top-level theorem;
    see the note in `IdCompatible.lean`. -/
theorem valWfFold_missing_elim (fs : List (Int × Field)) (k : Int) (f : Field)
    (P : Prop) :
    fs.lookup k = some f → valWfFold fs k .missing P → False := by
  intro hlk h
  unfold valWfFold at h
  rw [hlk] at h
  cases f <;> exact h.elim

/-- `valWfFold` only inspects the descriptor through `lookup`, so agreeing
    lookups can be swapped.  Mirrors `valid'Fold_lookup_congr`. -/
theorem valWfFold_lookup_congr (fs gs : List (Int × Field)) (k : Int) (v : Val)
    (P : Prop) :
    fs.lookup k = gs.lookup k → valWfFold fs k v P → valWfFold gs k v P := by
  intro hlookup h
  unfold valWfFold at h ⊢
  rw [← hlookup]
  exact h

/-- If `fs` and `gs` agree on the lookup of every key in `vs`, then
    `valWfFoldList` can switch between them.  Mirrors
    `valid'FoldList_lookup_congr`. -/
theorem valWfFoldList_lookup_congr (fs gs : List (Int × Field))
    (vs : List (Int × Val)) (P : Prop) :
    (∀ kv ∈ vs, fs.lookup kv.1 = gs.lookup kv.1) →
    valWfFoldList fs vs P → valWfFoldList gs vs P := by
  intro hlookup h
  rw [valWfFoldList_decomp] at h ⊢
  exact ⟨fun kv hkv =>
    valWfFold_lookup_congr fs gs kv.1 kv.2 True (hlookup kv hkv) (h.1 kv hkv), h.2⟩

/-- Removing the head field of the descriptor, when its key is below every key
    in `vs`, doesn't change `valueWf`.  Mirrors `valid'_drop_head_ds`. -/
theorem valueWf_drop_head_ds (k₀ : Int) (f₀ : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) :
    (∀ kv ∈ vs, k₀ < kv.1) →
    valWfFoldList ((k₀, f₀) :: rest_ds) vs True →
    valWfFoldList rest_ds vs True := by
  intro hgt
  apply valWfFoldList_lookup_congr
  intro kv hkv
  have hne : ¬ (kv.1 = k₀) := ne_of_gt (hgt kv hkv)
  rw [List.lookup_cons, show (kv.1 == k₀) = false from by rw [beq_eq_decide]; simp [hne]]

/-- Adding a fresh head field to the descriptor, when its key is below every key
    in `vs`, doesn't change `valueWf`.  Mirrors `valid'_add_head_ds`. -/
theorem valueWf_add_head_ds (k₀ : Int) (f₀ : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) :
    (∀ kv ∈ vs, k₀ < kv.1) →
    valWfFoldList rest_ds vs True →
    valWfFoldList ((k₀, f₀) :: rest_ds) vs True := by
  intro hgt
  apply valWfFoldList_lookup_congr
  intro kv hkv
  have hne : ¬ (kv.1 = k₀) := ne_of_gt (hgt kv hkv)
  rw [List.lookup_cons, show (kv.1 == k₀) = false from by rw [beq_eq_decide]; simp [hne]]

end Pollux.InterParse
