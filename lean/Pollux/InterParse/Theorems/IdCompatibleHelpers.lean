/-
  Helper lemmas for the IdCompatible round-trip proof.
-/
import Pollux.InterParse.Theorems.IdCompatible

namespace Pollux.InterParse

/-! ## valid' decomposition lemmas -/

/-
An entry checked against an empty descriptor must be `.missing`.
-/
theorem valid'Fold_empty_missing (k : Int) (v : Val) :
    valid'Fold [] k v True → v = Val.missing := by
  cases v <;> simp +decide [ valid'Fold ] at *

/-
If all keys in `vs` satisfy `fs.lookup k = gs.lookup k`, then
    `valid'Fold` can switch between `fs` and `gs`.
-/
theorem valid'Fold_lookup_congr (fs gs : List (Int × Field)) (k : Int) (v : Val) (P : Prop) :
    fs.lookup k = gs.lookup k →
    valid'Fold fs k v P → valid'Fold gs k v P := by
  unfold valid'Fold;
  cases v <;> aesop ( simp_config := { singlePass := true } )

/-
If every key in `vs` has the same lookup in `fs` and `gs`, then
    `valid'FoldList` can switch between `fs` and `gs`.
-/
theorem valid'FoldList_lookup_congr (fs gs : List (Int × Field)) (vs : List (Int × Val)) (P : Prop) :
    (∀ kv ∈ vs, fs.lookup kv.1 = gs.lookup kv.1) →
    valid'FoldList fs vs P → valid'FoldList gs vs P := by
  intro h_lookup h_valid ; simp_all +decide [ valid'FoldList ];
  induction' vs with kv vs ih generalizing P <;> simp_all +decide [ valid'FoldList ];
  convert ih _ _ h_valid using 1;
  · exact ⟨ fun h => valid'Fold_lookup_congr _ _ _ _ _ ( h_lookup _ _ ( Or.inl rfl ) |> Eq.symm ) h, fun h => valid'Fold_lookup_congr _ _ _ _ _ ( h_lookup _ _ ( Or.inl rfl ) ) h ⟩;
  · exact fun a b hab => h_lookup a b <| Or.inr hab

/-
When all keys in `vs` are `> k₀`, dropping the head `(k₀, f₀)` from `ds`
    doesn't change `valid'`.
-/
theorem valid'_drop_head_ds (k₀ : Int) (f₀ : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) :
    (∀ kv ∈ vs, k₀ < kv.1) →
    valid'FoldList ((k₀, f₀) :: rest_ds) vs True →
    valid'FoldList rest_ds vs True := by
  intro h_all_gt_k₀ h_valid'FoldList
  apply valid'FoldList_lookup_congr;
  any_goals assumption;
  grind +splitImp

/-
When all keys in `vs` are `> k₀`, adding the head `(k₀, f₀)` to `ds`
    doesn't change `valid'`.
-/
theorem valid'_add_head_ds (k₀ : Int) (f₀ : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) :
    (∀ kv ∈ vs, k₀ < kv.1) →
    valid'FoldList rest_ds vs True →
    valid'FoldList ((k₀, f₀) :: rest_ds) vs True := by
  intro h₁ h₂;
  apply valid'FoldList_lookup_congr;
  any_goals assumption;
  grind +qlia

/-! ## Lookup lemmas -/

/-
If `k` is less than every key in a sorted list, lookup returns `none`.
-/
theorem lookup_none_of_lt_all_field (k : Int) (l : List (Int × Field)) :
    (∀ p ∈ l, k < p.1) → l.lookup k = none := by
  induction l <;> aesop

/-
If `k` is less than every key in a sorted list, lookup returns `none`.
-/
theorem lookup_none_of_lt_all_val (k : Int) (l : List (Int × Val)) :
    (∀ p ∈ l, k < p.1) → l.lookup k = none := by
  grind +locals

/-
In a sorted list, the head key is less than all tail keys,
    so the head key doesn't appear in the tail.
-/
theorem lookup_head_not_in_tail_field (k : Int) (f : Field) (rest : List (Int × Field)) :
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) ((k, f) :: rest) →
    rest.lookup k = none := by
  intro h;
  apply lookup_none_of_lt_all_field;
  have := List.pairwise_cons.mp h; aesop;

/-
In a sorted list, the head key is less than all tail keys,
    so the head key doesn't appear in the tail.
-/
theorem lookup_head_not_in_tail_val (k : Int) (v : Val) (rest : List (Int × Val)) :
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k, v) :: rest) →
    rest.lookup k = none := by
  exact fun h => lookup_none_of_lt_all_val k rest fun p hp => by induction' rest with p rest ih <;> aesop;

/-! ## Transform prepend lemma -/

/-
If `k` is less than all keys in `ds`, the transform ignores the extra entry at `k`.
-/
theorem idCompatTransformAux_prepend_lt
    (ds : List (Int × Field)) (k : Int) (val : Val) (rest : List (Int × Val)) :
    (∀ p ∈ ds, k < p.1) →
    idCompatTransformAux ds (Value.mk ((k, val) :: rest)) =
    idCompatTransformAux ds (Value.mk rest) := by
  -- Apply the idCompatTransformAux_erase_irrelevant theorem to rewrite the goal in terms of the erased value.
  intro hds
  have h_erase : idCompatTransformAux ds ((Value.mk ((k, val) :: rest)).erase k) = idCompatTransformAux ds (Value.mk ((k, val) :: rest)) := by
    -- Apply the idCompatTransformAux_erase_irrelevant theorem to conclude the proof.
    apply idCompatTransformAux_erase_irrelevant; exact lookup_none_of_lt_all_field k ds hds;
  convert h_erase.symm using 2;
  exact Eq.symm ( by rw [ show ( Value.mk ( ( k, val ) :: rest ) ).erase k = Value.mk ( Value.sortedErase k ( ( k, val ) :: rest ) ) by rfl ] ; simp +decide [ Value.sortedErase ] )

/-! ## Value erase head -/

/-
Erasing the head key from a sorted value gives the tail.
-/
theorem value_erase_head (k : Int) (v : Val) (rest : List (Int × Val)) :
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k, v) :: rest) →
    Value.sortedErase k ((k, v) :: rest) = rest := by
  -- By definition of `Value.sortedErase`, if the first element is equal to `k`, then it returns the rest of the list.
  simp [Value.sortedErase]

/-! ## Transform keys in tail -/

/-
The keys of `idCompatTransformAux rest_ds v` are all `> k` when
    `rest_ds` is sorted and all keys in `rest_ds` are `> k`.
-/
theorem idCompatTransformAux_keys_gt (rest_ds : List (Int × Field)) (v : Value) (k : Int) :
    (∀ p ∈ rest_ds, k < p.1) →
    ∀ p ∈ idCompatTransformAux rest_ds v, k < p.1 := by
  -- By idCompatTransformAux_keys, the keys of the transform result are the same as the keys of rest_ds.
  have h_keys_eq : (idCompatTransformAux rest_ds v).map Prod.fst = rest_ds.map Prod.fst := by
    exact?;
  intro h p hp;
  have := List.mem_map.mp ( h_keys_eq ▸ List.mem_map.mpr ⟨ p, hp, rfl ⟩ ) ; aesop;

end Pollux.InterParse