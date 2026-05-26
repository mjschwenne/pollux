/-
  Helper lemmas for the IdCompatible round-trip proof.
-/
import Pollux.InterParse.Theorems.IdCompatible
import Pollux.InterParse.Theorems.Validity

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
  intro h_lookup h_valid
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

/-! ## Transform irrelevance and prepend lemmas -/

/-- `idCompatTransformAux` is independent of entries at keys not in `ds`. -/
theorem idCompatTransformAux_erase_irrelevant
    (ds : List (Int × Field)) (v : Value) (k : Int) :
    List.lookup k ds = none →
    idCompatTransformAux ds (v.erase k) = idCompatTransformAux ds v := by
  intro hk
  induction' ds with hd tl ih generalizing v k
  · rfl
  · have hne : k ≠ hd.1 := by
      intro heq; subst heq; simp [List.lookup] at hk
    have htl : List.lookup k tl = none := by
      have : List.lookup k (hd :: tl) =
        (match k == hd.1 with | true => some hd.2 | false => List.lookup k tl) := rfl
      rw [this, show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hne]] at hk
      simpa using hk
    unfold idCompatTransformAux
    have hlookup_eq : (v.erase k).get? hd.1 = v.get? hd.1 := by
      cases v with | mk vs =>
      simp [Value.erase, Value.get?, Value.vals]
      exact value_lookup_sortedErase_ne k hd.1 vs (Ne.symm hne)
    simp only [hlookup_eq]
    congr 1
    exact ih v k htl

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

/-! ## Drop-all-missing helper -/

/-
If the descriptor is empty and all entries in the value are `.missing`,
    dropping each entry gives `IdCompatible ∅ v ∅`.
-/
theorem idcompat_drop_all_missing (vs : List (Int × Val)) :
    (∀ kv ∈ vs, kv.2 = Val.missing) →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    (List.map Prod.fst vs).Nodup →
    IdCompatible (∅ : Desc) (.mk vs) (∅ : Value) := by
  induction' vs with kv vs ih;
  · exact fun _ _ _ => IdCompatible.emp;
  · intro h1 h2 h3;
    -- Apply the induction hypothesis to the rest of the list.
    have h_ind : IdCompatible ∅ (Value.mk vs) ∅ := by
      aesop;
    convert IdCompatible.drop ∅ ( Value.mk vs ) ∅ kv.1 kv.2 h_ind _ _ using 1;
    · unfold Value.insert;
      unfold Value.sortedInsert; aesop;
    · -- The empty list's lookup function returns none for any key.
      simp [Desc.get?];
      simp +decide [ Desc.fields ];
    · simp_all +decide [ Value.get? ];
      exact fun a b hab => ne_of_lt ( h2.1 a b hab )

/-! ## IdCompatible constructors for sorted-cons form

When the inserted key is below all existing keys, `Desc.insert` / `Value.insert`
act as a list cons. The following "smart constructors" expose this so that
case lemmas operating on raw lists can apply the inductive constructors
without unfolding `sortedInsert` repeatedly. -/

/-- addMissing when the insert acts as a cons (key below all others). -/
theorem IdCompatible.addMissing_cons (k : Int) (f : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, f) :: rest_ds)) (.mk vs) (.mk ((k, Val.missing) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k f = Desc.mk ((k, f) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk v2).insert k Val.missing = Value.mk ((k, Val.missing) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2]
  exact IdCompatible.addMissing _ _ _ k f ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- drop when the insert acts as a cons. -/
theorem IdCompatible.drop_cons (k : Int) (val : Val)
    (ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (ih : IdCompatible (.mk ds) (.mk rest_vs) (.mk v2))
    (h1 : ds.lookup k = none)
    (h2 : rest_vs.lookup k = none) :
    IdCompatible (.mk ds) (.mk ((k, val) :: rest_vs)) (.mk v2) := by
  have h_eq : (Value.mk rest_vs).insert k val = Value.mk ((k, val) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  rw [← h_eq]
  exact IdCompatible.drop _ _ _ k val ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2])

/-- insertInt when the insert acts as a cons. -/
theorem IdCompatible.insertInt_cons (k : Int) (z : Int)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .int) :: rest_ds)) (.mk ((k, .int z) :: rest_vs))
      (.mk ((k, .int z) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k .int = Desc.mk ((k, .int) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.int z) = Value.mk ((k, .int z) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.int z) = Value.mk ((k, .int z) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertInt _ _ _ k z ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- insertBool when the insert acts as a cons. -/
theorem IdCompatible.insertBool_cons (k : Int) (b : Bool)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .bool) :: rest_ds)) (.mk ((k, .bool b) :: rest_vs))
      (.mk ((k, .bool b) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k .bool = Desc.mk ((k, .bool) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.bool b) = Value.mk ((k, .bool b) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.bool b) = Value.mk ((k, .bool b) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertBool _ _ _ k b ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- insertMsg when the insert acts as a cons. -/
theorem IdCompatible.insertMsg_cons (k : Int) (d' : Desc) (v1' v2' : Value)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (ih_inner : IdCompatible d' v1' v2')
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .msg d') :: rest_ds)) (.mk ((k, .msg v1') :: rest_vs))
      (.mk ((k, .msg v2') :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k (.msg d') = Desc.mk ((k, .msg d') :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.msg v1') = Value.mk ((k, .msg v1') :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.msg v2') = Value.mk ((k, .msg v2') :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertMsg _ _ _ _ _ _ k ih ih_inner
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- inputMissing when the insert acts as a cons. -/
theorem IdCompatible.inputMissing_cons (k : Int) (f : Field)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, f) :: rest_ds)) (.mk ((k, .missing) :: rest_vs))
      (.mk ((k, .missing) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k f = Desc.mk ((k, f) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k .missing = Value.mk ((k, .missing) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k .missing = Value.mk ((k, .missing) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.inputMissing _ _ _ k f ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

end Pollux.InterParse
