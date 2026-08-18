/-
  Helper lemmas for the IdCompatible round-trip proof.
-/
import Pollux.InterParse.Theorems.IdCompatible
import Pollux.InterParse.Theorems.Validity
import Pollux.InterParse.Theorems.ValList

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
  intro h_lookup h_valid ; simp_all +decide;
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
  have h_keys_eq : (idCompatTransformAux rest_ds v).map Prod.fst = rest_ds.map Prod.fst :=
    idCompatTransformAux_keys rest_ds v
  intro h p hp;
  have := List.mem_map.mp ( h_keys_eq ▸ List.mem_map.mpr ⟨ p, hp, rfl ⟩ ) ; aesop;

/-! ## Drop-all-missing helper -/

/-- Against the empty descriptor every entry is dropped, whatever it holds.
    `IdCompatible.drop` places no constraint on the dropped value, so this needs
    no validity hypothesis — which is what lets the round-trip theorem run off
    `valueWf` alone (`valueWf` is vacuous on keys outside the descriptor). -/
theorem idcompat_drop_all (vs : List (Int × Val)) :
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    (List.map Prod.fst vs).Nodup →
    IdCompatible (∅ : Desc) (.mk vs) (∅ : Value) := by
  induction' vs with kv vs ih;
  · exact fun _ _ => IdCompatible.emp;
  · intro h2 h3;
    -- Apply the induction hypothesis to the rest of the list.
    have h_ind : IdCompatible ∅ (Value.mk vs) ∅ := ih h2.tail h3.of_cons
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

/-! ## listToValue / entryTransform / idCompatTransform bridge -/

/-
`entryTransform` preserves the key of a pair.
-/
theorem entryTransform_fst (d : Desc) (kv : Int × Val) :
    (entryTransform d kv).1 = kv.1 := by
  rcases kv with ⟨ k, v ⟩;
  rcases v with ( _ | _ | _ | _ ) <;> unfold entryTransform <;> aesop

/-- Lookup in the mapped list: `entryTransform` applies `idCompatTransform`
    to message values whose key has a message field in the descriptor. -/
theorem lookup_map_entryTransform (d : Desc) (vs : List (Int × Val)) (k : Int) :
    (vs.map (entryTransform d)).lookup k =
    match vs.lookup k with
    | none => none
    | some (.msg v') =>
      match d.fields.lookup k with
      | some (.msg d') => some (.msg (idCompatTransform d' v'))
      | _ => some (.msg v')
    | some val => some val := by
  induction vs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', val⟩ := hd
    simp only [List.map_cons]
    have hfst : (entryTransform d (k', val)).1 = k' := entryTransform_fst d (k', val)
    rw [List.lookup_cons, hfst, List.lookup_cons]
    by_cases h : k = k'
    · subst h; simp
      cases val with
      | bool b => simp [entryTransform]
      | int z => simp [entryTransform]
      | missing => simp [entryTransform]
      | msg v' =>
        simp [entryTransform]
        cases hf : d.fields.lookup k with
        | none => rfl
        | some f =>
          cases f with
          | bool => rfl
          | int => rfl
          | msg d' => rfl
    · simp only [show (k == k') = false from by rw [beq_eq_decide]; simp [h]]
      exact ih

/-
Characterize (valList d v).lookup k in terms of d.fields.lookup and v.get?.
-/
theorem valList_lookup_characterize (d : Desc) (v : Value) (k : Int) :
    v.WF →
    (valList d v).lookup k =
    match d.fields.lookup k, v.get? k with
    | none, _ => none
    | _, none => none
    | some _, some .missing => none
    | some _, some val => some val := by
  intro hv;
  have h_filter : ∀ (l : List (Int × Val)), List.Nodup (List.map Prod.fst l) → ∀ (k : Int), List.lookup k (List.filter (fun kv => match List.lookup kv.1 d.fields, kv.2 with | some val, Val.missing => false | none, x => false | x, x_1 => true) l) = match List.lookup k d.fields, List.lookup k l with | none, x => none | x, none => none | some val, some Val.missing => none | some val, some val_1 => some val_1 := by
    intro l hl k;
    induction' l with kv l ihizing k;
    · cases List.lookup k d.fields <;> simp +decide;
    · grind;
  convert h_filter v.vals _ k;
  convert hv.2 using 1;
  unfold Value.NodupKeys; aesop;

/-- Extract valid' constraint for a particular key-value pair. -/
private theorem valid'_entry_at_key (d : Desc) (v : Value) (k : Int) (val : Val)
    (hvalid : valid' d v) (hget : v.get? k = some val) :
    valid'Fold d.fields k val True := by
  rcases d with ⟨fs⟩; rcases v with ⟨vs⟩
  simp only [valid'] at hvalid; simp only [Value.get?, Value.vals] at hget
  have hmem : (k, val) ∈ vs := by
    have : ∀ (l : List (Int × Val)), l.lookup k = some val → (k, val) ∈ l := by
      intro l; induction l with
      | nil => intro h; cases h
      | cons hd tl ih =>
        intro h; rw [List.lookup_cons] at h
        by_cases hkk : k = hd.1
        · subst hkk; simp at h; subst h; exact List.mem_cons_self
        · rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hkk]] at h
          exact List.mem_cons_of_mem _ (ih h)
    exact this vs hget
  exact valid'FoldList_mem fs vs k val hvalid hmem

/-- The merged lookup of `listToValue` applied to the transformed valList
    agrees with the `idCompatTransform` lookup at every key. -/
theorem listToValue_entryTransform_lookup (d : Desc) (v : Value) (k : Int) :
    d.AllWF → v.AllWF → valueWf d v →
    (listToValue d ((valList d v).map (entryTransform d))).get? k =
    (idCompatTransform d v).get? k := by
  intro hd hv hvwf
  have h_d_wf : d.WF := hd.1
  have h_v_wf : v.WF := hv.1
  rcases d with ⟨fs⟩
  have h_nodup : (fs.map Prod.fst).Nodup := h_d_wf.2
  have h_lhs : (listToValue (.mk fs) ((valList (.mk fs) v).map (entryTransform (.mk fs)))).get? k =
    mergeFieldVal (fs.lookup k) ((List.map (entryTransform (.mk fs)) (valList (.mk fs) v)).lookup k) := by
    show (listMerge mergeFieldVal fs _).lookup k = _
    exact listMerge_mergeFieldVal_lookup fs _ k h_nodup
  rw [h_lhs, lookup_map_entryTransform (.mk fs), valList_lookup_characterize (.mk fs) v k h_v_wf]
  simp only [Desc.fields]
  cases hdk : fs.lookup k with
  | none =>
    have : (idCompatTransform (.mk fs) v).get? k = none :=
      idCompatTransform_get?_none (.mk fs) v k (by simp [Desc.get?, Desc.fields, hdk])
    rw [this]; cases v.get? k <;> rfl
  | some f =>
    rw [idCompatTransform_get?_some (.mk fs) v k f h_d_wf (by simp [Desc.get?, Desc.fields, hdk])]
    cases hvk : v.get? k with
    | none => cases f <;> simp [mergeFieldVal]
    | some val =>
      cases val with
      | missing => cases f <;> simp [mergeFieldVal]
      | bool b =>
        have hentry := valueWf_at_key (.mk fs) v k (.bool b) hvwf hvk
        simp only [Desc.fields] at hentry
        have hf := valWfFold_bool_field fs k b f True hdk hentry; subst hf
        simp [mergeFieldVal]
      | int z =>
        have hentry := valueWf_at_key (.mk fs) v k (.int z) hvwf hvk
        simp only [Desc.fields] at hentry
        have hf := valWfFold_int_field fs k z f True hdk hentry; subst hf
        simp [mergeFieldVal]
      | msg v' =>
        have hentry := valueWf_at_key (.mk fs) v k (.msg v') hvwf hvk
        simp only [Desc.fields] at hentry
        obtain ⟨d', hd', _⟩ := valWfFold_msg_field fs k v' f True hdk hentry
        subst hd'
        simp [mergeFieldVal]

/-- The LHS value is well-formed. -/
theorem listToValue_entryTransform_wf (d : Desc) (v : Value) :
    d.AllWF →
    (listToValue d ((valList d v).map (entryTransform d))).WF := by
  intro hd
  unfold listToValue
  rcases d with ⟨fs⟩
  have ⟨⟨hs, hnd⟩, _⟩ := hd
  simp only [Desc.fields]
  exact Pollux.InterParse.listMerge_mergeFieldVal_wf fs _ hs hnd

/-- The key equality: the round-trip via `listToValue ∘ map entryTransform ∘ valList`
    equals `idCompatTransform`. -/
theorem listToValue_map_eq_idCompatTransform (d : Desc) (v : Value) :
    d.AllWF → v.AllWF → valueWf d v →
    listToValue d ((valList d v).map (entryTransform d)) = idCompatTransform d v := by
  intro hd hv hwf
  apply Value.ext_lookup
  · exact listToValue_entryTransform_wf d v hd
  · exact idCompatTransform_wf d v hd.1
  · intro k; exact listToValue_entryTransform_lookup d v k hd hv hwf

end Pollux.InterParse