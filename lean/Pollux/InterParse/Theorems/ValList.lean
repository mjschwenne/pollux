/-
  Pollux.InterParse.Theorems.ValList — Theorems about `valList` and
  `listToValue`: filtering, membership, and the SC-roundtrip lemmas.
-/
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Pollux.InterParse.Theorems.SchemaCorrect
import Pollux.InterParse.Theorems.Compatible

namespace Pollux.InterParse

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
      · cases heq
        simp
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

/-! ### Helpers for `list_to_value_id` -/

/-- `mergeFieldVal` returns `none` whenever the field side is `none`. -/
private theorem mergeFieldVal_none_left (v : Option Val) :
    mergeFieldVal none v = none := by
  cases v <;> rfl

/-- `listMerge mergeFieldVal` simplifies: the `fromM2Only` part is always empty
    because `mergeFieldVal none _ = none`. -/
private theorem listMerge_mergeFieldVal_eq (fs : List (Int × Field))
    (vs : List (Int × Val)) :
    listMerge mergeFieldVal fs vs =
    fs.filterMap (fun kv : Int × Field =>
      (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1)) := by
  unfold listMerge
  suffices h : vs.filterMap (fun kv : Int × Val =>
        if (fs.lookup kv.1).isSome then none
        else (mergeFieldVal none (some kv.2)).map (Prod.mk kv.1)) = [] by
    simp [h]
  apply List.filterMap_eq_nil_iff.mpr
  intro x _
  by_cases hsome : (fs.lookup x.1).isSome
  · simp [hsome]
  · simp [hsome, mergeFieldVal_none_left]

/-- Lookup distributes over `listMerge mergeFieldVal` when the field list has
    no duplicate keys. -/
private theorem listMerge_mergeFieldVal_lookup (fs : List (Int × Field))
    (vs : List (Int × Val)) (k : Int)
    (hnd : (fs.map Prod.fst).Nodup) :
    (listMerge mergeFieldVal fs vs).lookup k =
    mergeFieldVal (fs.lookup k) (vs.lookup k) := by
  rw [listMerge_mergeFieldVal_eq]
  induction fs with
  | nil =>
    show ([] : List (Int × Val)).lookup k = mergeFieldVal none (vs.lookup k)
    rw [mergeFieldVal_none_left]; rfl
  | cons hd tl ih =>
    obtain ⟨k', f'⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk_notin, hndtl⟩ := hnd
    cases h_merge : mergeFieldVal (some f') (vs.lookup k') with
    | none =>
      have hfm : (List.filterMap (fun kv : Int × Field =>
          (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1)) ((k', f') :: tl)) =
            List.filterMap (fun kv : Int × Field =>
          (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1)) tl := by
        simp [h_merge]
      rw [hfm, List.lookup_cons]
      by_cases hkk' : k = k'
      · subst hkk'
        rw [show (k == k) = true from by simp]
        rw [ih hndtl, h_merge]
        have htl_none : tl.lookup k = none := by
          rw [List.lookup_eq_none_iff]
          intro x hx
          simp only [bne_iff_ne, ne_eq]
          rintro rfl
          exact hk_notin (List.mem_map.mpr ⟨x, hx, rfl⟩)
        rw [htl_none, mergeFieldVal_none_left]
      · rw [show (k == k') = false from by simp [hkk']]
        exact ih hndtl
    | some val =>
      have hfm : (List.filterMap (fun kv : Int × Field =>
          (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1)) ((k', f') :: tl)) =
            (k', val) :: List.filterMap (fun kv : Int × Field =>
          (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1)) tl := by
        simp [h_merge]
      rw [hfm, List.lookup_cons]
      by_cases hkk' : k = k'
      · subst hkk'
        rw [show (k == k) = true from by simp]
        rw [List.lookup_cons, show (k == k) = true from by simp]
        rw [h_merge]
      · rw [show (k == k') = false from by simp [hkk']]
        rw [List.lookup_cons, show (k == k') = false from by simp [hkk']]
        exact ih hndtl

/-- Helper: in a no-dup-keyed list, membership implies the lookup gives the
    expected value. -/
private theorem lookup_of_mem_nodup_val (l : List (Int × Val)) (k : Int) (val : Val)
    (hnd : (l.map Prod.fst).Nodup) (hmem : (k, val) ∈ l) :
    l.lookup k = some val := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk_notin, hndtl⟩ := hnd
    rcases List.mem_cons.mp hmem with heq | hin
    · cases heq
      simp
    · have hkne : k ≠ k' := by
        intro heq
        exact hk_notin (List.mem_map.mpr ⟨(k, val), hin, heq⟩)
      rw [List.lookup_cons, show (k == k') = false from by simp [hkne]]
      exact ih hndtl hin

/-- The filterMap function used in `listMerge_mergeFieldVal_eq` preserves keys:
    when it produces `some b`, `b.1 = a.1`. -/
private theorem mergeFieldVal_filterMap_key_preserved
    (vs : List (Int × Val)) (a : Int × Field) (b : Int × Val)
    (h : (mergeFieldVal (some a.2) (vs.lookup a.1)).map (Prod.mk a.1) = some b) :
    b.1 = a.1 := by
  cases hm : mergeFieldVal (some a.2) (vs.lookup a.1) with
  | none =>
    rw [hm] at h
    simp at h
  | some va =>
    rw [hm] at h
    simp at h
    rw [← h]

/-- The keys produced by the merge filterMap are a sublist of the field keys. -/
private theorem listMerge_mergeFieldVal_keys_sublist
    (fs : List (Int × Field)) (vs : List (Int × Val)) :
    ((fs.filterMap (fun kv : Int × Field =>
        (mergeFieldVal (some kv.2) (vs.lookup kv.1)).map (Prod.mk kv.1))).map
        Prod.fst).Sublist (fs.map Prod.fst) := by
  induction fs with
  | nil => exact List.Sublist.refl _
  | cons hd tl ih =>
    rw [List.filterMap_cons, List.map_cons]
    cases h : (mergeFieldVal (some hd.2) (vs.lookup hd.1)).map (Prod.mk hd.1) with
    | none =>
      exact ih.cons _
    | some b =>
      rw [List.map_cons]
      rw [mergeFieldVal_filterMap_key_preserved vs hd b h]
      exact ih.cons₂ _

/-- `listMerge mergeFieldVal` preserves sortedness and nodup-keys when the
    field side is well-ordered. -/
private theorem listMerge_mergeFieldVal_wf (fs : List (Int × Field))
    (vs : List (Int × Val))
    (h_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs)
    (h_nodup : (fs.map Prod.fst).Nodup) :
    List.Pairwise (fun a b : Int × Val => a.1 < b.1)
        (listMerge mergeFieldVal fs vs) ∧
    ((listMerge mergeFieldVal fs vs).map Prod.fst).Nodup := by
  rw [listMerge_mergeFieldVal_eq]
  refine ⟨?_, ?_⟩
  · -- Sortedness via Pairwise.filterMap
    apply List.Pairwise.filterMap
      (S := fun a b : Int × Val => a.1 < b.1)
      (R := fun a b : Int × Field => a.1 < b.1)
    · intros a a' hR b hb b' hb'
      rw [mergeFieldVal_filterMap_key_preserved vs a b hb,
          mergeFieldVal_filterMap_key_preserved vs a' b' hb']
      exact hR
    · exact h_sorted
  · -- Nodup keys via sublist preservation.
    exact (listMerge_mergeFieldVal_keys_sublist fs vs).nodup h_nodup

/-- Serializing and then parsing a schema-correct value recovers the original
    (up to list-to-value reconstruction). -/
theorem list_to_value_id (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → v = listToValue d (valList d v) := by
  intro h
  obtain ⟨hd_wf, hv_wf⟩ := sc_implies_wf d v h
  -- Unwrap Desc.Sorted/NodupKeys to the underlying list facts.
  have hd_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) d.fields := by
    rcases d with ⟨fs⟩; exact hd_wf.1
  have hd_nodup : (d.fields.map Prod.fst).Nodup := by
    rcases d with ⟨fs⟩; exact hd_wf.2
  -- Reduce to lookup equality via Value.ext_lookup.
  apply Value.ext_lookup _ _ hv_wf
  · -- (listToValue d (valList d v)).WF
    show Value.WF (Value.mk (listMerge mergeFieldVal d.fields (valList d v)))
    have := listMerge_mergeFieldVal_wf d.fields (valList d v) hd_sorted hd_nodup
    exact this
  · intro k
    -- (listToValue d (valList d v)).get? k = (listMerge ...).lookup k
    show v.get? k = (listMerge mergeFieldVal d.fields (valList d v)).lookup k
    rw [listMerge_mergeFieldVal_lookup d.fields (valList d v) k hd_nodup]
    -- Goal: v.get? k = mergeFieldVal (d.fields.lookup k) ((valList d v).lookup k)
    -- Case on d.fields.lookup k.
    cases hdk : d.fields.lookup k with
    | none =>
      -- d has no field k; v should also not have key k.
      rw [mergeFieldVal_none_left]
      -- Show v.get? k = none. By contrapositive of sc_implies_val_in_desc.
      by_contra hne
      rcases hv : v.get? k with _ | val
      · exact hne hv
      obtain ⟨f, hf⟩ := sc_implies_val_in_desc d v h k val hv
      have : d.fields.lookup k = some f := hf
      rw [this] at hdk
      cases hdk
    | some f =>
      -- d has field f at k. Get matching val from v.
      obtain ⟨val, hval, hmatch⟩ := sc_implies_desc_in_val_typed d v h k f hdk
      rw [hval]
      -- (valList d v).lookup k = some val
      have h_in_valList : (k, val) ∈ valList d v := by
        unfold valList
        rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · -- (k, val) ∈ v.vals from v.get? k = some val.
          rcases v with ⟨vs⟩
          show (k, val) ∈ vs
          have hlk : vs.lookup k = some val := hval
          -- Standard: lookup gives some val ⇒ (k, val) ∈ vs.
          have h_lookup_to_mem : ∀ (l : List (Int × Val)),
              l.lookup k = some val → (k, val) ∈ l := by
            intro l
            induction l with
            | nil => intro hlk; cases hlk
            | cons hd tl ih =>
              intro hlk
              obtain ⟨k', v'⟩ := hd
              rw [List.lookup_cons] at hlk
              by_cases hkk' : k = k'
              · subst hkk'
                rw [show (k == k) = true from by simp] at hlk
                simp at hlk
                subst hlk
                exact List.mem_cons_self
              · rw [show (k == k') = false from by simp [hkk']] at hlk
                exact List.mem_cons_of_mem _ (ih hlk)
          exact h_lookup_to_mem vs hlk
        · -- valListFilterP d (k, val) = true
          show valListFilterP d (k, val) = true
          unfold valListFilterP
          rw [hdk]
          cases val with
          | bool _ => rfl
          | int _ => rfl
          | msg _ => rfl
          | missing =>
            -- Contradiction via fieldValMatch
            exfalso
            cases f
            all_goals simp_all [fieldValMatch]
      -- Now use this to compute (valList d v).lookup k.
      have hv_nodup : (v.vals.map Prod.fst).Nodup := by
        rcases v with ⟨vs⟩; exact hv_wf.2
      have h_valList_nodup : ((valList d v).map Prod.fst).Nodup := by
        unfold valList
        exact (List.filter_sublist.map Prod.fst).nodup hv_nodup
      rw [lookup_of_mem_nodup_val (valList d v) k val h_valList_nodup h_in_valList]
      -- Goal: some val = mergeFieldVal (some f) (some val)
      -- This depends on fieldValMatch f val.
      cases f with
      | bool =>
        cases val with
        | bool b => rfl
        | _ => simp_all [fieldValMatch]
      | int =>
        cases val with
        | int z => rfl
        | _ => simp_all [fieldValMatch]
      | msg d' =>
        cases val with
        | msg v' => rfl
        | _ => simp_all [fieldValMatch]

theorem sc_filter_self (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → ⟨ listToValue d (valList d v) ∷ d ⟩ := by
  intro h
  rw [← list_to_value_id v d h]
  exact h

theorem fullDescriptor_roundTrip (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → ⟨v ∷ d⟩≼⟨(listToValue d (valList d v)) ∷ d⟩  := by
  intro h
  rw [← list_to_value_id v d h]
  exact Compatible.refl d d v h h

end Pollux.InterParse
