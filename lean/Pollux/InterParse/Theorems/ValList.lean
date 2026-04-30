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

end Pollux.InterParse
