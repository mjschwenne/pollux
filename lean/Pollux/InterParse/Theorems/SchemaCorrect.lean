/-
  Pollux.InterParse.Theorems.SchemaCorrect — The `SchemaCorrect` and
  `SchemaCorrectOrdered` relations and their structural lemmas.
-/
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Pollux.InterParse.Theorems.SortedHelpers

namespace Pollux.InterParse

/-! ## SchemaCorrect inductive relation

The `SchemaCorrect` relation establishes a correspondence between a descriptor
and a value: every field in the descriptor has a correctly-typed entry in the
value and vice versa, with no `V_MISSING` entries. -/

inductive SchemaCorrect : Desc → Value → Prop where
  | empty : SchemaCorrect (∅ : Desc) (∅ : Value)
  | insert (k : Int) (f : Field) (v : Val) (ds : Desc) (vs : Value) :
    fieldValMatch f v →
    (∀ d' v', f = .msg d' → v = .msg v' → SchemaCorrect d' v') →
    ds.get? k = none →
    vs.get? k = none →
    SchemaCorrect ds vs →
    SchemaCorrect (ds.insert k f) (vs.insert k v)

notation "⟨ " v " ∷ " d " ⟩" => SchemaCorrect d v

/-! ## SchemaCorrect lemmas -/

theorem sc_insert_field (k : Int) (f : Field) (val : Val) (d : Desc) (v : Value) :
    fieldValMatch f val →
    (∀ d' v', f = .msg d' → val = .msg v' → ⟨ v' ∷ d' ⟩) →
    d.get? k = none →
    v.get? k = none →
    ⟨ v ∷ d ⟩ →
    ⟨ v.insert k val ∷ d.insert k f ⟩ :=
  SchemaCorrect.insert k f val d v

theorem sc_empty : ⟨ (∅ : Value) ∷ (∅ : Desc) ⟩ :=
  SchemaCorrect.empty

/-
Every field in the value exists in the descriptor.
-/
theorem sc_implies_val_in_desc (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val → ∃ f, d.get? k = some f := by
      contrapose!; simp_all +decide [ Value.get? ] ;
      intro k val h₁ h₂ h₃;
      induction' h₃ with k' f val' d' v' h₄ h₅ h₆ h₇ h₈;
      · cases h₁;
      · by_cases hk : k = k' <;> simp_all +decide [ Value.insert ];
        · contrapose! h₂; simp_all +decide [ Value.get? ] ;
          -- By definition of `sortedInsert`, inserting `k'` into `d'.fields` will result in a list where `k'` is the first element.
          have h_sortedInsert : List.lookup k' (Desc.sortedInsert k' f d'.fields) = some f := by
            induction' d'.fields with k'' f'' d'' ih <;> simp_all +decide [ Desc.sortedInsert ];
            grind +qlia;
          exact ⟨ f, h_sortedInsert ⟩;
        · -- Since k is not equal to k', the lookup in the sortedInsert is the same as the lookup in the original list.
          have h_lookup_eq : List.lookup k (Value.sortedInsert k' val' v'.vals) = List.lookup k v'.vals := by
            have h_lookup_eq : ∀ {l : List (Int × Val)}, k ≠ k' → List.lookup k (Value.sortedInsert k' val' l) = List.lookup k l := by
              intros l hk; induction' l with hd tl ih <;> simp_all +decide [ Value.sortedInsert ] ;
              grind;
            exact h_lookup_eq hk;
          rename_i h₉ h₁₀;
          obtain ⟨ x, hx ⟩ := h₁₀ ( h_lookup_eq.symm.trans h₁ );
          exact h₂ x ( by rw [ show ( d'.insert k' f ).get? k = d'.get? k from by
                                have h_lookup_eq : ∀ {l : List (Int × Field)}, k ≠ k' → List.lookup k (Desc.sortedInsert k' f l) = List.lookup k l := by
                                  intros l hk; induction' l with l ih <;> simp +decide [ Desc.sortedInsert, hk ] ;
                                  grind;
                                exact h_lookup_eq hk ] ; exact hx )

/-
Every field in the value exists in the descriptor with matching type.
-/
theorem sc_implies_val_in_desc_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k val, v.get? k = some val →
    ∃ f, d.get? k = some f ∧ fieldValMatch f val := by
      intro h
      induction' h with kk fld val' d' v' h_match h_nested ih_nested h_dnone h_vnone h_sc ih
      · intro k val hval
        simp [Value.get?, Value.vals] at hval
      · intro k val hval
        by_cases hk : k = kk
        · subst hk
          refine ⟨fld, ?_, ?_⟩
          · unfold Desc.get? Desc.insert
            cases d'
            simp +decide [Desc.fields]
            have h_lookup_insert : ∀ (l : List (Int × Field)),
                List.lookup k (Desc.sortedInsert k fld l) = some fld := by
              intros l
              induction' l with hd tl ih2 <;> simp_all +decide [ Desc.sortedInsert ]
              grind
            exact h_lookup_insert _
          · unfold Value.get? Value.insert at hval
            cases v'
            simp +decide [Value.vals] at hval
            have h_lookup_insert : ∀ (l : List (Int × Val)),
                List.lookup k (Value.sortedInsert k val' l) = some val' := by
              intros l
              induction' l with hd tl ih2 <;> simp_all +decide [ Value.sortedInsert ]
              grind
            rw [h_lookup_insert] at hval
            cases hval
            exact h_match
        · have h_lookup_v : v'.get? k = some val := by
            unfold Value.get? Value.insert at hval
            cases v'
            simp +decide [Value.vals] at hval
            simp [Value.get?, Value.vals]
            rw [← sortedInsert_lookup_ne_val k kk val' _ hk]
            exact hval
          obtain ⟨f', hf', hmatch⟩ := ih k val h_lookup_v
          refine ⟨f', ?_, hmatch⟩
          unfold Desc.get? Desc.insert
          cases d'
          simp +decide [Desc.fields]
          rw [sortedInsert_lookup_ne_desc k kk fld _ hk]
          simp [Desc.get?, Desc.fields] at hf'
          exact hf'

/-
Every field in the descriptor exists in the value.
-/
theorem sc_implies_desc_in_val (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f → ∃ val, v.get? k = some val := by
      intro h k f hf
      induction' h with d' v' f' k' h_valid h_ind;
      · cases hf;
      · have h_lookup_insert : ∀ (l : List (Int × Field)) (k : Int) (d' : Int) (v' : Field), k ≠ d' → (List.lookup k (Desc.sortedInsert d' v' l)) = (List.lookup k l) := by
          intros l k d' v' hk_ne_d'; induction' l with l ih generalizing k d' v' <;> simp_all +decide [ Desc.sortedInsert ] ;
          grind;
        unfold Value.get? at *; by_cases h : k = d' <;> simp_all +decide [ Value.insert ] ;
        · have h_lookup_insert : ∀ (l : List (Int × Val)) (k : Int) (d' : Int) (v' : Val), k = d' → List.lookup k (Value.sortedInsert d' v' l) = some v' := by
            intros l k d' v' hk; induction' l with hd tl ih <;> simp_all +decide [ Value.sortedInsert ] ;
            grind;
          exact ⟨ _, h_lookup_insert _ _ _ _ rfl ⟩;
        · have h_lookup_insert : ∀ (l : List (Int × Val)) (k : Int) (d' : Int) (v' : Val), k ≠ d' → (List.lookup k (Value.sortedInsert d' v' l)) = (List.lookup k l) := by
            intros l k d' v' hk_ne_d'; induction' l with l ih generalizing k d' v' <;> simp_all +decide [ Value.sortedInsert ] ;
            grind +splitImp;
          simp_all +decide [ Value.vals ];
          exact ‹List.lookup k k'.fields = some f → ∃ val, List.lookup k _ = some val› ( by rename_i h₁ h₂ h₃ h₄ h₅ h₆; exact h₆ _ _ _ _ h ▸ hf )

/-
Every field in the descriptor exists in the value with matching type.
-/
theorem sc_implies_desc_in_val_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k f, d.get? k = some f →
    ∃ val, v.get? k = some val ∧ fieldValMatch f val := by
      intro hd k f hkf
      obtain ⟨val, hval⟩ : ∃ val, v.get? k = some val := by
        exact sc_implies_desc_in_val d v hd k f hkf;
      have := sc_implies_val_in_desc_typed d v hd k val hval; aesop;

/-
No `V_MISSING` values in a schema-correct value.
-/
theorem sc_implies_no_missing (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ k, v.get? k ≠ some .missing := by
      intros h k;
      have := sc_implies_desc_in_val_typed d v h k;
      have := sc_implies_val_in_desc d v h k Val.missing; aesop;

/-- Nested messages are schema-correct with their subdescriptors. -/
def nestedCorrect (d : Desc) (k : Int) (v : Val) : Prop :=
  match d.fields.lookup k, v with
  | some (.msg d'), .msg v' => ⟨ v' ∷ d' ⟩
  | _, _ => True

theorem sc_implies_nested_correct (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    ∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2 := by
  intro h
  induction' h with kk f val' d' v' h_match h_nested h_dn h_vn _ ih_nested ih
  · intro kv hkv
    -- (∅ : Value).vals = []
    simp [Value.vals] at hkv
  · intro kv hkv
    -- kv is in (v'.insert kk val').vals = sortedInsert kk val' v'.vals
    have hkv' : kv ∈ Value.sortedInsert kk val' v'.vals := by
      rcases v' with ⟨vs⟩
      simp [Value.insert, Value.vals] at hkv
      exact hkv
    rcases mem_value_sortedInsert kk val' v'.vals kv hkv' with heq | hmem
    · -- kv = (kk, val')
      subst heq
      -- Need: lookup kk in (d'.insert kk f).fields = some f
      have hlk : (d'.insert kk f).fields.lookup kk = some f := by
        unfold Desc.insert
        cases d'
        simp +decide [Desc.fields]
        have h_lookup_insert : ∀ (l : List (Int × Field)),
            List.lookup kk (Desc.sortedInsert kk f l) = some f := by
          intros l
          induction' l with hd tl ih2 <;> simp_all +decide [ Desc.sortedInsert ]
          grind
        exact h_lookup_insert _
      show nestedCorrect (d'.insert kk f) kk val'
      unfold nestedCorrect
      rw [hlk]
      cases f with
      | msg d'' =>
        cases val' with
        | msg v'' => exact h_nested d'' v'' rfl rfl
        | bool _ => exact trivial
        | int _ => exact trivial
        | missing => exact trivial
      | bool => exact trivial
      | int => exact trivial
    · -- kv ∈ v'.vals; kv.1 ≠ kk
      have hne : kv.1 ≠ kk := ne_of_get?_none v' kk kv h_vn hmem
      have hnc : nestedCorrect d' kv.1 kv.2 := ih kv hmem
      have hlk_eq : (d'.insert kk f).fields.lookup kv.1 = d'.fields.lookup kv.1 := by
        cases d' with | mk fs =>
        simp [Desc.insert, Desc.fields]
        exact sortedInsert_lookup_ne_desc kv.1 kk f fs hne
      show nestedCorrect (d'.insert kk f) kv.1 kv.2
      unfold nestedCorrect at hnc ⊢
      rw [hlk_eq]
      exact hnc

/-- Combined: all four properties of schema correctness. -/
theorem sc_implies_properties (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by
  intro h
  exact ⟨sc_implies_val_in_desc d v h,
         sc_implies_desc_in_val d v h,
         sc_implies_no_missing d v h,
         sc_implies_nested_correct d v h⟩

/-- Combined with typed witnesses. -/
theorem sc_implies_properties_typed (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ →
    (∀ k val, v.get? k = some val → ∃ f, d.get? k = some f ∧ fieldValMatch f val) ∧
    (∀ k f, d.get? k = some f → ∃ val, v.get? k = some val ∧ fieldValMatch f val) ∧
    (∀ k, v.get? k ≠ some .missing) ∧
    (∀ kv ∈ v.vals, nestedCorrect d kv.1 kv.2) := by
  intro h
  exact ⟨sc_implies_val_in_desc_typed d v h,
         sc_implies_desc_in_val_typed d v h,
         sc_implies_no_missing d v h,
         sc_implies_nested_correct d v h⟩

/-! ### Helpers for `sc_delete_key` -/

/-- WF is preserved by SC: every SC-derivable value is well-formed. -/
private theorem sc_implies_wf (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → d.WF ∧ v.WF := by
  intro h
  induction h with
  | empty => exact ⟨Desc.empty_wf, Value.empty_wf⟩
  | insert _ _ _ _ _ _ _ _ _ _ _ ih =>
    refine ⟨Desc.insert_wf _ _ _ ih.1, Value.insert_wf _ _ _ ih.2⟩

theorem sc_delete_key (d : Desc) (v : Value) (k : Int) :
    ⟨ v ∷ d ⟩ → ⟨ v.erase k ∷ d.erase k ⟩ := by
  intro h
  induction h with
  | empty =>
    -- erase on the empty maps yields empty
    show ⟨ (∅ : Value).erase k ∷ (∅ : Desc).erase k ⟩
    have h1 : (∅ : Desc).erase k = (∅ : Desc) := by
      show Desc.mk (Desc.sortedErase k []) = Desc.mk []
      rfl
    have h2 : (∅ : Value).erase k = (∅ : Value) := by
      show Value.mk (Value.sortedErase k []) = Value.mk []
      rfl
    rw [h1, h2]
    exact SchemaCorrect.empty
  | insert k0 f val' d' v' h_match h_nested h_dn h_vn h_sc ih_nested ih =>
    obtain ⟨hd_wf, hv_wf⟩ := sc_implies_wf _ _ h_sc
    rcases d' with ⟨fs⟩
    rcases v' with ⟨vs⟩
    by_cases hk : k = k0
    · -- erase undoes the insert; result is `⟨ v' ∷ d' ⟩`
      subst hk
      have h_d : ((Desc.mk fs).insert k f).erase k = Desc.mk fs := by
        show Desc.mk (Desc.sortedErase k (Desc.sortedInsert k f fs)) = Desc.mk fs
        congr 1
        apply desc_sortedErase_sortedInsert_same
        exact h_dn
      have h_v : ((Value.mk vs).insert k val').erase k = Value.mk vs := by
        show Value.mk (Value.sortedErase k (Value.sortedInsert k val' vs)) = Value.mk vs
        congr 1
        apply value_sortedErase_sortedInsert_same
        exact h_vn
      rw [h_d, h_v]
      exact h_sc
    · -- erase commutes with insert
      have h_d : ((Desc.mk fs).insert k0 f).erase k =
          ((Desc.mk fs).erase k).insert k0 f := by
        show Desc.mk (Desc.sortedErase k (Desc.sortedInsert k0 f fs)) =
             Desc.mk (Desc.sortedInsert k0 f (Desc.sortedErase k fs))
        congr 1
        apply desc_sortedErase_sortedInsert_ne
        · exact hk
        · exact hd_wf.1
      have h_v : ((Value.mk vs).insert k0 val').erase k =
          ((Value.mk vs).erase k).insert k0 val' := by
        show Value.mk (Value.sortedErase k (Value.sortedInsert k0 val' vs)) =
             Value.mk (Value.sortedInsert k0 val' (Value.sortedErase k vs))
        congr 1
        apply value_sortedErase_sortedInsert_ne
        · exact hk
        · exact hv_wf.1
      rw [h_d, h_v]
      have h_d_get : ((Desc.mk fs).erase k).get? k0 = none := by
        show List.lookup k0 (Desc.sortedErase k fs) = none
        rw [desc_lookup_sortedErase_ne k k0 fs (Ne.symm hk)]
        exact h_dn
      have h_v_get : ((Value.mk vs).erase k).get? k0 = none := by
        show List.lookup k0 (Value.sortedErase k vs) = none
        rw [value_lookup_sortedErase_ne k k0 vs (Ne.symm hk)]
        exact h_vn
      exact SchemaCorrect.insert k0 f val' ((Desc.mk fs).erase k)
        ((Value.mk vs).erase k) h_match h_nested h_d_get h_v_get ih

theorem sc_dom_eq (d : Desc) (v : Value) :
    ⟨ v ∷ d ⟩ → (v.vals.map Prod.fst) = (d.fields.map Prod.fst) := by
      -- We'll use induction on the structure of the schema correctness.
      intro h
      induction' h with d v h_ind;
      · native_decide +revert;
      · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
        have h_keys_eq : ∀ (l : List (Int × Val)) (l' : List (Int × Field)), List.map Prod.fst l = List.map Prod.fst l' → List.map Prod.fst (Value.sortedInsert d h_ind l) = List.map Prod.fst (Desc.sortedInsert d v l') := by
          intros l l' h_keys_eq;
          induction' l with l_head l_tail ih generalizing l' <;> induction' l' with l'_head l'_tail ih' <;> simp_all +decide [ Value.sortedInsert, Desc.sortedInsert ];
          grind +splitImp;
        exact h_keys_eq _ _ h₆

/-! ## SchemaCorrectOrdered -/

/-- Ordered variant of `SchemaCorrect` that additionally requires inserted keys
    to be first in the map ordering. Equivalent to `SchemaCorrect` for
    well-ordered maps. -/
inductive SchemaCorrectOrdered : Desc → Value → Prop where
  | empty : SchemaCorrectOrdered (∅ : Desc) (∅ : Value)
  | insert (k : Int) (f : Field) (val : Val) (d : Desc) (v : Value) :
    fieldValMatch f val →
    (∀ d' v', f = .msg d' → val = .msg v' → SchemaCorrectOrdered d' v') →
    d.get? k = none →
    v.get? k = none →
    SchemaCorrectOrdered d v →
    SchemaCorrectOrdered (d.insert k f) (v.insert k val)

notation "⟪ " v " ∷ " d " ⟫" => SchemaCorrectOrdered d v

theorem sc_sco (v : Value) (d : Desc) : ⟨ v ∷ d ⟩ ↔ ⟪ v ∷ d ⟫ := by
  constructor <;> intro h;
  · induction' h with k f val d v ih;
    · constructor;
    · exact SchemaCorrectOrdered.insert k f val d v ih ‹_› ‹_› ‹_› ‹_›;
  · induction h;
    · constructor;
    · constructor <;> assumption

/-! ## Descriptor invariance -/

/-- If a value is schema-correct for two descriptors, the descriptors are equal. -/
theorem sc_desc_inv (v : Value) (d1 d2 : Desc) :
    ⟨ v ∷ d1 ⟩ → ⟨ v ∷ d2 ⟩ → d1 = d2 := by sorry

end Pollux.InterParse
