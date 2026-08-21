/-
  Pollux.InterParse.Theorems.CompatRoundTrip — the cross-descriptor round-trip
  theorem: `compatTransform d₁ d₂ v` is always related to `v` by the full
  compatibility relation `≼`.

  This is the two-descriptor analogue of `idCompatRoundTrip`.  The derivation
  is assembled key by key, in increasing key order, walking the writer's
  fields, the writer's value entries and the reader's fields simultaneously.
  Because `≪` never removes a key, the reader's field list drives the walk: its
  head key is the smallest declared key on either side.
-/
import Pollux.InterParse.Theorems.CompatTransform
import Pollux.InterParse.Theorems.IdCompatibleRoundTrip
import Pollux.InterParse.Theorems.Validity

namespace Pollux.InterParse

/-! ## `insert` as a cons

  When the inserted key is below all existing keys, `Desc.insert` /
  `Value.insert` act as a list cons.  Compare the `_cons` smart constructors
  for `IdCompatible`. -/

theorem desc_insert_eq_cons (k : Int) (f : Field) (rest : List (Int × Field))
    (h : ∀ p ∈ rest, k < p.1) :
    (Desc.mk rest).insert k f = Desc.mk ((k, f) :: rest) := by
  unfold Desc.insert Desc.fields; congr 1
  cases rest with
  | nil => simp [Desc.sortedInsert]
  | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from h hd (by simp)]

theorem value_insert_eq_cons (k : Int) (val : Val) (rest : List (Int × Val))
    (h : ∀ p ∈ rest, k < p.1) :
    (Value.mk rest).insert k val = Value.mk ((k, val) :: rest) := by
  unfold Value.insert Value.vals; congr 1
  cases rest with
  | nil => simp [Value.sortedInsert]
  | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from h hd (by simp)]

/-! ## `≼` constructors in sorted-cons form -/

/-- M-Missing when the inserts act as conses. -/
theorem MsgCompat.missing_cons (k : Int) (f₂ : Field)
    (vs : List (Int × Val)) (fs₁ : List (Int × Field))
    (v₂ : List (Int × Val)) (fs₂ : List (Int × Field))
    (hv₂ : ∀ p ∈ v₂, k < p.1) (hfs₂ : ∀ p ∈ fs₂, k < p.1)
    (h : ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨ Value.mk v₂ ∷ Desc.mk fs₂ ⟩)
    (h1 : vs.lookup k = none) (h2 : fs₁.lookup k = none)
    (h3 : v₂.lookup k = none) (h4 : fs₂.lookup k = none) :
    ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨ Value.mk ((k, Val.missing) :: v₂) ∷
      Desc.mk ((k, f₂) :: fs₂) ⟩ := by
  rw [← value_insert_eq_cons k Val.missing v₂ hv₂,
    ← desc_insert_eq_cons k f₂ fs₂ hfs₂]
  exact MsgCompat.missing _ _ _ _ k f₂ h h1 h2 h3 h4

/-- M-Declare when the inserts act as conses. -/
theorem MsgCompat.declare_cons (k : Int) (f₁ f₂ : Field)
    (vs : List (Int × Val)) (fs₁ : List (Int × Field))
    (v₂ : List (Int × Val)) (fs₂ : List (Int × Field))
    (hfs₁ : ∀ p ∈ fs₁, k < p.1) (hv₂ : ∀ p ∈ v₂, k < p.1)
    (hfs₂ : ∀ p ∈ fs₂, k < p.1)
    (h : ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨ Value.mk v₂ ∷ Desc.mk fs₂ ⟩)
    (hfc : f₁ ∝ f₂)
    (h1 : vs.lookup k = none) (h2 : fs₁.lookup k = none)
    (h3 : v₂.lookup k = none) (h4 : fs₂.lookup k = none) :
    ⟨ Value.mk vs ∷ Desc.mk ((k, f₁) :: fs₁) ⟩⪯⟨ Value.mk ((k, Val.missing) :: v₂) ∷
      Desc.mk ((k, f₂) :: fs₂) ⟩ := by
  rw [← desc_insert_eq_cons k f₁ fs₁ hfs₁,
    ← value_insert_eq_cons k Val.missing v₂ hv₂,
    ← desc_insert_eq_cons k f₂ fs₂ hfs₂]
  exact MsgCompat.declare _ _ _ _ k f₁ f₂ h hfc h1 h2 h3 h4

/-- M-Drop-Unknown when the insert acts as a cons. -/
theorem MsgCompat.dropUnknown_cons (k : Int) (val : Val)
    (vs : List (Int × Val)) (fs₁ : List (Int × Field)) (m₂ : Value) (d₂ : Desc)
    (hvs : ∀ p ∈ vs, k < p.1)
    (h : ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩)
    (h1 : vs.lookup k = none) (h2 : fs₁.lookup k = none) :
    ⟨ Value.mk ((k, val) :: vs) ∷ Desc.mk fs₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩ := by
  rw [← value_insert_eq_cons k val vs hvs]
  exact MsgCompat.dropUnknown _ _ _ _ k val h h1 h2

/-- M-Drop followed by M-Update: the writer's entry at `k` enters on both
    sides, and the reader's reinterpretation of it enters on its side. -/
theorem MsgCompat.update_cons (k : Int) (val : Val) (f₁ : Field)
    (val₂ : Val) (f₂ : Field)
    (vs : List (Int × Val)) (fs₁ : List (Int × Field))
    (v₂ : List (Int × Val)) (fs₂ : List (Int × Field))
    (hvs : ∀ p ∈ vs, k < p.1) (hfs₁ : ∀ p ∈ fs₁, k < p.1)
    (hv₂ : ∀ p ∈ v₂, k < p.1) (hfs₂ : ∀ p ∈ fs₂, k < p.1)
    (h : ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨ Value.mk v₂ ∷ Desc.mk fs₂ ⟩)
    (hvc : ⟨ val ∷ f₁ ⟩≺⟨ val₂ ∷ f₂ ⟩) (hfc : f₁ ∝ f₂)
    (h1 : vs.lookup k = none) (h2 : fs₁.lookup k = none)
    (h3 : v₂.lookup k = none) (h4 : fs₂.lookup k = none) :
    ⟨ Value.mk ((k, val) :: vs) ∷ Desc.mk ((k, f₁) :: fs₁) ⟩⪯⟨
      Value.mk ((k, val₂) :: v₂) ∷ Desc.mk ((k, f₂) :: fs₂) ⟩ := by
  have hdrop : ⟨ Value.mk ((k, val) :: vs) ∷ Desc.mk ((k, f₁) :: fs₁) ⟩⪯⟨
      Value.mk v₂ ∷ Desc.mk fs₂ ⟩ := by
    rw [← value_insert_eq_cons k val vs hvs, ← desc_insert_eq_cons k f₁ fs₁ hfs₁]
    exact MsgCompat.drop _ _ _ _ k val f₁ h h1 h2 h3 h4
  rw [← value_insert_eq_cons k val₂ v₂ hv₂, ← desc_insert_eq_cons k f₂ fs₂ hfs₂]
  exact MsgCompat.update _ _ _ _ k val f₁ val₂ f₂ hdrop
    (by show List.lookup k ((k, val) :: vs) = _; simp)
    (by show List.lookup k ((k, f₁) :: fs₁) = _; simp) hvc hfc

/-- Against the empty reader descriptor every writer entry simply disappears. -/
theorem msgCompat_drop_all (vs : List (Int × Val)) :
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    ⟨ Value.mk vs ∷ Desc.mk [] ⟩⪯⟨ Value.mk [] ∷ Desc.mk [] ⟩ := by
  induction vs with
  | nil => intro _; exact MsgCompat.emp
  | cons kv rest ih =>
    intro hs
    obtain ⟨k, val⟩ := kv
    have hlt : ∀ p ∈ rest, k < p.1 := fun p hp => List.rel_of_pairwise_cons hs hp
    exact MsgCompat.dropUnknown_cons k val rest [] _ _ hlt (ih hs.tail)
      (lookup_none_of_lt_all_val k rest hlt) rfl

/-! ## Irrelevance lemmas for the transform -/

/-- The transform reads the writer's descriptor and value only at the reader's
    keys. -/
theorem compatTransformAux_congr (fs₂ : List (Int × Field))
    (d₁ d₁' : Desc) (v v' : Value)
    (hd : ∀ p ∈ fs₂, d₁.get? p.1 = d₁'.get? p.1)
    (hv : ∀ p ∈ fs₂, v.get? p.1 = v'.get? p.1) :
    compatTransformAux fs₂ d₁ v = compatTransformAux fs₂ d₁' v' := by
  induction fs₂ with
  | nil => rfl
  | cons hd' tl ih =>
    obtain ⟨k, f⟩ := hd'
    have h1 : d₁.get? k = d₁'.get? k := hd (k, f) (by simp)
    have h2 : v.get? k = v'.get? k := hv (k, f) (by simp)
    rw [compatTransformAux_cons, compatTransformAux_cons, h1, h2,
      ih (fun p hp => hd p (List.mem_cons_of_mem _ hp))
        (fun p hp => hv p (List.mem_cons_of_mem _ hp))]

/-- A writer field below all reader keys is invisible to the transform. -/
theorem compatTransformAux_prepend_ds (fs₂ : List (Int × Field)) (k : Int)
    (f₁ : Field) (rest₁ : List (Int × Field)) (v : Value)
    (h : ∀ p ∈ fs₂, k < p.1) :
    compatTransformAux fs₂ (Desc.mk ((k, f₁) :: rest₁)) v =
      compatTransformAux fs₂ (Desc.mk rest₁) v := by
  refine compatTransformAux_congr fs₂ _ _ v v (fun p hp => ?_) (fun _ _ => rfl)
  have hne : p.1 ≠ k := ne_of_gt (h p hp)
  show List.lookup p.1 ((k, f₁) :: rest₁) = List.lookup p.1 rest₁
  rw [List.lookup_cons, show (p.1 == k) = false from by simp [hne]]

/-- A writer entry below all reader keys is invisible to the transform. -/
theorem compatTransformAux_prepend_vs (fs₂ : List (Int × Field)) (k : Int)
    (val : Val) (rest : List (Int × Val)) (d₁ : Desc)
    (h : ∀ p ∈ fs₂, k < p.1) :
    compatTransformAux fs₂ d₁ (Value.mk ((k, val) :: rest)) =
      compatTransformAux fs₂ d₁ (Value.mk rest) := by
  refine compatTransformAux_congr fs₂ d₁ d₁ _ _ (fun _ _ => rfl) (fun p hp => ?_)
  have hne : p.1 ≠ k := ne_of_gt (h p hp)
  show List.lookup p.1 ((k, val) :: rest) = List.lookup p.1 rest
  rw [List.lookup_cons, show (p.1 == k) = false from by simp [hne]]

/-- The transform's keys inherit a lower bound from the reader's keys. -/
theorem compatTransformAux_keys_gt (fs₂ : List (Int × Field)) (d₁ : Desc)
    (v : Value) (k : Int) :
    (∀ p ∈ fs₂, k < p.1) → ∀ p ∈ compatTransformAux fs₂ d₁ v, k < p.1 := by
  intro h p hp
  have hmem : p.1 ∈ fs₂.map Prod.fst := by
    have := List.mem_map_of_mem (f := Prod.fst) hp
    rwa [compatTransformAux_keys] at this
  obtain ⟨q, hq, hq_eq⟩ := List.mem_map.mp hmem
  rw [← hq_eq]
  exact h q hq

/-! ## Association-list helpers -/

/-- A member of a field list is found by a lookup at its key. -/
theorem lookup_isSome_of_mem_field (fs : List (Int × Field)) (p : Int × Field) :
    p ∈ fs → ∃ f, fs.lookup p.1 = some f := by
  induction fs with
  | nil => intro hp; cases hp
  | cons hd tl ih =>
    intro hp
    by_cases h : p.1 = hd.1
    · refine ⟨hd.2, ?_⟩
      rw [List.lookup_cons, show (p.1 == hd.1) = true from by
        rw [beq_eq_decide]; simp [h]]
    · rcases List.mem_cons.mp hp with rfl | hmem
      · exact absurd rfl h
      · obtain ⟨f, hf⟩ := ih hmem
        refine ⟨f, ?_⟩
        rw [List.lookup_cons, show (p.1 == hd.1) = false from by
          rw [beq_eq_decide]; simp [h]]
        exact hf

/-- The counterpart of `mem_of_lookup_val` for field lists. -/
theorem mem_of_lookup_field (fs : List (Int × Field)) (k : Int) (f : Field) :
    fs.lookup k = some f → (k, f) ∈ fs := by
  induction fs with
  | nil => intro h; cases h
  | cons hd tl ih =>
    intro h; rw [List.lookup_cons] at h
    by_cases hkk : k = hd.1
    · subst hkk; simp at h; subst h; exact List.mem_cons_self
    · rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hkk]] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ## The induction -/

/-- The round-trip derivation, on raw sorted lists.  The writer's descriptor,
    the writer's value and the reader's descriptor are processed in increasing
    key order; `n` bounds the combined size, which strictly decreases both when
    a head is consumed and when the proof recurses into a nested message. -/
private theorem compatRoundTrip_aux_wf :
    ∀ (n : Nat) (fs₁ : List (Int × Field)) (vs : List (Int × Val))
      (fs₂ : List (Int × Field)),
    fieldListSize fs₁ + fieldListSize fs₂ + valListSize vs ≤ n →
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs₁ →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs₂ →
    fieldListAllWF fs₁ → valListAllWF vs → fieldListAllWF fs₂ →
    (∀ k f₁, fs₁.lookup k = some f₁ → ∃ f₂, fs₂.lookup k = some f₂ ∧ (f₁ ∝ f₂)) →
    valueWf (Desc.mk fs₁) (Value.mk vs) →
    ⟨ Value.mk vs ∷ Desc.mk fs₁ ⟩⪯⟨
      Value.mk (compatTransformAux fs₂ (Desc.mk fs₁) (Value.mk vs)) ∷
        Desc.mk fs₂ ⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
  intro fs₁ vs fs₂ hn hs₁ hsv hs₂ ha₁ hav ha₂ H hwf
  cases fs₂ with
  | nil =>
    -- The reader declares nothing, so the writer declares nothing either and
    -- every writer entry is an unknown field.
    have hfs₁ : fs₁ = [] := by
      cases fs₁ with
      | nil => rfl
      | cons hd tl =>
        obtain ⟨k, f⟩ := hd
        obtain ⟨g, hg, _⟩ := H k f (by simp)
        exact absurd hg (by simp)
    subst hfs₁
    exact msgCompat_drop_all vs hsv
  | cons hd₂ rest₂ =>
    obtain ⟨k₂, f₂⟩ := hd₂
    have hlt₂ : ∀ p ∈ rest₂, k₂ < p.1 := fun p hp => List.rel_of_pairwise_cons hs₂ hp
    have hrest₂_none : rest₂.lookup k₂ = none :=
      lookup_none_of_lt_all_field k₂ rest₂ hlt₂
    -- `≪` never removes a key, so the reader's head key bounds the writer's.
    have hfs₁_ge : ∀ p ∈ fs₁, k₂ ≤ p.1 := by
      intro p hp
      obtain ⟨f, hf⟩ := lookup_isSome_of_mem_field fs₁ p hp
      obtain ⟨g, hg, _⟩ := H p.1 f hf
      rw [List.lookup_cons] at hg
      by_cases hbeq : p.1 = k₂
      · exact le_of_eq hbeq.symm
      · rw [show (p.1 == k₂) = false from by rw [beq_eq_decide]; simp [hbeq]] at hg
        exact le_of_lt (hlt₂ (p.1, g) (mem_of_lookup_field rest₂ p.1 g hg))
    have hcase₁ : (fs₁.lookup k₂ = none ∧ ∀ p ∈ fs₁, k₂ < p.1) ∨
        (∃ f₁ rest₁, fs₁ = (k₂, f₁) :: rest₁) := by
      cases fs₁ with
      | nil => exact Or.inl ⟨rfl, by simp⟩
      | cons hd tl =>
        obtain ⟨k₁, f₁⟩ := hd
        rcases eq_or_lt_of_le (hfs₁_ge (k₁, f₁) (by simp)) with heq | hlt
        · exact Or.inr ⟨f₁, tl, by rw [heq]⟩
        · have hgt : ∀ p ∈ (k₁, f₁) :: tl, k₂ < p.1 := by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hmem
            · exact hlt
            · exact lt_trans hlt (List.rel_of_pairwise_cons hs₁ hmem)
          exact Or.inl ⟨lookup_none_of_lt_all_field k₂ _ hgt, hgt⟩
    have hcase_v : (∀ p ∈ vs, k₂ < p.1) ∨
        (∃ val rest_vs, vs = (k₂, val) :: rest_vs) ∨
        (∃ k_v val rest_vs, vs = (k_v, val) :: rest_vs ∧ k_v < k₂) := by
      cases vs with
      | nil => exact Or.inl (by simp)
      | cons kv rest_vs =>
        obtain ⟨k_v, val⟩ := kv
        rcases lt_trichotomy k_v k₂ with hlt | heq | hgt
        · exact Or.inr (Or.inr ⟨k_v, val, rest_vs, rfl, hlt⟩)
        · subst heq; exact Or.inr (Or.inl ⟨val, rest_vs, rfl⟩)
        · refine Or.inl (fun p hp => ?_)
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact hgt
          · exact lt_trans hgt (List.rel_of_pairwise_cons hsv hmem)
    rcases hcase_v with hvgt | ⟨val, rest_vs, rfl⟩ | ⟨k_v, val, rest_vs, rfl, hk_v⟩
    · -- The writer's value has nothing at `k₂`: the reader injects `V_MISSING`.
      have hvs_none : vs.lookup k₂ = none := lookup_none_of_lt_all_val k₂ vs hvgt
      have hgetnone : (Value.mk vs).get? k₂ = none := hvs_none
      rcases hcase₁ with ⟨hfs₁_none, hfs₁_gt⟩ | ⟨f₁, rest₁, rfl⟩
      · -- M-Missing: the reader declares a key the writer never had.
        rw [compatTransformAux_cons_none k₂ f₂ rest₂ _ _ hgetnone]
        refine MsgCompat.missing_cons k₂ f₂ vs fs₁ _ rest₂
          (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂) hlt₂ ?_
          hvs_none hfs₁_none
          (lookup_none_of_lt_all_val k₂ _
            (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂)) hrest₂_none
        refine ih_n (fieldListSize fs₁ + fieldListSize rest₂ + valListSize vs)
          ?_ fs₁ vs rest₂ le_rfl hs₁ hsv hs₂.tail ha₁ hav
          (fieldListAllWF_tail ha₂) ?_ hwf
        · have e2 : fieldListSize ((k₂, f₂) :: rest₂) =
            fieldSize f₂ + fieldListSize rest₂ := rfl
          have := fieldSize_positive f₂
          omega
        · intro k f hk
          have hne : k ≠ k₂ := by
            intro heq; rw [heq, hfs₁_none] at hk; exact absurd hk (by simp)
          obtain ⟨g, hg, hgc⟩ := H k f hk
          rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]] at hg
          exact ⟨g, hg, hgc⟩
      · -- M-Declare: the writer declares a key its own value never populates.
        have hlt₁ : ∀ p ∈ rest₁, k₂ < p.1 := fun p hp =>
          List.rel_of_pairwise_cons hs₁ hp
        have hf₁f₂ : f₁ ∝ f₂ := by
          obtain ⟨g, hg, hgc⟩ := H k₂ f₁ (by simp)
          rw [List.lookup_cons, show (k₂ == k₂) = true from by simp] at hg
          have hgf : f₂ = g := by simpa using hg
          rw [hgf]; exact hgc
        rw [compatTransformAux_cons_none k₂ f₂ rest₂ _ _ hgetnone,
          compatTransformAux_prepend_ds rest₂ k₂ f₁ rest₁ (Value.mk vs) hlt₂]
        refine MsgCompat.declare_cons k₂ f₁ f₂ vs rest₁ _ rest₂ hlt₁
          (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂) hlt₂ ?_ hf₁f₂
          hvs_none (lookup_none_of_lt_all_field k₂ rest₁ hlt₁)
          (lookup_none_of_lt_all_val k₂ _
            (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂)) hrest₂_none
        refine ih_n (fieldListSize rest₁ + fieldListSize rest₂ + valListSize vs)
          ?_ rest₁ vs rest₂ le_rfl hs₁.tail hsv hs₂.tail (fieldListAllWF_tail ha₁)
          hav (fieldListAllWF_tail ha₂) ?_ ?_
        · have e1 : fieldListSize ((k₂, f₁) :: rest₁) =
            fieldSize f₁ + fieldListSize rest₁ := rfl
          have e2 : fieldListSize ((k₂, f₂) :: rest₂) =
            fieldSize f₂ + fieldListSize rest₂ := rfl
          have h1 := fieldSize_positive f₁
          have h2 := fieldSize_positive f₂
          omega
        · intro k f hk
          have hne : k ≠ k₂ := by
            intro heq
            rw [heq, lookup_none_of_lt_all_field k₂ rest₁ hlt₁] at hk
            exact absurd hk (by simp)
          have hk' : ((k₂, f₁) :: rest₁).lookup k = some f := by
            rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]]
            exact hk
          obtain ⟨g, hg, hgc⟩ := H k f hk'
          rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]] at hg
          exact ⟨g, hg, hgc⟩
        · exact valueWf_drop_head_ds k₂ f₁ rest₁ vs (fun kv hkv => hvgt kv hkv) hwf
    · -- The writer's value has an entry at `k₂`.
      have hlt_vs : ∀ p ∈ rest_vs, k₂ < p.1 := fun p hp =>
        List.rel_of_pairwise_cons hsv hp
      have hvs_head : (Value.mk ((k₂, val) :: rest_vs)).get? k₂ = some val := by
        show List.lookup k₂ ((k₂, val) :: rest_vs) = _
        simp
      have hrest_vs_none : rest_vs.lookup k₂ = none :=
        lookup_none_of_lt_all_val k₂ rest_vs hlt_vs
      rcases hcase₁ with ⟨hfs₁_none, hfs₁_gt⟩ | ⟨f₁, rest₁, rfl⟩
      · -- The key is unknown to the writer's descriptor: the entry disappears
        -- (M-Drop-Unknown) and the reader injects `V_MISSING` (M-Missing).
        have hhead : compatVal (some f₂) ((Desc.mk fs₁).get? k₂) val
            = Val.missing := by
          rw [show (Desc.mk fs₁).get? k₂ = none from hfs₁_none]
          cases f₂ <;> cases val <;> rfl
        rw [compatTransformAux_cons_some k₂ f₂ rest₂ _ _ val hvs_head, hhead,
          compatTransformAux_prepend_vs rest₂ k₂ val rest_vs (Desc.mk fs₁) hlt₂]
        refine MsgCompat.dropUnknown_cons k₂ val rest_vs fs₁ _ _ hlt_vs ?_
          hrest_vs_none hfs₁_none
        refine MsgCompat.missing_cons k₂ f₂ rest_vs fs₁ _ rest₂
          (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂) hlt₂ ?_
          hrest_vs_none hfs₁_none
          (lookup_none_of_lt_all_val k₂ _
            (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂)) hrest₂_none
        refine ih_n (fieldListSize fs₁ + fieldListSize rest₂ + valListSize rest_vs)
          ?_ fs₁ rest_vs rest₂ le_rfl hs₁ hsv.tail hs₂.tail ha₁
          (valListAllWF_tail hav) (fieldListAllWF_tail ha₂) ?_ ?_
        · have e2 : fieldListSize ((k₂, f₂) :: rest₂) =
            fieldSize f₂ + fieldListSize rest₂ := rfl
          have e3 : valListSize ((k₂, val) :: rest_vs) =
            valSize val + valListSize rest_vs := rfl
          have h1 := fieldSize_positive f₂
          have h2 := valSize_positive val
          omega
        · intro k f hk
          have hne : k ≠ k₂ := by
            intro heq; rw [heq, hfs₁_none] at hk; exact absurd hk (by simp)
          obtain ⟨g, hg, hgc⟩ := H k f hk
          rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]] at hg
          exact ⟨g, hg, hgc⟩
        · exact valueWf_cons fs₁ (k₂, val) rest_vs hwf
      · -- M-Drop followed by M-Update: the entry is reinterpreted.
        have hlt₁ : ∀ p ∈ rest₁, k₂ < p.1 := fun p hp =>
          List.rel_of_pairwise_cons hs₁ hp
        have hdk : ((k₂, f₁) :: rest₁).lookup k₂ = some f₁ := by simp
        have hf₁f₂ : f₁ ∝ f₂ := by
          obtain ⟨g, hg, hgc⟩ := H k₂ f₁ hdk
          rw [List.lookup_cons, show (k₂ == k₂) = true from by simp] at hg
          have hgf : f₂ = g := by simpa using hg
          rw [hgf]; exact hgc
        have hentry : valWfFold ((k₂, f₁) :: rest₁) k₂ val True :=
          valueWf_entry_head ((k₂, f₁) :: rest₁) (k₂, val) rest_vs hwf
        have hhead : compatVal (some f₂) ((Desc.mk ((k₂, f₁) :: rest₁)).get? k₂) val
            = compatVal (some f₂) (some f₁) val := by
          rw [show (Desc.mk ((k₂, f₁) :: rest₁)).get? k₂ = some f₁ from hdk]
        -- The value relation at the head, recursing at nested messages.
        have hvc : ⟨ val ∷ f₁ ⟩≺⟨ compatVal (some f₂) (some f₁) val ∷ f₂ ⟩ := by
          cases val with
          | missing =>
            exact absurd hentry (fun h =>
              valWfFold_missing_elim _ k₂ f₁ True hdk h)
          | bool b =>
            have hf : f₁ = .bool := valWfFold_bool_field _ k₂ b f₁ True hdk hentry
            subst hf
            cases f₂ with
            | bool => exact ValCompat.refl _ _
            | int => exact ValCompat.boolInt b _ rfl
            | msg d₂' =>
              exact absurd rfl
                (fieldCompat_scalar_inv _ _ hf₁f₂ (by rintro d ⟨⟩) d₂')
          | int z =>
            have hf : f₁ = .int := valWfFold_int_field _ k₂ z f₁ True hdk hentry
            subst hf
            have hz : 0 ≤ z := by
              unfold valWfFold at hentry
              rw [hdk] at hentry
              exact hentry.2.2.2.1
            cases f₂ with
            | bool =>
              refine ValCompat.intBool z _ ?_
              show decide (0 < z) = if z = 0 then false else true
              by_cases h : z = 0
              · simp [h]
              · rw [if_neg h, decide_eq_true_eq]
                omega
            | int => exact ValCompat.refl _ _
            | msg d₂' =>
              exact absurd rfl
                (fieldCompat_scalar_inv _ _ hf₁f₂ (by rintro d ⟨⟩) d₂')
          | msg v' =>
            obtain ⟨d₁', hf, hwf'⟩ := valWfFold_msg_field _ k₂ v' f₁ True hdk hentry
            subst hf
            obtain ⟨d₂', hd₂eq, hdc⟩ := fieldCompat_msg_inv d₁' f₂ hf₁f₂
            subst hd₂eq
            refine ValCompat.msg v' d₁' (compatTransform d₁' d₂' v') d₂' ?_
            -- Recurse into the nested message.
            obtain ⟨g₁⟩ := d₁'
            obtain ⟨g₂⟩ := d₂'
            obtain ⟨ws⟩ := v'
            have hall₁ : fieldAllWF (Field.msg (Desc.mk g₁)) :=
              fieldListAllWF_head ha₁
            have hall₂ : fieldAllWF (Field.msg (Desc.mk g₂)) :=
              fieldListAllWF_head ha₂
            have hallv : valAllWF (Val.msg (Value.mk ws)) := valListAllWF_head hav
            refine ih_n (fieldListSize g₁ + fieldListSize g₂ + valListSize ws)
              ?_ g₁ ws g₂ le_rfl hall₁.1.1 hallv.1.1 hall₂.1.1 hall₁.2 hallv.2
              hall₂.2 (fun k f hk => descCompat_field _ _ k hdc f hk) hwf'
            have e1 : fieldListSize ((k₂, Field.msg (Desc.mk g₁)) :: rest₁) =
              (1 + (1 + fieldListSize g₁)) + fieldListSize rest₁ := rfl
            have e2 : fieldListSize ((k₂, Field.msg (Desc.mk g₂)) :: rest₂) =
              (1 + (1 + fieldListSize g₂)) + fieldListSize rest₂ := rfl
            have e3 : valListSize ((k₂, Val.msg (Value.mk ws)) :: rest_vs) =
              (1 + (1 + valListSize ws)) + valListSize rest_vs := rfl
            omega
        rw [compatTransformAux_cons_some k₂ f₂ rest₂ _ _ val hvs_head, hhead,
          compatTransformAux_prepend_ds rest₂ k₂ f₁ rest₁ _ hlt₂,
          compatTransformAux_prepend_vs rest₂ k₂ val rest_vs (Desc.mk rest₁) hlt₂]
        refine MsgCompat.update_cons k₂ val f₁ (compatVal (some f₂) (some f₁) val)
          f₂ rest_vs rest₁ _ rest₂ hlt_vs hlt₁
          (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂) hlt₂ ?_ hvc hf₁f₂
          hrest_vs_none (lookup_none_of_lt_all_field k₂ rest₁ hlt₁)
          (lookup_none_of_lt_all_val k₂ _
            (compatTransformAux_keys_gt rest₂ _ _ k₂ hlt₂)) hrest₂_none
        refine ih_n (fieldListSize rest₁ + fieldListSize rest₂ + valListSize rest_vs)
          ?_ rest₁ rest_vs rest₂ le_rfl hs₁.tail hsv.tail hs₂.tail
          (fieldListAllWF_tail ha₁) (valListAllWF_tail hav)
          (fieldListAllWF_tail ha₂) ?_ ?_
        · have e1 : fieldListSize ((k₂, f₁) :: rest₁) =
            fieldSize f₁ + fieldListSize rest₁ := rfl
          have e2 : fieldListSize ((k₂, f₂) :: rest₂) =
            fieldSize f₂ + fieldListSize rest₂ := rfl
          have e3 : valListSize ((k₂, val) :: rest_vs) =
            valSize val + valListSize rest_vs := rfl
          have h1 := fieldSize_positive f₁
          have h2 := fieldSize_positive f₂
          have h3 := valSize_positive val
          omega
        · intro k f hk
          have hne : k ≠ k₂ := by
            intro heq
            rw [heq, lookup_none_of_lt_all_field k₂ rest₁ hlt₁] at hk
            exact absurd hk (by simp)
          have hk' : ((k₂, f₁) :: rest₁).lookup k = some f := by
            rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]]
            exact hk
          obtain ⟨g, hg, hgc⟩ := H k f hk'
          rw [List.lookup_cons, show (k == k₂) = false from by simp [hne]] at hg
          exact ⟨g, hg, hgc⟩
        · exact valueWf_drop_head_ds k₂ f₁ rest₁ rest_vs hlt_vs
            (valueWf_cons _ (k₂, val) rest_vs hwf)
    · -- A writer entry below every declared key: M-Drop-Unknown.
      have hlt_vs : ∀ p ∈ rest_vs, k_v < p.1 := fun p hp =>
        List.rel_of_pairwise_cons hsv hp
      have hfs₂_gt : ∀ p ∈ (k₂, f₂) :: rest₂, k_v < p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact hk_v
        · exact lt_trans hk_v (hlt₂ p hmem)
      rw [compatTransformAux_prepend_vs ((k₂, f₂) :: rest₂) k_v val rest_vs
        (Desc.mk fs₁) hfs₂_gt]
      refine MsgCompat.dropUnknown_cons k_v val rest_vs fs₁ _ _ hlt_vs ?_
        (lookup_none_of_lt_all_val k_v rest_vs hlt_vs)
        (lookup_none_of_lt_all_field k_v fs₁
          (fun p hp => lt_of_lt_of_le hk_v (hfs₁_ge p hp)))
      refine ih_n (fieldListSize fs₁ + fieldListSize ((k₂, f₂) :: rest₂) +
        valListSize rest_vs) ?_ fs₁ rest_vs ((k₂, f₂) :: rest₂) le_rfl
        hs₁ hsv.tail hs₂ ha₁ (valListAllWF_tail hav) ha₂ H
        (valueWf_cons fs₁ (k_v, val) rest_vs hwf)
      have e3 : valListSize ((k_v, val) :: rest_vs) =
        valSize val + valListSize rest_vs := rfl
      have h3 := valSize_positive val
      omega

/-- The cross-descriptor round-trip theorem: a value `v` written under `d₁`
    and read back under any `d₂` the writer's schema evolves into is related
    to the result by `≼`. -/
theorem compatRoundTrip (v : Value) (d₁ d₂ : Desc) :
    d₁.AllWF → v.AllWF → d₂.AllWF → d₁ ⋘ d₂ → valueWf d₁ v →
    ⟨ v ∷ d₁ ⟩⪯⟨ compatTransform d₁ d₂ v ∷ d₂ ⟩ := by
  intro hd₁ hv hd₂ hc hwf
  cases d₁ with | mk fs₁ =>
  cases d₂ with | mk fs₂ =>
  cases v with | mk vs =>
  exact compatRoundTrip_aux_wf _ fs₁ vs fs₂ le_rfl hd₁.1.1 hv.1.1 hd₂.1.1
    hd₁.2 hv.2 hd₂.2 (fun k f hk => descCompat_field _ _ k hc f hk) hwf

end Pollux.InterParse
