/-
  Pollux.InterParse.Descriptor — Descriptor and Value types for the intermediate format.

  Corresponds to src/InterParse/Descriptor.v in the Rocq development.

  The intermediate format uses tagged key-value pairs with integer field numbers.
  Descriptors describe the schema (field types), and Values hold the data.

  ## Map with extensionality

  The mutual inductive types (`Desc`/`Field`, `Value`/`Val`) store their fields
  as `List (Int × _)` because Lean's kernel positivity checker cannot see through
  structures that bundle proof obligations (e.g. `AList`, `Finmap`, `TreeMap`).

  To obtain map semantics with extensionality, we impose a **sorted, no-dup**
  invariant (`Desc.WF` / `Value.WF`) on the key lists.  Under this invariant
  the lookup function uniquely determines the list, giving us:

      `Desc.ext_lookup : d₁.WF → d₂.WF → (∀ k, d₁.get? k = d₂.get? k) → d₁ = d₂`

  All constructor functions (`∅`, `insert`, `erase`) preserve the invariant.
-/
import Pollux.Parse.Input
import Pollux.Parse.Result
import Mathlib

namespace Pollux.InterParse

-- ## Descriptor types

-- A descriptor maps field numbers (integers) to field types.
-- Mutually defined with `Field` which may contain nested descriptors.
-- Corresponds to `Desc`/`Field` from `InterParse/Descriptor.v`.
mutual
inductive Desc where
  | mk (fs : List (Int × Field))
inductive Field where
  | msg (d : Desc)
  | bool
  | int
end

/-! ### Sorted-map predicates -/

/-- The key list of a `Desc` is strictly sorted by the first component. -/
def Desc.Sorted : Desc → Prop
  | .mk fs => List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs

/-- The key list of a `Desc` has no duplicate keys. -/
def Desc.NodupKeys : Desc → Prop
  | .mk fs => (fs.map Prod.fst).Nodup

/-- Well-formed descriptor: sorted and no duplicate keys. -/
def Desc.WF (d : Desc) : Prop := d.Sorted ∧ d.NodupKeys

namespace Desc

/-- Extract the field list from a descriptor. Corresponds to `Fields`. -/
def fields : Desc → List (Int × Field)
  | .mk fs => fs

/-- Lookup a field by number. Corresponds to `Fields d !! k`. -/
def get? (d : Desc) (k : Int) : Option Field := d.fields.lookup k

instance : EmptyCollection Desc := ⟨.mk []⟩

/-- Sorted insertion into a key-ordered association list, replacing any
    existing entry with the same key. -/
def sortedInsert (k : Int) (f : Field) :
    List (Int × Field) → List (Int × Field)
  | [] => [(k, f)]
  | (k', f') :: rest =>
    if k < k' then (k, f) :: (k', f') :: rest
    else if k == k' then (k, f) :: rest
    else (k', f') :: sortedInsert k f rest

/-- Insert a field, maintaining the sorted, no-dup invariant. -/
def insert (d : Desc) (k : Int) (f : Field) : Desc :=
  .mk (sortedInsert k f d.fields)

/-- Sorted deletion from a key-ordered association list. -/
def sortedErase (k : Int) : List (Int × Field) → List (Int × Field)
  | [] => []
  | (k', f') :: rest =>
    if k == k' then rest
    else if k < k' then (k', f') :: rest  -- k not present (list is sorted)
    else (k', f') :: sortedErase k rest

/-- Delete a field by key. -/
def erase (d : Desc) (k : Int) : Desc :=
  .mk (sortedErase k d.fields)

/-- The empty descriptor is well-formed. -/
theorem empty_wf : (∅ : Desc).WF :=
  ⟨List.Pairwise.nil, List.nodup_nil⟩

/-- `insert` preserves well-formedness. -/
theorem insert_wf (d : Desc) (k : Int) (f : Field) :
    d.WF → (d.insert k f).WF := by
  unfold Desc.insert;
  -- By definition of `sortedInsert`, the list `sortedInsert k f d.fields` is sorted.
  have h_sorted : ∀ (l : List (Int × Field)), List.Pairwise (fun a b => a.1 < b.1) l → List.Pairwise (fun a b => a.1 < b.1) (sortedInsert k f l) := by
    intro l hl;
    induction' l with l_head l_tail ih;
    · exact List.pairwise_singleton _ _;
    · by_cases h : k < l_head.1 <;> by_cases h' : k == l_head.1 <;> simp_all +decide [ List.pairwise_cons ];
      · rw [ sortedInsert ];
        simp_all +decide [ List.pairwise_cons ];
        exact ⟨ fun a b hab => lt_trans h ( hl.1 a b hab ), hl.1 ⟩;
      · unfold sortedInsert; aesop;
      · rw [ show sortedInsert k f ( l_head :: l_tail ) = l_head :: sortedInsert k f l_tail from ?_ ];
        · simp_all +decide [ List.pairwise_cons ];
          intro a b hab; induction l_tail <;> simp_all +decide [ sortedInsert ] ;
          · exact lt_of_le_of_ne h ( Ne.symm h' );
          · grind;
        · exact if_neg ( by aesop ) |> fun h => h.trans ( if_neg ( by aesop ) );
  intro h;
  cases h ; simp_all +decide [ Desc.WF ];
  have h_nodup : ∀ (l : List (Int × Field)), List.Pairwise (fun a b => a.1 < b.1) l → (List.map Prod.fst l).Nodup → (List.map Prod.fst (sortedInsert k f l)).Nodup := by
    grind +splitIndPred;
  unfold Desc.Sorted Desc.NodupKeys at *; aesop;

/-- `erase` preserves well-formedness. -/
theorem erase_wf (d : Desc) (k : Int) :
    d.WF → (d.erase k).WF := by
  intro hd;
  -- Show that the erased descriptor is sorted.
  have h_sorted : (d.erase k).Sorted := by
    obtain ⟨ hd₁, hd₂ ⟩ := hd;
    -- By definition of `sortedErase`, the resulting list is still sorted.
    have h_sorted_erase : ∀ (l : List (Int × Field)), List.Pairwise (fun a b => a.1 < b.1) l → ∀ (k : Int), List.Pairwise (fun a b => a.1 < b.1) (sortedErase k l) := by
      intros l hl k; induction' l with hd tl ih generalizing k <;> simp_all +decide [ List.pairwise_cons ] ;
      · exact List.Pairwise.nil;
      · by_cases hk : k == hd.1 <;> simp_all +decide [ sortedErase ];
        split_ifs <;> simp_all +decide [ List.pairwise_cons ];
        · exact hl.1;
        · intro a b hab;
          have h_sorted_erase : ∀ (l : List (ℤ × Field)), List.Pairwise (fun a b => a.1 < b.1) l → ∀ (k : ℤ), ∀ (a : ℤ × Field), a ∈ sortedErase k l → a ∈ l := by
            intros l hl k a ha; induction' l with hd tl ih generalizing k <;> simp_all +decide [ sortedErase ] ;
            grind;
          exact hl.1 _ _ ( h_sorted_erase _ hl.2 _ _ hab );
    cases d ; tauto;
  grind +locals

/-- Lookup after insert (same key). -/
theorem get?_insert_same (d : Desc) (k : Int) (f : Field) :
    d.WF → (d.insert k f).get? k = some f := by
  unfold Desc.insert Desc.get?;
  induction' d.fields with hd tl ih generalizing k f;
  · -- In the base case, when the list is empty, inserting k f results in [(k, f)], and looking up k in this list returns some f.
    simp [Desc.fields, sortedInsert];
  · unfold sortedInsert;
    unfold Desc.fields; simp +decide;
    unfold List.lookup; aesop;

/-- Lookup after insert (different key). -/
theorem get?_insert_ne (d : Desc) (k k' : Int) (f : Field) :
    d.WF → k ≠ k' → (d.insert k f).get? k' = d.get? k' := by
  cases d;
  induction ‹List _› <;> simp_all +decide [ Desc.insert, Desc.get? ];
  · simp +decide [ Desc.fields, sortedInsert ];
    tauto;
  · grind +locals

/-- Lookup after erase (same key). -/
theorem get?_erase_same (d : Desc) (k : Int) :
    d.WF → (d.erase k).get? k = none := by
  intro h;
  obtain ⟨h_sorted, h_nodup⟩ := h;
  -- By definition of `sortedErase`, if `k` is in the list, it will be removed.
  have h_erase : ∀ {l : List (Int × Field)}, List.Pairwise (fun a b => a.1 < b.1) l → ∀ k, (sortedErase k l).lookup k = none := by
    intros l hl k; induction' l with hd tl ih generalizing k <;> simp_all +decide ;
    · tauto;
    · intro a b hab; contrapose! ih; simp_all +decide [ sortedErase ] ;
      grind;
  nontriviality;
  cases d ; tauto

/-- Lookup after erase (different key). -/
theorem get?_erase_ne (d : Desc) (k k' : Int) :
    d.WF → k ≠ k' → (d.erase k).get? k' = d.get? k' := by
  rcases d with ⟨ fs ⟩;
  induction' fs with k' f' fs ih;
  · aesop;
  · grind +locals

/-- **Extensionality**: two well-formed descriptors with the same lookups are
equal. This is the main result that makes `Desc` behave like a proper map type. -/
theorem ext_lookup (d₁ d₂ : Desc) :
    d₁.WF → d₂.WF → (∀ k, d₁.get? k = d₂.get? k) → d₁ = d₂ := by
  rintro ⟨ h₁, h₂ ⟩ ⟨ h₃, h₄ ⟩ h₅;
  -- By induction on the length of the field list.
  have h_ind : ∀ (fs₁ fs₂ : List (Int × Field)), List.Pairwise (fun a b => a.1 < b.1) fs₁ → List.Pairwise (fun a b => a.1 < b.1) fs₂ → List.Nodup (List.map Prod.fst fs₁) → List.Nodup (List.map Prod.fst fs₂) → (∀ k, List.lookup k fs₁ = List.lookup k fs₂) → fs₁ = fs₂ := by
    intros fs₁ fs₂ h₁ h₂ h₃ h₄ h₅; induction' fs₁ with k₁ f₁ fs₁ ih generalizing fs₂ <;> induction' fs₂ with k₂ f₂ fs₂ ih' <;> simp_all +decide ;
    · specialize h₅ k₂.1 ; simp_all +decide [ List.lookup ];
    · simpa using h₅ k₁.1;
    · have h_eq : k₁.1 = k₂.1 := by
        contrapose! h₅;
        use if k₁.1 < k₂.1 then k₁.1 else k₂.1;
        grind +suggestions;
      have h_eq : k₁.2 = k₂.2 := by
        specialize h₅ k₁.1; aesop;
      have h_eq : ∀ k, List.lookup k f₁ = List.lookup k f₂ := by
        intro k; specialize h₅ k; by_cases hk : k = k₁.1 <;> simp_all +decide ;
        · grind +suggestions;
        · grind;
      exact ⟨ Prod.ext ‹_› ‹_›, fs₁ f₂ h₂.2 h₄.2 h_eq ⟩;
  cases d₁ ; cases d₂ ; aesop

end Desc

-- ## Value types

-- A value maps field numbers to typed values.
-- Mutually defined with `Val` which may contain nested values.
-- Corresponds to `Value`/`Val` from `InterParse/Descriptor.v`.
mutual
inductive Value where
  | mk (vs : List (Int × Val))
inductive Val where
  | msg (v : Value)
  | bool (b : Bool)
  | int (z : Int)
  | missing
end

/-! ### Sorted-map predicates for Value -/

/-- The key list of a `Value` is strictly sorted. -/
def Value.Sorted : Value → Prop
  | .mk vs => List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs

/-- The key list of a `Value` has no duplicate keys. -/
def Value.NodupKeys : Value → Prop
  | .mk vs => (vs.map Prod.fst).Nodup

/-- Well-formed value: sorted and no duplicate keys. -/
def Value.WF (v : Value) : Prop := v.Sorted ∧ v.NodupKeys

namespace Value

/-- Extract the val list from a value. Corresponds to `Vals`. -/
def vals : Value → List (Int × Val)
  | .mk vs => vs

/-- Lookup a val by field number. -/
def get? (v : Value) (k : Int) : Option Val := v.vals.lookup k

instance : EmptyCollection Value := ⟨.mk []⟩

/-- Sorted insertion into a key-ordered association list, replacing any
    existing entry with the same key. -/
def sortedInsert (k : Int) (val : Val) :
    List (Int × Val) → List (Int × Val)
  | [] => [(k, val)]
  | (k', v') :: rest =>
    if k < k' then (k, val) :: (k', v') :: rest
    else if k == k' then (k, val) :: rest
    else (k', v') :: sortedInsert k val rest

/-- Insert a val, maintaining the sorted, no-dup invariant. -/
def insert (v : Value) (k : Int) (val : Val) : Value :=
  .mk (sortedInsert k val v.vals)

/-- Sorted deletion from a key-ordered association list. -/
def sortedErase (k : Int) : List (Int × Val) → List (Int × Val)
  | [] => []
  | (k', v') :: rest =>
    if k == k' then rest
    else if k < k' then (k', v') :: rest
    else (k', v') :: sortedErase k rest

/-- Delete a val by key. -/
def erase (v : Value) (k : Int) : Value :=
  .mk (sortedErase k v.vals)

/-
The empty value is well-formed.
-/
theorem empty_wf : (∅ : Value).WF := by
  constructor;
  · exact List.Pairwise.nil;
  · exact List.nodup_nil

/-- `insert` preserves well-formedness. -/
theorem insert_wf (v : Value) (k : Int) (val : Val) :
    v.WF → (v.insert k val).WF := by
  intro hvWF
  obtain ⟨hvSorted, hvNodup⟩ := hvWF;
  -- By definition of `sortedInsert`, the resulting list is sorted and has no duplicate keys.
  have h_sorted_insert : ∀ (k : Int) (val : Val) (vs : List (Int × Val)), List.Pairwise (fun a b => a.1 < b.1) vs → List.Nodup (vs.map Prod.fst) → List.Pairwise (fun a b => a.1 < b.1) (sortedInsert k val vs) ∧ List.Nodup ((sortedInsert k val vs).map Prod.fst) := by
    intros k val vs hvSorted hvNodup;
    induction' vs with vs_head vs_tail ih generalizing k val <;> simp_all +decide [ List.pairwise_cons ];
    · exact ⟨ List.pairwise_singleton _ _, List.nodup_singleton _ ⟩;
    · by_cases hk : k < vs_head.1 <;> by_cases hk' : k == vs_head.1 <;> simp_all +decide [ sortedInsert ];
      · grind;
      · exact hvSorted.1;
      · split_ifs <;> simp_all +decide [ List.pairwise_cons, List.nodup_cons ];
        · linarith;
        · have h_sorted_insert : ∀ (k : Int) (val : Val) (vs : List (Int × Val)), List.Pairwise (fun a b => a.1 < b.1) vs → ∀ (a : Int × Val), a ∈ sortedInsert k val vs → a ∈ vs ∨ a = (k, val) := by
            intros k val vs hvSorted a ha
            induction' vs with vs_head vs_tail ih generalizing k val a;
            · exact?;
            · grind +locals;
          grind;
  cases v ; aesop

/-- `erase` preserves well-formedness. -/
theorem erase_wf (v : Value) (k : Int) :
    v.WF → (v.erase k).WF := by
  unfold Value.WF;
  unfold Value.NodupKeys Value.Sorted at *; simp +decide [ Value.vals, Value.erase ] at *;
  rcases v with ⟨ vs ⟩;
  induction vs <;> simp +decide [ sortedErase ] at *;
  split_ifs <;> simp_all +decide [ List.pairwise_cons ];
  · tauto;
  · rename_i h₁ h₂ h₃ h₄;
    intro h₅ h₆ h₇ h₈; specialize h₂ h₆ h₈; simp_all +decide [ List.pairwise_iff_get ] ;
    -- By definition of `sortedErase`, the elements in the resulting list are a subset of the original list.
    have h_subset : ∀ (l : List (ℤ × Val)), (∀ (a : ℤ) (b : Val), (a, b) ∈ sortedErase k l → (a, b) ∈ l) := by
      intros l a b hab; induction l <;> simp_all +decide [ sortedErase ] ;
      grind;
    exact ⟨ fun a b hab => h₅ a b ( h_subset _ _ _ hab ), fun x hx => h₇ x ( h_subset _ _ _ hx ) ⟩

/-- Lookup after insert (same key). -/
theorem get?_insert_same (v : Value) (k : Int) (val : Val) :
    v.WF → (v.insert k val).get? k = some val := by
  -- By definition of `sortedInsert`, inserting `k` with value `val` into `v` results in a new value `v'` such that `v'.get? k = some val`.
  unfold Value.insert;
  unfold Value.get?;
  induction' v.vals with hd tl ih;
  · unfold Value.vals; simp +decide [ sortedInsert ] ;
  · unfold sortedInsert;
    split_ifs <;> simp_all +decide [ Value.vals ];
    rw [ List.lookup_cons ] ; aesop

/-- Lookup after insert (different key). -/
theorem get?_insert_ne (v : Value) (k k' : Int) (val : Val) :
    v.WF → k ≠ k' → (v.insert k val).get? k' = v.get? k' := by
  intro hv hk; cases v; simp_all +decide [ Value.insert, Value.get? ] ;
  have h_sorted_insert : ∀ (k : ℤ) (val : Val) (vs : List (ℤ × Val)), List.Pairwise (fun a b => a.1 < b.1) vs → (k ≠ k' → List.lookup k' (sortedInsert k val vs) = List.lookup k' vs) := by
    intros k val vs hv hk; induction' vs with vs ih <;> simp_all +decide [ sortedInsert ] ;
    · tauto;
    · grind;
  exact h_sorted_insert k val _ hv.1 hk

/-- Lookup after erase (same key). -/
theorem get?_erase_same (v : Value) (k : Int) :
    v.WF → (v.erase k).get? k = none := by
  cases v;
  induction ‹List _› <;> simp_all +decide [ Value.erase, Value.get? ];
  · simp +decide [ Value.vals, sortedErase ];
  · unfold Value.WF at *; simp_all +decide [ Value.vals ] ;
    rename_i h₁ h₂ h₃;
    unfold sortedErase; simp_all +decide [ Value.Sorted, Value.NodupKeys ] ;
    grind

/-- Lookup after erase (different key). -/
theorem get?_erase_ne (v : Value) (k k' : Int) :
    v.WF → k ≠ k' → (v.erase k).get? k' = v.get? k' := by
  intros hv hk_ne_k';
  rcases v with ⟨ vs ⟩;
  induction vs <;> simp_all +decide [ Value.erase ];
  · rfl;
  · grind +locals

/-- **Extensionality**: two well-formed values with the same lookups are equal. -/
theorem ext_lookup (v₁ v₂ : Value) :
    v₁.WF → v₂.WF → (∀ k, v₁.get? k = v₂.get? k) → v₁ = v₂ := by
  -- By induction on the length of the lists, we can show that if two lists are sorted and have the same lookups, they are equal.
  have h_ind : ∀ (l₁ l₂ : List (Int × Val)), List.Pairwise (fun a b => a.1 < b.1) l₁ → List.Pairwise (fun a b => a.1 < b.1) l₂ → (∀ k, List.lookup k l₁ = List.lookup k l₂) → l₁ = l₂ := by
    intros l₁ l₂ hl₁ hl₂ h_eq
    induction' l₁ with a l₁ ih generalizing l₂;
    · cases l₂ <;> simp_all +decide [ List.lookup ];
      specialize h_eq ( ‹ℤ × Val›.1 ) ; simp_all +decide;
    · rcases l₂ with ( _ | ⟨ b, l₂ ⟩ ) <;> simp_all +decide;
      · simpa using h_eq a.1;
      · have h_eq_keys : a.1 = b.1 := by
          contrapose! h_eq;
          cases lt_or_gt_of_ne h_eq <;> simp_all +decide;
          · use a.1;
            simp +decide [ *, List.lookup ];
            rw [ show List.lookup a.1 l₂ = none from _ ];
            · cases h : a.1 == b.1 <;> simp_all +decide;
            · grind +revert;
          · use b.1;
            simp_all +decide [ List.lookup ];
            rw [ show List.lookup b.1 l₁ = none from _ ];
            · cases h : b.1 == a.1 <;> simp_all +decide;
            · grind;
        have h_eq_vals : a.2 = b.2 := by
          specialize h_eq a.1; aesop;
        specialize ih l₂ hl₂.2;
        simp_all +decide [ Prod.ext_iff ];
        apply ih;
        intro k; specialize h_eq k; simp_all +decide [ List.lookup ] ;
        by_cases hk : k == b.1 <;> simp_all +decide;
        rw [ List.lookup_eq_none_iff.mpr, List.lookup_eq_none_iff.mpr ];
        · grind;
        · grind;
  exact fun h₁ h₂ h₃ => by cases v₁; cases v₂; exact congr_arg _ ( h_ind _ _ h₁.1 h₂.1 h₃ ) ;

end Value

/-! ## Map helper: full outer join -/

/-- Full outer join of two association lists. Corresponds to `merge` from stdpp. -/
def listMerge {α β γ : Type} (f : Option α → Option β → Option γ)
    (m1 : List (Int × α)) (m2 : List (Int × β)) : List (Int × γ) :=
  let fromM1 := m1.filterMap fun (k, a) =>
    (f (some a) (m2.lookup k)).map (k, ·)
  let fromM2Only := m2.filterMap fun (k, b) =>
    if m1.lookup k |>.isSome then none
    else (f none (some b)).map (k, ·)
  fromM1 ++ fromM2Only

-- ## Size metrics
--
-- Structural size metrics for well-founded induction, mirroring the Rocq
-- `Desc_size`, `Field_size`, `Value_size`, `Val_size`.

mutual
def descSize : Desc → Nat
  | .mk fs => 1 + fieldListSize fs
def fieldSize : Field → Nat
  | .msg d => 1 + descSize d
  | .bool | .int => 1
def fieldListSize : List (Int × Field) → Nat
  | [] => 0
  | (_, f) :: rest => fieldSize f + fieldListSize rest
end

theorem fieldSize_positive : ∀ f : Field, fieldSize f > 0 := by
  intro f;
  unfold fieldSize;
  cases f <;> simp +arith +decide

theorem descSize_positive : ∀ d : Desc, descSize d > 0 := by
  unfold descSize;
  exact fun d => Nat.pos_of_ne_zero ( by cases d ; simp +decide )

theorem fieldInMap_smaller (m : List (Int × Field)) (k : Int) (f : Field) :
    (k, f) ∈ m → fieldSize f < 1 + fieldListSize m := by
  induction' m with m ih generalizing k f;
  · tauto;
  · cases m ; cases ih <;> simp_all +arith +decide [ fieldListSize ];
    grind

mutual
def valueSize : Value → Nat
  | .mk vs => 1 + valListSize vs
def valSize : Val → Nat
  | .msg v => 1 + valueSize v
  | .bool _ | .int _ | .missing => 1
def valListSize : List (Int × Val) → Nat
  | [] => 0
  | (_, v) :: rest => valSize v + valListSize rest
end

theorem valSize_positive : ∀ v : Val, valSize v > 0 := by
  intro v;
  cases v <;> simp_all +decide [ valSize ]

theorem valueSize_positive : ∀ v : Value, valueSize v > 0 := by
  intro v;
  rcases v with ⟨ _ | ⟨ k, v ⟩ ⟩;
  · exact Nat.succ_pos _;
  · exact add_pos_of_pos_of_nonneg zero_lt_one ( Nat.zero_le _ )

theorem valInMap_smaller (m : List (Int × Val)) (k : Int) (v : Val) :
    (k, v) ∈ m → valSize v < 1 + valListSize m := by
  intro hv;
  induction' m with m ih;
  · contradiction;
  · cases hv <;> simp_all +arith +decide;
    · exact Nat.le_add_right _ _;
    · exact le_trans ( by solve_by_elim ) ( Nat.le_add_left _ _ )

-- ## Initialization
--
-- Build a default value matching a descriptor's structure. Boolean and integer
-- fields default to `V_MISSING`; message fields recurse.

mutual
def Desc.init : Desc → Value
  | .mk fs => .mk (initFieldList fs)
def initFieldList : List (Int × Field) → List (Int × Val)
  | [] => []
  | (k, .msg d) :: rest => (k, .msg d.init) :: initFieldList rest
  | (k, _) :: rest => (k, .missing) :: initFieldList rest
end

-- ## Subset and equality

mutual
/-- Check whether `v1`'s entries are a subset of `v2`'s. -/
def valueSubset : Value → Value → Bool
  | .mk vs1, v2 => subsetAux v2 vs1
def subsetAux (v2 : Value) : List (Int × Val) → Bool
  | [] => true
  | (k, v) :: rest =>
    if !subsetAux v2 rest then false
    else match v2.get? k with
      | some (.bool b') => match v with | .bool b => b == b' | _ => false
      | some (.int z')  => match v with | .int z  => z == z' | _ => false
      | some .missing   => match v with | .missing => true | _ => false
      | some (.msg v')  => match v with | .msg v'' => valueSubset v'' v' | _ => false
      | none => false
end

/-- Bidirectional subset check. -/
def valueEqb (v1 v2 : Value) : Bool :=
  valueSubset v1 v2 && valueSubset v2 v1

-- ## Validity predicates

-- `valid d v` holds when every field required by descriptor `d` exists in
-- value `v` with the correct type. Values may have extra fields.
-- Corresponds to `Valid` in the Rocq development.
mutual
def valid : Desc → Value → Prop
  | .mk fs, .mk vs => validFoldList vs fs True
def validFold (vs : List (Int × Val)) (k : Int) (f : Field) (acc : Prop) : Prop :=
  match f with
  | .bool => acc ∧ ∃ b, vs.lookup k = some (.bool b)
  | .int  => acc ∧ ∃ z, vs.lookup k = some (.int z)
  | .msg d => acc ∧ ∃ v, vs.lookup k = some (.msg v) ∧ valid d v
def validFoldList (vs : List (Int × Val)) : List (Int × Field) → Prop → Prop
  | [], acc => acc
  | (k, f) :: rest, acc => validFoldList vs rest (validFold vs k f acc)
end

-- `valid' d v` is the dual: checks that every entry in `v` is described by `d`.
-- Corresponds to `Valid'` in the Rocq development.
mutual
def valid' : Desc → Value → Prop
  | .mk fs, .mk vs => valid'FoldList fs vs True
def valid'Fold (fs : List (Int × Field)) (k : Int) (v : Val) (acc : Prop) : Prop :=
  match v with
  | .bool _ => fs.lookup k = some .bool ∧ acc
  | .int _  => fs.lookup k = some .int ∧ acc
  | .msg value => (∃ d, fs.lookup k = some (.msg d) ∧ valid' d value) ∧ acc
  | .missing => True ∧ acc
def valid'FoldList (fs : List (Int × Field)) : List (Int × Val) → Prop → Prop
  | [], acc => acc
  | (k, v) :: rest, acc => valid'FoldList fs rest (valid'Fold fs k v acc)
end

-- ## Depth and encoding length metrics
--
-- These are used by the recursive serializer's termination argument and by
-- encoding-length correctness proofs.

mutual
def valueDepth : Value → Nat
  | .mk vs => valueDepthList vs 0
def valueDepthFold (v : Val) (acc : Nat) : Nat :=
  match v with
  | .bool _ | .int _ | .missing => acc
  | .msg v' => Nat.max acc (valueDepth v' + 1)
def valueDepthList : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (_, v) :: rest, acc => valueDepthList rest (valueDepthFold v acc)
end

mutual
def valueEncLen : Value → Nat
  | .mk vs => valueEncLenList vs 0
def valueEncLenFold (v : Val) (acc : Nat) : Nat :=
  match v with
  | .bool _ => acc + 5
  | .int _  => acc + 5
  | .missing => acc
  | .msg v' => acc + 2 + valueEncLen v'
def valueEncLenList : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (_, v) :: rest, acc => valueEncLenList rest (valueEncLenFold v acc)
end

mutual
def valueEncLen' : Desc → Value → Nat
  | .mk ds, .mk vs => valueEncLen'List ds vs 0
def valueEncLen'Fold (ds : List (Int × Field)) (k : Int) (v : Val) (acc : Nat) : Nat :=
  match ds.lookup k, v with
  | none, _ => acc
  | some _, .bool _ => acc + 5
  | some _, .int _  => acc + 5
  | some (.msg d), .msg val => acc + 2 + valueEncLen' d val
  | some _, _ => acc
def valueEncLen'List (ds : List (Int × Field)) : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (k, v) :: rest, acc => valueEncLen'List ds rest (valueEncLen'Fold ds k v acc)
end

-- ## Well-formedness for serialization

mutual
def valueWf : Desc → Value → Prop
  | .mk ds, .mk vs => valWfFoldList ds vs True
def valWfFold (ds : List (Int × Field)) (k : Int) (v : Val) (acc : Prop) : Prop :=
  match ds.lookup k, v with
  | none, _ => acc
  | some .bool, .bool _ => 0 ≤ k ∧ k < 256 ∧ acc
  | some .int, .int z => acc ∧ 0 ≤ k ∧ k < 256 ∧ 0 ≤ z ∧ z < 2 ^ 32
  | some (.msg d), .msg val => acc ∧ 0 ≤ k ∧ k < 256 ∧ valueWf d val
  | _, _ => False
def valWfFoldList (ds : List (Int × Field)) : List (Int × Val) → Prop → Prop
  | [], acc => acc
  | (k, v) :: rest, acc => valWfFoldList ds rest (valWfFold ds k v acc)
end

/-- Helper shim: well-formedness for a single key-value pair. -/
def valWf (d : Desc) (kv : Int × Val) : Prop :=
  valWfFold d.fields kv.1 kv.2 True

theorem valWfFold_unfold (d : Desc) (key : Int) (val : Val) :
    valWfFold d.fields key val True =
    match d.fields.lookup key, val with
    | none, _ => True
    | some .bool, .bool _ => 0 ≤ key ∧ key < 256 ∧ True
    | some .int, .int z => True ∧ 0 ≤ key ∧ key < 256 ∧ 0 ≤ z ∧ z < 2 ^ 32
    | some (.msg d'), .msg val' => True ∧ 0 ≤ key ∧ key < 256 ∧ valueWf d' val'
    | _, _ => False := by
  convert rfl;
  unfold valWfFold;
  convert Iff.rfl

/-! ## Filtering and merging for serialization -/

/-- Merge function for combining a descriptor field with a value entry.
    Corresponds to `Merge` in the Rocq development. -/
def mergeFieldVal (f : Option Field) (v : Option Val) : Option Val :=
  match f, v with
  | some f, some v =>
    match f, v with
    | .bool, .bool b => some (.bool b)
    | .int, .int z => some (.int z)
    | .msg _, .msg v' => some (.msg v')
    | _, _ => none
  | some _, none => some .missing
  | none, _ => none

/-- Build a `Value` from a descriptor and a list of key-value pairs.
    Uses `merge` to combine the descriptor's fields with the parsed entries.
    Corresponds to `list_to_value` in the Rocq development. -/
def listToValue (d : Desc) (vs : List (Int × Val)) : Value :=
  .mk (listMerge mergeFieldVal d.fields vs)

/-- Predicate for filtering value entries against a descriptor. -/
def valListFilterP (d : Desc) (kv : Int × Val) : Bool :=
  match d.fields.lookup kv.1, kv.2 with
  | some _, .missing => false
  | none, _ => false
  | _, _ => true

/-- Filter a value's entries according to a descriptor: drop missing entries
    and entries for unknown fields.
    Corresponds to `ValList` in the Rocq development. -/
def valList (d : Desc) (v : Value) : List (Int × Val) :=
  v.vals.filter (valListFilterP d)

/-- Check if a field type and value type match. -/
def fieldValMatch (f : Field) (v : Val) : Prop :=
  match v, f with
  | .bool _, .bool | .int _, .int | .msg _, .msg _ => True
  | _, _ => False

/-- A key-value pair will be encoded: the field exists in the descriptor
    and the pair is well-formed. -/
def willEncode (d : Desc) (kv : Int × Val) : Prop :=
  ∃ f, d.fields.lookup kv.1 = some f ∧ valWf d kv

/-- All entries in a list will be encoded. -/
def serialValueListWf (d : Desc) (vs : List (Int × Val)) : Prop :=
  ∀ kv ∈ vs, willEncode d kv

/-- Filter function for combining descriptor fields with value entries,
    dropping missing values and unknown fields.
    Corresponds to `Filter` in the Rocq development. -/
def filterFieldVal (f : Option Field) (v : Option Val) : Option Val :=
  match f, v with
  | none, none => none
  | some _, some .missing => none
  | some _, none => none
  | none, some _ => none
  | some _, some v => some v

/-- Alternative value list using merge-based filtering.
    Corresponds to `ValList'` in the Rocq development. -/
def valList' (d : Desc) (v : Value) : List (Int × Val) :=
  listMerge filterFieldVal d.fields v.vals

/-! ## Depth bound lemma statements -/

theorem valInMap_smallerDepth (v : Value) (k : Int) (val : Value) :
    v.get? k = some (.msg val) → valueDepth val < valueDepth v := by
  intro h;
  obtain ⟨l, hl⟩ : ∃ l : List (Int × Val), v.vals = l ∧ ∃ x ∈ l, x.1 = k ∧ x.2 = Val.msg val := by
    simp_all +decide [ Value.get? ];
    grind +suggestions;
  obtain ⟨ hl₁, x, hx₁, hx₂, hx₃ ⟩ := hl;
  have h_depth : ∀ {l : List (Int × Val)} {acc : Nat}, x ∈ l → valueDepthList l acc ≥ Nat.max acc (valueDepth val + 1) := by
    intros l acc hx₁; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ valueDepthList ] ;
    cases hx₁ <;> simp_all +decide [ valueDepthFold ];
    · have h_depth : ∀ {l : List (Int × Val)} {acc : Nat}, valueDepthList l acc ≥ acc := by
        intros l acc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ valueDepthList ] ;
        exact le_trans ( by cases hd.2 <;> simp +decide [ valueDepthFold ] ) ( ih );
      exact ⟨ le_trans ( Nat.le_max_left _ _ ) ( h_depth ), lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( le_trans ( Nat.le_max_right _ _ ) ( h_depth ) ) ⟩;
    · exact le_trans ( by
        cases hd.2 <;> simp +decide [ valueDepthFold ] ) ( ih.1 );
  have h_depth : valueDepth v = valueDepthList l 0 := by
    cases v ; aesop;
  grind

theorem valueEncLen'Fold_linear (d : Desc) (k : Int) (v : Val) (acc : Nat) :
    valueEncLen'Fold d.fields k v acc = valueEncLen'Fold d.fields k v 0 + acc := by
  unfold valueEncLen'Fold;
  rcases h : List.lookup k d.fields with ( _ | _ | _ | _ | _ ) <;> rcases h' : v with ( _ | _ | _ | _ | _ ) <;> simp_all +arith +decide

end Pollux.InterParse